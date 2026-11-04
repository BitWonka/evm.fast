import InitECandidate.Solver.BinopRegisterBounded

namespace Flapjack.RiscV.TargetProof.Bounded
open Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-- Local signed truncation composition, retaining both original endpoints.
No separately named HOL original is claimed for this toInt proof. -/
private theorem imm_reconstruct (c : BitVec 64)
    (bounds : -2048 ≤ c.toInt ∧ c.toInt ≤ 2047) :
    (c.setWidth 12).signExtend 64 = c := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide : 12 ≤ 64)]
  have et := BitVec.toInt_signExtend_eq_toInt_bmod_of_le c (by decide : 12 ≤ 64)
  rw [BitVec.signExtend_eq_setWidth_of_le c (by decide : 12 ≤ 64)] at et
  rw [et]
  apply Int.bmod_eq_of_le <;> omega

/-- Original Sub's strict lower bound excludes signed12 negation overflow.
This is local infrastructure; the full constructor derives these bounds from
original asmOk and takes no additional range premise. -/
private theorem imm_neg_reconstruct (c : BitVec 64)
    (bounds : -2048 < c.toInt ∧ c.toInt ≤ 2047) :
    (-(c.setWidth 12)).signExtend 64 = -c := by
  have eq := imm_reconstruct c ⟨by omega, bounds.2⟩
  have trunc : (c.setWidth 12).toInt = c.toInt := by
    have t := congrArg BitVec.toInt eq
    simpa only [BitVec.toInt_signExtend_of_le (by decide : 12 ≤ 64)] using t
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide : 12 ≤ 64)]
  simp only [BitVec.toInt_neg, trunc]
  norm_num
  rw [Int.bmod_eq_of_le (by omega) (by omega),
    Int.bmod_eq_of_le (by omega) (by omega)]

private def binopImmInstruction (op : HolBinop) (rd rs : BitVec 5)
    (c : BitVec 64) : instruction :=
  match op with
  | .add => .ArithI (.ADDI (rd, rs, c.setWidth 12))
  | .sub => .ArithI (.ADDI (rd, rs, -(c.setWidth 12)))
  | .and => .ArithI (.ANDI (rd, rs, c.setWidth 12))
  | .or => .ArithI (.ORI (rd, rs, c.setWidth 12))
  | .xor => .ArithI (.XORI (rd, rs, c.setWidth 12))

private def binopImmWord (op : HolBinop) (rd rs : BitVec 5) (c : BitVec 64) : BitVec 32 :=
  Encode (binopImmInstruction op rd rs c)

private theorem binop_imm_decode (op : HolBinop) (rd rs : BitVec 5) (c : BitVec 64) :
    DecodeAny (.Word (binopImmWord op rd rs c)) = binopImmInstruction op rd rs c := by
  cases op
  · exact decode_encode_addi rd rs (c.setWidth 12)
  · exact decode_encode_addi rd rs (-(c.setWidth 12))
  · exact decode_encode_andi rd rs (c.setWidth 12)
  · exact decode_encode_ori rd rs (c.setWidth 12)
  · exact decode_encode_xori rd rs (c.setWidth 12)

private theorem binop_imm_low (op : HolBinop) (rd rs : BitVec 5) (c : BitVec 64) :
    (binopImmWord op rd rs c).getLsbD 0 = true ∧
      (binopImmWord op rd rs c).getLsbD 1 = true := by
  cases op <;> simp only [binopImmWord, binopImmInstruction, Encode, Itype, opc,
    BitVec.setWidth_eq, BitVec.getLsbD_append] <;> simp

private theorem binop_imm_run (op : HolBinop) (rd rs : BitVec 5) (c : BitVec 64)
    (ms : riscv_state) (guard : riscvConfig.validImm (.inl op) c = true) :
    Run (binopImmInstruction op rd rs c) ms =
      «write'GPR» (binopValue op (GPR rs ms) c, rd) ms := by
  cases op
  all_goals
    simp [riscvConfig, BitVec.sle_eq_decide, BitVec.slt_eq_decide] at guard
  case add =>
    have eq := imm_reconstruct c guard
    simp [binopImmInstruction, Run, «dfn'ADDI», binopValue, eq]
  case sub =>
    have eq := imm_neg_reconstruct c guard
    simp [binopImmInstruction, Run, «dfn'ADDI», binopValue, eq, BitVec.sub_eq_add_neg]
  case and =>
    have eq := imm_reconstruct c guard
    simp [binopImmInstruction, Run, «dfn'ANDI», binopValue, eq]
  case or =>
    have eq := imm_reconstruct c guard
    simp [binopImmInstruction, Run, «dfn'ORI», binopValue, eq]
  case xor =>
    have eq := imm_reconstruct c guard
    simp [binopImmInstruction, Run, «dfn'XORI», binopValue, eq]

/-- The original Xor -1 exception also satisfies the original inclusive
signed12 guard. This discharges the exception without narrowing asmOk. -/
private theorem imm_valid_of_ok (op : HolBinop) (c : BitVec 64)
    (h : asmRegImmOkExact (.inl op) (.imm c) riscvConfig = true) :
    riscvConfig.validImm (.inl op) c = true := by
  cases op <;> simp [asmRegImmOkExact] at h
  all_goals
    rcases h with h | h
    · rw [h.2]
      decide
    · exact h

private theorem imm_reg_nonzero (r : Nat) (guard : asmRegOkExact r riscvConfig = true) :
    BitVec.ofNat 5 r ≠ 0#5 := by
  have g : r < 32 ∧ r ≠ 0 := by
    have g := guard
    simp [asmRegOkExact, riscvConfig] at g
    exact ⟨of_decide_eq_true g.1, g.2.1⟩
  intro eq
  have n := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat] at n
  norm_num at n
  rw [Nat.mod_eq_of_lt g.1] at n
  exact g.2 n

private theorem imm_reg_read (r : Nat) (s : AsmState 64) (ms : riscv_state)
    (guard : asmRegOkExact r riscvConfig = true)
    (rel : targetStateRel riscvTarget s ms) :
    GPR (BitVec.ofNat 5 r) ms = readReg r s := by
  have g : r < riscvConfig.regCount ∧ riscvConfig.avoidRegs.contains r = false := by
    simpa [asmRegOkExact] using guard
  have before := rel.2.2.2.1 r g
  change ms.c_gpr ms.procID (BitVec.ofNat 5 r) = s.regs r at before
  simpa [GPR, gpr, imm_reg_nonzero r guard, readReg] using before

/-- Genuine original Imm operand case of riscv_encoder_correct's Binop branch
(550-559). All five operators, unrestricted natural registers, original sole
asmStep/initial relation premise, and full existential/interference/assertion
conclusion are retained. Actual native Next is derived from all four emitted
bytes and literal Decode/Run, never supplied as a premise. The separate Reg operand case is proved in BinopRegister. Native state/Run inherits SOUNDNESS item8. -/
theorem riscv_encoder_correct_binopImmediate_bounded (op : HolBinop) (rd rs1 : Nat) (c : BitVec 64) (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.inst (.arith (.binop op rd rs1 (.imm c)))) s2 ∧
      targetStateRel riscvTarget s1 ms) :
    ∃ n : Nat, n + 1 ≤ (riscvTarget.config.encode (.inst (.arith (.binop op rd rs1 (.imm c))))).length / 4 ∧
      ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (riscvTarget.proj s1.memDomain) →
      let pcs := allPcs (riscvTarget.config.encode (.inst (.arith (.binop op rd rs1 (.imm c))))).length s1.pc
      asserts n (fun k s => env (n - k) (riscvTarget.next s)) ms
        (fun ms' => riscvTarget.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
          riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
        (fun ms' => targetStateRel riscvTarget s2 ms') ∧
      asserts2 (n + 1) (fun k => env (n + 1 - k)) riscvTarget.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x) := by
  have hs := h.1
  change asmStep riscvConfig s1 (.inst (.arith (.binop op rd rs1 (.imm c)))) s2 at hs
  have guards : asmRegOkExact rd riscvConfig = true ∧
      asmRegOkExact rs1 riscvConfig = true ∧ asmRegImmOkExact (.inl op) (.imm c) riscvConfig = true := by
    simpa [asmOkExact, asmInstOkExact, asmArithOkExact,
      riscvConfig, Bool.and_eq_true, and_assoc] using hs.2.2.2.2.2.2
  have bound : rd < 32 := by
    have g := guards.1
    simp [asmRegOkExact, riscvConfig] at g
    exact of_decide_eq_true g.1
  let value := binopValue op (readReg rs1 s1) c
  have source : s2 = updPc (s1.pc + 4) (updReg rd value s1) := by
    rw [binop_source_post op rd rs1 (.imm c) s1 s2 hs]
    cases op <;> rfl
  have enc : riscvConfig.encode (.inst (.arith (.binop op rd rs1 (.imm c)))) =
      [RiscV.L3.holWordExtract 8 7 0 (binopImmWord op (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) c),
       RiscV.L3.holWordExtract 8 15 8 (binopImmWord op (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) c),
       RiscV.L3.holWordExtract 8 23 16 (binopImmWord op (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) c),
       RiscV.L3.holWordExtract 8 31 24 (binopImmWord op (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) c)] := by cases op <;> rfl
  have hb := hs.1
  rw [enc] at hb
  have bytes := bytes_in_memory_thm () s1 ms _ _ _ _ ⟨h.2, hb⟩
  have left := imm_reg_read rs1 s1 ms guards.2.1 h.2
  have valid := imm_valid_of_ok op c guards.2.2
  let fetched : riscv_state := {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}
  have run : Run (binopImmInstruction op (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) c) fetched =
      «write'GPR» (value, BitVec.ofNat 5 rd) fetched := by
    rw [binop_imm_run op _ _ c fetched valid]
    simpa [fetched, GPR, gpr, value] using congrArg
      (fun v => «write'GPR» (v, BitVec.ofNat 5 rd) fetched)
      (congrArg (fun v => binopValue op v c) left)
  have low := binop_imm_low op (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) c
  have hn := write_next ms _ _ (BitVec.ofNat 5 rd) value (imm_reg_nonzero rd guards.1)
    h.2.1 (binop_imm_decode op _ _ c) run low.1 low.2
    bytes.2.2.2.2.2.1 bytes.2.2.2.2.2.2.1
    bytes.2.2.2.2.2.2.2.1 bytes.2.2.2.2.2.2.2.2.1
  have next : riscvTarget.next ms = writePost ms (BitVec.ofNat 5 rd) value := by
    change holThe (NextRISCV ms) = _
    rw [hn]
    rfl
  rw [source]
  refine ⟨0, by
    change 0 + 1 ≤ (riscvConfig.encode _).length / 4
    rw [enc]; simp, ?_⟩
  intro env interference
  have hp := write_post_rel s1 ms rd value bound h.2
  have projection := interference 0 (writePost ms (BitVec.ofNat 5 rd) value)
  have transport := (riscv_target_ok.2 (env 0 (writePost ms (BitVec.ofNat 5 rd) value))
    (writePost ms (BitVec.ofNat 5 rd) value) (updPc (s1.pc + 4) (updReg rd value s1)) projection).1
  constructor
  · simpa [asserts, next] using transport.mpr hp
  · simp only [asserts2]
    rw [next]
    exact ⟨fun _ _ => rfl, trivial⟩

end Flapjack.RiscV.TargetProof.Bounded
