import InitECandidate.Solver.BinopRegisterBounded
import Flapjack.RiscV.CorrectnessEncoding.DecodeShift
import Flapjack.RiscV.CorrectnessEncoding.ShiftRun
import InitECandidate.Solver.Common

namespace Flapjack.RiscV.TargetProof.Bounded
open Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

private def shiftWord (rd rs1 rs2 : BitVec 5) : BitVec 32 :=
  Encode (.Shift (.SLL (rd, rs1, rs2)))

private theorem shift_low (rd rs1 rs2 : BitVec 5) :
    (shiftWord rd rs1 rs2).getLsbD 0 = true ∧
      (shiftWord rd rs1 rs2).getLsbD 1 = true := by
  simp only [shiftWord, Encode, Rtype, opc, BitVec.setWidth_eq,
    BitVec.getLsbD_append]
  simp

private theorem reg_nonzero (r : Nat) (guard : asmRegOkExact r riscvConfig = true) :
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

private theorem reg_read (r : Nat) (s : AsmState 64) (ms : riscv_state)
    (guard : asmRegOkExact r riscvConfig = true)
    (rel : targetStateRel riscvTarget s ms) :
    GPR (BitVec.ofNat 5 r) ms = readReg r s := by
  have g : r < riscvConfig.regCount ∧ riscvConfig.avoidRegs.contains r = false := by
    simpa [asmRegOkExact] using guard
  have before := rel.2.2.2.1 r g
  change ms.c_gpr ms.procID (BitVec.ofNat 5 r) = s.regs r at before
  simpa [GPR, gpr, reg_nonzero r guard, readReg] using before

/-- Original Shift Reg/Lsl case560-620. Sole original asmStep/initial relation
and full existential/interference/asserts/asserts2 conclusion are retained.
The source count bound and actual fetched Decode/Run/Next are derived, never
input assumptions. The other Shift cases are sibling pieces, all assembled by
riscv_encoder_correct_shift_bounded (Shift.lean). Native state/Run inherits
reals_as_rational_cuts, SOUNDNESS item8. -/
theorem riscv_encoder_correct_shiftLslRegister_bounded (rd rs1 rs2 : Nat) (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.inst (.arith (.shift .lsl rd rs1 (.reg rs2)))) s2 ∧
      targetStateRel riscvTarget s1 ms) :
    ∃ n : Nat, n + 1 ≤ (riscvTarget.config.encode (.inst (.arith (.shift .lsl rd rs1 (.reg rs2))))).length / 4 ∧
      ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (riscvTarget.proj s1.memDomain) →
      let pcs := allPcs (riscvTarget.config.encode (.inst (.arith (.shift .lsl rd rs1 (.reg rs2))))).length s1.pc
      asserts n (fun k s => env (n - k) (riscvTarget.next s)) ms
        (fun ms' => riscvTarget.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
          riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
        (fun ms' => targetStateRel riscvTarget s2 ms') ∧
      asserts2 (n + 1) (fun k => env (n + 1 - k)) riscvTarget.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x) := by
  have hs := h.1
  change asmStep riscvConfig s1 (.inst (.arith (.shift .lsl rd rs1 (.reg rs2)))) s2 at hs
  have guards : asmRegOkExact rd riscvConfig = true ∧
      asmRegOkExact rs1 riscvConfig = true ∧ asmRegOkExact rs2 riscvConfig = true := by
    simpa [asmOkExact, asmInstOkExact, asmArithOkExact, asmRegImmOkExact,
      riscvConfig, Bool.and_eq_true, and_assoc] using hs.2.2.2.2.2.2
  have bound : rd < 32 := by
    have g := guards.1
    simp [asmRegOkExact, riscvConfig] at g
    exact of_decide_eq_true g.1
  let value := (readReg rs1 s1) <<< (readReg rs2 s1).toNat
  have source : s2 = updPc (s1.pc + 4) (updReg rd value s1) := by
    rw [shift_source_post .lsl rd rs1 (.reg rs2) s1 s2 hs]
    rfl
  have enc : riscvConfig.encode (.inst (.arith (.shift .lsl rd rs1 (.reg rs2)))) =
      [RiscV.L3.holWordExtract 8 7 0 (shiftWord (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) (BitVec.ofNat 5 rs2)),
       RiscV.L3.holWordExtract 8 15 8 (shiftWord (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) (BitVec.ofNat 5 rs2)),
       RiscV.L3.holWordExtract 8 23 16 (shiftWord (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) (BitVec.ofNat 5 rs2)),
       RiscV.L3.holWordExtract 8 31 24 (shiftWord (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) (BitVec.ofNat 5 rs2))] := rfl
  have hb := hs.1
  rw [enc] at hb
  have bytes := bytes_in_memory_thm () s1 ms _ _ _ _ ⟨h.2, hb⟩
  have left := reg_read rs1 s1 ms guards.2.1 h.2
  have right := reg_read rs2 s1 ms guards.2.2 h.2
  let fetched : riscv_state := {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}
  have run : Run (.Shift (.SLL (BitVec.ofNat 5 rd, BitVec.ofNat 5 rs1, BitVec.ofNat 5 rs2))) fetched =
      «write'GPR» (value, BitVec.ofNat 5 rd) fetched := by
    have ok : riscvOk fetched = true := by
      have original : riscvOk ms = true := h.2.1
      simpa [fetched, riscvOk, MCSR, NextFetch, PC] using original
    rw [shift_run_sll _ _ _ fetched ok]
    have count := shift_source_count .lsl rd rs1 (.reg rs2) s1 s2 hs
    have bound : (readReg rs2 s1).toNat < 64 := by
      exact of_decide_eq_true count
    have mask : ((RiscV.L3.holWordExtract 6 5 0 (readReg rs2 s1)).setWidth 64).toNat =
        (readReg rs2 s1).toNat := by
      simp [RiscV.L3.holWordExtract, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt bound]
      omega
    have leftf : GPR (BitVec.ofNat 5 rs1) fetched = readReg rs1 s1 := by
      simpa [fetched, GPR, gpr] using left
    have rightf : GPR (BitVec.ofNat 5 rs2) fetched = readReg rs2 s1 := by
      simpa [fetched, GPR, gpr] using right
    rw [leftf, rightf, mask]
  have low := shift_low (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) (BitVec.ofNat 5 rs2)
  have hn := write_next ms _ _ (BitVec.ofNat 5 rd) value (reg_nonzero rd guards.1)
    h.2.1 (decode_encode_sll _ _ _) run low.1 low.2
    bytes.2.2.2.2.2.1 bytes.2.2.2.2.2.2.1
    bytes.2.2.2.2.2.2.2.1 bytes.2.2.2.2.2.2.2.2.1
  have next : riscvTarget.next ms = writePost ms (BitVec.ofNat 5 rd) value := by
    change holThe (NextRISCV ms) = _
    rw [hn]
    rfl
  rw [source]
  refine ⟨0, Flapjack.RiscV.TargetProof.Bounded.one_le_words _, ?_⟩
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
