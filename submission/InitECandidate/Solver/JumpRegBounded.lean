import InitECandidate.Solver.SkipBounded
import Flapjack.RiscV.L3.Defs.UpperJump
import InitECandidate.Solver.Common

/-! Full original JumpReg constructor case. Native decoding and execution are
derived from emitted bytes; no target evaluation is assumed. Native Run
inherits the reviewed reals_as_rational_cuts assumption (SOUNDNESS item 8). -/
namespace Flapjack.RiscV.TargetProof.Bounded
open Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target

/-- Flapjack native encoding abbreviation, preserving every original register. -/
private def jumpWord (r : BitVec 5) : BitVec 32 := Encode (.Branch (.JALR (0,r,0)))

/-- Complete native decoder reduction for all original five-bit registers. -/
private theorem jump_decode (r : BitVec 5) :
    DecodeAny (.Word (jumpWord r)) = .Branch (.JALR (0,r,0)) := by
  revert r
  decide

/-- All register encodings share the original uncompressed JALR low byte. -/
private theorem jump_low (r : BitVec 5) : RiscV.L3.holWordExtract 8 7 0 (jumpWord r) = 103 := by
  revert r
  decide

/-- Exact reconstruction of the native word from its four original encoded bytes. -/
private theorem jump_reassemble (r : BitVec 5) :
    RiscV.L3.holWordExtract 8 31 24 (jumpWord r) ++
      (RiscV.L3.holWordExtract 8 23 16 (jumpWord r) ++
        (RiscV.L3.holWordExtract 8 15 8 (jumpWord r) ++ (103 : BitVec 8))) = jumpWord r := by
  revert r
  decide

/-- Bare VM full Fetch over four actual bytes of the original JALR encoding. -/
private theorem jump_fetch (ms : riscv_state) (r : BitVec 5)
    (vm : (ms.c_MCSR ms.procID).mstatus.VM = 0)
    (b0 : ms.MEM8 (ms.c_PC ms.procID) = RiscV.L3.holWordExtract 8 7 0 (jumpWord r))
    (b1 : ms.MEM8 (ms.c_PC ms.procID + 1) = RiscV.L3.holWordExtract 8 15 8 (jumpWord r))
    (b2 : ms.MEM8 (ms.c_PC ms.procID + 2) = RiscV.L3.holWordExtract 8 23 16 (jumpWord r))
    (b3 : ms.MEM8 (ms.c_PC ms.procID + 3) = RiscV.L3.holWordExtract 8 31 24 (jumpWord r)) :
    Fetch ms = (.Word (jumpWord r), {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}) := by
  rw [jump_low] at b0
  change ms.MEM8 (ms.c_PC ms.procID + 1#64) = _ at b1
  change ms.MEM8 (ms.c_PC ms.procID + 2#64) = _ at b2
  change ms.MEM8 (ms.c_PC ms.procID + 3#64) = _ at b3
  rw [fetch_bare ms vm]
  simp [rawReadInst, boolify8, b0, b1, b2, b3, «write'Skip»]
  exact jump_reassemble r

/-- Original four-byte alignment discharges the target's low-bit branch check. -/
private theorem aligned_low (pc : BitVec 64) (h : holAligned 2 pc = true) :
    pc.getLsbD 0 = false := by
  have he := of_decide_eq_true h
  rw [← he, holAlign_eq_shift]
  simp

/-- Literal original JALR mask is identity under the source alignment condition. -/
private theorem aligned_mask (pc : BitVec 64) (h : holAligned 2 pc = true) :
    pc &&& BitVec.signExtend 64 (2#2) = pc := by
  have low := aligned_low pc h
  have lowElem : pc[0] = false := by simpa using low
  have mask : BitVec.signExtend 64 (2#2) = (18446744073709551614 : BitVec 64) := by decide
  rw [mask]
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  interval_cases i <;> simp [lowElem]

/-- Full literal JALR Run reads the original register before setting branch control. -/
private theorem jump_run (ms : riscv_state) (r : BitVec 5)
    (h : holAligned 2 (GPR r ms) = true) :
    Run (.Branch (.JALR (0,r,0))) ms =
      {ms with c_NextFetch := holUpdate ms.procID (some (.BranchTo (GPR r ms))) ms.c_NextFetch} := by
  have hm : GPR r ms &&& (18446744073709551614#64) = GPR r ms := by
    simpa using aligned_mask (GPR r ms) h
  simp [Run, «dfn'JALR», «write'GPR», branchTo, «write'NextFetch»]
  rw [hm]

/-- Exact native post-record for a branch, retaining every unrelated source field. -/
private def jumpPost (ms : riscv_state) (a : BitVec 64) : riscv_state :=
  {ms with
    c_Skip := holUpdate ms.procID 4 ms.c_Skip
    c_PC := holUpdate ms.procID a ms.c_PC}

/-- Actual full native Next derived from source validity, encoding bytes and alignment. -/
private theorem jump_next (ms : riscv_state) (r : BitVec 5) (ok : riscvOk ms = true)
    (aligned : holAligned 2 (GPR r ms) = true)
    (b0 : ms.MEM8 (ms.c_PC ms.procID) = RiscV.L3.holWordExtract 8 7 0 (jumpWord r))
    (b1 : ms.MEM8 (ms.c_PC ms.procID + 1) = RiscV.L3.holWordExtract 8 15 8 (jumpWord r))
    (b2 : ms.MEM8 (ms.c_PC ms.procID + 2) = RiscV.L3.holWordExtract 8 23 16 (jumpWord r))
    (b3 : ms.MEM8 (ms.c_PC ms.procID + 3) = RiscV.L3.holWordExtract 8 31 24 (jumpWord r)) :
    NextRISCV ms = some (jumpPost ms (GPR r ms)) := by
  have fields := (riscvOk_iff ms).mp ok
  let fetched : riscv_state := {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}
  have hf := jump_fetch ms r fields.1 b0 b1 b2 b3
  have hrun := jump_run fetched r aligned
  have hn := nextRISCV_branch ms (.Word (jumpWord r)) fetched
    (.Branch (.JALR (0,r,0)))
    {fetched with
      c_NextFetch := holUpdate fetched.procID
        (some (.BranchTo (GPR r fetched))) fetched.c_NextFetch}
    (GPR r ms) ⟨hf, jump_decode r, hrun, fields.2.2.2.1, by simp [fetched, holUpdate, GPR, gpr]⟩
  have clear : holUpdate ms.procID none
      (holUpdate ms.procID (some (.BranchTo (GPR r ms))) ms.c_NextFetch) = ms.c_NextFetch := by
    funext key
    by_cases he : ms.procID = key
    · subst key
      simpa [holUpdate] using fields.2.2.1.symm
    · simp [holUpdate, he]
  change NextRISCV ms = some {ms with
    c_Skip := holUpdate ms.procID 4 ms.c_Skip
    c_PC := holUpdate ms.procID (GPR r ms) ms.c_PC
    c_NextFetch := holUpdate ms.procID none
        (holUpdate ms.procID (some (.BranchTo (GPR r ms))) ms.c_NextFetch)} at hn
  rw [clear] at hn
  exact hn

/-- Native post-relation keeps all memory/register fields and proves source target validity. -/
private theorem jump_post_rel (s : AsmState 64) (ms : riscv_state) (a : BitVec 64)
    (hr : targetStateRel riscvTarget s ms) (ha : holAligned 2 a = true) :
    targetStateRel riscvTarget (updPc a s) (jumpPost ms a) := by
  rcases hr with ⟨ok, pc, mem, regs, fp⟩
  have fields := (riscvOk_iff ms).mp ok
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply (riscvOk_iff _).mpr
    simpa [jumpPost, holUpdate] using
      ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1, ha⟩
  · change (jumpPost ms a).c_PC (jumpPost ms a).procID = a
    simp [jumpPost, holUpdate]
  · exact mem
  · exact regs
  · intro i hi
    change i < 0 at hi
    omega

/-- Full original JumpReg constructor case (riscv_targetProofScript730-736),
with the complete encoder_correct_def117-133 premise and conclusion. The
natural register is unrestricted in the statement; its bound and zero exclusion
come only from the original asmOk guard. Source nonfailure derives alignment,
actual native Fetch/DecodeAny/Run/Next derives execution, and original targetOk
transports the full post-relation under every interference environment. The
original zero assertion witness retains both full assertion predicates. -/
theorem riscv_encoder_correct_jumpReg_bounded (r : Nat) (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.jumpReg r) s2 ∧
      targetStateRel riscvTarget s1 ms) :
    ∃ n : Nat, n + 1 ≤ (riscvTarget.config.encode (.jumpReg r)).length / 4 ∧
      ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (riscvTarget.proj s1.memDomain) →
      let pcs := allPcs (riscvTarget.config.encode (.jumpReg r)).length s1.pc
      asserts n (fun k s => env (n - k) (riscvTarget.next s)) ms
        (fun ms' => riscvTarget.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
          riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
        (fun ms' => targetStateRel riscvTarget s2 ms') ∧
      asserts2 (n + 1) (fun k => env (n + 1 - k)) riscvTarget.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x) := by
  have hs := h.1
  change asmStep riscvConfig s1 (.jumpReg r) s2 at hs
  have enc : riscvConfig.encode (.jumpReg r) =
      [RiscV.L3.holWordExtract 8 7 0 (jumpWord (BitVec.ofNat 5 r)),
       RiscV.L3.holWordExtract 8 15 8 (jumpWord (BitVec.ofNat 5 r)),
       RiscV.L3.holWordExtract 8 23 16 (jumpWord (BitVec.ofNat 5 r)),
       RiscV.L3.holWordExtract 8 31 24 (jumpWord (BitVec.ofNat 5 r))] := rfl
  have guard : r < riscvConfig.regCount ∧ riscvConfig.avoidRegs.contains r = false := by
    simpa [asmOkExact, asmRegOkExact] using hs.2.2.2.2.2.2
  have hbound : r < 32 := guard.1
  have rn : r ≠ 0 := by
    have avoid := guard.2
    simp [riscvConfig] at avoid
    exact avoid.1
  have word_nonzero : BitVec.ofNat 5 r ≠ (0#5) := by
    intro hz
    have hn := congrArg BitVec.toNat hz
    simp only [BitVec.toNat_ofNat] at hn
    norm_num at hn
    have small : r % 32 = r := Nat.mod_eq_of_lt hbound
    omega
  have hreg := h.2.2.2.2.1 r guard
  change ms.c_gpr ms.procID (BitVec.ofNat 5 r) = s1.regs r at hreg
  have reg : GPR (BitVec.ofNat 5 r) ms = s1.regs r := by
    simpa [GPR, gpr, word_nonzero] using hreg
  have step := hs.2.2.2.2.1
  have failed := hs.2.2.2.2.2.1
  rw [← step] at failed
  simp [asmUpd, updPc, assertState] at failed
  have aligned : holAligned 2 (s1.regs r) = true := by
    have ha := failed.1
    have align := hs.2.2.2.1
    change s1.align = 2 at align
    simpa [readReg, align] using ha
  have he : s2 = updPc (s1.regs r) s1 := by
    have align := hs.2.2.2.1
    change s1.align = 2 at align
    simpa [asmUpd, assertState, updPc, readReg, align, aligned] using step.symm
  have hb := hs.1
  rw [enc] at hb
  have bytes := bytes_in_memory_thm () s1 ms _ _ _ _ ⟨h.2, hb⟩
  have native_align : holAligned 2 (GPR (BitVec.ofNat 5 r) ms) = true := by rw [reg]; exact aligned
  have hn := jump_next ms (BitVec.ofNat 5 r) h.2.1 native_align
    bytes.2.2.2.2.2.1 bytes.2.2.2.2.2.2.1
    bytes.2.2.2.2.2.2.2.1 bytes.2.2.2.2.2.2.2.2.1
  have next : riscvTarget.next ms = jumpPost ms (s1.regs r) := by
    change holThe (NextRISCV ms) = jumpPost ms (s1.regs r)
    rw [hn, reg]
    rfl
  rw [he]
  refine ⟨0, Flapjack.RiscV.TargetProof.Bounded.one_le_words _, ?_⟩
  intro env interference
  have hp := jump_post_rel s1 ms (s1.regs r) h.2 aligned
  have projection := interference 0 (jumpPost ms (s1.regs r))
  have transport := (riscv_target_ok.2 (env 0 (jumpPost ms (s1.regs r)))
    (jumpPost ms (s1.regs r)) (updPc (s1.regs r) s1) projection).1
  constructor
  · simpa [asserts, next] using transport.mpr hp
  · simp only [asserts2]
    rw [next]
    exact ⟨fun _ _ => rfl, trivial⟩

end Flapjack.RiscV.TargetProof.Bounded
