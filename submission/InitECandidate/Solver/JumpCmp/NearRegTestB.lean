import Flapjack.RiscV.CorrectnessEncoding.JumpCmp.Prefix
import Flapjack.RiscV.CorrectnessEncoding.JumpCmp.Arithmetic
import InitECandidate.Solver.Common
import InitECandidate.Solver.Words
import InitECandidate.Solver.Ranges

/-! Near register Test JumpCmp execution, derived from original source asmStep.
Untagged local assembly; the complete constructor also covers Reg and far. -/
namespace Flapjack.RiscV.TargetProof.Bounded.JumpCmp
set_option linter.unusedSimpArgs false
open Flapjack.RiscV.TargetProof.JumpCmp Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps Compiler.Encoders.RiscV.Target

def register_test_value (_c : Cmp) (r t : Nat) (s : AsmState 64) : BitVec 64 :=
  readReg r s &&& readReg t s

theorem near_register_test_first (c : Cmp) (r t : Nat) (a : BitVec 64)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.jumpCmp c r (.reg t) a) s2 ∧
      targetStateRel riscvTarget s1 ms)
    (range : -4092 ≤ a.toInt ∧ a.toInt ≤ 4095)
    (test : c = .test ∨ c = .notTest) :
    riscvTarget.next ms = writePost ms (31#5) (register_test_value c r t s1) := by
  have hs : asmStep riscvConfig s1 (.jumpCmp c r (.reg t) a) s2 := h.1
  have guard := source_guard c r (.reg t) a hs.2.2.2.2.2.2
  have read := reg_read r s1 ms guard.2.2.1 h.2
  have encoded := hs.1
  rw [near_register_test_encoding c r t a range test, bytesInMemory_append] at encoded
  have bytes := instruction_bytes s1 ms _ h.2 encoded.1
  have rightguard : asmRegOkExact t riscvConfig = true := by
    simpa [asmRegImmOkExact] using guard.2.2.2
  have rightread := reg_read t s1 ms rightguard h.2
  have next := next_encoded_and ms (31#5) (BitVec.ofNat 5 r) (BitVec.ofNat 5 t)
    (by decide) h.2.1 bytes
  change holThe (NextRISCV ms) = _
  rw [next, read, rightread]
  rfl

def register_test_dest (c : Cmp) (r t : Nat) (a : BitVec 64) (s : AsmState 64) : BitVec 64 :=
  if wordCmpHOL c (readReg r s) (readReg t s) then s.pc + a else s.pc + 8

theorem near_register_test_second (c : Cmp) (r t : Nat) (a : BitVec 64)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.jumpCmp c r (.reg t) a) s2 ∧
      targetStateRel riscvTarget s1 ms)
    (range : -4092 ≤ a.toInt ∧ a.toInt ≤ 4095)
    (test : c = .test ∨ c = .notTest)
    (env : Nat → riscv_state → riscv_state)
    (interference : interferenceOk env (riscvTarget.proj s1.memDomain)) :
    riscvTarget.next (env 0 (writePost ms (31#5) (register_test_value c r t s1))) =
      Jump.branchPost (env 0 (writePost ms (31#5) (register_test_value c r t s1)))
        (register_test_dest c r t a s1) := by
  have hs : asmStep riscvConfig s1 (.jumpCmp c r (.reg t) a) s2 := h.1
  have guard := source_guard c r (.reg t) a hs.2.2.2.2.2.2
  let value := register_test_value c r t s1
  let mid := env 0 (writePost ms (31#5) value)
  let src := updPc (s1.pc + 4) (updReg 31 value s1)
  have midrel : targetStateRel riscvTarget src mid :=
    scratch_interference_rel s1 ms value env h.2 interference
  have scratch : GPR (31#5) mid = value :=
    scratch_after_interference ms value s1.memDomain env interference
  have pc : mid.c_PC mid.procID = s1.pc + 4 := midrel.2.1
  have encoded := hs.1
  rw [near_register_test_encoding c r t a range test] at encoded
  have bytes := scratch_sequence_bytes s1 ms value _ _ env h.2 interference encoded
  have next := test_branch_next c (readReg r s1) (readReg t s1)
    ((a.sshiftRight 1).setWidth 12 - 2) mid midrel.1 test scratch bytes.2
  have offset : s1.pc + 4 +
      (((a.sshiftRight 1).setWidth 12 - 2).signExtend 64 <<< (1 : Nat)) = s1.pc + a := by
    simpa using near_offset_prefix4_pc s1.pc a range guard.2.1
  have fall : s1.pc + 4 + 4 = s1.pc + 8 := by
    simp only [BitVec.add_assoc]; rfl
  change holThe (NextRISCV mid) = _
  rw [next, pc, offset, fall]
  rfl

theorem near_register_test_post (c : Cmp) (r t : Nat) (a : BitVec 64)
    (s1 s2 : AsmState 64)
    (hs : asmStep riscvConfig s1 (.jumpCmp c r (.reg t) a) s2)
    (range : -4092 ≤ a.toInt ∧ a.toInt ≤ 4095)
    (test : c = .test ∨ c = .notTest) :
    s2 = updPc (register_test_dest c r t a s1) s1 := by
  have original := source_post c r (.reg t) a s1 s2 hs
  rw [near_register_test_encoding c r t a range test] at original
  dsimp [register_test_dest]
  split <;> rename_i chosen
  all_goals simpa [riscvEncode, regImm, chosen] using original

theorem near_register_test_case (c : Cmp) (r t : Nat) (a : BitVec 64)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.jumpCmp c r (.reg t) a) s2 ∧
      targetStateRel riscvTarget s1 ms)
    (range : -4092 ≤ a.toInt ∧ a.toInt ≤ 4095)
    (test : c = .test ∨ c = .notTest) :
    ∃ n : Nat, n + 1 ≤ (riscvTarget.config.encode (.jumpCmp c r (.reg t) a)).length / 4 ∧
      ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (riscvTarget.proj s1.memDomain) →
      let pcs := allPcs (riscvTarget.config.encode (.jumpCmp c r (.reg t) a)).length s1.pc
      asserts n (fun k s => env (n-k) (riscvTarget.next s)) ms
        (fun ms' => riscvTarget.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
          riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
        (fun ms' => targetStateRel riscvTarget s2 ms') ∧
      asserts2 (n+1) (fun k => env (n+1-k)) riscvTarget.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x) := by
  refine ⟨1, by
    first
    | (rw [Flapjack.RiscV.TargetProof.Bounded.words_eq]; simp_all [riscvAst]; done)
    | (rw [Flapjack.RiscV.TargetProof.Bounded.words_eq]
       simp only [riscvAst, Flapjack.RiscV.TargetProof.Bounded.inSignedRange_eq, Flapjack.RiscV.TargetProof.Bounded.toInt_jlo, Flapjack.RiscV.TargetProof.Bounded.toInt_jhi, Flapjack.RiscV.TargetProof.Bounded.toInt_clo, Flapjack.RiscV.TargetProof.Bounded.toInt_clo', Flapjack.RiscV.TargetProof.Bounded.toInt_chi, Flapjack.RiscV.TargetProof.Bounded.toInt_jlo', Flapjack.RiscV.TargetProof.Bounded.toInt_jhi', Flapjack.RiscV.TargetProof.Bounded.toInt_chi', decide_eq_true_eq]
       split <;> first | omega | (simp_all; done) | (cases c <;> simp_all)), ?_⟩
  intro env interference
  have hs : asmStep riscvConfig s1 (.jumpCmp c r (.reg t) a) s2 := h.1
  let value := register_test_value c r t s1
  let mid := writePost ms (31#5) value
  let src := updPc (s1.pc + 4) (updReg 31 value s1)
  let dest := register_test_dest c r t a s1
  have first : riscvTarget.next ms = mid := near_register_test_first c r t a s1 s2 ms h range test
  have second : riscvTarget.next (env 0 mid) = Jump.branchPost (env 0 mid) dest :=
    near_register_test_second c r t a s1 s2 ms h range test env interference
  have rel : targetStateRel riscvTarget src (env 0 mid) :=
    scratch_interference_rel s1 ms value env h.2 interference
  have guard := source_guard c r (.reg t) a hs.2.2.2.2.2.2
  have initial_aligned : holAligned 2 s1.pc = true := by
    have pc : ms.c_PC ms.procID = s1.pc := h.2.2.1
    simpa [pc] using (riscvOk_iff ms).mp h.2.1 |>.2.2.2.2
  have aligned : holAligned 2 dest = true := by
    dsimp [dest, register_test_dest]
    split
    · exact Jump.aligned_add s1.pc a initial_aligned guard.2.1
    · exact Jump.aligned_add s1.pc 8 initial_aligned (by decide)
  have post := near_register_test_post c r t a s1 s2 hs range test
  have finalrel := scratch_branch_final_rel s1 ms value dest env h.2 aligned interference
  rw [← post] at finalrel
  have code : ∀ pc, pc ∈ allPcs (riscvConfig.encode (.jumpCmp c r (.reg t) a)).length s1.pc 0 →
      riscvTarget.getByte (env 0 mid) pc = riscvTarget.getByte ms pc := by
    intro pc covered
    have domain := bytesInMemory_allPcs _ _ _ _ 0 hs.1 covered
    exact (rel.2.2.1 pc domain).trans (h.2.2.2.1 pc domain).symm
  have length : (riscvConfig.encode (.jumpCmp c r (.reg t) a)).length = 8 := by
    rw [near_register_test_encoding c r t a range test]
    simp [riscvEncode]
  have pc : riscvTarget.getPc (env 0 mid) ∈
      allPcs (riscvConfig.encode (.jumpCmp c r (.reg t) a)).length s1.pc riscvConfig.codeAlignment := by
    have address := rel.2.1
    change riscvTarget.getPc (env 0 mid) = s1.pc + 4 at address
    rw [address, allPcs_eq, length]
    refine ⟨1, ?_, ?_⟩
    · norm_num [riscvConfig]
    · rfl
  constructor
  · simpa [asserts, first, second] using ⟨⟨rel.1, code, pc⟩, finalrel⟩
  · simp only [asserts2]
    rw [first]
    change (∀ x, ¬s1.memDomain x → ms.MEM8 x = mid.MEM8 x) ∧
      (∀ x, ¬s1.memDomain x → (env 0 mid).MEM8 x =
        (riscvTarget.next (env 0 mid)).MEM8 x) ∧ True
    rw [second]
    exact ⟨fun _ _ => rfl, fun _ _ => rfl, trivial⟩

end Flapjack.RiscV.TargetProof.Bounded.JumpCmp
