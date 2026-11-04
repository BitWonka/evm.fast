import InitECandidate.Solver.JumpCmp.NearRegTestB
import Flapjack.RiscV.CorrectnessEncoding.JumpCmp.FarNative
import InitECandidate.Solver.Common
import InitECandidate.Solver.Words
import InitECandidate.Solver.Ranges

/-! Far register Test JumpCmp actual prefix and control steps. Untagged local
assembly retains original source premises; the full constructor discharges far. -/
namespace Flapjack.RiscV.TargetProof.Bounded.JumpCmp
set_option linter.unusedSimpArgs false
open Flapjack.RiscV.TargetProof.JumpCmp Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps Compiler.Encoders.RiscV.Target

theorem far_register_test_first (c : Cmp) (r t : Nat) (a : BitVec 64)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.jumpCmp c r (.reg t) a) s2 ∧
      targetStateRel riscvTarget s1 ms)
    (far : ¬(-4092 ≤ a.toInt ∧ a.toInt ≤ 4095))
    (test : c = .test ∨ c = .notTest) :
    riscvTarget.next ms = writePost ms (31#5) (register_test_value c r t s1) := by
  have hs : asmStep riscvConfig s1 (.jumpCmp c r (.reg t) a) s2 := h.1
  have guard := source_guard c r (.reg t) a hs.2.2.2.2.2.2
  have read := reg_read r s1 ms guard.2.2.1 h.2
  have encoded := hs.1
  rw [far_register_test_encoding c r t a far test, bytesInMemory_append] at encoded
  rw [bytesInMemory_append] at encoded
  have bytes := instruction_bytes s1 ms _ h.2 encoded.1.1
  have rightguard : asmRegOkExact t riscvConfig = true := by
    simpa [asmRegImmOkExact] using guard.2.2.2
  have rightread := reg_read t s1 ms rightguard h.2
  have next := next_encoded_and ms (31#5) (BitVec.ofNat 5 r) (BitVec.ofNat 5 t)
    (by decide) h.2.1 bytes
  change holThe (NextRISCV ms) = _
  rw [next, read, rightread]
  rfl

theorem far_register_test_second (c : Cmp) (r t : Nat) (a : BitVec 64)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.jumpCmp c r (.reg t) a) s2 ∧
      targetStateRel riscvTarget s1 ms)
    (far : ¬(-4092 ≤ a.toInt ∧ a.toInt ≤ 4095))
    (test : c = .test ∨ c = .notTest)
    (env : Nat → riscv_state → riscv_state)
    (interference : interferenceOk env (riscvTarget.proj s1.memDomain)) :
    riscvTarget.next (env 0 (writePost ms (31#5) (register_test_value c r t s1))) =
      Jump.branchPost (env 0 (writePost ms (31#5) (register_test_value c r t s1)))
        (if wordCmpHOL c (readReg r s1) (readReg t s1) then s1.pc + 8 else s1.pc + 12) := by
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
  rw [far_register_test_encoding c r t a far test] at encoded
  rw [bytesInMemory_append] at encoded
  have bytes := scratch_sequence_bytes s1 ms value _ _ env h.2 interference encoded.1
  have next := inverse_test_branch_next c (readReg r s1) (readReg t s1)
    mid midrel.1 test scratch bytes.2
  have four : s1.pc + 4 + 4 = s1.pc + 8 := by
    simp only [BitVec.add_assoc]; rfl
  have eight : s1.pc + 4 + 8 = s1.pc + 12 := by
    simp only [BitVec.add_assoc]; rfl
  change holThe (NextRISCV mid) = _
  rw [next, pc, four, eight]
  rfl

theorem far_register_test_post (c : Cmp) (r t : Nat) (a : BitVec 64)
    (s1 s2 : AsmState 64)
    (hs : asmStep riscvConfig s1 (.jumpCmp c r (.reg t) a) s2)
    (far : ¬(-4092 ≤ a.toInt ∧ a.toInt ≤ 4095))
    (test : c = .test ∨ c = .notTest) :
    s2 = updPc (if wordCmpHOL c (readReg r s1) (readReg t s1) then s1.pc + a else s1.pc + 12) s1 := by
  have original := source_post c r (.reg t) a s1 s2 hs
  rw [far_register_test_encoding c r t a far test] at original
  split <;> rename_i chosen
  all_goals simpa [riscvEncode, regImm, chosen] using original

theorem far_register_test_false_case (c : Cmp) (r t : Nat) (a : BitVec 64)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.jumpCmp c r (.reg t) a) s2 ∧
      targetStateRel riscvTarget s1 ms)
    (far : ¬(-4092 ≤ a.toInt ∧ a.toInt ≤ 4095))
    (test : c = .test ∨ c = .notTest)
    (chosen : wordCmpHOL c (readReg r s1) (readReg t s1) = false) :
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
  let dest := s1.pc + 12
  have first : riscvTarget.next ms = mid := far_register_test_first c r t a s1 s2 ms h far test
  have second : riscvTarget.next (env 0 mid) = Jump.branchPost (env 0 mid) dest :=
    by simpa [dest, chosen] using far_register_test_second c r t a s1 s2 ms h far test env interference
  have rel : targetStateRel riscvTarget src (env 0 mid) :=
    scratch_interference_rel s1 ms value env h.2 interference
  have initial_aligned : holAligned 2 s1.pc = true := by
    have pc : ms.c_PC ms.procID = s1.pc := h.2.2.1
    simpa [pc] using (riscvOk_iff ms).mp h.2.1 |>.2.2.2.2
  have aligned : holAligned 2 dest = true :=
    Jump.aligned_add s1.pc 12 initial_aligned (by decide)
  have post : s2 = updPc dest s1 := by
    simpa [dest, chosen] using far_register_test_post c r t a s1 s2 hs far test
  have finalrel := scratch_branch_final_rel s1 ms value dest env h.2 aligned interference
  rw [← post] at finalrel
  have code : ∀ pc, pc ∈ allPcs (riscvConfig.encode (.jumpCmp c r (.reg t) a)).length s1.pc 0 →
      riscvTarget.getByte (env 0 mid) pc = riscvTarget.getByte ms pc := by
    intro pc covered
    have domain := bytesInMemory_allPcs _ _ _ _ 0 hs.1 covered
    exact (rel.2.2.1 pc domain).trans (h.2.2.2.1 pc domain).symm
  have length : (riscvConfig.encode (.jumpCmp c r (.reg t) a)).length = 12 := by
    rw [far_register_test_encoding c r t a far test]
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

theorem far_register_test_third (c : Cmp) (r t : Nat) (a : BitVec 64)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.jumpCmp c r (.reg t) a) s2 ∧
      targetStateRel riscvTarget s1 ms)
    (far : ¬(-4092 ≤ a.toInt ∧ a.toInt ≤ 4095))
    (test : c = .test ∨ c = .notTest)
    (env : Nat → riscv_state → riscv_state)
    (interference : interferenceOk env (riscvTarget.proj s1.memDomain)) :
    let mid := env 1 (Jump.branchPost
      (env 0 (writePost ms (31#5) (register_test_value c r t s1))) (s1.pc + 8))
    riscvTarget.next mid = Jump.branchPost mid (s1.pc + a) := by
  dsimp only
  have hs : asmStep riscvConfig s1 (.jumpCmp c r (.reg t) a) s2 := h.1
  have guard := source_guard c r (.reg t) a hs.2.2.2.2.2.2
  have initial_pc : ms.c_PC ms.procID = s1.pc := h.2.2.1
  have initial_aligned : holAligned 2 s1.pc = true := by
    simpa [initial_pc] using (riscvOk_iff ms).mp h.2.1 |>.2.2.2.2
  have eight_aligned := Jump.aligned_add s1.pc 8 initial_aligned (by decide)
  have target_aligned := Jump.aligned_add s1.pc a initial_aligned guard.2.1
  let mid := env 1 (Jump.branchPost
    (env 0 (writePost ms (31#5) (register_test_value c r t s1))) (s1.pc + 8))
  let src := updPc (s1.pc + 8) s1
  have rel : targetStateRel riscvTarget src mid :=
    scratch_branch_final_rel s1 ms (register_test_value c r t s1) (s1.pc + 8)
      env h.2 eight_aligned interference
  have encoded := hs.1
  rw [far_register_test_encoding c r t a far test, bytesInMemory_append] at encoded
  have sourcebytes : bytesInMemoryHOL src.pc
      (riscvEncode (.Branch (.JAL (0,((a.sshiftRight 1).setWidth 20 - 2) - 2)))) src.mem src.memDomain := by
    simpa [src, updPc, riscvEncode] using encoded.2
  have bytes := instruction_bytes src mid _ rel sourcebytes
  have pc : mid.c_PC mid.procID = s1.pc + 8 := rel.2.1
  have offset : s1.pc + 8 +
      ((((a.sshiftRight 1).setWidth 20 - 2) - 2).signExtend 64 <<< (1 : Nat)) = s1.pc + a := by
    simpa [BitVec.sub_sub, BitVec.add_assoc] using far_offset_prefix8_pc s1.pc a guard.1 guard.2.1
  have aligned : holAligned 2 (mid.c_PC mid.procID +
      ((((a.sshiftRight 1).setWidth 20 - 2) - 2).signExtend 64 <<< (1 : Nat))) = true := by
    rw [pc, offset]
    exact target_aligned
  have next := Jump.near_jump_next mid (((a.sshiftRight 1).setWidth 20 - 2) - 2)
    rel.1 aligned bytes.1 bytes.2.1 bytes.2.2.1 bytes.2.2.2
  change holThe (NextRISCV mid) = _
  rw [next, pc, offset]
  rfl

theorem far_register_test_true_case (c : Cmp) (r t : Nat) (a : BitVec 64)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.jumpCmp c r (.reg t) a) s2 ∧
      targetStateRel riscvTarget s1 ms)
    (far : ¬(-4092 ≤ a.toInt ∧ a.toInt ≤ 4095))
    (test : c = .test ∨ c = .notTest)
    (chosen : wordCmpHOL c (readReg r s1) (readReg t s1) = true) :
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
  refine ⟨2, by
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
  let branch := Jump.branchPost (env 0 mid) (s1.pc + 8)
  let src2 := updPc (s1.pc + 8) s1
  have first : riscvTarget.next ms = mid := far_register_test_first c r t a s1 s2 ms h far test
  have second : riscvTarget.next (env 0 mid) = branch := by
    simpa [branch, chosen] using far_register_test_second c r t a s1 s2 ms h far test env interference
  have third : riscvTarget.next (env 1 branch) = Jump.branchPost (env 1 branch) (s1.pc + a) :=
    far_register_test_third c r t a s1 s2 ms h far test env interference
  have rel : targetStateRel riscvTarget src (env 0 mid) :=
    scratch_interference_rel s1 ms value env h.2 interference
  have initial_pc : ms.c_PC ms.procID = s1.pc := h.2.2.1
  have initial_aligned : holAligned 2 s1.pc = true := by
    simpa [initial_pc] using (riscvOk_iff ms).mp h.2.1 |>.2.2.2.2
  have eight_aligned := Jump.aligned_add s1.pc 8 initial_aligned (by decide)
  have rel2 : targetStateRel riscvTarget src2 (env 1 branch) :=
    scratch_branch_final_rel s1 ms value (s1.pc + 8) env h.2 eight_aligned interference
  have guard := source_guard c r (.reg t) a hs.2.2.2.2.2.2
  have aligned := Jump.aligned_add s1.pc a initial_aligned guard.2.1
  have post : s2 = updPc (s1.pc + a) s1 := by
    simpa [chosen] using far_register_test_post c r t a s1 s2 hs far test
  have finalbase : targetStateRel riscvTarget s2 (Jump.branchPost (env 1 branch) (s1.pc + a)) := by
    rw [post]
    simpa [src2, updPc] using Jump.branch_post_rel src2 (env 1 branch) (s1.pc + a) rel2 aligned
  have final := (riscv_target_ok.2
    (env 2 (Jump.branchPost (env 1 branch) (s1.pc + a)))
    (Jump.branchPost (env 1 branch) (s1.pc + a)) s2
    (by simpa [post, updPc] using interference 2 (Jump.branchPost (env 1 branch) (s1.pc + a)))).1.mpr finalbase
  have code : ∀ pc, pc ∈ allPcs (riscvConfig.encode (.jumpCmp c r (.reg t) a)).length s1.pc 0 →
      riscvTarget.getByte (env 0 mid) pc = riscvTarget.getByte ms pc := by
    intro pc covered
    have domain := bytesInMemory_allPcs _ _ _ _ 0 hs.1 covered
    exact (rel.2.2.1 pc domain).trans (h.2.2.2.1 pc domain).symm
  have code2 : ∀ pc, pc ∈ allPcs (riscvConfig.encode (.jumpCmp c r (.reg t) a)).length s1.pc 0 →
      riscvTarget.getByte (env 1 branch) pc = riscvTarget.getByte ms pc := by
    intro pc covered
    have domain := bytesInMemory_allPcs _ _ _ _ 0 hs.1 covered
    exact (rel2.2.2.1 pc domain).trans (h.2.2.2.1 pc domain).symm
  have length : (riscvConfig.encode (.jumpCmp c r (.reg t) a)).length = 12 := by
    rw [far_register_test_encoding c r t a far test]
    simp [riscvEncode]
  have pc : riscvTarget.getPc (env 0 mid) ∈
      allPcs (riscvConfig.encode (.jumpCmp c r (.reg t) a)).length s1.pc riscvConfig.codeAlignment := by
    have address := rel.2.1
    change riscvTarget.getPc (env 0 mid) = s1.pc + 4 at address
    rw [address, allPcs_eq, length]
    refine ⟨1, ?_, ?_⟩
    · norm_num [riscvConfig]
    · rfl
  have pc2 : riscvTarget.getPc (env 1 branch) ∈
      allPcs (riscvConfig.encode (.jumpCmp c r (.reg t) a)).length s1.pc riscvConfig.codeAlignment := by
    have address := rel2.2.1
    change riscvTarget.getPc (env 1 branch) = s1.pc + 8 at address
    rw [address, allPcs_eq, length]
    refine ⟨2, ?_, ?_⟩
    · norm_num [riscvConfig]
    · rfl
  constructor
  · simpa [asserts, first, second, third] using
      ⟨⟨rel.1, code, pc⟩, ⟨⟨rel2.1, code2, pc2⟩, final⟩⟩
  · simp only [asserts2]
    rw [first]
    change (∀ x, ¬s1.memDomain x → ms.MEM8 x = mid.MEM8 x) ∧
      (∀ x, ¬s1.memDomain x → (env 0 mid).MEM8 x = (riscvTarget.next (env 0 mid)).MEM8 x) ∧
      (∀ x, ¬s1.memDomain x → (env 1 (riscvTarget.next (env 0 mid))).MEM8 x =
        (riscvTarget.next (env 1 (riscvTarget.next (env 0 mid)))).MEM8 x) ∧ True
    rw [second, third]
    exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, trivial⟩

theorem far_register_test_case (c : Cmp) (r t : Nat) (a : BitVec 64)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.jumpCmp c r (.reg t) a) s2 ∧
      targetStateRel riscvTarget s1 ms)
    (far : ¬(-4092 ≤ a.toInt ∧ a.toInt ≤ 4095))
    (test : c = .test ∨ c = .notTest)
 :
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
  cases chosen : wordCmpHOL c (readReg r s1) (readReg t s1)
  · exact far_register_test_false_case c r t a s1 s2 ms h far test chosen
  · exact far_register_test_true_case c r t a s1 s2 ms h far test chosen

end Flapjack.RiscV.TargetProof.Bounded.JumpCmp
