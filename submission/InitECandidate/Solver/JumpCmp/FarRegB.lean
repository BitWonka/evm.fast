import Flapjack.RiscV.CorrectnessEncoding.JumpCmp.FarNative
import Flapjack.RiscV.CorrectnessEncoding.JumpCmp.Arithmetic
import InitECandidate.Solver.Common
import InitECandidate.Solver.Words
import InitECandidate.Solver.Ranges

/-! Far register JumpCmp assembly for the six simple comparisons.
Untagged local cases retain the original source premises and native semantics. -/
namespace Flapjack.RiscV.TargetProof.Bounded.JumpCmp
set_option linter.unusedSimpArgs false
open Flapjack.RiscV.TargetProof.JumpCmp Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps Compiler.Encoders.RiscV.Target

def far_reg_mid_pc (c : Cmp) (r t : Nat) (s : AsmState 64) : BitVec 64 :=
  if wordCmpHOL c (readReg r s) (readReg t s) then s.pc + 4 else s.pc + 8

theorem far_register_first (c : Cmp) (r t : Nat) (a : BitVec 64)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.jumpCmp c r (.reg t) a) s2 ∧
      targetStateRel riscvTarget s1 ms)
    (far : ¬(-4092 ≤ a.toInt ∧ a.toInt ≤ 4095))
    (simple : c ≠ .test ∧ c ≠ .notTest) :
    riscvTarget.next ms = Jump.branchPost ms (far_reg_mid_pc c r t s1) := by
  have hs : asmStep riscvConfig s1 (.jumpCmp c r (.reg t) a) s2 := h.1
  have guard := source_guard c r (.reg t) a hs.2.2.2.2.2.2
  have rightguard : asmRegOkExact t riscvConfig = true := by
    simpa [asmRegImmOkExact] using guard.2.2.2
  have leftread := reg_read r s1 ms guard.2.2.1 h.2
  have rightread := reg_read t s1 ms rightguard h.2
  have encoded := hs.1
  rw [far_register_simple_encoding c r t a far simple, bytesInMemory_append] at encoded
  have bytes := instruction_bytes s1 ms _ h.2 encoded.1
  have next := inverse_simple_branch_next c (BitVec.ofNat 5 r) (BitVec.ofNat 5 t)
    ms h.2.1 simple bytes
  have pc : ms.c_PC ms.procID = s1.pc := h.2.2.1
  change holThe (NextRISCV ms) = _
  rw [next, pc, leftread, rightread]
  rfl

/-- Source post-state uses the full two-instruction length even when native
execution skips JAL; this is derived from asmStep, never assumed. -/
theorem far_register_post (c : Cmp) (r t : Nat) (a : BitVec 64)
    (s1 s2 : AsmState 64)
    (hs : asmStep riscvConfig s1 (.jumpCmp c r (.reg t) a) s2)
    (far : ¬(-4092 ≤ a.toInt ∧ a.toInt ≤ 4095))
    (simple : c ≠ .test ∧ c ≠ .notTest) :
    s2 = updPc
      (if wordCmpHOL c (readReg r s1) (readReg t s1) then s1.pc + a else s1.pc + 8) s1 := by
  have original := source_post c r (.reg t) a s1 s2 hs
  rw [far_register_simple_encoding c r t a far simple] at original
  split <;> rename_i chosen
  all_goals simpa [riscvEncode, regImm, chosen] using original

theorem far_register_false_case (c : Cmp) (r t : Nat) (a : BitVec 64)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.jumpCmp c r (.reg t) a) s2 ∧
      targetStateRel riscvTarget s1 ms)
    (far : ¬(-4092 ≤ a.toInt ∧ a.toInt ≤ 4095))
    (simple : c ≠ .test ∧ c ≠ .notTest)
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
  have hs : asmStep riscvConfig s1 (.jumpCmp c r (.reg t) a) s2 := h.1
  have first := far_register_first c r t a s1 s2 ms h far simple
  have next : riscvTarget.next ms = Jump.branchPost ms (s1.pc + 8) := by
    simpa [far_reg_mid_pc, chosen] using first
  have pc : ms.c_PC ms.procID = s1.pc := h.2.2.1
  have initial_aligned : holAligned 2 s1.pc = true := by
    simpa [pc] using (riscvOk_iff ms).mp h.2.1 |>.2.2.2.2
  have aligned := Jump.aligned_add s1.pc 8 initial_aligned (by decide)
  have post : s2 = updPc (s1.pc + 8) s1 := by
    simpa [chosen] using far_register_post c r t a s1 s2 hs far simple
  have final := Jump.branch_post_rel s1 ms (s1.pc + 8) h.2 aligned
  rw [← post] at final
  refine ⟨0, Flapjack.RiscV.TargetProof.Bounded.one_le_words _, ?_⟩
  intro env interference
  have transport := (riscv_target_ok.2 (env 0 (Jump.branchPost ms (s1.pc + 8)))
    (Jump.branchPost ms (s1.pc + 8)) s2
    (by simpa [post, updPc] using interference 0 (Jump.branchPost ms (s1.pc + 8)))).1
  constructor
  · simpa [asserts, next] using transport.mpr final
  · simp only [asserts2]
    rw [next]
    exact ⟨fun _ _ => rfl, trivial⟩

theorem far_register_second (c : Cmp) (r t : Nat) (a : BitVec 64)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.jumpCmp c r (.reg t) a) s2 ∧
      targetStateRel riscvTarget s1 ms)
    (far : ¬(-4092 ≤ a.toInt ∧ a.toInt ≤ 4095))
    (simple : c ≠ .test ∧ c ≠ .notTest)
    (env : Nat → riscv_state → riscv_state)
    (interference : interferenceOk env (riscvTarget.proj s1.memDomain)) :
    riscvTarget.next (env 0 (Jump.branchPost ms (s1.pc + 4))) =
      Jump.branchPost (env 0 (Jump.branchPost ms (s1.pc + 4))) (s1.pc + a) := by
  have hs : asmStep riscvConfig s1 (.jumpCmp c r (.reg t) a) s2 := h.1
  have guard := source_guard c r (.reg t) a hs.2.2.2.2.2.2
  have initial_pc : ms.c_PC ms.procID = s1.pc := h.2.2.1
  have initial_aligned : holAligned 2 s1.pc = true := by
    simpa [initial_pc] using (riscvOk_iff ms).mp h.2.1 |>.2.2.2.2
  have four_aligned := Jump.aligned_add s1.pc 4 initial_aligned (by decide)
  have target_aligned := Jump.aligned_add s1.pc a initial_aligned guard.2.1
  let mid := env 0 (Jump.branchPost ms (s1.pc + 4))
  let src := updPc (s1.pc + 4) s1
  have base := Jump.branch_post_rel s1 ms (s1.pc + 4) h.2 four_aligned
  have rel : targetStateRel riscvTarget src mid :=
    (riscv_target_ok.2 mid (Jump.branchPost ms (s1.pc + 4)) src
      (interference 0 (Jump.branchPost ms (s1.pc + 4)))).1.mpr base
  have encoded := hs.1
  rw [far_register_simple_encoding c r t a far simple, bytesInMemory_append] at encoded
  have sourcebytes : bytesInMemoryHOL src.pc
      (riscvEncode (.Branch (.JAL (0,(a.sshiftRight 1).setWidth 20 - 2)))) src.mem src.memDomain := by
    simpa [src, updPc, riscvEncode] using encoded.2
  have bytes := instruction_bytes src mid _ rel sourcebytes
  have pc : mid.c_PC mid.procID = s1.pc + 4 := rel.2.1
  have offset : s1.pc + 4 +
      (((a.sshiftRight 1).setWidth 20 - 2).signExtend 64 <<< (1 : Nat)) = s1.pc + a := by
    simpa using far_offset_prefix4_pc s1.pc a guard.1 guard.2.1
  have aligned : holAligned 2 (mid.c_PC mid.procID +
      (((a.sshiftRight 1).setWidth 20 - 2).signExtend 64 <<< (1 : Nat))) = true := by
    rw [pc, offset]
    exact target_aligned
  have next := Jump.near_jump_next mid ((a.sshiftRight 1).setWidth 20 - 2)
    rel.1 aligned bytes.1 bytes.2.1 bytes.2.2.1 bytes.2.2.2
  change holThe (NextRISCV mid) = _
  rw [next, pc, offset]
  rfl

theorem far_register_true_case (c : Cmp) (r t : Nat) (a : BitVec 64)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.jumpCmp c r (.reg t) a) s2 ∧
      targetStateRel riscvTarget s1 ms)
    (far : ¬(-4092 ≤ a.toInt ∧ a.toInt ≤ 4095))
    (simple : c ≠ .test ∧ c ≠ .notTest)
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
  refine ⟨1, by
    first
    | (rw [Flapjack.RiscV.TargetProof.Bounded.words_eq]; simp_all [riscvAst]; done)
    | (rw [Flapjack.RiscV.TargetProof.Bounded.words_eq]
       simp only [riscvAst, Flapjack.RiscV.TargetProof.Bounded.inSignedRange_eq, Flapjack.RiscV.TargetProof.Bounded.toInt_jlo, Flapjack.RiscV.TargetProof.Bounded.toInt_jhi, Flapjack.RiscV.TargetProof.Bounded.toInt_clo, Flapjack.RiscV.TargetProof.Bounded.toInt_clo', Flapjack.RiscV.TargetProof.Bounded.toInt_chi, Flapjack.RiscV.TargetProof.Bounded.toInt_jlo', Flapjack.RiscV.TargetProof.Bounded.toInt_jhi', Flapjack.RiscV.TargetProof.Bounded.toInt_chi', decide_eq_true_eq]
       split <;> first | omega | (simp_all; done) | (cases c <;> simp_all)), ?_⟩
  intro env interference
  have hs : asmStep riscvConfig s1 (.jumpCmp c r (.reg t) a) s2 := h.1
  let mid := Jump.branchPost ms (s1.pc + 4)
  let src := updPc (s1.pc + 4) s1
  have first : riscvTarget.next ms = mid := by
    simpa [mid, far_reg_mid_pc, chosen] using far_register_first c r t a s1 s2 ms h far simple
  have second : riscvTarget.next (env 0 mid) = Jump.branchPost (env 0 mid) (s1.pc + a) :=
    far_register_second c r t a s1 s2 ms h far simple env interference
  have initial_pc : ms.c_PC ms.procID = s1.pc := h.2.2.1
  have initial_aligned : holAligned 2 s1.pc = true := by
    simpa [initial_pc] using (riscvOk_iff ms).mp h.2.1 |>.2.2.2.2
  have four_aligned := Jump.aligned_add s1.pc 4 initial_aligned (by decide)
  have guard := source_guard c r (.reg t) a hs.2.2.2.2.2.2
  have aligned := Jump.aligned_add s1.pc a initial_aligned guard.2.1
  have base := Jump.branch_post_rel s1 ms (s1.pc + 4) h.2 four_aligned
  have rel : targetStateRel riscvTarget src (env 0 mid) :=
    (riscv_target_ok.2 (env 0 mid) mid src (interference 0 mid)).1.mpr base
  have post : s2 = updPc (s1.pc + a) s1 := by
    simpa [chosen] using far_register_post c r t a s1 s2 hs far simple
  have finalbase : targetStateRel riscvTarget s2
      (Jump.branchPost (env 0 mid) (s1.pc + a)) := by
    rw [post]
    simpa [src, updPc] using Jump.branch_post_rel src (env 0 mid) (s1.pc + a) rel aligned
  have final := (riscv_target_ok.2
    (env 1 (Jump.branchPost (env 0 mid) (s1.pc + a)))
    (Jump.branchPost (env 0 mid) (s1.pc + a)) s2
    (by simpa [post, updPc] using interference 1 (Jump.branchPost (env 0 mid) (s1.pc + a)))).1.mpr finalbase
  have code : ∀ pc, pc ∈ allPcs (riscvConfig.encode (.jumpCmp c r (.reg t) a)).length s1.pc 0 →
      riscvTarget.getByte (env 0 mid) pc = riscvTarget.getByte ms pc := by
    intro pc covered
    have domain := bytesInMemory_allPcs _ _ _ _ 0 hs.1 covered
    exact (rel.2.2.1 pc domain).trans (h.2.2.2.1 pc domain).symm
  have length : (riscvConfig.encode (.jumpCmp c r (.reg t) a)).length = 8 := by
    rw [far_register_simple_encoding c r t a far simple]
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
  · simpa [asserts, first, second] using ⟨⟨rel.1, code, pc⟩, final⟩
  · simp only [asserts2]
    rw [first]
    change (∀ x, ¬s1.memDomain x → ms.MEM8 x = mid.MEM8 x) ∧
      (∀ x, ¬s1.memDomain x → (env 0 mid).MEM8 x =
        (riscvTarget.next (env 0 mid)).MEM8 x) ∧ True
    rw [second]
    exact ⟨fun _ _ => rfl, fun _ _ => rfl, trivial⟩

theorem far_register_simple_case (c : Cmp) (r t : Nat) (a : BitVec 64)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.jumpCmp c r (.reg t) a) s2 ∧
      targetStateRel riscvTarget s1 ms)
    (far : ¬(-4092 ≤ a.toInt ∧ a.toInt ≤ 4095))
    (simple : c ≠ .test ∧ c ≠ .notTest)
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
  · exact far_register_false_case c r t a s1 s2 ms h far simple chosen
  · exact far_register_true_case c r t a s1 s2 ms h far simple chosen

end Flapjack.RiscV.TargetProof.Bounded.JumpCmp
