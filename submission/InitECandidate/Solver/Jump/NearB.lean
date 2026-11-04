import Flapjack.RiscV.CorrectnessEncoding.Jump.Native
import InitECandidate.Solver.Common
import InitECandidate.Solver.Words
import InitECandidate.Solver.Ranges

/-! Near-path assembly infrastructure for the full Jump constructor. The branch
condition selects the actual source encoder path; only the assembling theorem
will be tagged as the complete original constructor case. -/
namespace Flapjack.RiscV.TargetProof.Bounded.Jump
set_option linter.unusedSimpArgs false
open Flapjack.RiscV.TargetProof.Jump Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target

theorem jump_guard (c : BitVec 64)
    (h : asmOkExact (.jump c) riscvConfig = true) :
    (-2147483648 ≤ c.toInt ∧ c.toInt ≤ 2147481599) ∧ c.toNat % 4 = 0 := by
  have decoded : (decide (-2147483648 ≤ c.toInt) = true ∧
      decide (c.toInt ≤ 2147481599) = true) ∧ decide (c.toNat % 4 = 0) = true := by
    have original := h
    simp only [asmOkExact, asmJumpOffsetOkExact, asmOffsetOkExact,
      asmAligned, Bool.and_eq_true] at original
    exact original
  exact ⟨⟨of_decide_eq_true decoded.1.1, of_decide_eq_true decoded.1.2⟩,
    of_decide_eq_true decoded.2⟩

theorem jump_post (c : BitVec 64) (s1 s2 : AsmState 64)
    (h : asmStep riscvConfig s1 (.jump c) s2) :
    s2 = updPc (s1.pc + c) s1 := by
  simpa [asmUpd, jumpToOffset] using h.2.2.2.2.1.symm

theorem near_case (c : BitVec 64) (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.jump c) s2 ∧ targetStateRel riscvTarget s1 ms)
    (range : -1048576 ≤ c.toInt ∧ c.toInt ≤ 1048575) :
    ∃ n : Nat, n + 1 ≤ (riscvTarget.config.encode (.jump c)).length / 4 ∧
      ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (riscvTarget.proj s1.memDomain) →
      let pcs := allPcs (riscvTarget.config.encode (.jump c)).length s1.pc
      asserts n (fun k s => env (n-k) (riscvTarget.next s)) ms
        (fun ms' => riscvTarget.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
          riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
        (fun ms' => targetStateRel riscvTarget s2 ms') ∧
      asserts2 (n+1) (fun k => env (n+1-k)) riscvTarget.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x) := by
  have hs : asmStep riscvConfig s1 (.jump c) s2 := h.1
  have guard := jump_guard c hs.2.2.2.2.2.2
  have offset := near_jump_offset c range guard.2
  have bounds : (18446744073708503040#64).sle c = true ∧
      c.sle (1048575#64) = true := by
    simp only [BitVec.sle_eq_decide, decide_eq_true_eq]
    change -1048576 ≤ c.toInt ∧ c.toInt ≤ 1048575
    exact range
  have enc : riscvConfig.encode (.jump c) =
      riscvEncode (.Branch (.JAL (0,(c.sshiftRight 1).setWidth 20))) := by
    simp [riscvConfig, riscvEnc, riscvAst, inSignedRange, bounds.1, bounds.2]
  have hb := hs.1
  rw [enc] at hb
  have bytes := bytes_in_memory_thm () s1 ms _ _ _ _ ⟨h.2, hb⟩
  have pc := h.2.2.1
  change ms.c_PC ms.procID = s1.pc at pc
  have aligned := aligned_add (ms.c_PC ms.procID) c
    ((riscvOk_iff ms).mp h.2.1).2.2.2.2 guard.2
  have native_aligned : holAligned 2
      (ms.c_PC ms.procID + (((c.sshiftRight 1).setWidth 20).signExtend 64 <<< (1 : Nat))) = true := by
    rw [offset]
    exact aligned
  have hn := near_jump_next ms ((c.sshiftRight 1).setWidth 20) h.2.1 native_aligned
    bytes.2.2.2.2.2.1 bytes.2.2.2.2.2.2.1
    bytes.2.2.2.2.2.2.2.1 bytes.2.2.2.2.2.2.2.2.1
  have next : riscvTarget.next ms = branchPost ms (s1.pc+c) := by
    change holThe (NextRISCV ms) = _
    rw [hn, offset, pc]
    rfl
  have target_aligned : holAligned 2 (s1.pc+c) = true := by simpa [pc] using aligned
  have hp := branch_post_rel s1 ms (s1.pc+c) h.2 target_aligned
  rw [← jump_post c s1 s2 hs] at hp
  refine ⟨0, Flapjack.RiscV.TargetProof.Bounded.one_le_words _, ?_⟩
  intro env interference
  have projection := interference 0 (branchPost ms (s1.pc+c))
  have transport := (riscv_target_ok.2 (env 0 (branchPost ms (s1.pc+c)))
    (branchPost ms (s1.pc+c)) s2
    (by simpa [jump_post c s1 s2 hs, updPc] using projection)).1
  constructor
  · simpa [asserts, next] using transport.mpr hp
  · simp only [asserts2]
    rw [next]
    exact ⟨fun _ _ => rfl, trivial⟩

end Flapjack.RiscV.TargetProof.Bounded.Jump
