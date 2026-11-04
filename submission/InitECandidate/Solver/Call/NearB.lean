import Flapjack.RiscV.CorrectnessEncoding.Call.Native
import InitECandidate.Solver.Jump.NearB
import InitECandidate.Solver.Common
import InitECandidate.Solver.Words
import InitECandidate.Solver.Ranges

/-! Near-path assembly infrastructure for the full Call constructor. The branch
condition selects the actual source encoder path; only the assembling theorem
will be tagged as the complete original constructor case. -/
namespace Flapjack.RiscV.TargetProof.Bounded.Call
set_option linter.unusedSimpArgs false
open Flapjack.RiscV.TargetProof.Call Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target

theorem call_guard (c : BitVec 64)
    (h : asmOkExact (.call c) riscvConfig = true) :
    (-2147483648 ≤ c.toInt ∧ c.toInt ≤ 2147481599) ∧ c.toNat % 4 = 0 := by
  change (asmRegOkExact 1 riscvConfig && asmJumpOffsetOkExact riscvConfig c) = true at h
  have both : asmRegOkExact 1 riscvConfig = true ∧
      asmJumpOffsetOkExact riscvConfig c = true := by
    simpa only [Bool.and_eq_true] using h
  exact Jump.jump_guard c both.2

theorem call_post (c : BitVec 64) (s1 s2 : AsmState 64)
    (h : asmStep riscvConfig s1 (.call c) s2) :
    s2 = updPc (s1.pc+c)
      (updReg 1 (s1.pc+BitVec.ofNat 64 (riscvConfig.encode (.call c)).length) s1) := by
  have lr : s1.lr = 1 := h.2.1
  simpa [asmUpd,jumpToOffset,updReg,lr] using h.2.2.2.2.1.symm

theorem near_case (c : BitVec 64) (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.call c) s2 ∧ targetStateRel riscvTarget s1 ms)
    (range : -1048576 ≤ c.toInt ∧ c.toInt ≤ 1048575) :
    ∃ n : Nat, n + 1 ≤ (riscvTarget.config.encode (.call c)).length / 4 ∧
      ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (riscvTarget.proj s1.memDomain) →
      let pcs := allPcs (riscvTarget.config.encode (.call c)).length s1.pc
      asserts n (fun k s => env (n-k) (riscvTarget.next s)) ms
        (fun ms' => riscvTarget.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
          riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
        (fun ms' => targetStateRel riscvTarget s2 ms') ∧
      asserts2 (n+1) (fun k => env (n+1-k)) riscvTarget.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x) := by
  have hs : asmStep riscvConfig s1 (.call c) s2 := h.1
  have guard := call_guard c hs.2.2.2.2.2.2
  have offset := Jump.near_jump_offset c range guard.2
  have bounds : (18446744073708503040#64).sle c = true ∧
      c.sle (1048575#64) = true := by
    simp only [BitVec.sle_eq_decide, decide_eq_true_eq]
    change -1048576 ≤ c.toInt ∧ c.toInt ≤ 1048575
    exact range
  have enc : riscvConfig.encode (.call c) =
      riscvEncode (.Branch (.JAL (1#5,(c.sshiftRight 1).setWidth 20))) := by
    simp [riscvConfig, riscvEnc, riscvAst, inSignedRange, bounds.1, bounds.2]
  have hb := hs.1
  rw [enc] at hb
  have bytes := bytes_in_memory_thm () s1 ms _ _ _ _ ⟨h.2, hb⟩
  have pc := h.2.2.1
  change ms.c_PC ms.procID = s1.pc at pc
  have aligned := Jump.aligned_add (ms.c_PC ms.procID) c
    ((riscvOk_iff ms).mp h.2.1).2.2.2.2 guard.2
  have native_aligned : holAligned 2
      (ms.c_PC ms.procID + (((c.sshiftRight 1).setWidth 20).signExtend 64 <<< (1 : Nat))) = true := by
    rw [offset]
    exact aligned
  have hn := near_call_next ms ((c.sshiftRight 1).setWidth 20) h.2.1 native_aligned
    bytes.2.2.2.2.2.1 bytes.2.2.2.2.2.2.1
    bytes.2.2.2.2.2.2.2.1 bytes.2.2.2.2.2.2.2.2.1
  have next : riscvTarget.next ms = callPost ms (s1.pc+c) := by
    change holThe (NextRISCV ms) = _
    rw [hn, offset, pc]
    rfl
  have target_aligned : holAligned 2 (s1.pc+c) = true := by simpa [pc] using aligned
  have hp := call_post_rel s1 ms (s1.pc+c) h.2 target_aligned
  have length : (riscvConfig.encode (.call c)).length = 4 := by
    rw [enc]
    rfl
  have post : s2 = updPc (s1.pc+c) (updReg 1 (s1.pc+4) s1) := by
    simpa [length] using call_post c s1 s2 hs
  rw [←post] at hp
  refine ⟨0, Flapjack.RiscV.TargetProof.Bounded.one_le_words _, ?_⟩
  intro env interference
  have projection := interference 0 (callPost ms (s1.pc+c))
  have transport := (riscv_target_ok.2 (env 0 (callPost ms (s1.pc+c)))
    (callPost ms (s1.pc+c)) s2
    (by simpa [post,updPc,updReg] using projection)).1
  constructor
  · simpa [asserts, next] using transport.mpr hp
  · simp only [asserts2]
    rw [next]
    exact ⟨fun _ _ => rfl, trivial⟩

end Flapjack.RiscV.TargetProof.Bounded.Call
