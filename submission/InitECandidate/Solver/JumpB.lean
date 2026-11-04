import Flapjack.HolRef
import InitECandidate.Solver.Jump.FarB
import InitECandidate.Solver.Common
import InitECandidate.Solver.Words
import InitECandidate.Solver.Ranges

/-! Full original Jump constructor case. Both source-selected near JAL rd0
and far AUIPC31/JALR rd0 execute from literal encoded bytes, with source bounds
and alignment discharged from asmStep. Native Run inherits the reviewed
reals_as_rational_cuts assurance limit (SOUNDNESS item 8). -/
namespace Flapjack.RiscV.TargetProof.Bounded
set_option linter.unusedSimpArgs false
open Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target

/-- Original riscv_targetProof682-687 constructor, retaining the complete
encoder_correct_def premise and conclusion. Near uses witness0, far witness1;
both quantify every original interference environment and retain both asserts
and asserts2, code-byte preservation, intermediate PC membership and the full
final state relation. Source asm_ok supplies bounds/alignment. In the far path,
the full projection preserves scratch31 across interference; no decoder, native
Run, post-state relation or successful-target-execution premise is assumed. -/
theorem riscv_encoder_correct_jump_bounded (c : BitVec 64) (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.jump c) s2 ∧ targetStateRel riscvTarget s1 ms) :
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
  by_cases range : -1048576 ≤ c.toInt ∧ c.toInt ≤ 1048575
  · exact Jump.near_case c s1 s2 ms h range
  · exact Jump.far_case c s1 s2 ms h range

end Flapjack.RiscV.TargetProof.Bounded
