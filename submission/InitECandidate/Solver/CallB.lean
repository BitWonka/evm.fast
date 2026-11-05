import Flapjack.HolRef
import InitECandidate.Solver.Call.FarB
import InitECandidate.Solver.Common
import InitECandidate.Solver.Words
import InitECandidate.Solver.Ranges

/-! Full original Call constructor case. Both source-selected near JALrd1
and far AUIPCrd1/JALRrd1=rs1 execute from literal bytes, preserving source
PC+4/PC+8 link values and read-before-write aliasing. Native Run inherits the
reviewed reals_as_rational_cuts assurance limit (SOUNDNESS item8). -/
namespace Flapjack.RiscV.TargetProof.Bounded
set_option linter.unusedSimpArgs false
open Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target

/-- Original riscv_targetProof723-730 Call constructor, retaining complete
encoder_correct_def hypotheses and conclusion. Near witness0 and far witness1
quantify all original interference environments and retain both assertions,
code-byte preservation, intermediate PC membership and final full state relation.
Source asmStep supplies lr=1, offset bounds and alignment. Far AUIPC writes the
source register before JALR reads it; JALR then overwrites that same register
with the return link. No non-alias, decoder, run or post-state premise is added. -/
theorem riscv_encoder_correct_call_bounded (c : BitVec 64) (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.call c) s2 ∧ targetStateRel riscvTarget s1 ms) :
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
  by_cases range : -1048576 ≤ c.toInt ∧ c.toInt ≤ 1048575
  · exact Call.near_case c s1 s2 ms h range
  · exact Call.far_case c s1 s2 ms h range

end Flapjack.RiscV.TargetProof.Bounded
