import InitECandidate.Solver.JumpCmp.NearB
import InitECandidate.Solver.JumpCmp.FarRegB
import InitECandidate.Solver.JumpCmp.FarRegTestB
import InitECandidate.Solver.JumpCmp.FarImmB
import InitECandidate.Solver.Common
import InitECandidate.Solver.Words
import InitECandidate.Solver.Ranges

/-! Full original native JumpCmp encoder correctness constructor. Native target
statements inherit the reviewed reals_as_rational_cuts assurance limit
(SOUNDNESS section 8). -/
namespace Flapjack.RiscV.TargetProof.Bounded
set_option linter.unusedSimpArgs false
open Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target

/-- Original JumpCmp case (690–720): both Reg/Imm operands, all eight comparisons,
near/far lowering, actual AND/ANDI/ORI scratch prefix, inverse conditional
branches and corrected JAL displacement. Only original asmStep and initial
state relation are premises; all fetch, alignment and intermediate relations
are derived. The complete existential/all-environments/both-assertions result
includes code bytes, PC membership, final state relation and memory frame.
Inherits reals_as_rational_cuts from the native state (SOUNDNESS section 8). -/
theorem riscv_encoder_correct_jumpCmp_bounded (c : Cmp) (r : Nat) (right : HolRegImm 64)
    (a : BitVec 64) (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.jumpCmp c r right a) s2 ∧
      targetStateRel riscvTarget s1 ms) :
    ∃ n : Nat, n + 1 ≤ (riscvTarget.config.encode (.jumpCmp c r right a)).length / 4 ∧
      ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (riscvTarget.proj s1.memDomain) →
      let pcs := allPcs (riscvTarget.config.encode (.jumpCmp c r right a)).length s1.pc
      asserts n (fun k s => env (n-k) (riscvTarget.next s)) ms
        (fun ms' => riscvTarget.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
          riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
        (fun ms' => targetStateRel riscvTarget s2 ms') ∧
      asserts2 (n+1) (fun k => env (n+1-k)) riscvTarget.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x) := by
  by_cases near : -4092 ≤ a.toInt ∧ a.toInt ≤ 4095
  · exact JumpCmp.near_case c r right a s1 s2 ms h near
  · cases right with
    | imm i => exact JumpCmp.far_immediate_case c r i a s1 s2 ms h near
    | reg t =>
      by_cases test : c = .test ∨ c = .notTest
      · exact JumpCmp.far_register_test_case c r t a s1 s2 ms h near test
      · exact JumpCmp.far_register_simple_case c r t a s1 s2 ms h near
          ⟨fun eq => test (Or.inl eq), fun eq => test (Or.inr eq)⟩

end Flapjack.RiscV.TargetProof.Bounded
