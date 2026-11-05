import InitECandidate.Solver.JumpCmp.NearRegB
import InitECandidate.Solver.JumpCmp.NearRegTestB
import InitECandidate.Solver.JumpCmp.NearImmB
import InitECandidate.Solver.Common
import InitECandidate.Solver.Words
import InitECandidate.Solver.Ranges

/-! All near JumpCmp lowering cases with the full original conclusion.
The original near guard is discharged by the final near/far constructor split.
Native target statements inherit reals_as_rational_cuts (SOUNDNESS section 8). -/
namespace Flapjack.RiscV.TargetProof.Bounded.JumpCmp
set_option linter.unusedSimpArgs false
open Flapjack.RiscV.TargetProof.JumpCmp Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target

theorem near_case (c : Cmp) (r : Nat) (right : HolRegImm 64) (a : BitVec 64)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.jumpCmp c r right a) s2 ∧
      targetStateRel riscvTarget s1 ms)
    (range : -4092 ≤ a.toInt ∧ a.toInt ≤ 4095) :
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
  cases right with
  | imm i => exact near_immediate_case c r i a s1 s2 ms h range
  | reg t =>
    by_cases test : c = .test ∨ c = .notTest
    · exact near_register_test_case c r t a s1 s2 ms h range test
    · exact near_reg_simple c r t a s1 s2 ms h range
        ⟨fun eq => test (Or.inl eq), fun eq => test (Or.inr eq)⟩

end Flapjack.RiscV.TargetProof.Bounded.JumpCmp
