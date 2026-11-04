import InitECandidate.Proofs.BootstrapTrace
import InitECandidate.Solver.BootstrapLiteralB

/-! The submitted bootstrap reaches the installed native entry in at most 23,077 evaluator steps
(EVM.fast K certificate, route 1). Same statement as `BootstrapTrace.full_evaluator`, plus the bound. -/
namespace InitECandidate.Proofs.Bounded
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps
open InitECandidate.Proofs.BootstrapCopy InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Proofs.BootstrapTrace InitE

theorem full_evaluator_bounded {σ : Type} (io : HolFfiState σ) (ms : riscv_state)
    (initial : targetStateRel riscvTarget initialAsm ms) :
    ∃ count post, count ≤ 23077 ∧
      (∀ clock, evaluateTargetHOL baselineMachineConfig io (count + clock) ms =
        evaluateTargetHOL baselineMachineConfig io clock post) ∧
      targetStateRel riscvTarget installedAsm post := by
  obtain ⟨count, post, le, shift, relation⟩ :=
    checked_trace_evaluator_bounded baselineMachineConfig rfl rfl fullBootstrapCode initialAsm
      full_checked full_guards ms io initial
  refine ⟨count, post, ?_, shift, by rwa [full_endpoint] at relation⟩
  have code : fullBootstrapCode = prefixCode ++ (loopProgram 4606 ++ tailCode) := rfl
  rw [code, words_bootstrap] at le
  exact le

end InitECandidate.Proofs.Bounded
