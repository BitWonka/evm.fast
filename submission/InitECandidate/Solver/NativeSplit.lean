import InitECandidate.Proofs.FullBaseline
import InitECandidate.Proofs.BaselineSubmission
import InitECandidate.Solver.BootstrapFullB
import InitECandidate.Solver.FiniteGlue

/-! Route 1 split (EVM.fast): the bootstrap costs at most 23,077 evaluator steps (proved), so a
finite ceiling reduces to a bound on the native run that starts at the installed compiler state. -/
set_option maxRecDepth 1000000

namespace InitE.Bounded
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps

/-- The remaining obligation: every installed native state reached by the bootstrap (with the
input's oracle) halts within `n` steps whenever the source terminates in a covered outcome. -/
def NativeHaltsWithin (n : Nat) : Prop :=
  ∀ input : Guest.InputBlob,
    Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
    ∀ outcome events,
      sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      ∀ count post,
        (∀ clock, evaluateTargetHOL baselineMachineConfig (sourceFfi input) (count + clock)
          (baselineInitialState input) =
            evaluateTargetHOL baselineMachineConfig (sourceFfi input) clock post) →
        targetStateRel riscvTarget installedAsm post →
        ∃ steps, steps ≤ n ∧ targetTerminatesAt baselineMachineConfig (sourceFfi input) post steps

theorem halts_within_of_native (k : NatE) (n : Nat) (native : NativeHaltsWithin n) :
    HaltsWithin { baselineSubmission with K := k } (23077 + n) := by
  intro input gas outcome events source covered
  obtain ⟨count, post, le, shift, related⟩ :=
    InitECandidate.Proofs.Bounded.full_evaluator_bounded (sourceFfi input)
      (baselineInitialState input) (baselineInitialState_related input)
  obtain ⟨steps, stepsLe, result, ms', ffi', run⟩ :=
    native input gas outcome events source covered count post shift related
  refine ⟨count + steps, by omega, result, ms', ffi', ?_⟩
  change evaluateTargetHOL baselineSubmission.machineConfig (sourceFfi input) (count + steps)
    (baselineSubmission.initialState input) = _
  rw [baselineSubmission_machineConfig, baselineSubmission_initialState, shift, run]

end InitE.Bounded
