import InitECandidate.Solver.NativeSplit
import InitECandidate.Solver.LinesWitness

/-!
Draft, not Lean checked. This conditional bridge isolates the remaining real
obligation: construct a correctly initialized Lab state and prove its finite
clock for every covered source execution. It is not a finite certificate.
-/
namespace InitE.Bounded

open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabToTarget.Bounded
open Flapjack.Compiler.Backend.Semantics.TargetProps

set_option maxRecDepth 1000000

/-- A bounded Lab run, with the same oracle and a valid relation to each
native-entry machine reached by bootstrap. This is intentionally a hypothesis,
not a theorem about the guest. -/
def NativeLabWitnessWithin (c : Nat) : Prop :=
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
        ∃ (p : BitVec 64) (s : LabSem.State 64 Config Guest.HostMemory)
          (o : HolOutcome) (s2 : LabSem.State 64 Config Guest.HostMemory),
          s.ffi = sourceFfi input ∧
          initOk (baselineMachineConfig, p) s post ∧
          NoInstall s.code ∧
          evaluate { s with clock := c } = (.halt o, s2)

/-- If the native entry has the stated Lab witness, the already-built
Lab-to-target line-bound theorem gives a conditional native target bound. -/
theorem native_halts_of_lab (c : Nat)
    (encoder : encoderCorrectBounded baselineMachineConfig.target)
    (witness : NativeLabWitnessWithin c) :
    NativeHaltsWithin ((2^62 + 1) * c) := by
  intro input gas outcome events source covered count post shift related
  obtain ⟨p, s, o, s2, hffi, hinit, hni, hev⟩ :=
    witness input gas outcome events source covered count post shift related
  obtain ⟨ms2, run⟩ :=
    lab_halt_within_address_space64 baselineMachineConfig p post s c o s2
      encoder hinit hni hev
  refine ⟨(2^62 + 1) * c, le_refl _, o, ms2, s2.ffi, ?_⟩
  simpa only [hffi] using run

end InitE.Bounded
