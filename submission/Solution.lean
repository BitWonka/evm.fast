import InitECandidate.Solver.LabNativeBridge
import InitECandidate.Solver.MemzeroAst
import InitECandidate.Solver.SourceOracleAdapter
import InitECandidate.Solver.NativeSplit
import InitECandidate.Solver.NoInstallBridge
import InitECandidate.Solver.LinesWitness
import InitE
import InitECandidate.Proofs.FullBaseline
import InitECandidate.Proofs.BaselineSubmission
import InitECandidate.Solver.FiniteGlue

set_option maxRecDepth 200000

namespace InitE.Challenge
open Flapjack

/-- The baseline ROM, bootstrap and dispatch metadata, with a finite claimed step ceiling. -/
noncomputable def submission : InitE.Submission :=
  { InitE.baselineSubmission with K := .finite 1000000000000000000000000000000 }

def code : List (BitVec 8) := submission.code

/-- PROBE: finite ceiling of 10^30 target evaluator steps. -/
def claimedScore : InitE.NatE := .finite 1000000000000000000000000000000

/-- The proved baseline result: exact behaviour with an input-dependent finite halt witness. -/
theorem baseline_certificate : InitE.Certificate InitE.baselineSubmission .infinity := by
  apply InitE.certificate_of_exact_behaviour InitE.baselineSubmission rfl InitE.baselineSubmission_admitted
  intro input outcome events source behaviour execution
  have nonfail : InitE.sourceBehaviour input ≠ HolBehaviour.fail := by
    rw [source]
    intro impossible
    cases impossible
  change machineSemHOL InitE.baselineSubmission.machineConfig (InitE.sourceFfi input)
    (InitE.baselineSubmission.initialState input) behaviour at execution
  rw [InitE.baselineSubmission_machineConfig, InitE.baselineSubmission_initialState] at execution
  exact (InitE.full_baseline_correct input nonfail behaviour execution).trans source

/-- PROBE, UNPROVED: every covered source termination halts the target within 10^30 evaluator
steps. Route 1: the bootstrap part is bounded by Bounded.BootstrapCountB (about 23k steps); the
compiled-guest part needs per-loop visit counts from a source-side bound that is not proved yet. -/
theorem halts_within : InitE.Bounded.HaltsWithin submission 1000000000000000000000000000000 := by
  sorry

theorem certificate : InitE.Certificate submission claimedScore :=
  InitE.Bounded.certificate_withK InitE.baselineSubmission 1000000000000000000000000000000
    baseline_certificate halts_within

end InitE.Challenge

#print axioms InitE.Challenge.certificate
