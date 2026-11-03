import InitE
import InitECandidate.Proofs.BaselineSubmission
import InitECandidate.Solver.CompactBaseline
import InitECandidate.Solver.FiniteBoundReduction
import InitECandidate.Solver.BootstrapClockBound

namespace InitE.Challenge
open Flapjack
open InitECandidate.Solver

/-- The submitted ROM includes the proved zero-RAM bootstrap and data initializer. -/
def submission : InitE.Submission := InitE.baselineSubmission

/-- Certified step bound for the submission. -/
def claimedScore : InitE.NatE := .infinity

/-- Full end-to-end certificate using the compact solver proof chain
(`InitECandidate.Solver.CompactBaseline`), which eliminates the 14 `decide_cbv`
invocations in `PanInstallation`, `BaselineCertificate`, and `OracleBaselineCorrectness`
from the exported `comparator` declaration closure. -/
theorem certificate : InitE.Certificate submission claimedScore := by
  apply InitE.certificate_of_exact_behaviour submission rfl InitE.baselineSubmission_admitted
  intro input outcome events source behaviour execution
  have nonfail : InitE.sourceBehaviour input ≠ HolBehaviour.fail := by
    rw [source]
    intro impossible
    cases impossible
  change machineSemHOL InitE.baselineSubmission.machineConfig (InitE.sourceFfi input)
    (InitE.baselineSubmission.initialState input) behaviour at execution
  rw [InitE.baselineSubmission_machineConfig, InitE.baselineSubmission_initialState] at execution
  exact (compact_full_baseline_correct input nonfail behaviour execution).trans source

end InitE.Challenge
