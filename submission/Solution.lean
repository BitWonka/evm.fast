import InitE
import InitECandidate.Proofs.FullBaseline
import InitECandidate.Proofs.BaselineSubmission

namespace InitE.Challenge
open Flapjack

/-- Loose finite budget for the probe: 2^256 target steps. -/
def bound : Nat := 115792089237316195423570985008687907853269984665640564039457584007913129639936

/-- The baseline ROM and dispatch metadata, with a finite claimed score. Only `K` changes. -/
def submission : InitE.Submission := { InitE.baselineSubmission with K := .finite 115792089237316195423570985008687907853269984665640564039457584007913129639936 }

def code : List (BitVec 8) := submission.code

def claimedScore : InitE.NatE := .finite 115792089237316195423570985008687907853269984665640564039457584007913129639936

theorem submission_machineConfig : submission.machineConfig = InitE.baselineSubmission.machineConfig := rfl

theorem submission_initialState (input : Guest.InputBlob) :
    submission.initialState input = InitE.baselineSubmission.initialState input := rfl

theorem submission_admitted : submission.Admitted :=
  have h := InitE.baselineSubmission_admitted
  ⟨h.code_nonempty, h.code_limit, h.anchor_lower, h.anchor_upper, h.anchor_aligned, h.name_boundary, h.metadata_length, h.ordinary_slots_loaded, h.mmio_valid, h.entry_distinct, h.entry_loaded, h.entry_aligned, h.entry_dispatch_separate, h.mmio_program, h.exit_loaded, h.layout_bound⟩

/-- The baseline's infinity certificate, unchanged from the initial submission. -/
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

/-- PROBE, UNPROVED: on every covered terminating input with declared gas at most 200,000,000, a baseline
target run that halts at some clock has already halted, with the same result, by clock `bound`. This is the
uniform step bound that the finite score needs (source cost bound pushed through the compiler, or a
target-side cost sum on the fixed ROM). -/
theorem baseline_halts_by_bound (input : Guest.InputBlob)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (source : InitE.sourceBehaviour input = .terminate outcome events)
    (covered : InitE.coveredOutcome outcome)
    (steps : Nat) (targetOutcome : HolOutcome) (post : RiscV.L3.riscv_state) (finalFfi : HolFfiState Guest.HostMemory)
    (run : evaluateTargetHOL InitE.baselineSubmission.machineConfig (InitE.sourceFfi input) steps
      (InitE.baselineSubmission.initialState input) = (.halt targetOutcome, post, finalFfi)) :
    evaluateTargetHOL InitE.baselineSubmission.machineConfig (InitE.sourceFfi input) bound
      (InitE.baselineSubmission.initialState input) = (.halt targetOutcome, post, finalFfi) := by
  sorry

theorem certificate : InitE.Certificate submission claimedScore := by
  refine ⟨rfl, submission_admitted, ?_⟩
  intro input gas outcome events source covered
  obtain ⟨steps, _, targetOutcome, post, finalFfi, run, matching⟩ :=
    baseline_certificate.correct input gas outcome events source covered
  refine ⟨bound, le_refl _, targetOutcome, post, finalFfi, ?_, matching⟩
  rw [submission_machineConfig, submission_initialState]
  exact baseline_halts_by_bound input gas outcome events source covered steps targetOutcome post finalFfi run

end InitE.Challenge

#print axioms InitE.Challenge.certificate
