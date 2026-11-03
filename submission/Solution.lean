import InitE
import Flapjack.Compiler.Backend.Semantics.TargetProps.EvaluateAddClock
import Flapjack.Compiler.Backend.LabToTarget.EvaluateIgnoreClocks
import InitECandidate.Proofs.FullBaseline
import InitECandidate.Proofs.BaselineSubmission

namespace InitE.Challenge
open Flapjack

/-- Loose finite budget for the probe: 2^256 target steps. -/
def bound : Nat := 115792089237316195423570985008687907853269984665640564039457584007913129639936

/-- Replace only the claimed score of a submission. -/
def withScore (s : InitE.Submission) (k : InitE.NatE) : InitE.Submission := { s with K := k }

/- The following facts are proved for an ARBITRARY submission `s`, so no large literal (the 1 MiB ROM) is ever
unfolded; they are then instantiated at the baseline. (Probe 1 failed with "maximum recursion depth" when `rfl`
was checked directly against `baselineSubmission`.) -/
theorem withScore_machineConfig (s : InitE.Submission) (k : InitE.NatE) :
    (withScore s k).machineConfig = s.machineConfig := rfl

theorem withScore_initialState (s : InitE.Submission) (k : InitE.NatE) (input : Guest.InputBlob) :
    (withScore s k).initialState input = s.initialState input := rfl

theorem withScore_admitted (s : InitE.Submission) (k : InitE.NatE) (h : s.Admitted) :
    (withScore s k).Admitted :=
  ⟨h.code_nonempty, h.code_limit, h.anchor_lower, h.anchor_upper, h.anchor_aligned, h.name_boundary, h.metadata_length, h.ordinary_slots_loaded, h.mmio_valid, h.entry_distinct, h.entry_loaded, h.entry_aligned, h.entry_dispatch_separate, h.mmio_program, h.exit_loaded, h.layout_bound⟩

theorem withScore_K (s : InitE.Submission) (k : InitE.NatE) : (withScore s k).K = k := rfl

/-- The baseline ROM and dispatch metadata, with a finite claimed score. Only `K` changes. -/
def submission : InitE.Submission :=
  withScore InitE.baselineSubmission (.finite 115792089237316195423570985008687907853269984665640564039457584007913129639936)

def code : List (BitVec 8) := submission.code

def claimedScore : InitE.NatE := .finite 115792089237316195423570985008687907853269984665640564039457584007913129639936

theorem submission_machineConfig : submission.machineConfig = InitE.baselineSubmission.machineConfig :=
  withScore_machineConfig _ _

theorem submission_initialState (input : Guest.InputBlob) :
    submission.initialState input = InitE.baselineSubmission.initialState input :=
  withScore_initialState _ _ input

theorem submission_admitted : submission.Admitted :=
  withScore_admitted _ _ InitE.baselineSubmission_admitted

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

/-- PROBE, UNPROVED (the uniform ceiling itself): on every input with declared gas at most 200,000,000 whose
source behaviour is a covered termination, the baseline target run halts at SOME clock not above `bound`. No claim
about the result: equality with any other halting run is proved below from determinism. -/
theorem baseline_halt_clock_le_bound (input : Guest.InputBlob)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (source : InitE.sourceBehaviour input = .terminate outcome events)
    (covered : InitE.coveredOutcome outcome) :
    ∃ s, s ≤ bound ∧ ∃ o p f, evaluateTargetHOL InitE.baselineSubmission.machineConfig (InitE.sourceFfi input) s
      (InitE.baselineSubmission.initialState input) = (.halt o, p, f) := by
  sorry

/-- Proved: a halting run reaches the same result at the clock `bound` once some halting clock is at most `bound`
(`evaluateTargetIgnoreClocks` for equality of the two halting runs, `evaluateTargetAddClock` to move up to `bound`). -/
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
  obtain ⟨s, hs, o, p, f, hrun⟩ := baseline_halt_clock_le_bound input gas outcome events source covered
  have same := evaluateTargetIgnoreClocks _ _ s steps _ _ _ _ _ _ _
    ⟨hrun, by simp, run, by simp⟩
  have up := evaluateTargetAddClock _ _ s _ (bound - s) _ _ _ hrun (by simp)
  rw [Nat.add_sub_cancel' hs] at up
  rw [up]
  exact same

theorem certificate : InitE.Certificate submission claimedScore := by
  refine ⟨withScore_K _ _, submission_admitted, ?_⟩
  intro input gas outcome events source covered
  obtain ⟨steps, _, targetOutcome, post, finalFfi, run, matching⟩ :=
    baseline_certificate.correct input gas outcome events source covered
  refine ⟨bound, le_refl _, targetOutcome, post, finalFfi, ?_, matching⟩
  rw [submission_machineConfig, submission_initialState]
  exact baseline_halts_by_bound input gas outcome events source covered steps targetOutcome post finalFfi run

end InitE.Challenge

#print axioms InitE.Challenge.certificate
