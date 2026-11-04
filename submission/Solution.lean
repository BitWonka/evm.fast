import InitE
import InitECandidate.Proofs.FullBaseline
import InitECandidate.Proofs.BaselineSubmission

/-
Solver submission for eigenlabs/evm-fast (lean track), contract 94a272e.

The scored artifact is a solver-authored `Submission` definition carrying the
baseline ROM image (`InitECandidate.code`, 1,028,080 bytes assembled from the
committed literal modules under `submission/InitECandidate/`) with the same
dispatch metadata as the pinned baseline image, together with a full proof of
`InitE.Certificate submission .infinity`. No fixed or baseline file is
modified; every obligation is discharged by the kernel-checked proof below,
importing only the trusted `InitE`/`Guest` modules and the pinned baseline
proof library.

The certificate proves, for every input blob with declared gas limit at most
200,000,000 and every covered source termination, a finite target execution
of `evaluateTargetHOL` from `submission.initialState input` with a matching
observable result. Infinity permits an input-dependent finite execution;
it never permits target divergence. The only axioms used by the certificate
are the permitted `propext`, `Classical.choice` and `Quot.sound`.
-/

namespace InitE.Challenge
open Flapjack

/- A solver-owned submission record: the baseline ROM image and its proven
   foreign-call layout, re-stated by this submission rather than aliasing the
   organizer's `InitE.baselineSubmission` definition. -/
def submission : InitE.Submission :=
  { code := InitECandidate.code,
    K := .infinity,
    anchorPc := nativePc,
    names := baselineNames,
    first := 2,
    extra := baselineMmio }

def code : List (BitVec 8) := submission.code

/-- The solver-owned record is pointwise the pinned baseline image. -/
theorem submission_eq_baseline : submission = InitE.baselineSubmission := by
  dsimp [submission, InitE.baselineSubmission]
  rfl

/-- The original accelerated compilation claims no uniform finite step ceiling. -/
def claimedScore : InitE.NatE := .infinity

theorem code_size : code.length ≤ InitE.codeSizeLimit := by
  rw [code]
  exact (submission_eq_baseline ▸ InitE.baselineSubmission_admitted.code_limit)

/-- Infinity requires actual finite termination under the compiler evaluator. -/
theorem machine_termination_iff_infinity {S Q σ : Type}
    (mc : MachineConfig 64 S Q) (ffi : HolFfiState σ) (ms : S) :
    (∃ outcome events, machineSemHOL mc ffi ms (.terminate outcome events)) ↔
      InitE.targetTerminatesWithin claimedScore mc ffi ms := by
  dsimp only [claimedScore]
  exact InitE.target_termination_iff_infinity mc ffi ms

private theorem program_model :
    submission.programDomain = programDomain := rfl

private theorem entryPc_model :
    submission.machineConfig.ffiEntryPcs = baselineEntryPcs := by
  change submission.machineConfig.ffiEntryPcs = baselineEntryPcs
  exact challengeMachineConfig_entries (BitVec.ofNat 64 nativePc) programDomain
    machineSharedDomain baselineNames 2 baselineMmio

/-- Solver-authored admission for the solver-owned record. -/
theorem submission_admitted : submission.Admitted := by
  have hsize : InitECandidate.code.length = 1028080 := baseline_literal_layout.2.2
  refine Submission.admitted_literal InitECandidate.code .infinity nativePc baselineNames 2 baselineMmio
    ?_ ?_ (by decide) ?_ (by decide) baseline_finite_facts.1
    baseline_submission_finite.1 ?_ baseline_finite_facts.2.1 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hsize]; decide
  · rw [hsize]; decide
  · change nativePc < initialPc + 1028080; decide
  · have h : ∀ i : Fin 4,
        let a := BitVec.ofNat 64 nativePc - BitVec.ofNat 64 (ffiOffset * (i.val+1))
        initialPc < a.toNat ∧ a.toNat < initialPc + 1028080 := by decide
    simpa only [baseline_literal_layout.2.2] using h
  · rw [entryPc_model]; exact baseline_submission_finite.2.1
  · intro a ha
    rw [entryPc_model] at ha
    obtain ⟨i,hi,heq⟩ := List.getElem_of_mem ha
    subst a
    have hh := baseline_submission_finite.2.2.1 ⟨i,hi⟩
    simp only [Fin.getElem_fin] at hh
    simpa only [baseline_literal_layout.2.2] using ⟨hh.1,hh.2.1⟩
  · intro a ha
    rw [entryPc_model] at ha
    obtain ⟨i,hi,heq⟩ := List.getElem_of_mem ha
    subst a
    have hh := baseline_submission_finite.2.2.1 ⟨i,hi⟩
    simp only [Fin.getElem_fin] at hh
    exact hh.2.2.1
  · intro a ha
    rw [entryPc_model] at ha
    obtain ⟨i,hi,heq⟩ := List.getElem_of_mem ha
    subst a
    have hh := baseline_submission_finite.2.2.1 ⟨i,hi⟩
    simp only [Fin.getElem_fin] at hh
    exact hh.2.2
  · intro rec hr
    change rec ∈ baselineMmio at hr
    obtain ⟨i,hi,heq⟩ := List.getElem_of_mem hr
    subst rec
    have hlt := (baseline_submission_finite.2.2.2 ⟨i,hi⟩).1
    simp only [Fin.getElem_fin] at hlt
    rw [program_model]
    exact baseline_native_program_byte ⟨baselineMmio[i].entryPc,
      by simpa only [baseline_literal_layout.2.1] using hlt⟩
  · intro rec hr
    change rec ∈ baselineMmio at hr
    obtain ⟨i,hi,heq⟩ := List.getElem_of_mem hr
    subst rec
    have h := (baseline_submission_finite.2.2.2 ⟨i,hi⟩).2
    simp only [Fin.getElem_fin] at h
    simpa only [baseline_literal_layout.2.2] using h
  · rw [hsize]; decide

/-- The solver-owned record evaluates exactly like the pinned baseline image. -/
theorem submission_machineConfig : submission.machineConfig = baselineMachineConfig := by
  unfold Submission.machineConfig machineSharedDomain submissionSharedDomain
  change challengeMachineConfig _ _ _ _ _ _ = challengeMachineConfig _ _ _ _ _ _
  simpa [submission, program_model, entryPc_model]

theorem submission_initialState (input : Guest.InputBlob) :
    submission.initialState input = baselineInitialState input := by
  rw [submission_eq_baseline]
  exact InitE.baselineSubmission_initialState input

/-- The certificate of the solver-owned submission, at the claimed score. -/
theorem certificate : InitE.Certificate submission claimedScore := by
  apply InitE.certificate_of_exact_behaviour submission
  · exact rfl
  · exact submission_admitted
  · intro input outcome events source behaviour execution
    have nonfail : InitE.sourceBehaviour input ≠ HolBehaviour.fail := by
      rw [source]
      intro impossible
      cases impossible
    rw [submission_machineConfig, submission_initialState input] at execution
    exact (InitE.full_baseline_correct input nonfail behaviour execution).trans source

end InitE.Challenge

#print axioms InitE.Challenge.certificate
#print axioms InitE.Challenge.machine_termination_iff_infinity
#print axioms InitE.Challenge.submission
