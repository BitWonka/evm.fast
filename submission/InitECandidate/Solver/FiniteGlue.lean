import InitE.Challenge
import Flapjack.Compiler.Backend.LabToTarget.EvaluateIgnoreClocks

/-! Finite-K certificate glue (EVM.fast, route 1).
A submission whose behaviour is already certified with an input-dependent halt witness (the
infinity certificate) gets a finite certificate `K = n` from a single extra fact: every covered
source termination halts the target within `n` evaluator steps. The matching observation is
transferred from the existing witness, because a completed target run's full result does not
depend on the clock (`evaluateTargetIgnoreClocks`). -/
namespace InitE.Bounded
open Flapjack

/-- The single obligation that turns the baseline infinity certificate into a finite one. -/
def HaltsWithin (s : Submission) (n : Nat) : Prop :=
  ∀ input : Guest.InputBlob,
    Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
    ∀ outcome events,
      sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      ∃ steps, steps ≤ n ∧
        targetTerminatesAt s.machineConfig (sourceFfi input) (s.initialState input) steps

theorem certificate_of_halts_within (s : Submission) (n : Nat)
    (score : s.K = .finite n) (admitted : s.Admitted)
    (exact : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        NatE.infinity.Within (matchingExecutionAt s input outcome events))
    (within : HaltsWithin s n) :
    Certificate s (.finite n) := by
  refine ⟨score, admitted, ?_⟩
  intro input gas outcome events source covered
  obtain ⟨steps₁, -, targetOutcome, post, finalFfi, run₁, matching⟩ :=
    exact input gas outcome events source covered
  obtain ⟨steps₂, bound, outcome₂, post₂, ffi₂, run₂⟩ :=
    within input gas outcome events source covered
  have same := evaluateTargetIgnoreClocks s.machineConfig (sourceFfi input) steps₁ steps₂
    (s.initialState input) _ _ _ _ _ _ ⟨run₁, by simp, run₂, by simp⟩
  refine ⟨steps₂, bound, targetOutcome, post, finalFfi, ?_, matching⟩
  rw [run₂]
  exact same.symm

/-- Admission never mentions the score field. -/
theorem admitted_withK (s : Submission) (k : NatE) (h : s.Admitted) :
    Submission.Admitted { s with K := k } := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩

/-- Re-score a submission that already has the exact-behaviour (infinity) certificate: the same
ROM and dispatch metadata with a finite ceiling `n`, given the single halting bound. -/
theorem certificate_withK (s : Submission) (n : Nat)
    (cert : Certificate s .infinity)
    (within : HaltsWithin { s with K := .finite n } n) :
    Certificate { s with K := .finite n } (.finite n) := by
  exact certificate_of_halts_within _ n rfl (admitted_withK s _ cert.admitted)
    (fun input gas outcome events source covered =>
      cert.correct input gas outcome events source covered) within

end InitE.Bounded
