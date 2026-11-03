import InitE
import InitE.SubmissionAdmission
import InitE.SubmissionInitialization
import Flapjack.Compiler.Backend.Semantics.TargetProps.EvaluateAddClock
import Flapjack.Compiler.Backend.LabToTarget.EvaluateIgnoreClocks

namespace InitECandidate.Solver

open InitE Flapjack

/-- Replace only the claimed step bound `K` of a `Submission`, leaving the ROM
and all FFI/MMIO dispatch metadata untouched. -/
def withScore (s : Submission) (k : NatE) : Submission :=
  { s with K := k }

@[simp]
theorem withScore_code (s : Submission) (k : NatE) :
    (withScore s k).code = s.code := rfl

@[simp]
theorem withScore_K (s : Submission) (k : NatE) :
    (withScore s k).K = k := rfl

@[simp]
theorem withScore_anchorPc (s : Submission) (k : NatE) :
    (withScore s k).anchorPc = s.anchorPc := rfl

@[simp]
theorem withScore_names (s : Submission) (k : NatE) :
    (withScore s k).names = s.names := rfl

@[simp]
theorem withScore_first (s : Submission) (k : NatE) :
    (withScore s k).first = s.first := rfl

@[simp]
theorem withScore_extra (s : Submission) (k : NatE) :
    (withScore s k).extra = s.extra := rfl

@[simp]
theorem withScore_programDomain (s : Submission) (k : NatE) :
    (withScore s k).programDomain = s.programDomain := rfl

@[simp]
theorem withScore_machineConfig (s : Submission) (k : NatE) :
    (withScore s k).machineConfig = s.machineConfig := rfl

@[simp]
theorem withScore_initialMemory (s : Submission) (k : NatE) (input : Guest.InputBlob) :
    (withScore s k).initialMemory input = s.initialMemory input := rfl

@[simp]
theorem withScore_initialState (s : Submission) (k : NatE) (input : Guest.InputBlob) :
    (withScore s k).initialState input = s.initialState input := rfl

/-- Symbolic admission preservation under score replacement: never unfolds `s.code`. -/
theorem withScore_admitted (s : Submission) (k : NatE) (h : s.Admitted) :
    (withScore s k).Admitted :=
  ⟨h.code_nonempty, h.code_limit, h.anchor_lower, h.anchor_upper,
    h.anchor_aligned, h.name_boundary, h.metadata_length,
    h.ordinary_slots_loaded, h.mmio_valid, h.entry_distinct,
    h.entry_loaded, h.entry_aligned, h.entry_dispatch_separate,
    h.mmio_program, h.exit_loaded, h.layout_bound⟩

@[simp]
theorem withScore_admitted_iff (s : Submission) (k : NatE) :
    (withScore s k).Admitted ↔ s.Admitted :=
  ⟨fun h =>
    ⟨h.code_nonempty, h.code_limit, h.anchor_lower, h.anchor_upper,
      h.anchor_aligned, h.name_boundary, h.metadata_length,
      h.ordinary_slots_loaded, h.mmio_valid, h.entry_distinct,
      h.entry_loaded, h.entry_aligned, h.entry_dispatch_separate,
      h.mmio_program, h.exit_loaded, h.layout_bound⟩,
   withScore_admitted s k⟩

@[simp]
theorem matchingExecutionAt_withScore_iff (s : Submission) (k : NatE)
    (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (steps : Nat) :
    matchingExecutionAt (withScore s k) input outcome events steps ↔
      matchingExecutionAt s input outcome events steps := Iff.rfl

/-- Any two halting evaluations of `evaluateTargetHOL` from the same initial
configuration and FFI state produce the exact same outcome, machine state, and
final FFI state, regardless of their clocks. -/
theorem evaluateTarget_halt_unique {width : Nat} [NeZero width]
    {state projection σ : Type} (mc : MachineConfig width state projection)
    (ffi : HolFfiState σ) (steps s : Nat) (ms : state)
    (targetOutcome o : HolOutcome) (post p : state)
    (finalFfi f : HolFfiState σ)
    (hsteps : evaluateTargetHOL mc ffi steps ms = (.halt targetOutcome, post, finalFfi))
    (hs : evaluateTargetHOL mc ffi s ms = (.halt o, p, f)) :
    (.halt targetOutcome, post, finalFfi) = (MachineResult.halt o, p, f) :=
  evaluateTargetIgnoreClocks mc ffi steps s ms
    (.halt targetOutcome) (.halt o) post p finalFfi f
    ⟨hsteps, nofun, hs, nofun⟩

/-- If `evaluateTargetHOL` halts at some clock `steps` with `(targetOutcome, post, finalFfi)`
and also halts at some clock `s ≤ bound`, then evaluating at clock `bound` itself
halts with the exact same `(targetOutcome, post, finalFfi)`. -/
theorem evaluateTarget_halt_at_bound {width : Nat} [NeZero width]
    {state projection σ : Type} (mc : MachineConfig width state projection)
    (ffi : HolFfiState σ) (steps bound : Nat) (ms : state)
    (targetOutcome : HolOutcome) (post : state) (finalFfi : HolFfiState σ)
    (hsteps : evaluateTargetHOL mc ffi steps ms = (.halt targetOutcome, post, finalFfi))
    (hbound : ∃ s ≤ bound, ∃ o p f, evaluateTargetHOL mc ffi s ms = (.halt o, p, f)) :
    evaluateTargetHOL mc ffi bound ms = (.halt targetOutcome, post, finalFfi) := by
  rcases hbound with ⟨s, hs_le, o, p, f, hs⟩
  have huniq := evaluateTarget_halt_unique mc ffi steps s ms targetOutcome o post p finalFfi f hsteps hs
  have hs_same : evaluateTargetHOL mc ffi s ms = (.halt targetOutcome, post, finalFfi) := by
    rw [huniq]
    exact hs
  have hadd := evaluateTargetAddClock mc ffi s ms (bound - s)
    (.halt targetOutcome) post finalFfi hs_same nofun
  rwa [Nat.add_sub_of_le hs_le] at hadd

/-- Transport a matching execution at an arbitrary clock `steps` to clock `bound`
under `withScore sub (.finite bound)` whenever any halting execution exists within `bound`. -/
theorem matchingExecutionAt_withScore_at_bound (sub : Submission) (bound : Nat)
    (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (steps : Nat)
    (hexec : matchingExecutionAt sub input outcome events steps)
    (hbound : ∃ s ≤ bound, ∃ o p f,
      evaluateTargetHOL sub.machineConfig (sourceFfi input) s
        (sub.initialState input) = (.halt o, p, f)) :
    matchingExecutionAt (withScore sub (.finite bound)) input outcome events bound := by
  rcases hexec with ⟨targetOutcome, post, finalFfi, hsteps, hmatch⟩
  refine ⟨targetOutcome, post, finalFfi, ?_, hmatch⟩
  exact evaluateTarget_halt_at_bound sub.machineConfig (sourceFfi input)
    steps bound (sub.initialState input) targetOutcome post finalFfi hsteps hbound

/-- Upgrade an `.infinity` certificate for `sub` to a `.finite bound` certificate
for `withScore sub (.finite bound)` given a uniform halting bound `bound` on all
covered terminating inputs within the declared gas limit. -/
theorem certificate_of_uniform_halt_bound (sub : Submission) (bound : Nat)
    (hcert : Certificate sub .infinity)
    (hbound : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∃ s ≤ bound, ∃ o p f,
          evaluateTargetHOL sub.machineConfig (sourceFfi input) s
            (sub.initialState input) = (.halt o, p, f)) :
    Certificate (withScore sub (.finite bound)) (.finite bound) := by
  refine ⟨withScore_K sub (.finite bound), withScore_admitted sub (.finite bound) hcert.admitted, ?_⟩
  intro input hgas outcome events hsrc hcov
  rcases hcert.correct input hgas outcome events hsrc hcov with ⟨steps, _, hexec⟩
  refine ⟨bound, Nat.le_refl bound, ?_⟩
  exact matchingExecutionAt_withScore_at_bound sub bound input outcome events steps
    hexec (hbound input hgas outcome events hsrc hcov)

/-- Streamlined wrapper around `InitE.certificate_of_exact_behaviour` that accepts
any submission `sub` and produces `Certificate (withScore sub .infinity) .infinity`. -/
theorem certificate_of_exact_behaviour_compact (sub : Submission)
    (admitted : sub.Admitted)
    (correct : ∀ input outcome events,
      sourceBehaviour input = .terminate outcome events →
      ∀ behaviour, machineSemHOL sub.machineConfig (sourceFfi input)
        (sub.initialState input) behaviour → behaviour = .terminate outcome events) :
    Certificate (withScore sub .infinity) .infinity :=
  InitE.certificate_of_exact_behaviour (withScore sub .infinity)
    (withScore_K sub .infinity)
    (withScore_admitted sub .infinity admitted)
    correct

#print axioms withScore_admitted
#print axioms evaluateTarget_halt_unique
#print axioms evaluateTarget_halt_at_bound
#print axioms matchingExecutionAt_withScore_at_bound
#print axioms certificate_of_uniform_halt_bound
#print axioms certificate_of_exact_behaviour_compact

end InitECandidate.Solver
