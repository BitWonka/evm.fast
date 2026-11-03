import InitE.Challenge
import Flapjack.Compiler.Backend.Semantics.TargetSem.MachineSem
import Flapjack.Compiler.Backend.Semantics.TargetProps.EvaluateAddClock
import Flapjack.Compiler.Backend.Semantics.TargetProps.EvaluateAddClockIoEventsMono

/-! Quantitative clock-shift and finite bootstrap composition lemmas for
`evaluateTargetHOL`, `targetTerminatesAt`, `targetTerminatesWithin`, and
`matchingExecutionAt`.

This module imports only pre-built `InitE` and `Flapjack` modules so that it
elaborates standalone in ~2 seconds without pulling in the 55k-file baseline
proof DAG. -/

namespace InitECandidate.Solver
open InitE
open Flapjack

section GeneralWidth
variable {width : Nat} [NeZero width] {State Projection : Type}

/-- Every guard checked by one ordinary target instruction. Writable ordinary
RAM belongs to `progAddresses`; input/output shared memory is handled through FFI. -/
structure OrdinaryStep (mc : MachineConfig width State Projection) (before : State) : Prop where
  program : mc.progAddresses (mc.target.getPc before)
  nonFfi : mc.target.getPc before ∉ mc.ffiEntryPcs
  encoded : encodedBytesInMemHOL mc.target.config (mc.target.getPc before)
    (mc.target.getByte before) mc.progAddresses
  beforeOk : mc.target.stateOk before = true
  afterOk : mc.target.stateOk (mc.target.next before) = true
  outside : ∀ address, ¬ mc.progAddresses address →
    mc.target.getByte (mc.target.next before) address = mc.target.getByte before address

/-- An ordinary prefix reaches its final state after exactly `count` instructions. -/
inductive OrdinaryPrefix (mc : MachineConfig width State Projection) : Nat → State → State → Prop
  | nil (state : State) : OrdinaryPrefix mc 0 state state
  | cons {count : Nat} {before after : State} (step : OrdinaryStep mc before)
      (tail : OrdinaryPrefix mc count (mc.target.next before) after) :
      OrdinaryPrefix mc (count + 1) before after

variable {mc : MachineConfig width State Projection}

/-- Quantitative clock-shift composition for `evaluateTargetHOL`:
If a bootstrap prefix of `c1` steps shifts `evaluateTargetHOL` from `s0` to `s1`
for all clocks, and `s1` halts in `c2 ≤ K_body` steps, then `s0` halts in
`c1 + c2` steps with `c1 + c2 ≤ c1 + K_body`. -/
theorem evaluateTargetHOL_clock_shift_halt {σ : Type} (ffi : HolFfiState σ)
    {c1 c2 K_body : Nat} {s0 s1 post : State} {outcome : HolOutcome} {finalFfi : HolFfiState σ}
    (hshift : ∀ clock, evaluateTargetHOL mc ffi (c1 + clock) s0 =
      evaluateTargetHOL mc ffi clock s1)
    (hhalt : evaluateTargetHOL mc ffi c2 s1 = (.halt outcome, post, finalFfi))
    (hbound : c2 ≤ K_body) :
    evaluateTargetHOL mc ffi (c1 + c2) s0 = (.halt outcome, post, finalFfi) ∧
      c1 + c2 ≤ c1 + K_body := by
  refine ⟨(hshift c2).trans hhalt, ?_⟩
  omega

/-- Because halting target executions are monotonic in the clock (`evaluateTargetAddClock`),
a clock-shifted execution that halts at `c2 ≤ K_body` also halts at the exact
upper bound `c1 + K_body`. -/
theorem evaluateTargetHOL_clock_shift_halt_at_bound {σ : Type} (ffi : HolFfiState σ)
    {c1 c2 K_body : Nat} {s0 s1 post : State} {outcome : HolOutcome} {finalFfi : HolFfiState σ}
    (hshift : ∀ clock, evaluateTargetHOL mc ffi (c1 + clock) s0 =
      evaluateTargetHOL mc ffi clock s1)
    (hhalt : evaluateTargetHOL mc ffi c2 s1 = (.halt outcome, post, finalFfi))
    (hbound : c2 ≤ K_body) :
    evaluateTargetHOL mc ffi (c1 + K_body) s0 = (.halt outcome, post, finalFfi) := by
  have hmono := evaluateTargetAddClock mc ffi c2 s1 (K_body - c2)
    (.halt outcome) post finalFfi hhalt (by rintro ⟨⟩)
  rw [show c2 + (K_body - c2) = K_body by omega] at hmono
  exact (hshift K_body).trans hmono

/-- Existential form of quantitative clock-shift composition for `evaluateTargetHOL`. -/
theorem evaluateTargetHOL_clock_shift_exists {σ : Type} (ffi : HolFfiState σ)
    {c1 K_body : Nat} {s0 s1 post : State} {outcome : HolOutcome} {finalFfi : HolFfiState σ}
    (hshift : ∀ clock, evaluateTargetHOL mc ffi (c1 + clock) s0 =
      evaluateTargetHOL mc ffi clock s1)
    (hbody : ∃ c2, c2 ≤ K_body ∧
      evaluateTargetHOL mc ffi c2 s1 = (.halt outcome, post, finalFfi)) :
    ∃ c, c ≤ c1 + K_body ∧
      evaluateTargetHOL mc ffi c s0 = (.halt outcome, post, finalFfi) := by
  rcases hbody with ⟨c2, hbound, hhalt⟩
  have hcomp := evaluateTargetHOL_clock_shift_halt ffi hshift hhalt hbound
  exact ⟨c1 + c2, hcomp.2, hcomp.1⟩

/-- One ordinary instruction under the identity interference oracle shifts the
target evaluator clock by 1. -/
theorem ordinary_step_evaluate
    (identity : mc.nextInterfer = fun _ state => state)
    {σ : Type} (ffi : HolFfiState σ) (clock : Nat)
    {before : State} (step : OrdinaryStep mc before) :
    evaluateTargetHOL mc ffi (clock + 1) before =
      evaluateTargetHOL mc ffi clock (mc.target.next before) := by
  classical
  have hshift : holShiftSeq 1 mc.nextInterfer = mc.nextInterfer := by rw [identity]; rfl
  have hnext : mc.nextInterfer 0 (mc.target.next before) = mc.target.next before := by
    rw [identity]
  have hprogram : mc.progAddresses (mc.target.getPc before) ∧
      mc.target.getPc before ∉ mc.ffiEntryPcs := ⟨step.program, step.nonFfi⟩
  have hok : mc.target.stateOk before = true ∧
      mc.target.stateOk (mc.target.next before) = true ∧
      mc.target.stateOk (mc.target.next before) = true ∧
      (∀ x, ¬ mc.progAddresses x →
        mc.target.getByte (mc.target.next before) x = mc.target.getByte before x) :=
    ⟨step.beforeOk, step.afterOk, step.afterOk, step.outside⟩
  simp only [evaluateTargetHOL, if_pos hprogram,
    if_pos step.encoded, applyOracleHOL, hshift, hnext]
  simp only [if_pos hok]

/-- An `OrdinaryPrefix` of `count` steps under the identity interference oracle
shifts `evaluateTargetHOL` by exactly `count` steps. -/
theorem prefix_evaluate
    (identity : mc.nextInterfer = fun _ state => state)
    {σ : Type} (ffi : HolFfiState σ)
    {count : Nat} {before after : State} (runPrefix : OrdinaryPrefix mc count before after)
    (clock : Nat) :
    evaluateTargetHOL mc ffi (count + clock) before = evaluateTargetHOL mc ffi clock after := by
  induction runPrefix with
  | nil state => simp
  | @cons count before after step tail ih =>
    rw [show count + 1 + clock = (count + clock) + 1 by omega,
      ordinary_step_evaluate identity ffi (count + clock) step]
    exact ih

/-- Any clock up to `count` times out during an `OrdinaryPrefix` of length `count`
without modifying the FFI state. -/
theorem prefix_short_clock
    (identity : mc.nextInterfer = fun _ state => state)
    {σ : Type} (ffi : HolFfiState σ)
    {count : Nat} {before after : State} (runPrefix : OrdinaryPrefix mc count before after)
    (clock : Nat) (short : clock ≤ count) :
    ∃ middle, evaluateTargetHOL mc ffi clock before = (.timeOut, middle, ffi) := by
  induction runPrefix generalizing clock with
  | nil state =>
    have : clock = 0 := by omega
    subst clock
    exact ⟨state, rfl⟩
  | @cons count before after step tail ih =>
    cases clock with
    | zero => exact ⟨before, rfl⟩
    | succ clock =>
      rw [ordinary_step_evaluate identity ffi clock step]
      exact ih clock (by omega)

/-- Composing an `OrdinaryPrefix` of `count` steps with a halting body execution
of `c2 ≤ K_body` steps yields a halting execution in `count + c2 ≤ count + K_body` steps. -/
theorem ordinaryPrefix_clock_shift_halt
    (identity : mc.nextInterfer = fun _ state => state)
    {σ : Type} (ffi : HolFfiState σ)
    {count c2 K_body : Nat} {before after post : State}
    {outcome : HolOutcome} {finalFfi : HolFfiState σ}
    (runPrefix : OrdinaryPrefix mc count before after)
    (hhalt : evaluateTargetHOL mc ffi c2 after = (.halt outcome, post, finalFfi))
    (hbound : c2 ≤ K_body) :
    evaluateTargetHOL mc ffi (count + c2) before = (.halt outcome, post, finalFfi) ∧
      count + c2 ≤ count + K_body :=
  evaluateTargetHOL_clock_shift_halt ffi (prefix_evaluate identity ffi runPrefix) hhalt hbound

end GeneralWidth

section Width64
variable {S Q : Type}

/-- Clock-shift composition for `targetTerminatesAt`. -/
theorem targetTerminatesAt_of_clock_shift {σ : Type}
    (mc : MachineConfig 64 S Q) (ffi : HolFfiState σ)
    {c1 c2 K_body : Nat} {s0 s1 : S}
    (hshift : ∀ clock, evaluateTargetHOL mc ffi (c1 + clock) s0 =
      evaluateTargetHOL mc ffi clock s1)
    (hterm : targetTerminatesAt mc ffi s1 c2)
    (hbound : c2 ≤ K_body) :
    targetTerminatesAt mc ffi s0 (c1 + c2) ∧ c1 + c2 ≤ c1 + K_body := by
  rcases hterm with ⟨outcome, ms', ffi', hhalt⟩
  have hcomp := evaluateTargetHOL_clock_shift_halt ffi hshift hhalt hbound
  exact ⟨⟨outcome, ms', ffi', hcomp.1⟩, hcomp.2⟩

/-- Clock-shift composition for `targetTerminatesWithin` with a finite budget. -/
theorem targetTerminatesWithin_of_clock_shift {σ : Type}
    (mc : MachineConfig 64 S Q) (ffi : HolFfiState σ)
    {c1 K_body : Nat} {s0 s1 : S}
    (hshift : ∀ clock, evaluateTargetHOL mc ffi (c1 + clock) s0 =
      evaluateTargetHOL mc ffi clock s1)
    (hwithin : targetTerminatesWithin (.finite K_body) mc ffi s1) :
    targetTerminatesWithin (.finite (c1 + K_body)) mc ffi s0 := by
  rcases hwithin with ⟨c2, hbound, hterm⟩
  have hcomp := targetTerminatesAt_of_clock_shift mc ffi hshift hterm hbound
  exact ⟨c1 + c2, hcomp.2, hcomp.1⟩

/-- State-parameterized form of `InitE.matchingExecutionAt`, starting from an
arbitrary machine state `s` under configuration `mc`. -/
noncomputable def matchingExecutionFromState (mc : MachineConfig 64 S Q)
    (input : Guest.InputBlob) (s : S) (outcome : HolOutcome) (events : List HolIoEvent)
    (steps : Nat) : Prop :=
  ∃ targetOutcome post finalFfi,
    evaluateTargetHOL mc (sourceFfi input) steps s = (.halt targetOutcome, post, finalFfi) ∧
    matchingResult input outcome events targetOutcome finalFfi.ioEvents

@[simp] theorem matchingExecutionFromState_initialState (submission : Submission)
    (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (steps : Nat) :
    matchingExecutionFromState submission.machineConfig input
      (submission.initialState input) outcome events steps ↔
      matchingExecutionAt submission input outcome events steps :=
  Iff.rfl

/-- Quantitative clock-shift composition for `matchingExecutionFromState`. -/
theorem matchingExecutionFromState_of_clock_shift
    (mc : MachineConfig 64 S Q) (input : Guest.InputBlob)
    {c1 c2 K_body : Nat} {s0 s1 : S}
    {outcome : HolOutcome} {events : List HolIoEvent}
    (hshift : ∀ clock, evaluateTargetHOL mc (sourceFfi input) (c1 + clock) s0 =
      evaluateTargetHOL mc (sourceFfi input) clock s1)
    (hexec : matchingExecutionFromState mc input s1 outcome events c2)
    (hbound : c2 ≤ K_body) :
    matchingExecutionFromState mc input s0 outcome events (c1 + c2) ∧
      c1 + c2 ≤ c1 + K_body := by
  rcases hexec with ⟨targetOutcome, post, finalFfi, hhalt, hmatch⟩
  have hcomp := evaluateTargetHOL_clock_shift_halt (sourceFfi input) hshift hhalt hbound
  exact ⟨⟨targetOutcome, post, finalFfi, hcomp.1, hmatch⟩, hcomp.2⟩

/-- Finite-budget `Within` composition for `matchingExecutionFromState`. -/
theorem matchingExecutionFromState_within_of_clock_shift
    (mc : MachineConfig 64 S Q) (input : Guest.InputBlob)
    {c1 K_body : Nat} {s0 s1 : S}
    {outcome : HolOutcome} {events : List HolIoEvent}
    (hshift : ∀ clock, evaluateTargetHOL mc (sourceFfi input) (c1 + clock) s0 =
      evaluateTargetHOL mc (sourceFfi input) clock s1)
    (hwithin : (NatE.finite K_body).Within
      (matchingExecutionFromState mc input s1 outcome events)) :
    (NatE.finite (c1 + K_body)).Within
      (matchingExecutionFromState mc input s0 outcome events) := by
  rcases hwithin with ⟨c2, hbound, hexec⟩
  have hcomp := matchingExecutionFromState_of_clock_shift mc input hshift hexec hbound
  exact ⟨c1 + c2, hcomp.2, hcomp.1⟩

/-- Quantitative clock-shift composition directly producing `InitE.matchingExecutionAt`
at step `c1 + c2 ≤ c1 + K_body`. -/
theorem matchingExecutionAt_of_clock_shift
    (submission : Submission) (input : Guest.InputBlob)
    {c1 c2 K_body : Nat} {s1 : Flapjack.RiscV.L3.riscv_state}
    {outcome : HolOutcome} {events : List HolIoEvent}
    (hshift : ∀ clock,
      evaluateTargetHOL submission.machineConfig (sourceFfi input) (c1 + clock)
        (submission.initialState input) =
      evaluateTargetHOL submission.machineConfig (sourceFfi input) clock s1)
    (hexec : matchingExecutionFromState submission.machineConfig input s1 outcome events c2)
    (hbound : c2 ≤ K_body) :
    matchingExecutionAt submission input outcome events (c1 + c2) ∧
      c1 + c2 ≤ c1 + K_body :=
  matchingExecutionFromState_of_clock_shift submission.machineConfig input hshift hexec hbound

/-- Quantitative clock-shift composition producing
`(NatE.finite (c1 + K_body)).Within (matchingExecutionAt submission input outcome events)`. -/
theorem matchingExecutionAt_within_of_clock_shift
    (submission : Submission) (input : Guest.InputBlob)
    {c1 K_body : Nat} {s1 : Flapjack.RiscV.L3.riscv_state}
    {outcome : HolOutcome} {events : List HolIoEvent}
    (hshift : ∀ clock,
      evaluateTargetHOL submission.machineConfig (sourceFfi input) (c1 + clock)
        (submission.initialState input) =
      evaluateTargetHOL submission.machineConfig (sourceFfi input) clock s1)
    (hwithin : (NatE.finite K_body).Within
      (matchingExecutionFromState submission.machineConfig input s1 outcome events)) :
    (NatE.finite (c1 + K_body)).Within
      (matchingExecutionAt submission input outcome events) :=
  matchingExecutionFromState_within_of_clock_shift submission.machineConfig input hshift hwithin

/-- Under `mc.nextInterfer = fun _ state => state`, an `OrdinaryPrefix` of `count`
steps shifts `matchingExecutionFromState` by `count` steps and preserves the bound
`count + K_body`. -/
theorem ordinaryPrefix_matchingExecutionFromState
    (mc : MachineConfig 64 S Q)
    (identity : mc.nextInterfer = fun _ state => state)
    (input : Guest.InputBlob)
    {count c2 K_body : Nat} {before after : S}
    {outcome : HolOutcome} {events : List HolIoEvent}
    (runPrefix : OrdinaryPrefix mc count before after)
    (hexec : matchingExecutionFromState mc input after outcome events c2)
    (hbound : c2 ≤ K_body) :
    matchingExecutionFromState mc input before outcome events (count + c2) ∧
      count + c2 ≤ count + K_body :=
  matchingExecutionFromState_of_clock_shift mc input
    (prefix_evaluate identity (sourceFfi input) runPrefix) hexec hbound

/-- Under `mc.nextInterfer = fun _ state => state`, an `OrdinaryPrefix` of `count`
steps preserves `(NatE.finite K_body).Within (matchingExecutionFromState ...)`
with step bound `count + K_body`. -/
theorem ordinaryPrefix_matchingExecutionFromState_within
    (mc : MachineConfig 64 S Q)
    (identity : mc.nextInterfer = fun _ state => state)
    (input : Guest.InputBlob)
    {count K_body : Nat} {before after : S}
    {outcome : HolOutcome} {events : List HolIoEvent}
    (runPrefix : OrdinaryPrefix mc count before after)
    (hwithin : (NatE.finite K_body).Within
      (matchingExecutionFromState mc input after outcome events)) :
    (NatE.finite (count + K_body)).Within
      (matchingExecutionFromState mc input before outcome events) :=
  matchingExecutionFromState_within_of_clock_shift mc input
    (prefix_evaluate identity (sourceFfi input) runPrefix) hwithin

/-- Every `Submission.machineConfig` has the identity `nextInterfer` oracle. -/
theorem submission_machineConfig_nextInterfer (submission : Submission) :
    submission.machineConfig.nextInterfer = fun _ state => state :=
  rfl

/-- An `OrdinaryPrefix` from `submission.initialState input` to `after` shifts the
clock by `count` steps and preserves `matchingExecutionAt` with step bound `count + K_body`. -/
theorem ordinaryPrefix_preserves_matchingExecutionAt
    (submission : Submission) (input : Guest.InputBlob)
    {count c2 K_body : Nat} {after : Flapjack.RiscV.L3.riscv_state}
    {outcome : HolOutcome} {events : List HolIoEvent}
    (runPrefix : OrdinaryPrefix submission.machineConfig count
      (submission.initialState input) after)
    (hexec : matchingExecutionFromState submission.machineConfig input after outcome events c2)
    (hbound : c2 ≤ K_body) :
    matchingExecutionAt submission input outcome events (count + c2) ∧
      count + c2 ≤ count + K_body :=
  ordinaryPrefix_matchingExecutionFromState submission.machineConfig
    (submission_machineConfig_nextInterfer submission) input runPrefix hexec hbound

/-- An `OrdinaryPrefix` from `submission.initialState input` to `after` maps a
`K_body`-bounded post-bootstrap execution to a `(count + K_body)`-bounded
`matchingExecutionAt` witness. -/
theorem ordinaryPrefix_preserves_matchingExecutionAt_within
    (submission : Submission) (input : Guest.InputBlob)
    {count K_body : Nat} {after : Flapjack.RiscV.L3.riscv_state}
    {outcome : HolOutcome} {events : List HolIoEvent}
    (runPrefix : OrdinaryPrefix submission.machineConfig count
      (submission.initialState input) after)
    (hwithin : (NatE.finite K_body).Within
      (matchingExecutionFromState submission.machineConfig input after outcome events)) :
    (NatE.finite (count + K_body)).Within
      (matchingExecutionAt submission input outcome events) :=
  ordinaryPrefix_matchingExecutionFromState_within submission.machineConfig
    (submission_machineConfig_nextInterfer submission) input runPrefix hwithin

/-- If an `OrdinaryPrefix` connects two submissions' initial states under the same
`machineConfig`, then `matchingExecutionAt` at `c2 ≤ K_body` for the post-prefix
submission transfers to `matchingExecutionAt` at `count + c2 ≤ count + K_body`
for the pre-prefix submission. -/
theorem ordinaryPrefix_submission_matchingExecutionAt
    {subBefore subAfter : Submission}
    (hmc : subBefore.machineConfig = subAfter.machineConfig)
    (input : Guest.InputBlob)
    {count c2 K_body : Nat}
    {outcome : HolOutcome} {events : List HolIoEvent}
    (runPrefix : OrdinaryPrefix subBefore.machineConfig count
      (subBefore.initialState input) (subAfter.initialState input))
    (hexec : matchingExecutionAt subAfter input outcome events c2)
    (hbound : c2 ≤ K_body) :
    matchingExecutionAt subBefore input outcome events (count + c2) ∧
      count + c2 ≤ count + K_body := by
  have hexec' : matchingExecutionFromState subBefore.machineConfig input
      (subAfter.initialState input) outcome events c2 := by
    simpa only [matchingExecutionFromState, matchingExecutionAt, hmc] using hexec
  exact ordinaryPrefix_preserves_matchingExecutionAt subBefore input runPrefix hexec' hbound

/-- Finite-budget `Within` version of `ordinaryPrefix_submission_matchingExecutionAt`. -/
theorem ordinaryPrefix_submission_matchingExecutionAt_within
    {subBefore subAfter : Submission}
    (hmc : subBefore.machineConfig = subAfter.machineConfig)
    (input : Guest.InputBlob)
    {count K_body : Nat}
    {outcome : HolOutcome} {events : List HolIoEvent}
    (runPrefix : OrdinaryPrefix subBefore.machineConfig count
      (subBefore.initialState input) (subAfter.initialState input))
    (hwithin : (NatE.finite K_body).Within
      (matchingExecutionAt subAfter input outcome events)) :
    (NatE.finite (count + K_body)).Within
      (matchingExecutionAt subBefore input outcome events) := by
  rcases hwithin with ⟨c2, hbound, hexec⟩
  have hcomp := ordinaryPrefix_submission_matchingExecutionAt hmc input runPrefix hexec hbound
  exact ⟨count + c2, hcomp.2, hcomp.1⟩

end Width64

end InitECandidate.Solver
