import InitECandidate.Solver.InputCopyAst
import InitECandidate.Solver.Chunk32Control
import InitECandidate.Solver.StoreSequence

/-!
Unelaborated research draft: normal-result local-state progression for the
fixed 32-byte memzero body. It depends on other unverified candidate modules,
and does not establish domain invariants, loop reachability or a score.
-/
namespace InitECandidate.Solver.Chunk32Step
open Flapjack Flapjack.Pancake.PanLang

/-- Prepending a word store preserves the normal-result local transformation
of the remaining program, assuming that transformation for every state. -/
theorem prepend_store_normal_step {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (address value : Exp (RiscV.Word 64)) (rest : Prog (RiscV.Word 64))
    (index : RiscV.Word 64)
    (hrest : ∀ state : PanSemState (RiscV.Word 64) (FfiState σ),
      state.locals "i" = some (.word index) →
      (panSemTotalEvaluate primitive rest state).1 = none →
      (panSemTotalEvaluate primitive rest state).2.locals =
        updatePanValueMap state.locals "i" (.word (index + BitVec.ofNat 64 32))) :
    ∀ state : PanSemState (RiscV.Word 64) (FfiState σ),
      state.locals "i" = some (.word index) →
      (panSemTotalEvaluate primitive (.seq (.store address value) rest) state).1 = none →
      (panSemTotalEvaluate primitive (.seq (.store address value) rest) state).2.locals =
        updatePanValueMap state.locals "i" (.word (index + BitVec.ofNat 64 32)) := by
  intro state hi hnormal
  have hfirst := InitECandidate.Solver.StoreSequence.normal_seq_first_normal primitive
    (.store address value) rest state hnormal
  let next := panSemFixClock state.clock (panSemTotalEvaluate primitive (.store address value) state).2
  have hlocals : next.locals = state.locals := by
    dsimp only [next, panSemFixClock]
    rw [panSemTotalEvaluate]
    exact InitECandidate.Solver.InputCopyAst.store_preserves_locals state address value
  have hnormalRest : (panSemTotalEvaluate primitive rest next).1 = none := by
    have h := hnormal
    rw [panSemTotalEvaluate] at h
    simpa only [hfirst, next] using h
  have hstep := hrest next (by simpa only [hlocals] using hi) hnormalRest
  rw [panSemTotalEvaluate]
  simpa only [hfirst, next, hlocals] using hstep

/-- Proposed normal local update for the fixed `i := i + 32` assignment. -/
theorem increment_normal_step {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) (index : RiscV.Word 64) :
    ∀ state : PanSemState (RiscV.Word 64) (FfiState σ),
      state.locals "i" = some (.word index) →
      (panSemTotalEvaluate primitive (.assign .local "i"
        (.op .add [.var .local "i", .const (BitVec.ofNat 64 32)])) state).1 = none →
      (panSemTotalEvaluate primitive (.assign .local "i"
        (.op .add [.var .local "i", .const (BitVec.ofNat 64 32)])) state).2.locals =
        updatePanValueMap state.locals "i" (.word (index + BitVec.ofNat 64 32)) := by
  intro state hi hnormal
  have heval : evalPanSemStateExp state
      (.op .add [.var .local "i", .const (BitVec.ofNat 64 32)]) =
        some (.word (index + BitVec.ofNat 64 32)) := by
    simp [evalPanSemStateExp, evalPanValueExp, evalPanValueExp.evalPanValueExps, hi,
      panSemBitVec64MemoryAccess_wordOp, wordOpHOL, wordOp]
  have hclause : (panSemTotalAssignClause state .local "i"
      (.op .add [.var .local "i", .const (BitVec.ofNat 64 32)])).1 = none := by
    simpa only [panSemTotalEvaluate] using hnormal
  have h := Flapjack.L3.Pilot.assign_none_locals state "i"
    (.op .add [.var .local "i", .const (BitVec.ofNat 64 32)])
    (.word (index + BitVec.ofNat 64 32)) heval hclause
  simpa only [panSemTotalEvaluate] using h

/-- Proposed normal-result local update for the concrete four-store body. -/
theorem chunk32Body_normal_step {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) (index : RiscV.Word 64) :
    ∀ state : PanSemState (RiscV.Word 64) (FfiState σ),
      state.locals "i" = some (.word index) →
      (panSemTotalEvaluate primitive InitECandidate.Solver.Chunk32Control.chunk32Body state).1 = none →
      (panSemTotalEvaluate primitive InitECandidate.Solver.Chunk32Control.chunk32Body state).2.locals =
        updatePanValueMap state.locals "i" (.word (index + BitVec.ofNat 64 32)) := by
  unfold InitECandidate.Solver.Chunk32Control.chunk32Body
  apply prepend_store_normal_step primitive
  apply prepend_store_normal_step primitive
  apply prepend_store_normal_step primitive
  apply prepend_store_normal_step primitive
  exact increment_normal_step primitive index

end InitECandidate.Solver.Chunk32Step
