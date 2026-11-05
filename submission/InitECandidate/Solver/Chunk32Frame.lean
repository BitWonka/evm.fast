import InitECandidate.Solver.OrdinaryDomain
import InitECandidate.Solver.Chunk32Control

/-!
Unelaborated draft: compose the proposed store and assignment domain frames
through sequences to the fixed 32-byte memzero body. It does not show loop
invariants, operand values, memory contents, termination or a target bound.
-/
namespace InitECandidate.Solver.Chunk32Frame
open Flapjack Flapjack.Pancake.PanLang

/-- Proposed domain frame for an evaluated word-store statement. -/
theorem store_domain {σ : Type} (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64)) :
    (panSemTotalEvaluate primitive (.store address value) state).2.memaddrs = state.memaddrs := by
  rw [panSemTotalEvaluate]
  exact InitECandidate.Solver.OrdinaryDomain.storeClause_preserves_domain state address value

/-- Proposed domain frame for an evaluated assignment. -/
theorem assign_domain {σ : Type} (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (kind : VarKind) (name : VarName) (value : Exp (RiscV.Word 64)) :
    (panSemTotalEvaluate primitive (.assign kind name value) state).2.memaddrs = state.memaddrs := by
  rw [panSemTotalEvaluate]
  exact InitECandidate.Solver.OrdinaryDomain.assignClause_preserves_domain state kind name value

/-- Proposed sequence frame, including error and other early outcomes. -/
theorem seq_domain {σ : Type} (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (first second : Prog (RiscV.Word 64))
    (hfirst : ∀ s : PanSemState (RiscV.Word 64) (FfiState σ),
      (panSemTotalEvaluate primitive first s).2.memaddrs = s.memaddrs)
    (hsecond : ∀ s : PanSemState (RiscV.Word 64) (FfiState σ),
      (panSemTotalEvaluate primitive second s).2.memaddrs = s.memaddrs) :
    ∀ s : PanSemState (RiscV.Word 64) (FfiState σ),
      (panSemTotalEvaluate primitive (.seq first second) s).2.memaddrs = s.memaddrs := by
  intro state
  rw [panSemTotalEvaluate]
  cases hr : (panSemTotalEvaluate primitive first state).1 with
  | none =>
      simp only [hr]
      have hh := hsecond (panSemFixClock state.clock (panSemTotalEvaluate primitive first state).2)
      simpa only [panSemFixClock, hfirst state] using hh
  | some result =>
      simp [hr, panSemFixClock, hfirst state]

/-- Proposed frame for all outcomes of the concrete four-store/assign body. -/
theorem chunk32Body_domain {σ : Type} (primitive : PanPrimitiveHandler (RiscV.Word 64)) :
    ∀ s : PanSemState (RiscV.Word 64) (FfiState σ),
      (panSemTotalEvaluate primitive InitECandidate.Solver.Chunk32Control.chunk32Body s).2.memaddrs =
        s.memaddrs := by
  unfold InitECandidate.Solver.Chunk32Control.chunk32Body
  apply seq_domain primitive
  · intro s; exact store_domain primitive s _ _
  · apply seq_domain primitive
    · intro s; exact store_domain primitive s _ _
    · apply seq_domain primitive
      · intro s; exact store_domain primitive s _ _
      · apply seq_domain primitive
        · intro s; exact store_domain primitive s _ _
        · intro s; exact assign_domain primitive s _ _ _

end InitECandidate.Solver.Chunk32Frame
