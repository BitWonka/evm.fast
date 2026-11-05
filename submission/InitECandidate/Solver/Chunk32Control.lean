import InitECandidate.Solver.MemzeroChunk32
import InitECandidate.Solver.SourceCost

/-!
Unelaborated draft about control results of the fixed memzero 32-byte body.
It does not prove domain invariants, loop iteration bounds or a target score.
-/
namespace InitECandidate.Solver.Chunk32Control
open Flapjack Flapjack.Pancake.PanLang

/-- Proposed result shape for one generic word-store clause. -/
theorem store_clause_result {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64)) :
    (panSemTotalStoreClause state address value).1 = none ∨
      (panSemTotalStoreClause state address value).1 = some .error := by
  cases he : evalPanSemStateExp state address with
  | none => simp [panSemTotalStoreClause, panSemTotalExprStep, he]
  | some addressValue =>
      cases addressValue with
      | rStruct fields => simp [panSemTotalStoreClause, panSemTotalExprStep, he]
      | nStruct name fields => simp [panSemTotalStoreClause, panSemTotalExprStep, he]
      | word addr =>
          cases hv : evalPanSemStateExp state value with
          | none => simp [panSemTotalStoreClause, panSemTotalExprStep, he, hv]
          | some stored =>
              cases hm : panValueStoreWithAccess state.memory panSemBitVec64BytesInWord addr
                  stored (some (panSemBitVec64MemoryAccess state)) with
              | none => simp [panSemTotalStoreClause, panSemTotalExprStep, he, hv, hm]
              | some memory => simp [panSemTotalStoreClause, panSemTotalExprStep, he, hv, hm]

theorem store_no_continue {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64)) :
    (panSemTotalEvaluate primitive (.store address value) state).1 ≠ some .continue := by
  rw [panSemTotalEvaluate]
  rcases store_clause_result state address value with h | h <;> rw [h] <;> simp

theorem assign_no_continue {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (kind : VarKind) (name : VarName) (value : Exp (RiscV.Word 64)) :
    (panSemTotalEvaluate primitive (.assign kind name value) state).1 ≠ some .continue := by
  rw [panSemTotalEvaluate]
  rcases Flapjack.L3.Pilot.assign_res state kind name value with h | h <;> rw [h] <;> simp

theorem seq_no_continue {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (first second : Prog (RiscV.Word 64))
    (hfirst : ∀ s : PanSemState (RiscV.Word 64) (FfiState σ),
      (panSemTotalEvaluate primitive first s).1 ≠ some .continue)
    (hsecond : ∀ s : PanSemState (RiscV.Word 64) (FfiState σ),
      (panSemTotalEvaluate primitive second s).1 ≠ some .continue) :
    ∀ s : PanSemState (RiscV.Word 64) (FfiState σ),
      (panSemTotalEvaluate primitive (.seq first second) s).1 ≠ some .continue := by
  intro state
  rw [panSemTotalEvaluate]
  cases hr : (panSemTotalEvaluate primitive first state).1 with
  | none =>
      simpa [hr] using hsecond (panSemFixClock state.clock (panSemTotalEvaluate primitive first state).2)
  | some result =>
      simpa [hr] using hfirst state

def chunk32Body : Prog (RiscV.Word 64) :=
  .seq (.store (.op .add [.var .local "dst", .var .local "i"]) (.const (BitVec.ofNat 64 0)))
    (.seq (.store (.op .add [.var .local "dst", .var .local "i", .const (BitVec.ofNat 64 8)]) (.const (BitVec.ofNat 64 0)))
      (.seq (.store (.op .add [.var .local "dst", .var .local "i", .const (BitVec.ofNat 64 16)]) (.const (BitVec.ofNat 64 0)))
        (.seq (.store (.op .add [.var .local "dst", .var .local "i", .const (BitVec.ofNat 64 24)]) (.const (BitVec.ofNat 64 0)))
          (.assign .local "i" (.op .add [.var .local "i", .const (BitVec.ofNat 64 32)])))))

theorem extractedBody_eq :
    InitECandidate.Solver.MemzeroChunk32.extractedBody = some chunk32Body := by
  rfl

theorem chunk32Body_no_continue {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) :
    ∀ s : PanSemState (RiscV.Word 64) (FfiState σ),
      (panSemTotalEvaluate primitive chunk32Body s).1 ≠ some .continue := by
  unfold chunk32Body
  apply seq_no_continue primitive
  · intro s; exact store_no_continue primitive s _ _
  · apply seq_no_continue primitive
    · intro s; exact store_no_continue primitive s _ _
    · apply seq_no_continue primitive
      · intro s; exact store_no_continue primitive s _ _
      · apply seq_no_continue primitive
        · intro s; exact store_no_continue primitive s _ _
        · intro s; exact assign_no_continue primitive s _ _ _

end InitECandidate.Solver.Chunk32Control
