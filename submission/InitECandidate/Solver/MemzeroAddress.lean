import InitECandidate.Solver.StoreSequence

/-!
Unelaborated draft connecting the fixed memzero first-store address to local
word values. It does not establish those locals at entry or prove the loop.
-/
namespace InitECandidate.Solver.MemzeroAddress
open Flapjack Flapjack.Pancake.PanLang

/-- Proposed evaluation of the first store address from explicit locals. -/
theorem firstAddress_eval {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (dst index : RiscV.Word 64)
    (hdst : state.locals "dst" = some (.word dst))
    (hi : state.locals "i" = some (.word index)) :
    evalPanSemStateExp state InitECandidate.Solver.StoreSequence.memzeroFirstAddress =
      some (.word (dst + index)) := by
  simp [evalPanSemStateExp, InitECandidate.Solver.StoreSequence.memzeroFirstAddress,
    evalPanValueExp, evalPanValueExp.evalPanValueExps, hdst, hi,
    panSemBitVec64MemoryAccess_wordOp, wordOpHOL, wordOp]

/-- Proposed evaluation of the concrete stored zero value. -/
theorem zeroValue_eval {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) :
    evalPanSemStateExp state (.const (BitVec.ofNat 64 0)) =
      some (.word (BitVec.ofNat 64 0)) := by
  simp [evalPanSemStateExp, evalPanValueExp]

/-- Proposed consequence for a normal run of the fixed chunk body, under
explicit state-domain and local-word assumptions. -/
theorem normal_chunk_first_address_interval {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (body : Prog (RiscV.Word 64)) (dst index : RiscV.Word 64)
    (hbody : InitECandidate.Solver.MemzeroChunk32.extractedBody = some body)
    (hdom : ∀ x, state.memaddrs x = true ↔ InitE.ordinaryDomain x)
    (hdst : state.locals "dst" = some (.word dst))
    (hi : state.locals "i" = some (.word index))
    (h : (panSemTotalEvaluate primitive body state).1 = none) :
    holByteAligned (dst + index) = true ∧
      BitVec.ofNat 64 InitE.sourceBase ≤ dst + index ∧
      dst + index < BitVec.ofNat 64 InitE.heapEnd := by
  exact InitECandidate.Solver.StoreSequence.normal_memzero32_body_first_store_interval
    primitive state body (dst + index) hbody hdom
    (firstAddress_eval state dst index hdst hi) (zeroValue_eval state) h

end InitECandidate.Solver.MemzeroAddress
