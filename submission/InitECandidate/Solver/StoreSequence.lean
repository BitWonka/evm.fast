import InitECandidate.Solver.OrdinaryDomain
import InitECandidate.Solver.SourceCost
import InitECandidate.Solver.MemzeroChunk32

/-!
Unelaborated draft connecting a normal sequence result to its first scalar
store. This is conditional on expression evaluation and domain equivalence;
it is not a memzero loop bound or a target certificate.
-/
namespace InitECandidate.Solver.StoreSequence
open Flapjack Flapjack.Pancake.PanLang

/-- A normally completed sequence necessarily completed its first statement
normally; errors and other control outcomes are propagated by `Seq`. -/
theorem normal_seq_first_normal {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (first second : Prog (RiscV.Word 64))
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (h : (panSemTotalEvaluate primitive (.seq first second) state).1 = none) :
    (panSemTotalEvaluate primitive first state).1 = none := by
  by_cases hf : (panSemTotalEvaluate primitive first state).1 = none
  · exact hf
  · cases hr : (panSemTotalEvaluate primitive first state).1 with
    | none => exact False.elim (hf hr)
    | some result =>
        rw [panSemTotalEvaluate] at h
        simp [hr] at h

/-- Under explicit operand and domain premises, a normal sequence beginning
with a scalar store must start at an address in the ordinary interval. -/
theorem normal_seq_first_store_interval {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64)) (rest : Prog (RiscV.Word 64))
    (addr word : RiscV.Word 64)
    (hdom : ∀ x, state.memaddrs x = true ↔ InitE.ordinaryDomain x)
    (ha : evalPanSemStateExp state address = some (.word addr))
    (hv : evalPanSemStateExp state value = some (.word word))
    (h : (panSemTotalEvaluate primitive (.seq (.store address value) rest) state).1 = none) :
    holByteAligned addr = true ∧ BitVec.ofNat 64 InitE.sourceBase ≤ addr ∧
      addr < BitVec.ofNat 64 InitE.heapEnd := by
  have hfirst := normal_seq_first_normal primitive (.store address value) rest state h
  have hstore : (panSemTotalStoreClause state address value).1 = none := by
    simpa only [panSemTotalEvaluate] using hfirst
  exact InitECandidate.Solver.OrdinaryDomain.normal_word_store_in_ordinary_interval
    state address value addr word hdom ha hv hstore

/-- First word-store address in the aligned 32-byte memzero body. -/
def memzeroFirstAddress : Exp (RiscV.Word 64) :=
  .op .add [.var .local "dst", .var .local "i"]

/-- Remaining body after its first store, extracted from the same fixed AST. -/
def memzero32Rest : Prog (RiscV.Word 64) :=
  match Guest.Software.guestFn_memzero with
  | .function f =>
      match f.body with
      | .dec _ _ _ (.seq (.ite _ (.seq (.while _ (.seq (.store _ _) rest)) _) _) _) => rest
      | _ => .skip
  | _ => .skip

/-- Proposed exact syntactic decomposition of the body extracted by the
separate chunk module. -/
theorem memzero32Body_shape :
    InitECandidate.Solver.MemzeroChunk32.extractedBody =
      some (.seq (.store memzeroFirstAddress (.const (BitVec.ofNat 64 0))) memzero32Rest) := by
  rfl

/-- Conditional first-store interval fact for the actual extracted body. -/
theorem normal_memzero32_body_first_store_interval {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (body : Prog (RiscV.Word 64)) (addr : RiscV.Word 64)
    (hbody : InitECandidate.Solver.MemzeroChunk32.extractedBody = some body)
    (hdom : ∀ x, state.memaddrs x = true ↔ InitE.ordinaryDomain x)
    (ha : evalPanSemStateExp state memzeroFirstAddress = some (.word addr))
    (hv : evalPanSemStateExp state (.const (BitVec.ofNat 64 0)) =
      some (.word (BitVec.ofNat 64 0)))
    (h : (panSemTotalEvaluate primitive body state).1 = none) :
    holByteAligned addr = true ∧ BitVec.ofNat 64 InitE.sourceBase ≤ addr ∧
      addr < BitVec.ofNat 64 InitE.heapEnd := by
  have hshape : body = .seq (.store memzeroFirstAddress (.const (BitVec.ofNat 64 0))) memzero32Rest :=
    Option.some.inj (hbody.symm.trans memzero32Body_shape)
  subst body
  exact normal_seq_first_store_interval primitive state memzeroFirstAddress
    (.const (BitVec.ofNat 64 0)) memzero32Rest addr (BitVec.ofNat 64 0) hdom ha hv h

end InitECandidate.Solver.StoreSequence
