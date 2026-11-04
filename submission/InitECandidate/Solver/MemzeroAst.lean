import Guest.SoftwareAst
import InitECandidate.Solver.SourceCost

/-!
Draft only. This isolates the candidate loop from the fixed software AST;
`rfl` and the generic FFI proof have not been checked by Lean. It does not
bound the rest of memzero, prove execution termination, or bound target steps.
-/
namespace InitECandidate.Solver.MemzeroAst
open Flapjack
open Flapjack.Pancake.PanLang

/-- The final byte-at-a-time loop of the generated memzero function, provided
its outer AST has the expected shape. -/
def extractedTail : Option (Prog (BitVec 64)) :=
  match Guest.Software.guestFn_memzero with
  | .function f =>
      match f.body with
      | .dec _ _ _ (.seq _ (.seq _ (.seq tail _))) => some tail
      | _ => none
  | _ => none

/-- Proposed definitional identification with the source-cost pilot. -/
theorem extractedTail_eq : extractedTail = some Flapjack.L3.Pilot.tailLoop := by
  rfl

/-- Conditional application of the generic-FFI pilot to the extracted AST.
This bounds consumed source clock, not the whole memzero or guest execution. -/
theorem extractedTail_cost {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) (n0 : RiscV.Word 64)
    (p : Prog (RiscV.Word 64)) (hp : extractedTail = some p)
    (s : PanSemState (RiscV.Word 64) (FfiState σ))
    (hs : ∃ i, s.locals "i" = some (.word i) ∧ s.locals "n" = some (.word n0)) :
    s.clock ≤ (panSemTotalEvaluate primitive p s).2.clock +
      (match s.locals "i" with | some (.word i) => n0.toNat - i.toNat | _ => 0) * (0 + 1) := by
  have eq : p = Flapjack.L3.Pilot.tailLoop := Option.some.inj (hp.symm.trans extractedTail_eq)
  subst p
  exact Flapjack.L3.Pilot.tailLoop_cost primitive n0 s hs

end InitECandidate.Solver.MemzeroAst
