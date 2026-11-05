import Guest.SoftwareAst
import InitECandidate.Solver.SourceCost

/-!
Unelaborated draft extracting the 32-byte body from the fixed memzero AST.
The result concerns the body clock only; it does not prove its memory frame,
number of executions, loop termination, or a target bound.
-/
namespace InitECandidate.Solver.MemzeroChunk32
open Flapjack Flapjack.Pancake.PanLang

/-- The aligned branch's first while-body in the fixed source AST. -/
def extractedBody : Option (Prog (BitVec 64)) :=
  match Guest.Software.guestFn_memzero with
  | .function f =>
      match f.body with
      | .dec _ _ _ (.seq (.ite _ (.seq (.while _ body) _) _) _) => some body
      | _ => none
  | _ => none

/-- Proposed syntactic fact: four stores followed by one assignment charge no
source clock in the already-built `SourceCost` framework. -/
theorem extractedBody_clockFree :
    extractedBody.map Flapjack.L3.ClockFree = some true := by
  rfl

theorem extractedBody_clock {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) (body : Prog (RiscV.Word 64))
    (hbody : extractedBody = some body)
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) :
    (panSemTotalEvaluate primitive body state).2.clock = state.clock := by
  have hfree : Flapjack.L3.ClockFree body = true := by
    simpa [hbody] using extractedBody_clockFree
  exact Flapjack.L3.clockFree_clock primitive body state hfree

end InitECandidate.Solver.MemzeroChunk32
