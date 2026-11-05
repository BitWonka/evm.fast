import Guest.SoftwareAst
import Flapjack.Pancake.PanToTarget.ProductionSourceEntry
import Flapjack.Pancake.Semantics.PanSem.TotalEvalAgree
import InitE.SourceDeclarationsCore

/-!
Conditional AST name-range bridge. Draft only; not Lean-elaborated.
Rangedness of the original AST is an explicit, unproved premise.
This does not establish state invariants, execution bounds or a certificate.
-/
namespace InitECandidate.Solver.ParserRange
open Flapjack Flapjack.Pancake.PanLang Flapjack.Pancake.PanToTarget
open Flapjack.Basis.Pure.MlString

/-- Proposed byte-range closure for parameter lists decoded from HOL. -/
theorem paramsOfHOL_byteRanged (parameters : List (MlS × ShapeHOL)) :
    ListParamByteRanged (parameters.map paramOfHOL) := by
  intro parameter h
  obtain ⟨⟨name, shape⟩, _, rfl⟩ := List.mem_map.mp h
  exact ⟨nameRanged_toStringOfBytes_bridge name, shapeOfHOL_byteRanged_bridge shape⟩

/-- Proposed extension of the existing program/expression/shape decoded-range
lemmas to a whole decoded declaration. -/
theorem declOfHOL_byteRanged (declaration : DeclHOL 64) :
    DeclByteRanged (declOfHOL declaration) := by
  cases declaration with
  | function function =>
      exact ⟨nameRanged_toStringOfBytes_bridge function.name,
        paramsOfHOL_byteRanged function.params,
        progOfHOL_byteRanged_bridge function.body,
        shapeOfHOL_byteRanged_bridge function.returnShape⟩
  | decl shape name value =>
      exact ⟨shapeOfHOL_byteRanged_bridge shape, nameRanged_toStringOfBytes_bridge name,
        expOfHOL_byteRanged_bridge value⟩
  | exnDecl name shape =>
      exact ⟨nameRanged_toStringOfBytes_bridge name, shapeOfHOL_byteRanged_bridge shape⟩
  | name name fields =>
      exact ⟨nameRanged_toStringOfBytes_bridge name, paramsOfHOL_byteRanged fields⟩

/-- A byte-normalized production view of the actual exact source declarations. -/
def canonicalDeclarations : List (Decl (BitVec 64)) :=
  (Guest.Software.guestAst.map declToHOL).map declOfHOL

theorem canonicalDeclarations_byteRanged :
    ∀ declaration ∈ canonicalDeclarations, DeclByteRanged declaration := by
  intro declaration h
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp h
  exact declOfHOL_byteRanged source

theorem canonicalDeclarations_exact :
    canonicalDeclarations.map declToHOL = Guest.Software.guestAst.map declToHOL := by
  simp [canonicalDeclarations, List.map_map]

/-- Conditional original-source entry bridge without importing Guest.Source,
whose included text is absent in the isolated verifier project. -/
theorem software_source_entry_matches_compiler
    (hranged : ∀ d ∈ Guest.Software.guestAst, DeclByteRanged d) :
    (panTargetMoveStartToFront "main"
      (panTargetDeclarationsWithDefaultMain Guest.Software.guestAst)).map declToHOL =
        InitE.sourceDeclarations := by
  simpa [InitE.sourceDeclarations] using
    (Flapjack.Pancake.PanToTarget.sourceEntry_encode Guest.Software.guestAst hranged)

end InitECandidate.Solver.ParserRange
