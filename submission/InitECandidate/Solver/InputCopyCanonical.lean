import InitECandidate.Solver.InputCopyAst
import InitECandidate.Solver.ParserRange

/-! Diagnostic-only wrapper; no theorem is yet kernel-verified. -/
namespace InitECandidate.Solver.InputCopyAst
open Flapjack Flapjack.Pancake.PanLang

/-- Proposed fixed-AST reduction after the exact/production byte codecs. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem canonical_trap_lookup_reduction
    (initial : Option (PanSemFunctionEntry (RiscV.Word 64))) :
    installDeclarationLookup "trap_with"
      InitECandidate.Solver.ParserRange.canonicalDeclarations initial = some trapWithEntry := by
  rfl

/-- Proposed trap entry in a successfully installed canonical declaration
state. This does not assert that declaration evaluation succeeds. -/
theorem canonical_declared_trap_lookup {σ : Type}
    (state result : PanSemDeclarationState (RiscV.Word 64) σ)
    (h : evaluateDecls state InitECandidate.Solver.ParserRange.canonicalDeclarations =
      some result) :
    lookupInfo "trap_with" result.code = some trapWithEntry := by
  rw [evaluateDecls_code_projection _ state result h, installDeclarationCode_lookup]
  exact canonical_trap_lookup_reduction _

theorem canonical_entry_trap_code {σ : Type}
    (machine : PanSemState (RiscV.Word 64) (FfiState σ))
    (state result : PanSemDeclarationState (RiscV.Word 64) σ)
    (h : evaluateDecls state InitECandidate.Solver.ParserRange.canonicalDeclarations =
      some result) :
    panSemCodeLookup (panSemEntryStateOfDecls machine result).code "trap_with" =
      some ([("code", .one)], trapWithBody, .one) := by
  rw [panSemEntryStateOfDecls_codeLookup, canonical_declared_trap_lookup state result h]
  rfl

end InitECandidate.Solver.InputCopyAst
