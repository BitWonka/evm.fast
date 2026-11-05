import Guest.SoftwareAst
import InitECandidate.Solver.SourceCost
import Flapjack.Pancake.Semantics.PanSem.TotalEvalExpBridge
import Flapjack.Pancake.Semantics.PanSem.EntryState

/-!
Uncompiled draft. This isolates the body of the input-copy loop in the fixed
software AST. It does not bound the number of iterations, prove normal
completion of shared-memory operations, bound `alloc`, or bound the guest or
target program as a whole.
-/
namespace InitECandidate.Solver.InputCopyAst
open Flapjack
open Flapjack.Pancake.PanLang
open PanSemStateFiniteExact

/-- The code-map projection of declaration installation, independent of the
runtime values used to check declarations. -/
def installDeclarationCode : List (Decl (RiscV.Word 64)) →
    InfoMap (PanSemFunctionEntry (RiscV.Word 64)) →
    InfoMap (PanSemFunctionEntry (RiscV.Word 64))
  | [], code => code
  | .function function :: rest, code =>
      installDeclarationCode rest (panSemDeclUpdateInfo code function.name
        { params := function.params, body := function.body, returnShape := function.returnShape })
  | _ :: rest, code => installDeclarationCode rest code

/-- Track one code-map key through declaration installation. A later function
with the same name replaces an earlier one. -/
def installDeclarationLookup (key : String) : List (Decl (RiscV.Word 64)) →
    Option (PanSemFunctionEntry (RiscV.Word 64)) →
    Option (PanSemFunctionEntry (RiscV.Word 64))
  | [], value => value
  | .function function :: rest, value =>
      installDeclarationLookup key rest
        (if function.name == key then
          some { params := function.params, body := function.body, returnShape := function.returnShape }
         else value)
  | _ :: rest, value => installDeclarationLookup key rest value

theorem installDeclarationCode_lookup (key : String) :
    ∀ (declarations : List (Decl (RiscV.Word 64))) code,
      lookupInfo key (installDeclarationCode declarations code) =
        installDeclarationLookup key declarations (lookupInfo key code) := by
  intro declarations
  induction declarations with
  | nil => intro code; rfl
  | cons declaration rest ih =>
      intro code
      cases declaration with
      | name name fields => simpa [installDeclarationCode, installDeclarationLookup] using ih code
      | decl shape name expression => simpa [installDeclarationCode, installDeclarationLookup] using ih code
      | exnDecl name shape => simpa [installDeclarationCode, installDeclarationLookup] using ih code
      | function function =>
          simp only [installDeclarationCode, installDeclarationLookup]
          rw [ih, lookupInfo_panSemDeclUpdateInfo, FLOOKUP_update]

/-- Proposed production-carrier analogue of the upstream exact-carrier
`evaluateDeclsHOLFinite_functions` code-frame theorem. -/
theorem evaluateDecls_code_projection {σ : Type} :
    ∀ (declarations : List (Decl (RiscV.Word 64)))
      (state result : PanSemDeclarationState (RiscV.Word 64) σ),
      evaluateDecls state declarations = some result →
      result.code = installDeclarationCode declarations state.code := by
  intro declarations
  induction declarations with
  | nil =>
      intro state result h
      simp only [evaluateDecls, Option.some.injEq] at h
      subst result
      rfl
  | cons declaration rest ih =>
      intro state result h
      cases declaration with
      | name name fields =>
          simp only [evaluateDecls, installDeclarationCode] at h ⊢
          exact ih state result h
      | decl shape name expression =>
          simp only [evaluateDecls, installDeclarationCode] at h ⊢
          split at h
          · cases h
          · split at h
            · have hcode := ih _ result h
              simpa using hcode
            · cases h
      | function function =>
          simp only [evaluateDecls, installDeclarationCode] at h ⊢
          split at h
          · exact ih _ result h
          · cases h
      | exnDecl exception shape =>
          simp only [evaluateDecls, installDeclarationCode] at h ⊢
          split at h
          · cases h
          · split at h
            · have hcode := ih _ result h
              simpa using hcode
            · cases h

/-- A statement never returns a value from the current function. -/
def NeverReturns {σ : Type} (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (program : Prog (RiscV.Word 64)) : Prop :=
  ∀ (state : PanSemState (RiscV.Word 64) (FfiState σ)) value,
    (panSemTotalEvaluate primitive program state).1 ≠ some (.returned value)

theorem neverReturns_seq {σ : Type} (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (first second : Prog (RiscV.Word 64))
    (hfirst : NeverReturns (σ := σ) primitive first)
    (hsecond : NeverReturns (σ := σ) primitive second) :
    NeverReturns (σ := σ) primitive (.seq first second) := by
  intro state value
  rw [panSemTotalEvaluate]
  cases hr : (panSemTotalEvaluate primitive first state).1 with
  | none =>
      simpa [hr] using hsecond (panSemFixClock state.clock
        (panSemTotalEvaluate primitive first state).2) value
  | some result =>
      have h := hfirst state value
      simpa [hr] using h

theorem neverReturns_raise {σ : Type} (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (exception : ExceptionId) (expression : Exp (RiscV.Word 64)) :
    NeverReturns (σ := σ) primitive (.raise exception expression) := by
  intro state value
  rw [panSemTotalEvaluate]
  cases he : evalPanSemStateExp state expression with
  | none => simp [panSemTotalRaiseClause, panSemTotalExprStep, he]
  | some raised =>
      cases hs : state.exceptionShapes exception with
      | none => simp [panSemTotalRaiseClause, panSemTotalExprStep, he, hs]
      | some shape =>
          by_cases hcheck : panShapeMatches shape (panSemShapeOf raised) = true ∧
              sizeOfShWithCtxt state.structs.toHOL (panSemShapeOf raised) ≤ 32
          · simp [panSemTotalRaiseClause, panSemTotalExprStep, he, hs, hcheck]
          · simp [panSemTotalRaiseClause, panSemTotalExprStep, he, hs, hcheck]

theorem shMemStoreResult_not_returned {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (result : PanShMemStoreResult (RiscV.Word 64) σ) (value : PanValue (RiscV.Word 64)) :
    (panSemTotalShMemStoreResult state result).1 ≠ some (.returned value) := by
  cases result <;> simp [panSemTotalShMemStoreResult]

theorem neverReturns_shMemStore {σ : Type} (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (size : OpSize) (address value : Exp (RiscV.Word 64)) :
    NeverReturns (σ := σ) primitive (.shMemStore size address value) := by
  intro state result
  rw [panSemTotalEvaluate]
  cases he : evalPanSemStateExp state address with
  | none => simp [panSemTotalShMemStoreClause, panSemTotalExprStep, he]
  | some addressValue =>
      cases addressValue with
      | rStruct fields => simp [panSemTotalShMemStoreClause, panSemTotalExprStep, he]
      | nStruct name fields => simp [panSemTotalShMemStoreClause, panSemTotalExprStep, he]
      | word addr =>
          cases hv : evalPanSemStateExp state value with
          | none => simp [panSemTotalShMemStoreClause, panSemTotalExprStep, he, hv]
          | some stored =>
              cases stored with
              | rStruct fields => simp [panSemTotalShMemStoreClause, panSemTotalExprStep, he, hv]
              | nStruct name fields => simp [panSemTotalShMemStoreClause, panSemTotalExprStep, he, hv]
              | word bytes =>
                  have hn := shMemStoreResult_not_returned state
                    (panShMemStore (panSemTotalShMemContext state) (panSemTotalShMemState state)
                      bytes addr size) result
                  simpa [panSemTotalShMemStoreClause, panSemTotalExprStep, he, hv] using hn

/-- Proposed reusable result-shape fact for external calls. -/
theorem extCallStep_not_returned {α σ : Type}
    (state : PanSemState α (FfiState σ))
    (p1 n1 p2 n2 : Option (PanValue α))
    (readBytes : α → α → Option (List UInt8))
    (invoke : FfiState σ → FfiName → List UInt8 → List UInt8 → FfiResult σ)
    (writeBytes : PanSemState α (FfiState σ) → α → List UInt8 → PanSemState α (FfiState σ))
    (name : FunName) (result : PanValue α) :
    (panSemTotalExtCallStep state p1 n1 p2 n2 readBytes invoke writeBytes name).1 ≠
      some (.returned result) := by
  cases p1 with
  | none => simp [panSemTotalExtCallStep]
  | some v1 =>
    cases v1 with
    | rStruct fields => simp [panSemTotalExtCallStep]
    | nStruct name fields => simp [panSemTotalExtCallStep]
    | word a1 =>
      cases n1 with
      | none => simp [panSemTotalExtCallStep]
      | some v2 =>
        cases v2 with
        | rStruct fields => simp [panSemTotalExtCallStep]
        | nStruct name fields => simp [panSemTotalExtCallStep]
        | word l1 =>
          cases p2 with
          | none => simp [panSemTotalExtCallStep]
          | some v3 =>
            cases v3 with
            | rStruct fields => simp [panSemTotalExtCallStep]
            | nStruct name fields => simp [panSemTotalExtCallStep]
            | word a2 =>
              cases n2 with
              | none => simp [panSemTotalExtCallStep]
              | some v4 =>
                cases v4 with
                | rStruct fields => simp [panSemTotalExtCallStep]
                | nStruct name fields => simp [panSemTotalExtCallStep]
                | word l2 =>
                  cases hr1 : readBytes a1 l1 with
                  | none => simp [panSemTotalExtCallStep, hr1]
                  | some bytes1 =>
                    cases hr2 : readBytes a2 l2 with
                    | none => simp [panSemTotalExtCallStep, hr1, hr2]
                    | some bytes2 =>
                      cases hf : invoke state.ffi (.extCall name) bytes1 bytes2 with
                      | final event => simp [panSemTotalExtCallStep, hr1, hr2, hf]
                      | returned nextFfi output => simp [panSemTotalExtCallStep, hr1, hr2, hf]

theorem neverReturns_extCall {σ : Type} (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (name : FunName) (a b c d : Exp (RiscV.Word 64)) :
    NeverReturns (σ := σ) primitive (.extCall name a b c d) := by
  intro state result
  rw [panSemTotalEvaluate]
  unfold panSemTotalExtCallClause panSemTotalExprStep
  repeat' split
  all_goals first | exact extCallStep_not_returned _ _ _ _ _ _ _ _ _ _ | simp

/-- Actual software `trap_with` body, extracted from the fixed AST. -/
def trapWithBody : Prog (RiscV.Word 64) :=
  match Guest.Software.guestFn_trap_with with
  | .function function => function.body
  | _ => .skip

def trapWithEntry : PanSemFunctionEntry (RiscV.Word 64) :=
  { params := [("code", .one)], body := trapWithBody, returnShape := .one }

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Proposed reduction of the fixed declaration list, including every later
function declaration. This has not been evaluated by Lean in this workspace. -/
theorem guestAst_trap_lookup_reduction
    (initial : Option (PanSemFunctionEntry (RiscV.Word 64))) :
    installDeclarationLookup "trap_with" Guest.Software.guestAst initial = some trapWithEntry := by
  rfl

/-- Proposed consequence for any successful production declaration install. -/
theorem guestAst_declared_trap_lookup {σ : Type}
    (state result : PanSemDeclarationState (RiscV.Word 64) σ)
    (h : evaluateDecls state Guest.Software.guestAst = some result) :
    lookupInfo "trap_with" result.code = some trapWithEntry := by
  rw [evaluateDecls_code_projection Guest.Software.guestAst state result h,
    installDeclarationCode_lookup]
  exact guestAst_trap_lookup_reduction _

/-- Proposed production entry-state consequence of a successful installation. -/
theorem guestAst_entry_trap_code {σ : Type}
    (machine : PanSemState (RiscV.Word 64) (FfiState σ))
    (state result : PanSemDeclarationState (RiscV.Word 64) σ)
    (h : evaluateDecls state Guest.Software.guestAst = some result) :
    panSemCodeLookup (panSemEntryStateOfDecls machine result).code "trap_with" =
      some ([("code", .one)], trapWithBody, .one) := by
  rw [panSemEntryStateOfDecls_codeLookup,
    guestAst_declared_trap_lookup state result h]
  rfl

/-- Proposed proof that the literal `trap_with` body cannot return a value,
even if its FFI calls return normally. -/
theorem trapWithBody_neverReturns {σ : Type} (primitive : PanPrimitiveHandler (RiscV.Word 64)) :
    NeverReturns (σ := σ) primitive trapWithBody := by
  unfold trapWithBody Guest.Software.guestFn_trap_with
  apply neverReturns_seq
  · apply neverReturns_shMemStore
  · apply neverReturns_seq
    · apply neverReturns_shMemStore
    · apply neverReturns_seq
      · apply neverReturns_shMemStore
      · apply neverReturns_seq
        · apply neverReturns_extCall
        · apply neverReturns_raise

/-- A code-map lookup for the fixed body entails that any successful call
lookup selects that body, regardless of argument matching or fresh locals. -/
theorem trapWith_call_lookup_body {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (parameters : List (VarName × Shape)) (returnShape : Shape)
    (hcode : panSemCodeLookup state.code "trap_with" =
      some (parameters, trapWithBody, returnShape)) :
    ∀ values callee locals shape,
      panSemTotalCodeLookup state "trap_with" values = some (callee, locals, shape) →
      callee = trapWithBody := by
  intro values callee locals shape h
  simp only [panSemTotalCodeLookup, lookupPanSemCodeCall, hcode, Option.bind_some] at h
  repeat' split at h
  all_goals simp_all

/-- The upstream evaluator frame preserves a known `trap_with` entry through
any whole program evaluation, independent of the result category. -/
theorem trapWith_code_preserved {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (program : Prog (RiscV.Word 64))
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (parameters : List (VarName × Shape)) (returnShape : Shape)
    (hcode : panSemCodeLookup state.code "trap_with" =
      some (parameters, trapWithBody, returnShape)) :
    panSemCodeLookup (panSemTotalEvaluate primitive program state).2.code "trap_with" =
      some (parameters, trapWithBody, returnShape) := by
  rw [panSemTotalEvaluate_code primitive program state]
  exact hcode

/-- Proposed composition of successful declaration installation with the
upstream production-evaluator code frame. It does not establish that the
production entry is related to the challenge's exact input state. -/
theorem guestAst_trap_code_after_run {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (program : Prog (RiscV.Word 64))
    (machine : PanSemState (RiscV.Word 64) (FfiState σ))
    (state result : PanSemDeclarationState (RiscV.Word 64) σ)
    (h : evaluateDecls state Guest.Software.guestAst = some result) :
    panSemCodeLookup
      (panSemTotalEvaluate primitive program (panSemEntryStateOfDecls machine result)).2.code
      "trap_with" = some ([("code", .one)], trapWithBody, .one) := by
  exact trapWith_code_preserved primitive program (panSemEntryStateOfDecls machine result)
    [("code", .one)] .one (guestAst_entry_trap_code machine state result h)

/-- If the state-owned lookup resolves `trap_with` to the fixed body, the
unhandled call cannot complete normally. The lookup premise is not proved here. -/
theorem trapWithCall_not_normal {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hlookup : ∀ values callee locals shape,
      panSemTotalCodeLookup state "trap_with" values = some (callee, locals, shape) →
      callee = trapWithBody) :
    (panSemTotalEvaluate primitive
      (.call (some (none, none)) "trap_with" [.const 8]) state).1 ≠ none := by
  rw [panSemTotalEvaluate]
  cases he : evalPanSemStateExps state [.const 8] with
  | none => simp [he]
  | some values =>
      cases hc : panSemTotalCodeLookup state "trap_with" values with
      | none => simp [he, hc]
      | some found =>
          rcases found with ⟨callee, locals, shape⟩
          have hbody := hlookup values callee locals shape hc
          subst callee
          by_cases hz : state.clock = 0
          · simp [he, hc, hz]
          · simp only [he, hc, if_neg hz]
            let entry := { state with clock := state.clock - 1, locals := locals }
            have hnr := trapWithBody_neverReturns (σ := σ) primitive
            cases hr : (panSemTotalEvaluate primitive trapWithBody entry).1 with
            | none => simp [entry, hr]
            | some result =>
                cases result with
                | returned value => exact False.elim (hnr entry value hr)
                | error => simp [entry, hr]
                | timeOut => simp [entry, hr]
                | «break» => simp [entry, hr]
                | «continue» => simp [entry, hr]
                | exception exception value => simp [entry, hr]
                | finalFfi event => simp [entry, hr]

/-- Natural-number loop variant for `i := i + 8`. -/
theorem copy_variant_decreases (i n : Nat) (h : i < n) :
    (n - (i + 8) + 7) / 8 < (n - i + 7) / 8 := by
  omega

/-- The source's input-size guard prevents wraparound in a continuing copy
iteration. The guard must still be linked to the actual evaluator state. -/
theorem copy_increment_no_wrap (i n : Nat) (hi : i < n)
    (hn : n ≤ 1073741808) : (i + 8) % (2 ^ 64) = i + 8 := by
  apply Nat.mod_eq_of_lt
  omega

/-- A normal shared-memory load to `w` preserves any other local. This does
not apply to a final FFI result, which clears the locals. -/
theorem load_w_normal_preserves {σ : Type}
    (context : PanValueFfiContext (RiscV.Word 64))
    (state post : PanShMemLoadState (RiscV.Word 64) σ)
    (address : RiscV.Word 64) (name : VarName) (hne : name ≠ "w")
    (h : panShMemLoad context state .local "w" .opW address = .normal post) :
    post.locals name = state.locals name := by
  simp only [panShMemLoad, panValueFfiWidth, ↓reduceIte] at h
  split at h
  · simp at h
  · split at h
    · cases h
      simp [updatePanValueMap, hne, Ne.symm hne]
    · simp at h

/-- Lift the normal-read frame through the total evaluator's load-result
adapter. The address and domain checks in the caller remain separate. -/
theorem load_result_w_normal_preserves {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address : RiscV.Word 64) (name : VarName) (hne : name ≠ "w")
    (h : (panSemTotalShMemLoadResult state
      (panShMemLoad (panSemTotalShMemContext state) (panSemTotalShMemState state)
        .local "w" .opW address)).1 = none) :
    (panSemTotalShMemLoadResult state
      (panShMemLoad (panSemTotalShMemContext state) (panSemTotalShMemState state)
        .local "w" .opW address)).2.locals name = state.locals name := by
  cases hr : panShMemLoad (panSemTotalShMemContext state) (panSemTotalShMemState state)
      .local "w" .opW address with
  | error failed =>
      simp [hr, panSemTotalShMemLoadResult] at h
  | normal post =>
      have frame := load_w_normal_preserves (panSemTotalShMemContext state)
        (panSemTotalShMemState state) post address name hne hr
      simpa [hr, panSemTotalShMemLoadResult, panSemTotalShMemStateBack,
        panSemTotalShMemState] using frame
  | final post event =>
      simp [hr, panSemTotalShMemLoadResult] at h

/-- Proposed frame for the total shared-load clause in the real loop body. -/
theorem load_clause_w_normal_preserves {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address : Exp (RiscV.Word 64)) (name : VarName) (hne : name ≠ "w")
    (h : (panSemTotalShMemLoadClause state .opW .local "w" address).1 = none) :
    (panSemTotalShMemLoadClause state .opW .local "w" address).2.locals name =
      state.locals name := by
  simp only [panSemTotalShMemLoadClause, panSemTotalExprStep] at h ⊢
  cases he : evalPanSemStateExp state address with
  | none => simp [he] at h
  | some value =>
      cases value with
      | rStruct fields => simp [he] at h
      | nStruct structName fields => simp [he] at h
      | word addr =>
          cases hw : state.locals "w" with
          | none => simp [he, hw] at h
          | some value =>
              cases value with
              | rStruct fields => simp [he, hw] at h
              | nStruct structName fields => simp [he, hw] at h
              | word old =>
                  simp only [he, hw] at h ⊢
                  exact load_result_w_normal_preserves state addr name hne h

/-- Word stores preserve all locals, including on an error path. -/
theorem store_preserves_locals {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64)) :
    (panSemTotalStoreClause state address value).2.locals = state.locals := by
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

/-- The load-result adapter cannot produce a language-level continue. -/
theorem load_result_not_continue {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (result : PanShMemLoadResult (RiscV.Word 64) σ) :
    (panSemTotalShMemLoadResult state result).1 ≠ some .continue := by
  cases result <;> simp [panSemTotalShMemLoadResult]

theorem load_clause_not_continue {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address : Exp (RiscV.Word 64)) :
    (panSemTotalShMemLoadClause state .opW .local "w" address).1 ≠ some .continue := by
  cases he : evalPanSemStateExp state address with
  | none => simp [panSemTotalShMemLoadClause, panSemTotalExprStep, he]
  | some addressValue =>
      cases addressValue with
      | rStruct fields => simp [panSemTotalShMemLoadClause, panSemTotalExprStep, he]
      | nStruct name fields => simp [panSemTotalShMemLoadClause, panSemTotalExprStep, he]
      | word addr =>
          cases hw : state.locals "w" with
          | none => simp [panSemTotalShMemLoadClause, panSemTotalExprStep, he, hw]
          | some current =>
              cases current with
              | rStruct fields => simp [panSemTotalShMemLoadClause, panSemTotalExprStep, he, hw]
              | nStruct name fields => simp [panSemTotalShMemLoadClause, panSemTotalExprStep, he, hw]
              | word old =>
                  have h := load_result_not_continue state
                    (panShMemLoad (panSemTotalShMemContext state) (panSemTotalShMemState state)
                      .local "w" .opW addr)
                  simpa [panSemTotalShMemLoadClause, panSemTotalExprStep, he, hw] using h

theorem store_not_continue {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64)) :
    (panSemTotalStoreClause state address value).1 ≠ some .continue := by
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

def extractedBody : Option (Prog (BitVec 64)) :=
  match Guest.Software.guestFn_input_blob with
  | .function f =>
      match f.body with
      | .dec _ _ _ (.seq _ (.seq _
          (.decCall _ _ _ _ (.dec _ _ _ (.dec _ _ _ (.seq (.while _ body) _)))))) =>
          some body
      | _ => none
  | _ => none

def copyIndex : Exp (RiscV.Word 64) := .var .local "i"
def copyLoadAddress : Exp (RiscV.Word 64) :=
  .op .add [.const (BitVec.ofNat 64 1073741840), copyIndex]
def copyStoreAddress : Exp (RiscV.Word 64) :=
  .op .add [.var .local "p", copyIndex]
def copyBody : Prog (RiscV.Word 64) :=
  .seq (.shMemLoad .opW .local "w" copyLoadAddress)
    (.seq (.store copyStoreAddress (.var .local "w"))
      (.assign .local "i" (.op .add [copyIndex, .const (BitVec.ofNat 64 8)])))

/-- Proposed literal identification of the actual input-copy loop body. -/
theorem extractedBody_eq : extractedBody = some copyBody := by
  rfl

/-- Proposed exclusion of `continue` for this specific body. -/
theorem copyBody_not_continue {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) :
    (panSemTotalEvaluate primitive copyBody state).1 ≠ some .continue := by
  unfold copyBody
  rw [panSemTotalEvaluate]
  have hload : ∀ s : PanSemState (RiscV.Word 64) (FfiState σ),
      panSemTotalEvaluate primitive (.shMemLoad .opW .local "w" copyLoadAddress) s =
        panSemTotalShMemLoadClause s .opW .local "w" copyLoadAddress := by
    intro s; rw [panSemTotalEvaluate]
  have hstore : ∀ s : PanSemState (RiscV.Word 64) (FfiState σ),
      panSemTotalEvaluate primitive (.store copyStoreAddress (.var .local "w")) s =
        panSemTotalStoreClause s copyStoreAddress (.var .local "w") := by
    intro s; rw [panSemTotalEvaluate]
  simp only [hload]
  cases hl : (panSemTotalShMemLoadClause state .opW .local "w" copyLoadAddress).1 with
  | some result =>
      have hn := load_clause_not_continue state copyLoadAddress
      simpa [hl] using hn
  | none =>
      simp only [hl]
      rw [panSemTotalEvaluate]
      simp only [hstore]
      cases hs : (panSemTotalStoreClause
          (panSemFixClock state.clock
            (panSemTotalShMemLoadClause state .opW .local "w" copyLoadAddress).2)
          copyStoreAddress (.var .local "w")).1 with
      | some result =>
          have hn := store_not_continue
            (panSemFixClock state.clock
              (panSemTotalShMemLoadClause state .opW .local "w" copyLoadAddress).2)
            copyStoreAddress (.var .local "w")
          simpa [hs] using hn
      | none =>
          simp only [hs]
          rw [panSemTotalEvaluate]
          rcases Flapjack.L3.Pilot.assign_res _ .local "i" (.op .add [copyIndex, .const (BitVec.ofNat 64 8)]) with h | h <;>
            rw [h] <;> simp

/-- Proposed frame for one normally completed copy iteration. -/
theorem copyBody_normal_step {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (index length : RiscV.Word 64)
    (hi : state.locals "i" = some (.word index))
    (hl : state.locals "len" = some (.word length))
    (h : (panSemTotalEvaluate primitive copyBody state).1 = none) :
    (panSemTotalEvaluate primitive copyBody state).2.locals "i" = some (.word (index + 8)) ∧
    (panSemTotalEvaluate primitive copyBody state).2.locals "len" = some (.word length) := by
  have hload : ∀ s : PanSemState (RiscV.Word 64) (FfiState σ),
      panSemTotalEvaluate primitive (.shMemLoad .opW .local "w" copyLoadAddress) s =
        panSemTotalShMemLoadClause s .opW .local "w" copyLoadAddress := by
    intro s; rw [panSemTotalEvaluate]
  have hstore : ∀ s : PanSemState (RiscV.Word 64) (FfiState σ),
      panSemTotalEvaluate primitive (.store copyStoreAddress (.var .local "w")) s =
        panSemTotalStoreClause s copyStoreAddress (.var .local "w") := by
    intro s; rw [panSemTotalEvaluate]
  have hassign : ∀ s : PanSemState (RiscV.Word 64) (FfiState σ),
      panSemTotalEvaluate primitive (.assign .local "i" (.op .add [copyIndex, .const (BitVec.ofNat 64 8)])) s =
        panSemTotalAssignClause s .local "i" (.op .add [copyIndex, .const (BitVec.ofNat 64 8)]) := by
    intro s; rw [panSemTotalEvaluate]
  unfold copyBody at h ⊢
  rw [panSemTotalEvaluate] at h ⊢
  simp only [hload] at h ⊢
  generalize hr : panSemTotalShMemLoadClause state .opW .local "w" copyLoadAddress = r at h ⊢
  rcases r with ⟨result, loaded⟩
  cases result with
  | some error => simp at h
  | none =>
      have hreadClock : loaded.clock = state.clock := by
        have e := Flapjack.L3.shMemLoad_clock state .opW .local "w" copyLoadAddress
        rw [hr] at e
        exact e
      have hfixClock : (panSemFixClock state.clock loaded).clock = state.clock := by
        simp [panSemFixClock, hreadClock]
      have hiLoad : loaded.locals "i" = state.locals "i" := by
        have e := load_clause_w_normal_preserves state copyLoadAddress "i" (by decide)
          (by rw [hr])
        rw [hr] at e; exact e
      have hlLoad : loaded.locals "len" = state.locals "len" := by
        have e := load_clause_w_normal_preserves state copyLoadAddress "len" (by decide)
          (by rw [hr])
        rw [hr] at e; exact e
      dsimp only at h ⊢
      rw [panSemTotalEvaluate] at h ⊢
      simp only [hfixClock] at h ⊢
      simp only [hstore] at h ⊢
      generalize hs : panSemTotalStoreClause (panSemFixClock state.clock loaded)
        copyStoreAddress (.var .local "w") = r at h ⊢
      rcases r with ⟨result, stored⟩
      cases result with
      | some error => simp at h
      | none =>
          have hlocals : stored.locals = loaded.locals := by
            have e := store_preserves_locals (panSemFixClock state.clock loaded)
              copyStoreAddress (.var .local "w")
            rw [hs] at e
            simpa [panSemFixClock] using e
          dsimp only at h ⊢
          simp only [hassign] at h ⊢
          have he : evalPanSemStateExp (panSemFixClock state.clock stored)
              (.op .add [copyIndex, .const (BitVec.ofNat 64 8)]) = some (.word (index + 8)) := by
            simp [evalPanSemStateExp, panSemFixClock, copyIndex, evalPanValueExp,
              evalPanValueExp.evalPanValueExps, hlocals, hiLoad, hi,
              panSemBitVec64MemoryAccess_wordOp, wordOpHOL, wordOp]
          have ha := Flapjack.L3.Pilot.assign_none_locals
            (panSemFixClock state.clock stored) "i" _ _ he h
          rw [ha]
          simp [panSemFixClock, hlocals, hiLoad, hlLoad, hi, hl, updatePanValueMap]

def copyCondition : Exp (RiscV.Word 64) :=
  .cmp .lower copyIndex (.var .local "len")
def copyLoop : Prog (RiscV.Word 64) := .while copyCondition copyBody

/-- Extract the condition and body together from the software AST. -/
def extractedLoop : Option (Prog (BitVec 64)) :=
  match Guest.Software.guestFn_input_blob with
  | .function f =>
      match f.body with
      | .dec _ _ _ (.seq _ (.seq _
          (.decCall _ _ _ _ (.dec _ _ _ (.dec _ _ _ (.seq (.while cond body) _)))))) =>
          some (.while cond body)
      | _ => none
  | _ => none

theorem extractedLoop_eq : extractedLoop = some copyLoop := by
  rfl

/-- Proposed source-clock bound for the isolated copy loop. It assumes the
length guard and the actual local-state invariant at loop entry. -/
theorem copyLoop_cost {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (length : RiscV.Word 64) (lengthBound : length.toNat ≤ 1073741808) :
    ∀ state : PanSemState (RiscV.Word 64) (FfiState σ),
      (∃ index, state.locals "i" = some (.word index) ∧
        state.locals "len" = some (.word length)) →
      state.clock ≤ (panSemTotalEvaluate primitive copyLoop state).2.clock +
        (match state.locals "i" with
         | some (.word index) => (length.toNat - index.toNat + 7) / 8
         | _ => 0) * (0 + 1) := by
  intro state hstate
  apply Flapjack.L3.costLe_while primitive
    (fun s => ∃ index, s.locals "i" = some (.word index) ∧
      s.locals "len" = some (.word length))
    (fun s => match s.locals "i" with
      | some (.word index) => (length.toNat - index.toNat + 7) / 8
      | _ => 0)
    copyCondition copyBody 0 _ _ _ state hstate
  · intro s v ⟨index, hi, hl⟩ hv hv0
    have hc : evalPanSemStateExp s copyCondition =
        some (.word (if index < length then 1 else 0)) := by
      simp [evalPanSemStateExp, copyCondition, copyIndex, evalPanValueExp, hi, hl,
        panSemBitVec64MemoryAccess_compare, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hc] at hv
    simp only [Option.some.injEq, PanValue.word.injEq] at hv
    split at hv
    · rename_i hlt
      have hn := BitVec.lt_def.mp hlt
      simp only [hi]
      omega
    · subst hv; exact absurd rfl hv0
  · intro s v _ _ _ _
    rw [Flapjack.L3.clockFree_clock primitive copyBody _ rfl]
    simp
  · intro s v ⟨index, hi, hl⟩ hv hv0 hclock hresult
    have hc : evalPanSemStateExp s copyCondition =
        some (.word (if index < length then 1 else 0)) := by
      simp [evalPanSemStateExp, copyCondition, copyIndex, evalPanValueExp, hi, hl,
        panSemBitVec64MemoryAccess_compare, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hc] at hv
    simp only [Option.some.injEq, PanValue.word.injEq] at hv
    have hlt : index < length := by
      split at hv
      · assumption
      · subst hv; exact absurd rfl hv0
    have hnormal : (panSemTotalEvaluate primitive copyBody { s with clock := s.clock - 1 }).1 = none := by
      rcases hresult with h | h
      · exact h
      · exact absurd h (copyBody_not_continue primitive _)
    have hstep := copyBody_normal_step primitive { s with clock := s.clock - 1 }
      index length hi hl hnormal
    have hnat := BitVec.lt_def.mp hlt
    have hnowrap := copy_increment_no_wrap index.toNat length.toNat hnat lengthBound
    have hnext : (index + 8).toNat = index.toNat + 8 := by
      rw [BitVec.toNat_add]
      simpa using hnowrap
    refine ⟨⟨index + 8, ?_, ?_⟩, ?_⟩
    · simpa [panSemFixClock] using hstep.1
    · simpa [panSemFixClock] using hstep.2
    · simp only [panSemFixClock, hstep.1, hi, hnext]
      exact copy_variant_decreases index.toNat length.toNat hnat

/-- Conditional source-clock bound applied to the extracted literal AST. -/
theorem extractedLoop_cost {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (length : RiscV.Word 64) (lengthBound : length.toNat ≤ 1073741808)
    (program : Prog (RiscV.Word 64)) (hp : extractedLoop = some program)
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (hstate : ∃ index, state.locals "i" = some (.word index) ∧
      state.locals "len" = some (.word length)) :
    state.clock ≤ (panSemTotalEvaluate primitive program state).2.clock +
      (match state.locals "i" with
       | some (.word index) => (length.toNat - index.toNat + 7) / 8
       | _ => 0) * (0 + 1) := by
  have eq : program = copyLoop := Option.some.inj (hp.symm.trans extractedLoop_eq)
  subst program
  exact copyLoop_cost primitive length lengthBound state hstate

/-- Proposed uniform source-clock consumption bound under the loop-entry
length and local-state assumptions; this says nothing about other code. -/
theorem extractedLoop_uniform_cost {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (length : RiscV.Word 64) (lengthBound : length.toNat ≤ 1073741808)
    (program : Prog (RiscV.Word 64)) (hp : extractedLoop = some program)
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (index : RiscV.Word 64)
    (hi : state.locals "i" = some (.word index))
    (hl : state.locals "len" = some (.word length)) :
    state.clock ≤ (panSemTotalEvaluate primitive program state).2.clock + 134217726 := by
  have bound := extractedLoop_cost primitive length lengthBound program hp state ⟨index, hi, hl⟩
  simp only [hi] at bound
  have hnum : length.toNat - index.toNat + 7 ≤ 1073741815 := by omega
  have hcost : (length.toNat - index.toNat + 7) / 8 ≤ 134217726 := by
    have hdiv : (length.toNat - index.toNat + 7) / 8 ≤ 1073741815 / 8 :=
      Nat.div_le_div_right hnum
    simpa using hdiv
  omega

/-- The fixed copy loop uses only byte-ranged identifier literals. -/
theorem copyLoop_byteRanged : ProgByteRanged copyLoop := by
  simp [copyLoop, copyCondition, copyBody, copyLoadAddress, copyStoreAddress,
    copyIndex, ProgByteRanged, ExpByteRanged, ListExpByteRanged, NameRanged]

/-- Proposed transfer of the isolated loop cost to the exact evaluator. All
state, code, exception and primitive relations remain explicit hypotheses. -/
theorem exact_copyLoop_uniform_cost {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (hprimBridge : ∀ (operator : PrimOp) (values : List (PanValue (RiscV.Word 64))),
      Option.map panValueToHOL (primitive operator values) =
        panPrimopHOLExact operator (values.map panValueToHOL))
    (hprimRanged : PanPrimitiveHandlerByteRanged primitive)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (hcode : PanSemCodeRanged production)
    (hexn : PanSemExceptionShapesRanged production)
    (length index : RiscV.Word 64) (lengthBound : length.toNat ≤ 1073741808)
    (hi : production.locals "i" = some (.word index))
    (hl : production.locals "len" = some (.word length)) :
    exact.clock ≤ (PanSemStateFiniteExact.evaluateHOLFiniteState exact (progToHOL copyLoop)).2.clock +
      134217726 := by
  apply Flapjack.L3.exact_cost_of_production primitive hprimBridge hprimRanged
    (progToHOL copyLoop) production exact hrel hranged hcode hexn 134217726
  simpa only [progOfHOL_progToHOL copyLoop copyLoop_byteRanged] using
    (extractedLoop_uniform_cost primitive length lengthBound copyLoop extractedLoop_eq
      production index hi hl)

/-- Loop-entry state on the successful `alloc`/declaration branch: `decCall`
restores the caller's locals before binding `p`, then `dec` binds `i` and `w`.
This is not a proof that those successful branches are reached. -/
def copyLoopEntry {σ : Type}
    (caller post : PanSemState (RiscV.Word 64) (FfiState σ))
    (allocResult : PanValue (RiscV.Word 64)) : PanSemState (RiscV.Word 64) (FfiState σ) :=
  panSemTotalDecBind
    (panSemTotalDecBind
      { post with locals := updatePanValueMap caller.locals "p" allocResult }
      "i" (.word 0))
    "w" (.word 0)

theorem copyLoopEntry_code {σ : Type}
    (caller post : PanSemState (RiscV.Word 64) (FfiState σ))
    (allocResult : PanValue (RiscV.Word 64)) :
    (copyLoopEntry caller post allocResult).code = post.code := by
  rfl

def inputLengthGuard : Exp (RiscV.Word 64) :=
  .cmp .lower (.const (BitVec.ofNat 64 1073741808)) (.var .local "len")

def extractedLengthGuard : Option (Exp (BitVec 64)) :=
  match Guest.Software.guestFn_input_blob with
  | .function f =>
      match f.body with
      | .dec _ _ _ (.seq _ (.seq (.ite condition _ _) _)) => some condition
      | _ => none
  | _ => none

theorem extractedLengthGuard_eq : extractedLengthGuard = some inputLengthGuard := by
  rfl

/-- If the input-size guard evaluates false for the local length, that length
fits the copy-loop bound. This does not exclude the guard's true branch. -/
theorem inputLengthGuard_false_bound {σ : Type}
    (caller : PanSemState (RiscV.Word 64) (FfiState σ)) (length : RiscV.Word 64)
    (hlen : caller.locals "len" = some (.word length))
    (hguard : evalPanSemStateExp caller inputLengthGuard = some (.word 0)) :
    length.toNat ≤ 1073741808 := by
  have hc : evalPanSemStateExp caller inputLengthGuard =
      some (.word (if (BitVec.ofNat 64 1073741808) < length then 1 else 0)) := by
    simp [evalPanSemStateExp, inputLengthGuard, evalPanValueExp, hlen,
      panSemBitVec64MemoryAccess_compare, Compiler.Encoders.Asm.wordCmpHOL]
  rw [hc] at hguard
  have hn : ¬ (BitVec.ofNat 64 1073741808) < length := by
    intro hlt
    simp [hlt] at hguard
  by_cases hbound : length.toNat ≤ 1073741808
  · exact hbound
  · have hnat : 1073741808 < length.toNat := by omega
    have hlt : (BitVec.ofNat 64 1073741808) < length := by
      apply BitVec.lt_def.mpr
      simpa using hnat
    exact False.elim (hn hlt)

/-- If the actual guard statement completes normally and lookup resolves the
trap body, the length is within the copy bound. -/
theorem inputLengthGuard_normal_bound {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (length : RiscV.Word 64)
    (hlen : state.locals "len" = some (.word length))
    (hlookup : ∀ values callee locals shape,
      panSemTotalCodeLookup state "trap_with" values = some (callee, locals, shape) →
      callee = trapWithBody)
    (hnormal : (panSemTotalEvaluate primitive
      (.ite inputLengthGuard (.call (some (none, none)) "trap_with" [.const 8]) .skip)
        state).1 = none) : length.toNat ≤ 1073741808 := by
  have hc : evalPanSemStateExp state inputLengthGuard =
      some (.word (if (BitVec.ofNat 64 1073741808) < length then 1 else 0)) := by
    simp [evalPanSemStateExp, inputLengthGuard, evalPanValueExp, hlen,
      panSemBitVec64MemoryAccess_compare, Compiler.Encoders.Asm.wordCmpHOL]
  by_cases hgt : (BitVec.ofNat 64 1073741808) < length
  · have hcall : (panSemTotalEvaluate primitive
        (.call (some (none, none)) "trap_with" [.const 8]) state).1 = none := by
      rw [panSemTotalEvaluate] at hnormal
      simpa [hc, hgt] using hnormal
    exact False.elim (trapWithCall_not_normal primitive state hlookup hcall)
  · apply inputLengthGuard_false_bound state length hlen
    simpa [hc, hgt]

/-- The same bound using one explicit code-map entry instead of a premise over
all successful call lookups. Installation of this entry remains unproved. -/
theorem inputLengthGuard_normal_bound_of_code {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (state : PanSemState (RiscV.Word 64) (FfiState σ)) (length : RiscV.Word 64)
    (parameters : List (VarName × Shape)) (returnShape : Shape)
    (hlen : state.locals "len" = some (.word length))
    (hcode : panSemCodeLookup state.code "trap_with" =
      some (parameters, trapWithBody, returnShape))
    (hnormal : (panSemTotalEvaluate primitive
      (.ite inputLengthGuard (.call (some (none, none)) "trap_with" [.const 8]) .skip)
        state).1 = none) : length.toNat ≤ 1073741808 := by
  exact inputLengthGuard_normal_bound primitive state length hlen
    (trapWith_call_lookup_body state parameters returnShape hcode) hnormal

theorem copyLoopEntry_locals {σ : Type}
    (caller post : PanSemState (RiscV.Word 64) (FfiState σ))
    (allocResult : PanValue (RiscV.Word 64)) (length : RiscV.Word 64)
    (hlen : caller.locals "len" = some (.word length)) :
    (copyLoopEntry caller post allocResult).locals "i" = some (.word 0) ∧
      (copyLoopEntry caller post allocResult).locals "len" = some (.word length) := by
  simp [copyLoopEntry, panSemTotalDecBind, updatePanValueMap, hlen]

/-- Proposed uniform loop cost on that branch, still conditional on the
caller's length guard and successful extraction of the literal loop. -/
theorem copyLoopEntry_uniform_cost {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (caller post : PanSemState (RiscV.Word 64) (FfiState σ))
    (allocResult : PanValue (RiscV.Word 64)) (length : RiscV.Word 64)
    (hlen : caller.locals "len" = some (.word length))
    (lengthBound : length.toNat ≤ 1073741808) :
    (copyLoopEntry caller post allocResult).clock ≤
      (panSemTotalEvaluate primitive copyLoop (copyLoopEntry caller post allocResult)).2.clock +
        134217726 := by
  obtain ⟨hi, hl⟩ := copyLoopEntry_locals caller post allocResult length hlen
  exact extractedLoop_uniform_cost primitive length lengthBound copyLoop extractedLoop_eq
    (copyLoopEntry caller post allocResult) 0 hi hl

/-- Conditional cost for the actual guard-false and alloc-return branch. -/
theorem copyLoopEntry_guard_false_cost {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (caller post : PanSemState (RiscV.Word 64) (FfiState σ))
    (allocResult : PanValue (RiscV.Word 64)) (length : RiscV.Word 64)
    (hlen : caller.locals "len" = some (.word length))
    (hguard : evalPanSemStateExp caller inputLengthGuard = some (.word 0)) :
    (copyLoopEntry caller post allocResult).clock ≤
      (panSemTotalEvaluate primitive copyLoop (copyLoopEntry caller post allocResult)).2.clock +
        134217726 := by
  exact copyLoopEntry_uniform_cost primitive caller post allocResult length hlen
    (inputLengthGuard_false_bound caller length hlen hguard)

/-- Proposed syntactic check that the actual loop body does not charge source
clock. The successful or failed result of its FFI operation is unrestricted. -/
theorem extractedBody_clockFree :
    extractedBody.map Flapjack.L3.ClockFree = some true := by
  rfl

/-- Conditional on the extraction succeeding, each evaluation of the loop
body preserves the production evaluator's source clock. -/
theorem extractedBody_clock {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (p : Prog (RiscV.Word 64)) (hp : extractedBody = some p)
    (s : PanSemState (RiscV.Word 64) (FfiState σ)) :
    (panSemTotalEvaluate primitive p s).2.clock = s.clock := by
  have h : Flapjack.L3.ClockFree p = true := by
    have he := extractedBody_clockFree
    rw [hp] at he
    exact Option.some.inj he
  exact Flapjack.L3.clockFree_clock primitive p s h

end InitECandidate.Solver.InputCopyAst
