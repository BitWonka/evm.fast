import InitE.SourceSemantics
import Flapjack.Pancake.Semantics.PanSem.StateBridge
import Flapjack.Pancake.Semantics.PanSem.TotalEvalBridge
import Flapjack.Pancake.Semantics.PanSem.EntryState
import InitECandidate.Solver.ParserRange

/-!
Exploratory adapter. Not elaborated or kernel checked. In particular, this
file does not establish `OracleRel`, `FfiStateRel`, or a guest step bound.
The challenge source oracle treats halt and trap as final, while the guest
model oracle returns normally for them; all other guest external calls fail.
Thus the candidate adapter finalizes every external call.
-/
namespace InitECandidate.Solver.SourceOracleAdapter
open Flapjack
open Flapjack.Basis.Pure.MlString

def canonicalName (name : String) : String :=
  toStringOfBytes (ofString name)

/-- Normalization preserves the HOL byte name used by `FfiNameRel`. -/
theorem canonicalName_preserves (name : String) :
    ofString (canonicalName name) = ofString name := by
  exact ofString_toStringOfBytes (ofString name)

/-- Once normalized, an external name remains normalized. -/
theorem canonicalName_idempotent (name : String) :
    canonicalName (canonicalName name) = canonicalName name := by
  unfold canonicalName
  rw [ofString_toStringOfBytes]

/-- A normalized target is recognized exactly when its HOL name matches. -/
theorem canonicalName_eq_iff (name target : String)
    (ht : canonicalName target = target) :
    canonicalName name = target ↔ ofString name = ofString target := by
  constructor
  · intro h
    calc
      ofString name = ofString (canonicalName name) := (canonicalName_preserves name).symm
      _ = ofString target := congrArg ofString h
  · intro h
    calc
      canonicalName name = canonicalName target := congrArg toStringOfBytes h
      _ = target := ht

/-- `BytesRel` identifies the production bytes with decoded HOL bytes. -/
theorem bytesRel_decode {prod : List UInt8} {hol : List (BitVec 8)}
    (h : BytesRel prod hol) : hol.map bitsToByte = prod := by
  have hm := congrArg (List.map UInt8.ofNat) h
  simpa [List.map_map, Function.comp_def, bitsToByte] using hm

/-- Decoding a bounded HOL byte preserves its numeric value. -/
theorem bitsToByte_toNat (value : BitVec 8) :
    (bitsToByte value).toNat = value.toNat := by
  simp [bitsToByte, UInt8.toNat_ofNat', Nat.mod_eq_of_lt value.isLt]

/-- Re-encoding decoded HOL output preserves the byte relation. -/
theorem bytesRel_decode_output (hol : List (BitVec 8)) :
    BytesRel (hol.map bitsToByte) hol := by
  simp [BytesRel, List.map_map, Function.comp_def, bitsToByte_toNat]

/-- Convert a production oracle result in the same way as `sourceOracle`. -/
def holResult {σ : Type} : FfiOracleResult σ → HolOracleResult σ
  | .returned state bytes => .ret state (bytes.map byteToBits)
  | .final .failed => .final .failed
  | .final .diverged => .final .diverged

theorem holResult_rel {σ : Type} (result : FfiOracleResult σ) :
    OracleResultRel result (holResult result) := by
  cases result with
  | returned state bytes =>
      simp [holResult, OracleResultRel, bytesRel_map_byteToBits]
  | final outcome =>
      cases outcome <;> simp [holResult, OracleResultRel, OutcomeRel]

def oracle : FfiOracle Guest.HostMemory := fun name host configuration bytes =>
  match name with
  | .extCall _ => .final .failed
  | .sharedMem op => Guest.guestOracle (.sharedMem op) host configuration bytes

/-- Every challenge external call has a final failed oracle result. -/
theorem source_extCall_failed (name : MlString) (host : Guest.HostMemory)
    (configuration bytes : List (BitVec 8)) :
    InitE.sourceOracle (.extCall name) host configuration bytes = .final .failed := by
  by_cases h : name = ofString "halt" ∨ name = ofString "trap"
  · simp [InitE.sourceOracle, h]
  · have hhalt : toStringOfBytes name ≠ "halt" := by
      intro heq
      apply h
      left
      calc
        name = ofString (toStringOfBytes name) := (ofString_toStringOfBytes name).symm
        _ = ofString "halt" := congrArg ofString heq
    have htrap : toStringOfBytes name ≠ "trap" := by
      intro heq
      apply h
      right
      calc
        name = ofString (toStringOfBytes name) := (ofString_toStringOfBytes name).symm
        _ = ofString "trap" := congrArg ofString heq
    simp [InitE.sourceOracle, h, Guest.guestOracle, hhalt, htrap]

/-- All production and challenge external calls have related results. -/
theorem external_calls_rel (name : String) (holName : MlString)
    (host : Guest.HostMemory) (configuration bytes : List UInt8)
    (holConfiguration holBytes : List (BitVec 8)) :
    OracleResultRel (oracle (.extCall name) host configuration bytes)
      (InitE.sourceOracle (.extCall holName) host holConfiguration holBytes) := by
  rw [source_extCall_failed]
  simp [oracle, OracleResultRel, OutcomeRel]

/-- Shared-memory calls agree for byte-related inputs. -/
theorem shared_calls_rel (op : FfiShmemOp) (host : Guest.HostMemory)
    (configuration bytes : List UInt8) (holConfiguration holBytes : List (BitVec 8))
    (hc : BytesRel configuration holConfiguration) (hb : BytesRel bytes holBytes) :
    OracleResultRel (oracle (.sharedMem op) host configuration bytes)
      (InitE.sourceOracle
        (.sharedMem (match op with | .mappedRead => .mappedRead | .mappedWrite => .mappedWrite))
        host holConfiguration holBytes) := by
  have hcfg := bytesRel_decode hc
  have hbytes := bytesRel_decode hb
  cases op with
  | mappedRead =>
      simpa only [oracle, InitE.sourceOracle, hcfg, hbytes, holResult] using
        (holResult_rel (Guest.guestOracle (.sharedMem .mappedRead) host configuration bytes))
  | mappedWrite =>
      simpa only [oracle, InitE.sourceOracle, hcfg, hbytes, holResult] using
        (holResult_rel (Guest.guestOracle (.sharedMem .mappedWrite) host configuration bytes))

/-- Proposed persistent correspondence for all related names and bytes. -/
theorem oracle_rel : OracleRel oracle InitE.sourceOracle := by
  intro name holName hn host configuration holConfiguration bytes holBytes hc hb
  cases name with
  | extCall name =>
      cases holName with
      | extCall holName =>
          exact external_calls_rel name holName host configuration bytes holConfiguration holBytes
      | sharedMem op => simp [FfiNameRel] at hn
  | sharedMem op =>
      cases holName with
      | extCall holName => simp [FfiNameRel] at hn
      | sharedMem holOp =>
          cases op with
          | mappedRead =>
              cases holOp with
              | mappedRead => exact shared_calls_rel .mappedRead host configuration bytes holConfiguration holBytes hc hb
              | mappedWrite => simp [FfiNameRel, ShmemOpRel] at hn
          | mappedWrite =>
              cases holOp with
              | mappedRead => simp [FfiNameRel, ShmemOpRel] at hn
              | mappedWrite => exact shared_calls_rel .mappedWrite host configuration bytes holConfiguration holBytes hc hb

/-- Production state paired with the challenge's initial FFI state. -/
def initialFfi (input : Guest.InputBlob) : FfiState Guest.HostMemory :=
  { oracle := oracle, state := Guest.guestHostMemory input, ioEvents := [] }

theorem initialFfi_rel (input : Guest.InputBlob) :
    FfiStateRel (initialFfi input) (InitE.sourceFfi input) := by
  exact ⟨rfl, trivial, oracle_rel⟩

/-- Terminal external calls agree, including non-ASCII names that encode to
the same HOL bytes. This does not cover other names or shared-memory calls. -/
theorem terminal_calls_rel (name : String) (host : Guest.HostMemory)
    (configuration bytes : List UInt8) (holConfiguration holBytes : List (BitVec 8))
    (hname : ofString name = ofString "halt" ∨ ofString name = ofString "trap") :
    OracleResultRel (oracle (.extCall name) host configuration bytes)
      (InitE.sourceOracle (.extCall (ofString name)) host holConfiguration holBytes) := by
  exact external_calls_rel name (ofString name) host configuration bytes holConfiguration holBytes

/-- Replace the FFI carrier while retaining every ordinary production field. -/
def withExecutableFfi {σ : Type}
    (state : PanSemState (RiscV.Word 64) (HolFfiState σ)) (ffi : FfiState σ) :
    PanSemState (RiscV.Word 64) (FfiState σ) where
  locals := state.locals
  globals := state.globals
  structs := state.structs
  code := state.code
  exceptionShapes := state.exceptionShapes
  memory := state.memory
  memaddrs := state.memaddrs
  sharedMemaddrs := state.sharedMemaddrs
  clock := state.clock
  be := state.be
  ffi := ffi
  baseAddress := state.baseAddress
  topAddress := state.topAddress

/-- Proposed generic bridge: the old representation relation handles the
ordinary fields; an explicit FFI relation handles the changed carrier. -/
theorem withExecutableFfi_rel {σ : Type}
    (state : PanSemState (RiscV.Word 64) (HolFfiState σ))
    (exact : PanSemStateExact 64 σ) (ffi : FfiState σ)
    (hstate : PanSemStateRel state exact) (hffi : FfiStateRel ffi exact.ffi) :
    PanSemStateRelExec (withExecutableFfi state ffi) exact := by
  obtain ⟨hl, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, _, hb, ht⟩ := hstate
  exact ⟨hl, hg, hs, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩

/-- Proposed executable state obtained from the challenge's exact initial
state and the corresponding production FFI. -/
noncomputable def sourceProduction (input : Guest.InputBlob) :
    PanSemState (RiscV.Word 64) (FfiState Guest.HostMemory) := by
  classical
  let source := InitE.sourceInitialState input
  exact withExecutableFfi
    (panSemStateOfExact source.toExact source.toExact_finiteSupport.2.2.1)
    (initialFfi input)

/-- Proposed production/exact correspondence before declaration evaluation. -/
theorem sourceProduction_rel (input : Guest.InputBlob) :
    PanSemStateRelExec (sourceProduction input) (InitE.sourceInitialState input).toExact := by
  classical
  unfold sourceProduction
  apply withExecutableFfi_rel
  · exact panSemStateRel_ofExact _ _
  · simpa [InitE.sourceInitialState, PanSemStateFiniteExact.toExact] using initialFfi_rel input

/-- Proposed rangedness of the initial locals, globals and structure context.
The declaration-code rangedness after installation is a separate obligation. -/
theorem sourceProduction_ranged (input : Guest.InputBlob) :
    PanSemStateRelExecRanged (sourceProduction input) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro name value h
    simp [sourceProduction, withExecutableFfi, panSemStateOfExact,
      InitE.sourceInitialState, PanSemStateFiniteExact.toExact,
      HolFiniteMapExact.empty] at h
  · intro name value h
    simp [sourceProduction, withExecutableFfi, panSemStateOfExact,
      InitE.sourceInitialState, PanSemStateFiniteExact.toExact,
      HolFiniteMapExact.empty] at h
  · simp [sourceProduction, withExecutableFfi, panSemStateOfExact,
      InitE.sourceInitialState, PanSemStateFiniteExact.toExact,
      panStructContextOfHOL, structContextOfHOL, StructContext.toHOL,
      StructContextByteRanged]

/-- Declaration evaluator input for the challenge's initially empty code and
exception maps. The caller must still perform the structure prepass. -/
noncomputable def sourceDeclarationState (input : Guest.InputBlob) :
    PanSemDeclarationState (RiscV.Word 64) Guest.HostMemory :=
  let machine := sourceProduction input
  { runtime :=
      { structs := machine.structs
        functions := []
        locals := machine.locals
        globals := machine.globals
        memory := machine.memory
        ffi := machine.ffi
        clock := machine.clock
        baseAddress := machine.baseAddress
        topAddress := machine.topAddress
        bytesInWord := panSemBitVec64BytesInWord
        memoryAccess := some (panSemBitVec64MemoryAccess machine)
        contracts := none
        memoryHandler := none }
    code := []
    eshapes := []
    memoryAccess := panSemBitVec64MemoryAccess machine }

/-- Proposed declaration-state relation before the structure prepass. -/
theorem sourceDeclarationState_rel (input : Guest.InputBlob) :
    PanSemDeclEntryRel (sourceProduction input) (sourceDeclarationState input)
      (InitE.sourceInitialState input) := by
  classical
  obtain ⟨hl, hg, hs, _, _, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩ :=
    sourceProduction_rel input
  refine ⟨?_, ?_, rfl, rfl⟩
  · refine ⟨hl, hg, hs, ?_, ?_, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩
    · intro name _
      simp [sourceDeclarationState, panSemEntryStateOfDecls, panSemCodeLookup,
        lookupInfo, InitE.sourceInitialState, PanSemStateFiniteExact.toExact,
        HolFiniteMapExact.empty]
    · intro name _
      simp [sourceDeclarationState, panSemEntryStateOfDecls, lookupInfo,
        InitE.sourceInitialState, PanSemStateFiniteExact.toExact, HolFiniteMapExact.empty]
  · simpa [sourceDeclarationState, panSemEntryStateOfDecls] using sourceProduction_ranged input

/-- Lift the declaration-entry relation through the structure prepass when
the resulting decoded context satisfies its separate rangedness premise. -/
theorem declEntryRel_with_structs {σ : Type}
    (machine : PanSemState (RiscV.Word 64) (FfiState σ))
    (decl : PanSemDeclarationState (RiscV.Word 64) σ)
    (exact : PanSemStateFiniteExact 64 σ) (context : StructContextExact)
    (h : PanSemDeclEntryRel machine decl exact)
    (hcontext : StructContextByteRanged (panStructContextOfHOL context).toHOL) :
    PanSemDeclEntryRel machine
      { decl with runtime := { decl.runtime with structs := panStructContextOfHOL context } }
      { exact with structs := context } := by
  obtain ⟨⟨hl, hg, _, hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩,
    ⟨hrl, hrg, _⟩, hma, hbw⟩ := h
  exact ⟨⟨hl, hg, panStructContextToHOL_panStructContextOfHOL context,
    hc, he, hm, hmd, hsm, hck, hbe, hffi, hb, ht⟩,
    ⟨hrl, hrg, hcontext⟩, hma, hbw⟩

/-- Proposed reduction of the fixed AST's structure-name prepass. The source
contains no `Decl.name` constructors. Not yet evaluated by Lean. -/
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sourceStructures_empty :
    decsStcnamesHOLExact (width := 64) ([] : StructContextExact)
      (Guest.Software.guestAst.map Flapjack.Pancake.PanLang.declToHOL) = some [] := by
  rfl

/-- Proposed relation after the actual fixed-AST structure prepass. -/
theorem sourcePrepass_rel (input : Guest.InputBlob) (context : StructContextExact)
    (hpre : decsStcnamesHOLExact (width := 64) ([] : StructContextExact)
      (Guest.Software.guestAst.map Flapjack.Pancake.PanLang.declToHOL) = some context) :
    PanSemDeclEntryRel (sourceProduction input)
      { sourceDeclarationState input with runtime :=
        { (sourceDeclarationState input).runtime with structs := panStructContextOfHOL context } }
      { InitE.sourceInitialState input with structs := context } := by
  have eq : context = [] := Option.some.inj (hpre.symm.trans sourceStructures_empty)
  subst context
  apply declEntryRel_with_structs _ _ _ [] (sourceDeclarationState_rel input)
  simp [panStructContextOfHOL, structContextOfHOL, StructContext.toHOL,
    StructContextByteRanged]

/-- Proposed initial-entry agreement, conditional on byte-ranged names in the
original software AST. This does not prove that premise or any cost bound. -/
theorem sourceEntry_agree_of_ranged (input : Guest.InputBlob) (clock : Nat)
    (hranged : ∀ d ∈ Guest.Software.guestAst, Flapjack.Pancake.PanLang.DeclByteRanged d) :
    match panSemRunEntryCake (sourceProduction input) (sourceDeclarationState input)
        Guest.Software.guestAst (toStringOfBytes (ofString "main")) clock,
      panSemRunEntryExact (InitE.sourceInitialState input) Guest.Software.guestAst
        (ofString "main") clock with
    | none, none => True
    | some production, some exactRun =>
        PanSemHOLResultOptionRel production.1 exactRun.1 ∧
          PanSemStateRelExec production.2 exactRun.2.toExact
    | _, _ => False := by
  apply panSemRunEntryCake_agree
  · exact hranged
  · intro context hpre
    exact sourcePrepass_rel input context hpre
  · simp [sourceDeclarationState]
  · simp [sourceDeclarationState]

/-- Proposed exact-entry identity for the byte-normalized production view. -/
theorem canonicalEntry_exact (input : Guest.InputBlob) (clock : Nat) :
    panSemRunEntryExact (InitE.sourceInitialState input)
        InitECandidate.Solver.ParserRange.canonicalDeclarations (ofString "main") clock =
      panSemRunEntryExact (InitE.sourceInitialState input)
        Guest.Software.guestAst (ofString "main") clock := by
  simp only [panSemRunEntryExact,
    InitECandidate.Solver.ParserRange.canonicalDeclarations_exact]

/-- Proposed production/exact entry agreement on decoded declarations,
without requiring the text parser to reconstruct the committed AST. -/
theorem sourceEntry_agree_canonical (input : Guest.InputBlob) (clock : Nat) :
    match panSemRunEntryCake (sourceProduction input) (sourceDeclarationState input)
        InitECandidate.Solver.ParserRange.canonicalDeclarations
        (toStringOfBytes (ofString "main")) clock,
      panSemRunEntryExact (InitE.sourceInitialState input) Guest.Software.guestAst
        (ofString "main") clock with
    | none, none => True
    | some production, some exactRun =>
        PanSemHOLResultOptionRel production.1 exactRun.1 ∧
          PanSemStateRelExec production.2 exactRun.2.toExact
    | _, _ => False := by
  rw [← canonicalEntry_exact input clock]
  apply panSemRunEntryCake_agree
  · exact InitECandidate.Solver.ParserRange.canonicalDeclarations_byteRanged
  · intro context hpre
    apply sourcePrepass_rel input context
    simpa only [InitECandidate.Solver.ParserRange.canonicalDeclarations_exact] using hpre
  · simp [sourceDeclarationState]
  · simp [sourceDeclarationState]

end InitECandidate.Solver.SourceOracleAdapter
