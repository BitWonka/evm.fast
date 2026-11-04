import InitE.SourceSemantics

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
  simpa only [List.map_map, Function.comp_def, bitsToByte, UInt8.ofNat_toNat] using hm

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
  cases op <;>
    simpa only [oracle, InitE.sourceOracle, hcfg, hbytes, holResult] using
      (holResult_rel (Guest.guestOracle (.sharedMem _) host configuration bytes))

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

end InitECandidate.Solver.SourceOracleAdapter
