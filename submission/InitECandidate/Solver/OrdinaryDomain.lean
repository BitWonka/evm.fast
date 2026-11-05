import InitE.SourceSemantics
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyMemory
import Flapjack.Pancake.Semantics.PanSem.TotalSteps
import Flapjack.Pancake.Semantics.PanSem.TotalEvalBridge
import Lean.Elab.Tactic.Omega

/-!
Unelaborated research draft: specialize the upstream aligned interval theorem to
the exact challenge ordinary memory domain. This does not show preservation
through execution, a store failure, termination, or a target step bound.
-/
namespace InitECandidate.Solver.OrdinaryDomain
open Flapjack Flapjack.Compiler.Backend Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget

/-- Proposed range characterization for one address in the initial domain. -/
theorem ordinaryDomain_range (address : BitVec 64) (h : InitE.ordinaryDomain address) :
    holByteAligned address = true ∧
      BitVec.ofNat 64 InitE.sourceBase ≤ address ∧
      address < BitVec.ofNat 64 InitE.heapEnd := by
  have good : goodDimindex 64 := by decide
  have ha : holByteAligned (BitVec.ofNat 64 InitE.sourceBase) = true := by decide
  have hb : holByteAligned (BitVec.ofNat 64 InitE.heapEnd) = true := by decide
  have hab : BitVec.ofNat 64 InitE.sourceBase ≤ BitVec.ofNat 64 InitE.heapEnd := by decide
  have hcount :
      (-1 * BitVec.ofNat 64 InitE.sourceBase + BitVec.ofNat 64 InitE.heapEnd).toNat /
          (64 / 8) = (InitE.stackStart - InitE.sourceBase) / 8 - InitE.globalsWords := by
    decide
  have heq := alignedInterval_eq_addresses good (BitVec.ofNat 64 InitE.sourceBase)
    (BitVec.ofNat 64 InitE.heapEnd) ha hb hab
  rw [hcount] at heq
  apply (congrFun heq address).mpr
  simpa only [InitE.ordinaryDomain] using h

/-- Convert the proposed word-order characterization to natural endpoints. -/
theorem ordinaryDomain_toNat_bounds (address : BitVec 64) (h : InitE.ordinaryDomain address) :
    InitE.sourceBase ≤ address.toNat ∧ address.toNat < InitE.heapEnd := by
  obtain ⟨_, hlo, hhi⟩ := ordinaryDomain_range address h
  have hbase : (BitVec.ofNat 64 InitE.sourceBase).toNat = InitE.sourceBase := by decide
  have hend : (BitVec.ofNat 64 InitE.heapEnd).toNat = InitE.heapEnd := by decide
  have hlo' : (BitVec.ofNat 64 InitE.sourceBase).toNat ≤ address.toNat := hlo
  have hhi' : address.toNat < (BitVec.ofNat 64 InitE.heapEnd).toNat := hhi
  exact ⟨by simpa only [hbase] using hlo', by simpa only [hend] using hhi'⟩

/-- Proposed bridge from successful scalar word store to the evaluator's
state-owned ordinary-memory domain. -/
theorem scalar_store_requires_domain {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : RiscV.Word 64)
    (post : RiscV.Word 64 → Option (PanValue (RiscV.Word 64)))
    (h : panValueStoreWithAccess state.memory panSemBitVec64BytesInWord address
      (.word value) (some (panSemBitVec64MemoryAccess state)) = some post) :
    state.memaddrs address = true := by
  cases hd : state.memaddrs address with
  | false =>
      simp [panValueStoreWithAccess, panValueFlatWords, panValueFlatValueFuel,
        panValueFlatWordsFuel, panValueFlatStoreWords, panSemBitVec64MemoryAccess,
        panValueMemoryAccessOfModel, hd] at h
  | true => exact hd

/-- Proposed state-frame fact for the total word-store clause. -/
theorem storeClause_preserves_domain {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64)) :
    (panSemTotalStoreClause state address value).2.memaddrs = state.memaddrs := by
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

/-- Proposed domain frame for assignments, including error outcomes. -/
theorem assignClause_preserves_domain {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (kind : VarKind) (name : VarName) (expression : Exp (RiscV.Word 64)) :
    (panSemTotalAssignClause state kind name expression).2.memaddrs = state.memaddrs := by
  cases he : evalPanSemStateExp state expression with
  | none => simp [panSemTotalAssignClause, panSemTotalExprStep, he]
  | some value =>
      by_cases hv : panValueAssignmentValid state.structs state.locals state.globals kind name value = true
      · cases kind <;> simp [panSemTotalAssignClause, panSemTotalExprStep, he, hv]
      · cases kind <;> simp [panSemTotalAssignClause, panSemTotalExprStep, he, hv]

/-- A normally completed scalar word store requires its address in the domain. -/
theorem normal_word_store_requires_domain {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64)) (addr word : RiscV.Word 64)
    (ha : evalPanSemStateExp state address = some (.word addr))
    (hv : evalPanSemStateExp state value = some (.word word))
    (hnormal : (panSemTotalStoreClause state address value).1 = none) :
    state.memaddrs addr = true := by
  cases hs : panValueStoreWithAccess state.memory panSemBitVec64BytesInWord addr
      (.word word) (some (panSemBitVec64MemoryAccess state)) with
  | none => simp [panSemTotalStoreClause, panSemTotalExprStep, ha, hv, hs] at hnormal
  | some memory => exact scalar_store_requires_domain state addr word memory hs

/-- Project the ordinary-domain correspondence from an existing complete
production/exact state relation. The relation and exact-domain invariant are
premises, not conclusions of this lemma. -/
theorem related_exact_domain {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateExact 64 σ)
    (hrel : PanSemStateRelExec production exact)
    (hexact : exact.memaddrs = InitE.ordinaryDomain) :
    ∀ address, production.memaddrs address = true ↔ InitE.ordinaryDomain address := by
  rcases hrel with ⟨_, _, _, _, _, _, hdomains, _, _, _, _, _, _⟩
  intro address
  simpa only [hexact] using hdomains address

/-- Conditional composition at the production/exact domain boundary. -/
theorem normal_word_store_in_ordinary_interval {σ : Type}
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (address value : Exp (RiscV.Word 64)) (addr word : RiscV.Word 64)
    (hdom : ∀ x, state.memaddrs x = true ↔ InitE.ordinaryDomain x)
    (ha : evalPanSemStateExp state address = some (.word addr))
    (hv : evalPanSemStateExp state value = some (.word word))
    (hnormal : (panSemTotalStoreClause state address value).1 = none) :
    holByteAligned addr = true ∧
      BitVec.ofNat 64 InitE.sourceBase ≤ addr ∧
      addr < BitVec.ofNat 64 InitE.heapEnd := by
  apply ordinaryDomain_range addr
  exact (hdom addr).mp (normal_word_store_requires_domain state address value addr word ha hv hnormal)

/-- Arithmetic only: starting below `stop`, the first 32-byte step past the
end occurs before word wrap if the end has 31 bytes of headroom. -/
theorem firstOutside32 (a stop modulus : Nat) (ha : a < stop)
    (hspace : stop + 31 < modulus) :
    let k := (stop - a + 31) / 32
    stop ≤ a + 32 * k ∧ a + 32 * k < stop + 32 ∧
      a + 32 * k < modulus ∧ ∀ j < k, a + 32 * j < stop := by
  dsimp
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · intro j hj
    omega

/-- Conditional contradiction: one additional 32-byte-spaced address cannot
stay below the interval end through the first crossing. -/
theorem cannotRemainBelowStop32 (a stop modulus : Nat) (ha : a < stop)
    (hspace : stop + 31 < modulus)
    (hall : ∀ j ≤ (stop - a + 31) / 32, (a + 32 * j) % modulus < stop) : False := by
  have hcross := firstOutside32 a stop modulus ha hspace
  dsimp at hcross
  obtain ⟨hge, _, hnowrap, _⟩ := hcross
  have hinside := hall ((stop - a + 31) / 32) (Nat.le_refl _)
  rw [Nat.mod_eq_of_lt hnowrap] at hinside
  omega

/-- One extra unit lets a loop attempt an out-of-domain store and terminate
with an error; it does not assert that a store or loop actually terminates. -/
def rangeBudget32 (base stop address : Nat) : Nat :=
  if base ≤ address ∧ address < stop then 1 + (stop - address + 31) / 32 else 1

/-- The measure itself has a uniform interval-size bound, including outside
addresses. This is an arithmetic fact, not yet an execution bound. -/
theorem rangeBudget32_uniform (base stop address : Nat) :
    rangeBudget32 base stop address ≤ 1 + (stop - base + 31) / 32 := by
  unfold rangeBudget32
  split <;> omega

/-- Proposed arithmetic decrease once a valid in-range address advances by 32. -/
theorem rangeBudget32_step (base stop address modulus : Nat)
    (hbase : base ≤ address) (hstop : address < stop) (hspace : stop + 31 < modulus) :
    (address + 32) % modulus = address + 32 ∧
      rangeBudget32 base stop (address + 32) < rangeBudget32 base stop address := by
  have hnowrap : address + 32 < modulus := by omega
  constructor
  · exact Nat.mod_eq_of_lt hnowrap
  · have hin : base ≤ address ∧ address < stop := ⟨hbase, hstop⟩
    simp only [rangeBudget32, if_pos hin]
    by_cases hn : address + 32 < stop
    · have hnext : base ≤ address + 32 ∧ address + 32 < stop := by omega
      simp only [if_pos hnext]
      omega
    · have hout : ¬ (base ≤ address + 32 ∧ address + 32 < stop) := by omega
      simp only [if_neg hout]
      omega

end InitECandidate.Solver.OrdinaryDomain
