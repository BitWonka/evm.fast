import Flapjack.Pancake.Semantics.PanSem.TotalEvalAgree

/-! # L3 source-cost kit for EVM.fast (lane L3)

Cost calculus on flapjack `panSemTotalEvaluate`, transfer to the contract evaluator,
and a first real-guest loop bound. The inherited Unit-specialized version was
reported built by its author; the generic-FFI draft below has not been checked.

## Gap A, base case: a program with no `while`, `call`, `decCall` or `tick`
does not consume source clock under the production total evaluator. -/

namespace Flapjack.L3
open Flapjack.Pancake.PanLang

def ClockFree {α : Type} : Prog α → Bool
  | .skip | .assign .. | .primitive .. | .store .. | .store32 .. | .storeByte .. => true
  | .break | .continue | .extCall .. | .raise .. | .return .. => true
  | .shMemLoad .. | .shMemStore .. | .annot .. => true
  | .dec _ _ _ body => ClockFree body
  | .seq a b => ClockFree a && ClockFree b
  | .ite _ a b => ClockFree a && ClockFree b
  | .while .. | .call .. | .decCall .. | .tick => false

variable {σ : Type} [NeZero 64]
    [BEq (RiscV.Word 64)] [DecidableEq (RiscV.Word 64)]
    [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)] [BEq String] [LawfulBEq String]

theorem ite_clock {β : Type} (c : Prop) [Decidable c]
    (a b : β × PanSemState (RiscV.Word 64) (FfiState σ)) (k : Nat)
    (ha : a.2.clock = k) (hb : b.2.clock = k) : (if c then a else b).2.clock = k := by
  by_cases h : c <;> simp [h, ha, hb]

theorem exprStep_clock (s : PanSemState (RiscV.Word 64) (FfiState σ)) (e : Exp (RiscV.Word 64))
    (k : PanValue (RiscV.Word 64) → Option (PanSemHOLResult (RiscV.Word 64)) ×
      PanSemState (RiscV.Word 64) (FfiState σ))
    (hk : ∀ v, (k v).2.clock = s.clock) : (panSemTotalExprStep s e k).2.clock = s.clock := by
  unfold panSemTotalExprStep; split
  · exact hk _
  · rfl

theorem store_clock (s : PanSemState (RiscV.Word 64) (FfiState σ)) (a b : Exp (RiscV.Word 64)) :
    (panSemTotalStoreClause s a b).2.clock = s.clock := by
  unfold panSemTotalStoreClause
  apply exprStep_clock; intro va
  cases va <;> (try rfl)
  apply exprStep_clock; intro vb
  split <;> rfl

theorem assign_clock (s : PanSemState (RiscV.Word 64) (FfiState σ)) (k : VarKind) (n : VarName)
    (e : Exp (RiscV.Word 64)) : (panSemTotalAssignClause s k n e).2.clock = s.clock := by
  unfold panSemTotalAssignClause
  apply exprStep_clock; intro v
  apply ite_clock <;> (cases k <;> rfl)

theorem exprListStep_clock (s : PanSemState (RiscV.Word 64) (FfiState σ)) (es : List (Exp (RiscV.Word 64)))
    (k : List (PanValue (RiscV.Word 64)) → Option (PanSemHOLResult (RiscV.Word 64)) ×
      PanSemState (RiscV.Word 64) (FfiState σ))
    (hk : ∀ v, (k v).2.clock = s.clock) : (panSemTotalExprListStep s es k).2.clock = s.clock := by
  unfold panSemTotalExprListStep; split
  · exact hk _
  · rfl

theorem store32_clock (s : PanSemState (RiscV.Word 64) (FfiState σ)) (a b : Exp (RiscV.Word 64)) :
    (panSemTotalStore32Clause s a b).2.clock = s.clock := by
  unfold panSemTotalStore32Clause
  apply exprStep_clock; intro va
  cases va <;> (try rfl)
  all_goals (apply exprStep_clock; intro vb; cases vb <;> (try rfl))
  all_goals (repeat' split)
  all_goals rfl

theorem storeByte_clock (s : PanSemState (RiscV.Word 64) (FfiState σ)) (a b : Exp (RiscV.Word 64)) :
    (panSemTotalStoreByteClause s a b).2.clock = s.clock := by
  unfold panSemTotalStoreByteClause
  apply exprStep_clock; intro va
  cases va <;> (try rfl)
  all_goals (apply exprStep_clock; intro vb; cases vb <;> (try rfl))
  all_goals (repeat' split)
  all_goals rfl

theorem raise_clock (s : PanSemState (RiscV.Word 64) (FfiState σ)) (x : ExceptionId) (e : Exp (RiscV.Word 64)) :
    (panSemTotalRaiseClause s x e).2.clock = s.clock := by
  unfold panSemTotalRaiseClause
  apply exprStep_clock; intro v
  split
  · apply ite_clock <;> rfl
  · rfl

theorem return_clock (s : PanSemState (RiscV.Word 64) (FfiState σ)) (e : Exp (RiscV.Word 64)) :
    (panSemTotalReturnClause s e).2.clock = s.clock := by
  unfold panSemTotalReturnClause
  apply exprStep_clock; intro v
  apply ite_clock <;> rfl

theorem primitive_clock (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (s : PanSemState (RiscV.Word 64) (FfiState σ)) (n : VarName) (o : PrimOp) (es : List (Exp (RiscV.Word 64))) :
    (panSemTotalPrimitiveClause s n o es primitive).2.clock = s.clock := by
  unfold panSemTotalPrimitiveClause
  apply exprListStep_clock; intro v
  split
  · apply ite_clock <;> rfl
  · rfl

theorem extCall_clock (s : PanSemState (RiscV.Word 64) (FfiState σ)) (f : FunName)
    (a b c d : Exp (RiscV.Word 64)) :
    (panSemTotalExtCallClause s f a b c d).2.clock = s.clock := by
  unfold panSemTotalExtCallClause
  apply exprStep_clock; intro va
  apply exprStep_clock; intro vb
  apply exprStep_clock; intro vc
  apply exprStep_clock; intro vd
  unfold panSemTotalExtCallStep
  repeat' split
  all_goals (try rfl)
  all_goals (simp [panSemTotalMachineWriteBytes])

theorem shLoad_res_clock (s : PanSemState (RiscV.Word 64) (FfiState σ))
    (ctx : PanValueFfiContext (RiscV.Word 64)) (st : PanShMemLoadState (RiscV.Word 64) σ)
    (h : st.clock = s.clock) (k : VarKind) (n : VarName) (z : OpSize) (a : RiscV.Word 64) :
    (panSemTotalShMemLoadResult s (panShMemLoad ctx st k n z a)).2.clock = s.clock := by
  have key : ∀ r, r = panShMemLoad ctx st k n z a →
      (panSemTotalShMemLoadResult s r).2.clock = s.clock := by
    intro r hr
    unfold panShMemLoad at hr
    dsimp only at hr
    repeat' (split at hr)
    all_goals (subst hr; simp [panSemTotalShMemLoadResult, panSemTotalShMemStateBack, h])
  exact key _ rfl

theorem shStore_res_clock (s : PanSemState (RiscV.Word 64) (FfiState σ))
    (ctx : PanValueFfiContext (RiscV.Word 64)) (st : PanShMemLoadState (RiscV.Word 64) σ)
    (h : st.clock = s.clock) (b : RiscV.Word 64) (a : RiscV.Word 64) (z : OpSize) :
    (panSemTotalShMemStoreResult s (panShMemStore ctx st b a z)).2.clock = s.clock := by
  have key : ∀ r, r = panShMemStore ctx st b a z →
      (panSemTotalShMemStoreResult s r).2.clock = s.clock := by
    intro r hr
    unfold panShMemStore at hr
    dsimp only at hr
    repeat' (split at hr)
    all_goals (subst hr; simp [panSemTotalShMemStoreResult, panSemTotalShMemStateBack, h])
  exact key _ rfl

theorem shMemLoad_clock (s : PanSemState (RiscV.Word 64) (FfiState σ)) (z : OpSize) (k : VarKind)
    (n : VarName) (a : Exp (RiscV.Word 64)) :
    (panSemTotalShMemLoadClause s z k n a).2.clock = s.clock := by
  unfold panSemTotalShMemLoadClause
  apply exprStep_clock; intro va
  cases va <;> (try rfl)
  repeat' split
  all_goals (first | rfl | exact shLoad_res_clock _ _ _ rfl _ _ _ _)

theorem shMemStore_clock (s : PanSemState (RiscV.Word 64) (FfiState σ)) (z : OpSize)
    (a b : Exp (RiscV.Word 64)) :
    (panSemTotalShMemStoreClause s z a b).2.clock = s.clock := by
  unfold panSemTotalShMemStoreClause
  apply exprStep_clock; intro va
  cases va <;> (try rfl)
  all_goals (apply exprStep_clock; intro vb; cases vb <;> (try rfl))
  all_goals (repeat' split)
  all_goals (first | rfl | exact shStore_res_clock _ _ _ rfl _ _ _)

theorem clockFree_clock (primitive : PanPrimitiveHandler (RiscV.Word 64)) :
    (p : Prog (RiscV.Word 64)) → (s : PanSemState (RiscV.Word 64) (FfiState σ)) →
      ClockFree p = true → (panSemTotalEvaluate primitive p s).2.clock = s.clock
  | .skip, s, _ => by rw [panSemTotalEvaluate]; simp [panSemEvaluateClockLeaf]
  | .break, s, _ => by rw [panSemTotalEvaluate]; simp [panSemEvaluateClockLeaf]
  | .continue, s, _ => by rw [panSemTotalEvaluate]; simp [panSemEvaluateClockLeaf]
  | .annot _ _, s, _ => by rw [panSemTotalEvaluate]
  | .assign k n e, s, _ => by rw [panSemTotalEvaluate]; exact assign_clock s k n e
  | .primitive n o es, s, _ => by rw [panSemTotalEvaluate]; exact primitive_clock primitive s n o es
  | .store a b, s, _ => by rw [panSemTotalEvaluate]; exact store_clock s a b
  | .store32 a b, s, _ => by rw [panSemTotalEvaluate]; exact store32_clock s a b
  | .storeByte a b, s, _ => by rw [panSemTotalEvaluate]; exact storeByte_clock s a b
  | .raise x e, s, _ => by rw [panSemTotalEvaluate]; exact raise_clock s x e
  | .return e, s, _ => by rw [panSemTotalEvaluate]; exact return_clock s e
  | .extCall f a b c d, s, _ => by rw [panSemTotalEvaluate]; exact extCall_clock s f a b c d
  | .shMemLoad z k n a, s, _ => by rw [panSemTotalEvaluate]; exact shMemLoad_clock s z k n a
  | .shMemStore z a b, s, _ => by rw [panSemTotalEvaluate]; exact shMemStore_clock s z a b
  | .dec n sh e body, s, h => by
      rw [panSemTotalEvaluate]
      have hb : ClockFree body = true := h
      split
      · rfl
      · split
        · dsimp only
          rw [clockFree_clock primitive body _ hb]
          rfl
        · rfl
  | .seq a b, s, h => by
      rw [panSemTotalEvaluate]
      have ha : ClockFree a = true := by simp [ClockFree] at h; exact h.1
      have hb : ClockFree b = true := by simp [ClockFree] at h; exact h.2
      have hfix : (panSemFixClock s.clock (panSemTotalEvaluate primitive a s).2).clock = s.clock := by
        simp [panSemFixClock, clockFree_clock primitive a s ha]
      (try dsimp only)
      split
      · rw [clockFree_clock primitive b _ hb, hfix]
      · exact hfix
  | .ite c a b, s, h => by
      rw [panSemTotalEvaluate]
      have ha : ClockFree a = true := by simp [ClockFree] at h; exact h.1
      have hb : ClockFree b = true := by simp [ClockFree] at h; exact h.2
      split
      · split
        · exact clockFree_clock primitive b s hb
        · exact clockFree_clock primitive a s ha
      · rfl
  | .while _ _, _, h => by simp [ClockFree] at h
  | .call _ _ _, _, h => by simp [ClockFree] at h
  | .decCall _ _ _ _ _, _, h => by simp [ClockFree] at h
  | .tick, _, h => by simp [ClockFree] at h

/-- A program uses at most `n` source clock from every state satisfying `P`. -/
def CostLe (primitive : PanPrimitiveHandler (RiscV.Word 64)) (P : PanSemState (RiscV.Word 64) (FfiState σ) → Prop)
    (p : Prog (RiscV.Word 64)) (n : Nat) : Prop :=
  ∀ s, P s → s.clock ≤ (panSemTotalEvaluate primitive p s).2.clock + n

theorem costLe_clockFree (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (P : PanSemState (RiscV.Word 64) (FfiState σ) → Prop) (p : Prog (RiscV.Word 64))
    (h : ClockFree p = true) : CostLe primitive P p 0 := by
  intro s _; rw [clockFree_clock primitive p s h]; omega

/-- Sequencing: costs add. `Q` must hold on every intermediate state the second part starts from. -/
theorem costLe_seq (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (P Q : PanSemState (RiscV.Word 64) (FfiState σ) → Prop) (a b : Prog (RiscV.Word 64)) (n m : Nat)
    (ha : CostLe primitive P a n) (hb : CostLe primitive Q b m)
    (hQ : ∀ s, P s → Q (panSemFixClock s.clock (panSemTotalEvaluate primitive a s).2)) :
    CostLe primitive P (.seq a b) (n + m) := by
  intro s hs
  rw [panSemTotalEvaluate]
  have h1 := ha s hs
  have hfix : s.clock ≤ (panSemFixClock s.clock (panSemTotalEvaluate primitive a s).2).clock + n := by
    simp only [panSemFixClock]; omega
  (try dsimp only)
  split
  · have h2 := hb _ (hQ s hs); omega
  · show s.clock ≤ (panSemFixClock s.clock (panSemTotalEvaluate primitive a s).2).clock + (n + m)
    omega

/-- While loops: a measure that strictly drops on every continuing iteration bounds the cost
by `μ s * (b + 1)`, where `b` bounds one body run. -/
theorem costLe_while (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (I : PanSemState (RiscV.Word 64) (FfiState σ) → Prop)
    (μ : PanSemState (RiscV.Word 64) (FfiState σ) → Nat)
    (c : Exp (RiscV.Word 64)) (body : Prog (RiscV.Word 64)) (b : Nat)
    (hpos : ∀ s v, I s → evalPanSemStateExp s c = some (.word v) → v ≠ 0 → 0 < μ s)
    (hbody : ∀ s v, I s → evalPanSemStateExp s c = some (.word v) → v ≠ 0 → s.clock ≠ 0 →
      s.clock - 1 ≤ (panSemTotalEvaluate primitive body { s with clock := s.clock - 1 }).2.clock + b)
    (hstep : ∀ s v, I s → evalPanSemStateExp s c = some (.word v) → v ≠ 0 → s.clock ≠ 0 →
      ((panSemTotalEvaluate primitive body { s with clock := s.clock - 1 }).1 = none ∨
       (panSemTotalEvaluate primitive body { s with clock := s.clock - 1 }).1 = some .continue) →
      I (panSemFixClock (s.clock - 1) (panSemTotalEvaluate primitive body { s with clock := s.clock - 1 }).2) ∧
      μ (panSemFixClock (s.clock - 1) (panSemTotalEvaluate primitive body { s with clock := s.clock - 1 }).2) < μ s) :
    ∀ s, I s → s.clock ≤ (panSemTotalEvaluate primitive (.while c body) s).2.clock + μ s * (b + 1) := by
  intro s
  induction h : μ s using Nat.strongRecOn generalizing s with
  | _ k ih =>
  intro hs
  rw [panSemTotalEvaluate]
  split
  · rename_i v hv
    split
    · show s.clock ≤ s.clock + _; omega
    · rename_i hv0
      have hk : 0 < k := h ▸ hpos s v hs hv hv0
      split
      · show s.clock ≤ (panEmptyLocals s).clock + _
        simp [panEmptyLocals]
      · rename_i hc
        have hb := hbody s v hs hv hv0 hc
        have hfix : s.clock - 1 ≤ (panSemFixClock (s.clock - 1)
            (panSemTotalEvaluate primitive body { s with clock := s.clock - 1 }).2).clock + b := by
          simp only [panSemFixClock]; omega
        have kb : b + 1 ≤ k * (b + 1) := Nat.le_mul_of_pos_left _ hk
        dsimp only
        split
        · rename_i hr
          obtain ⟨hI, hμ⟩ := hstep s v hs hv hv0 hc (.inl hr)
          have := ih _ (h ▸ hμ) _ rfl hI
          have : μ (panSemFixClock (s.clock - 1)
              (panSemTotalEvaluate primitive body { s with clock := s.clock - 1 }).2) * (b + 1)
              + (b + 1) ≤ k * (b + 1) := by
            rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (h ▸ hμ)
          omega
        · rename_i hr
          obtain ⟨hI, hμ⟩ := hstep s v hs hv hv0 hc (.inr hr)
          have := ih _ (h ▸ hμ) _ rfl hI
          have : μ (panSemFixClock (s.clock - 1)
              (panSemTotalEvaluate primitive body { s with clock := s.clock - 1 }).2) * (b + 1)
              + (b + 1) ≤ k * (b + 1) := by
            rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (h ▸ hμ)
          omega
        · show s.clock ≤ (panSemFixClock (s.clock - 1) _).clock + _; omega
        · show s.clock ≤ (panSemFixClock (s.clock - 1) _).clock + _; omega
  · show s.clock ≤ s.clock + _; omega

/-- Calls: one tick for the call, plus the callee's cost, plus an exception handler's cost. -/
theorem costLe_call (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (P : PanSemState (RiscV.Word 64) (FfiState σ) → Prop)
    (info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog (RiscV.Word 64))))
    (f : FunName) (args : List (Exp (RiscV.Word 64))) (cb hb : Nat)
    (hcallee : ∀ s vals callee nl rs, P s → evalPanSemStateExps s args = some vals →
      panSemTotalCodeLookup s f vals = some (callee, nl, rs) → s.clock ≠ 0 →
      s.clock - 1 ≤ (panSemTotalEvaluate primitive callee
        { s with clock := s.clock - 1, locals := nl }).2.clock + cb)
    (hhandler : ∀ r hid hv hp, info = some (r, some (hid, hv, hp)) →
      ∀ st : PanSemState (RiscV.Word 64) (FfiState σ),
        st.clock ≤ (panSemTotalEvaluate primitive hp st).2.clock + hb) :
    CostLe primitive P (.call info f args) (1 + cb + hb) := by
  intro s hs
  rw [panSemTotalEvaluate]
  split
  · show s.clock ≤ s.clock + _; omega
  · rename_i vals hvals
    split
    · show s.clock ≤ s.clock + _; omega
    · rename_i callee nl rs hlk
      split
      · show s.clock ≤ (panEmptyLocals s).clock + _; simp [panEmptyLocals]
      · rename_i hc
        have h1 := hcallee s vals callee nl rs hs hvals hlk hc
        have hfix : s.clock ≤ (panSemFixClock (s.clock - 1) (panSemTotalEvaluate primitive callee
            { s with clock := s.clock - 1, locals := nl }).2).clock + (1 + cb) := by
          simp only [panSemFixClock]; omega
        dsimp only
        repeat' split
        all_goals (first
          | (simp only [panEmptyLocals, panSemFixClock] at hfix ⊢; omega)
          | (simp only [panSemFixClock] at hfix ⊢; omega)
          | skip)
        all_goals (
          have hh := hhandler _ _ _ _ rfl
          rw [show ∀ x : Nat, x + (1 + cb + hb) = (x + hb) + (1 + cb) from fun x => by omega]
          refine Nat.le_trans ?_ (Nat.add_le_add_right (hh _) _)
          simp only [panSemFixClock] at hfix ⊢
          omega)

/-- Declared calls: one tick, the callee, then the continuation. -/
theorem costLe_decCall (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (P : PanSemState (RiscV.Word 64) (FfiState σ) → Prop)
    (n : VarName) (sh : Shape) (f : FunName) (args : List (Exp (RiscV.Word 64)))
    (cont : Prog (RiscV.Word 64)) (cb kb : Nat)
    (hcallee : ∀ s vals callee nl rs, P s → evalPanSemStateExps s args = some vals →
      panSemTotalCodeLookup s f vals = some (callee, nl, rs) → s.clock ≠ 0 →
      s.clock - 1 ≤ (panSemTotalEvaluate primitive callee
        { s with clock := s.clock - 1, locals := nl }).2.clock + cb)
    (hcont : ∀ st : PanSemState (RiscV.Word 64) (FfiState σ),
        st.clock ≤ (panSemTotalEvaluate primitive cont st).2.clock + kb) :
    CostLe primitive P (.decCall n sh f args cont) (1 + cb + kb) := by
  intro s hs
  rw [panSemTotalEvaluate]
  split
  · show s.clock ≤ s.clock + _; omega
  · rename_i vals hvals
    split
    · show s.clock ≤ s.clock + _; omega
    · rename_i callee nl rs hlk
      split
      · show s.clock ≤ (panEmptyLocals s).clock + _; simp [panEmptyLocals]
      · rename_i hc
        have h1 := hcallee s vals callee nl rs hs hvals hlk hc
        have hfix : s.clock ≤ (panSemFixClock (s.clock - 1) (panSemTotalEvaluate primitive callee
            { s with clock := s.clock - 1, locals := nl }).2).clock + (1 + cb) := by
          simp only [panSemFixClock]; omega
        dsimp only
        repeat' split
        all_goals (first
          | (simp only [panEmptyLocals, panSemFixClock] at hfix ⊢; omega)
          | (simp only [panSemFixClock] at hfix ⊢; omega)
          | skip)
        all_goals (
          rw [show ∀ x : Nat, x + (1 + cb + kb) = (x + kb) + (1 + cb) from fun x => by omega]
          refine Nat.le_trans ?_ (Nat.add_le_add_right (hcont _) _)
          simp only [panSemFixClock] at hfix ⊢
          omega)

/-- `dec`: the body's cost. -/
theorem costLe_dec (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (P : PanSemState (RiscV.Word 64) (FfiState σ) → Prop)
    (n : VarName) (sh : Shape) (e : Exp (RiscV.Word 64)) (body : Prog (RiscV.Word 64)) (b : Nat)
    (hbody : ∀ st : PanSemState (RiscV.Word 64) (FfiState σ),
        st.clock ≤ (panSemTotalEvaluate primitive body st).2.clock + b) :
    CostLe primitive P (.dec n sh e body) b := by
  intro s _
  rw [panSemTotalEvaluate]
  split
  · show s.clock ≤ s.clock + _; omega
  · rename_i v _
    split
    · have := hbody (panSemTotalDecBind s n v)
      simp only [panSemTotalDecBind] at this ⊢
      exact this
    · show s.clock ≤ s.clock + _; omega

/-- `if`: the larger branch cost. -/
theorem costLe_ite (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (P : PanSemState (RiscV.Word 64) (FfiState σ) → Prop)
    (c : Exp (RiscV.Word 64)) (a b : Prog (RiscV.Word 64)) (n m : Nat)
    (ha : CostLe primitive P a n) (hb : CostLe primitive P b m) :
    CostLe primitive P (.ite c a b) (max n m) := by
  intro s hs
  rw [panSemTotalEvaluate]
  split
  · split
    · have := hb s hs; omega
    · have := ha s hs; omega
  · show s.clock ≤ s.clock + _; omega

end Flapjack.L3


namespace Flapjack.L3.Pilot
open Flapjack

variable {σ : Type}

def iV : Exp (RiscV.Word 64) := .var .local "i"
def nV : Exp (RiscV.Word 64) := .var .local "n"
def tailCond : Exp (RiscV.Word 64) := .cmp .lower iV nV

example (s : PanSemState (RiscV.Word 64) (FfiState σ)) (i n : RiscV.Word 64)
    (hi : s.locals "i" = some (.word i)) (hn : s.locals "n" = some (.word n)) :
    evalPanSemStateExp s tailCond = some (.word (if i < n then 1 else 0)) := by
  simp [evalPanSemStateExp, tailCond, iV, nV, evalPanValueExp, hi, hn,
    panSemBitVec64MemoryAccess_compare, Compiler.Encoders.Asm.wordCmpHOL]

def dV : Exp (RiscV.Word 64) := .var .local "dst"
def tailBody : Prog (RiscV.Word 64) :=
  .seq (.storeByte (.op .add [dV, iV]) (.const 0))
       (.assign .local "i" (.op .add [iV, .const 1]))
def tailLoop : Prog (RiscV.Word 64) := .while tailCond tailBody

theorem storeByte_none_locals (s : PanSemState (RiscV.Word 64) (FfiState σ)) (a b : Exp (RiscV.Word 64))
    (h : (panSemTotalStoreByteClause s a b).1 = none) :
    (panSemTotalStoreByteClause s a b).2.locals = s.locals := by
  revert h
  unfold panSemTotalStoreByteClause panSemTotalExprStep
  split
  · rename_i va _
    split
    · rename_i vb _
      cases va <;> (try simp)
      cases vb <;> (try simp)
      split <;> simp
    · cases va <;> simp
  · simp

theorem assign_none_locals (s : PanSemState (RiscV.Word 64) (FfiState σ)) (n : VarName)
    (e : Exp (RiscV.Word 64)) (v : PanValue (RiscV.Word 64)) (he : evalPanSemStateExp s e = some v)
    (h : (panSemTotalAssignClause s .local n e).1 = none) :
    (panSemTotalAssignClause s .local n e).2.locals = updatePanValueMap s.locals n v := by
  revert h
  unfold panSemTotalAssignClause panSemTotalExprStep
  rw [he]
  dsimp only
  split <;> simp_all

theorem tailBody_step (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (t : PanSemState (RiscV.Word 64) (FfiState σ)) (i0 : RiscV.Word 64)
    (hi : t.locals "i" = some (.word i0))
    (h : (panSemTotalEvaluate primitive tailBody t).1 = none) :
    (panSemTotalEvaluate primitive tailBody t).2.locals = updatePanValueMap t.locals "i" (.word (i0 + 1)) := by
  have hsb : ∀ u : PanSemState (RiscV.Word 64) (FfiState σ), panSemTotalEvaluate primitive (.storeByte (.op .add [dV, iV]) (.const 0)) u =
      panSemTotalStoreByteClause u (.op .add [dV, iV]) (.const 0) := fun u => by rw [panSemTotalEvaluate]
  have has : ∀ u : PanSemState (RiscV.Word 64) (FfiState σ), panSemTotalEvaluate primitive (.assign .local "i" (.op .add [iV, .const 1])) u =
      panSemTotalAssignClause u .local "i" (.op .add [iV, .const 1]) := fun u => by rw [panSemTotalEvaluate]
  have hseq : panSemTotalEvaluate primitive tailBody t =
      (let r := panSemTotalEvaluate primitive (.storeByte (.op .add [dV, iV]) (.const 0)) t
       let f := panSemFixClock t.clock r.2
       match r.1 with
       | none => panSemTotalEvaluate primitive (.assign .local "i" (.op .add [iV, .const 1])) f
       | some res => (some res, f)) := by
    unfold tailBody
    conv => lhs; rw [panSemTotalEvaluate]
    rfl
  rw [hseq] at h ⊢
  rw [hsb] at h ⊢
  generalize hr : panSemTotalStoreByteClause t (.op .add [dV, iV]) (.const 0) = r at h ⊢
  rcases r with ⟨r1, t1⟩
  cases r1 with
  | some x => simp at h
  | none =>
    have hloc : t1.locals = t.locals := by
      have := storeByte_none_locals t (.op .add [dV, iV]) (.const 0) (by rw [hr])
      rw [hr] at this; exact this
    simp only [has] at h ⊢
    have he : evalPanSemStateExp (panSemFixClock t.clock t1) (.op .add [iV, .const 1]) = some (.word (i0 + 1)) := by
      simp [evalPanSemStateExp, panSemFixClock, iV, evalPanValueExp, evalPanValueExp.evalPanValueExps, hloc, hi,
        panSemBitVec64MemoryAccess_wordOp]
      simp [wordOpHOL, wordOp]
    have := assign_none_locals _ "i" _ _ he h
    rw [this]
    simp [panSemFixClock, hloc]

theorem storeByte_res (s : PanSemState (RiscV.Word 64) (FfiState σ)) (a b : Exp (RiscV.Word 64)) :
    (panSemTotalStoreByteClause s a b).1 = none ∨ (panSemTotalStoreByteClause s a b).1 = some .error := by
  unfold panSemTotalStoreByteClause panSemTotalExprStep
  split
  · rename_i va _
    split
    · rename_i vb _
      cases va <;> (try simp)
      cases vb <;> (try simp)
      split <;> simp
    · cases va <;> simp
  · simp

theorem assign_res (s : PanSemState (RiscV.Word 64) (FfiState σ)) (k : VarKind) (n : VarName)
    (e : Exp (RiscV.Word 64)) :
    (panSemTotalAssignClause s k n e).1 = none ∨ (panSemTotalAssignClause s k n e).1 = some .error := by
  unfold panSemTotalAssignClause panSemTotalExprStep
  split
  · rename_i v _
    by_cases hv : panValueAssignmentValid s.structs s.locals s.globals k n v = true
    · cases k <;> simp [hv]
    · cases k <;> simp [hv]
  · simp

theorem tailBody_not_continue (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (t : PanSemState (RiscV.Word 64) (FfiState σ)) :
    (panSemTotalEvaluate primitive tailBody t).1 ≠ some .continue := by
  have hsb : ∀ u : PanSemState (RiscV.Word 64) (FfiState σ), panSemTotalEvaluate primitive (.storeByte (.op .add [dV, iV]) (.const 0)) u =
      panSemTotalStoreByteClause u (.op .add [dV, iV]) (.const 0) := fun u => by rw [panSemTotalEvaluate]
  have has : ∀ u : PanSemState (RiscV.Word 64) (FfiState σ), panSemTotalEvaluate primitive (.assign .local "i" (.op .add [iV, .const 1])) u =
      panSemTotalAssignClause u .local "i" (.op .add [iV, .const 1]) := fun u => by rw [panSemTotalEvaluate]
  unfold tailBody
  rw [panSemTotalEvaluate]
  simp only [hsb, has]
  rcases storeByte_res t (.op .add [dV, iV]) (.const 0) with h | h
  · rw [h]; dsimp only
    rcases assign_res (panSemFixClock t.clock (panSemTotalStoreByteClause t (.op .add [dV, iV]) (.const 0)).2)
      .local "i" (.op .add [iV, .const 1]) with h2 | h2 <;> rw [h2] <;> simp
  · rw [h]; simp

/-- **Pilot on a real guest loop** (memzero's tail loop, guest/src/lib/mem.pnk:166):
`while i <+ n { st8 dst + i, 0; i = i + 1 }` uses at most `n - i` source clock. -/
theorem tailLoop_cost (primitive : PanPrimitiveHandler (RiscV.Word 64)) (n0 : RiscV.Word 64) :
    ∀ s : PanSemState (RiscV.Word 64) (FfiState σ),
      (∃ i, s.locals "i" = some (.word i) ∧ s.locals "n" = some (.word n0)) →
      s.clock ≤ (panSemTotalEvaluate primitive tailLoop s).2.clock +
        (match s.locals "i" with | some (.word i) => n0.toNat - i.toNat | _ => 0) * (0 + 1) := by
  intro s hs
  apply costLe_while primitive
    (fun s => ∃ i, s.locals "i" = some (.word i) ∧ s.locals "n" = some (.word n0))
    (fun s => match s.locals "i" with | some (.word i) => n0.toNat - i.toNat | _ => 0)
    tailCond tailBody 0 _ _ _ s hs
  · intro s v ⟨i, hi, hn⟩ hv hv0
    have : evalPanSemStateExp s tailCond = some (.word (if i < n0 then 1 else 0)) := by
      simp [evalPanSemStateExp, tailCond, iV, nV, evalPanValueExp, hi, hn,
        panSemBitVec64MemoryAccess_compare, Compiler.Encoders.Asm.wordCmpHOL]
    rw [this] at hv
    simp only [Option.some.injEq, PanValue.word.injEq] at hv
    split at hv
    · rename_i hlt
      simp only [hi]
      have := BitVec.lt_def.mp hlt
      omega
    · subst hv; exact absurd rfl hv0
  · intro s v _ _ _ _
    rw [clockFree_clock primitive tailBody _ rfl]
    simp
  · intro s v ⟨i, hi, hn⟩ hv hv0 hc hres
    have hcond : evalPanSemStateExp s tailCond = some (.word (if i < n0 then 1 else 0)) := by
      simp [evalPanSemStateExp, tailCond, iV, nV, evalPanValueExp, hi, hn,
        panSemBitVec64MemoryAccess_compare, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcond] at hv
    simp only [Option.some.injEq, PanValue.word.injEq] at hv
    have hlt : i < n0 := by
      split at hv
      · assumption
      · subst hv; exact absurd rfl hv0
    have hnone : (panSemTotalEvaluate primitive tailBody { s with clock := s.clock - 1 }).1 = none := by
      rcases hres with h | h
      · exact h
      · exact absurd h (tailBody_not_continue primitive _)
    have hloc := tailBody_step primitive { s with clock := s.clock - 1 } i hi hnone
    have hl : ∀ x, (panSemFixClock (s.clock - 1)
        (panSemTotalEvaluate primitive tailBody { s with clock := s.clock - 1 }).2).locals x =
        updatePanValueMap s.locals "i" (.word (i + 1)) x := by
      intro x; simp only [panSemFixClock]; rw [hloc]
    have hlt' := BitVec.lt_def.mp hlt
    have hsucc : (i + 1).toNat = i.toNat + 1 := by
      rw [BitVec.toNat_add]; simp; omega
    refine ⟨⟨i + 1, ?_, ?_⟩, ?_⟩
    · rw [hl]; simp [updatePanValueMap]
    · rw [hl]; simp [updatePanValueMap, hn]
    · simp only [hl, hi, updatePanValueMap]
      simp
      omega

end Flapjack.L3.Pilot

/-! ## Transfer a production-evaluator clock-cost bound to the contract's exact evaluator
`evaluateHOLFiniteState`, through `panSemTotalEvaluate_agree` (clock-exact relation). -/

namespace Flapjack.L3
open Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem relExec_clock {σ : Type} {production : PanSemState (RiscV.Word 64) (FfiState σ)}
    {exact : PanSemStateExact 64 σ} (h : PanSemStateRelExec production exact) :
    exact.clock = production.clock := h.2.2.2.2.2.2.2.2.1

theorem exact_cost_of_production {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (hprimBridge : ∀ (operator : PrimOp) (values : List (PanValue (RiscV.Word 64))),
      Option.map panValueToHOL (primitive operator values)
        = panPrimopHOLExact operator (values.map panValueToHOL))
    (hprimRanged : PanPrimitiveHandlerByteRanged primitive)
    (p : ProgHOL 64) (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (exact : PanSemStateFiniteExact 64 σ)
    (hrel : PanSemStateRelExec production exact.toExact)
    (hranged : PanSemStateRelExecRanged production)
    (hcode : PanSemCodeRanged production)
    (hexn : PanSemExceptionShapesRanged production) (n : Nat)
    (hcost : production.clock ≤ (panSemTotalEvaluate primitive (progOfHOL p) production).2.clock + n) :
    exact.clock ≤ (evaluateHOLFiniteState exact p).2.clock + n := by
  have ag := panSemTotalEvaluate_agree primitive hprimBridge hprimRanged p production exact
    hrel hranged hcode hexn
  have h1 := relExec_clock hrel
  have h2 := relExec_clock ag.2
  simp only at h1 h2
  omega

end Flapjack.L3
