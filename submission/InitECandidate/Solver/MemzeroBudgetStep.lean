import InitECandidate.Solver.OrdinaryDomain

/-!
Unelaborated arithmetic draft: connect a 64-bit `i := i + 32` update to the
interval budget. No body execution, state invariant or loop result is proved.
-/
namespace InitECandidate.Solver.MemzeroBudgetStep
open Flapjack

/-- Proposed budget decrease for the actual modular word-address update,
conditional on the current first-store address lying in the source interval. -/
theorem wordSum_budget_decreases (dst index : BitVec 64)
    (hbase : InitE.sourceBase ≤ (dst + index).toNat)
    (hstop : (dst + index).toNat < InitE.heapEnd) :
    InitECandidate.Solver.OrdinaryDomain.rangeBudget32 InitE.sourceBase InitE.heapEnd
      (dst + (index + BitVec.ofNat 64 32)).toNat <
    InitECandidate.Solver.OrdinaryDomain.rangeBudget32 InitE.sourceBase InitE.heapEnd
      (dst + index).toNat := by
  have hspace : InitE.heapEnd + 31 < 2 ^ 64 := by decide
  obtain ⟨hnowrap, hdecrease⟩ :=
    InitECandidate.Solver.OrdinaryDomain.rangeBudget32_step InitE.sourceBase InitE.heapEnd
      (dst + index).toNat (2 ^ 64) hbase hstop hspace
  have haddr : (dst + (index + BitVec.ofNat 64 32)).toNat = (dst + index).toNat + 32 := by
    calc
      (dst + (index + BitVec.ofNat 64 32)).toNat =
          ((dst + index) + BitVec.ofNat 64 32).toNat := by rw [add_assoc]
      _ = ((dst + index).toNat + 32) % (2 ^ 64) := by
        simpa using (BitVec.toNat_add (dst + index) (BitVec.ofNat 64 32))
      _ = (dst + index).toNat + 32 := hnowrap
  rw [haddr]
  exact hdecrease

end InitECandidate.Solver.MemzeroBudgetStep
