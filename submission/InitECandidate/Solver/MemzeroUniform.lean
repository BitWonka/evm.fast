import InitECandidate.Solver.MemzeroAst
import Lean.Elab.Tactic.Omega

/-!
Unelaborated draft: the already-built conditional memzero tail-loop cost can be
made uniform for a 64-bit length. This concerns only that loop's source-clock
consumption under its stated local-state and AST extraction premises; it is
not a whole memzero, whole-guest, target, or benchmark certificate.
-/
namespace InitECandidate.Solver.MemzeroUniform
open Flapjack
open Flapjack.Pancake.PanLang

/-- Proposed uniform source-clock bound for the extracted memzero tail loop. -/
theorem extractedTail_uniform_cost {σ : Type}
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) (n0 : RiscV.Word 64)
    (p : Prog (RiscV.Word 64)) (hp : InitECandidate.Solver.MemzeroAst.extractedTail = some p)
    (s : PanSemState (RiscV.Word 64) (FfiState σ))
    (hs : ∃ i, s.locals "i" = some (.word i) ∧ s.locals "n" = some (.word n0)) :
    s.clock ≤ (panSemTotalEvaluate primitive p s).2.clock + 18446744073709551615 := by
  obtain ⟨i, hi, hn⟩ := hs
  have h := InitECandidate.Solver.MemzeroAst.extractedTail_cost primitive n0 p hp s ⟨i, hi, hn⟩
  simp only [hi, Nat.zero_add, Nat.mul_one] at h
  have hn64 : n0.toNat < 18446744073709551616 := by
    simpa using n0.isLt
  omega

/-- Arithmetic only: a chunk increment cannot wrap and decreases the natural
variant if a stronger caller-supplied length bound and guard both hold. -/
theorem chunk_step_no_wrap_and_decreases
    (modulus i n step : Nat) (hstep : 0 < step)
    (hwidth : n + step < modulus) (hi : i ≤ n) (hguard : i + step ≤ n) :
    (i + step) % modulus = i + step ∧ n - (i + step) < n - i := by
  have hnowrap : i + step < modulus := by omega
  constructor
  · exact Nat.mod_eq_of_lt hnowrap
  · omega

end InitECandidate.Solver.MemzeroUniform
