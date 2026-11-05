import InitECandidate.Proofs.BootstrapCodeFacts
import InitECandidate.Solver.BootstrapCountB

/-! Literal step budget of the submitted bootstrap list (EVM.fast K certificate, route 1). -/
namespace InitECandidate.Proofs.Bounded
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Proofs.BootstrapCopy InitECandidate.Proofs.BootstrapStraightLine InitE

theorem words_append (a b : List (HolAsm 64)) : words (a ++ b) = words a + words b := by
  simp [words]

theorem words_loopProgram (n : Nat) : words (loopProgram n) = n * words loopBody := by
  induction n with
  | zero => simp [loopProgram, words]
  | succ n ih =>
    have : loopProgram (n + 1) = loopBody ++ loopProgram n := by
      simp [loopProgram, List.replicate_succ]
    rw [this, words_append, ih, Nat.succ_mul, Nat.add_comm]

theorem words_loopBody : words loopBody = 5 := by decide
theorem words_prefixCode : words prefixCode = 6 := by decide
theorem words_tailCode : words tailCode = 41 := by decide

/-- The submitted bootstrap list (`BootstrapTrace.fullBootstrapCode`) executes at most 23,077 machine steps. -/
theorem words_bootstrap : words (prefixCode ++ (loopProgram 4606 ++ tailCode)) = 23077 := by
  rw [words_append, words_append, words_loopProgram, words_loopBody, words_prefixCode, words_tailCode]

end InitECandidate.Proofs.Bounded
