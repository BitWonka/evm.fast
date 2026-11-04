import InitECandidate.Solver.BinopImmediateBounded
import InitECandidate.Solver.Common
import InitECandidate.Solver.Words
import InitECandidate.Solver.Ranges

namespace Flapjack.RiscV.TargetProof.Bounded
set_option linter.unusedSimpArgs false
open Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target
set_option autoImplicit false

/-- Full original Binop constructor at source550-559, assembled along HOL's
RegImm case split. All five operators and both original operand forms retain
only the original asmStep/initial relation premise and complete existential,
interference and assertion conclusion. The reviewed cases derive actual native
Next from emitted bytes; no target run or range fact is an added premise.
Inherited reals_as_rational_cuts assumption of the full native target/Run
closure is retained (SOUNDNESS item8). `CorrectnessEncoding.Complete`
assembles the full encoder correctness theorem. -/
theorem riscv_encoder_correct_binop_bounded (op : HolBinop) (rd rs1 : Nat) (right : HolRegImm 64) (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.inst (.arith (.binop op rd rs1 right))) s2 ∧
      targetStateRel riscvTarget s1 ms) :
    ∃ n : Nat, n + 1 ≤ (riscvTarget.config.encode (.inst (.arith (.binop op rd rs1 right)))).length / 4 ∧
      ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (riscvTarget.proj s1.memDomain) →
      let pcs := allPcs (riscvTarget.config.encode (.inst (.arith (.binop op rd rs1 right)))).length s1.pc
      asserts n (fun k s => env (n - k) (riscvTarget.next s)) ms
        (fun ms' => riscvTarget.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
          riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
        (fun ms' => targetStateRel riscvTarget s2 ms') ∧
      asserts2 (n + 1) (fun k => env (n + 1 - k)) riscvTarget.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x) := by
  cases right with
  | reg rs2 => exact riscv_encoder_correct_binopRegister_bounded op rd rs1 rs2 s1 s2 ms h
  | imm c => exact riscv_encoder_correct_binopImmediate_bounded op rd rs1 c s1 s2 ms h

end Flapjack.RiscV.TargetProof.Bounded
