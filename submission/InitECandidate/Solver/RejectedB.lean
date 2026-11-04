import Flapjack.HolRef
import InitECandidate.Solver.SkipBounded
import Flapjack.Compiler.Encoders.RiscV.Target.AsmOkRewrites
import InitECandidate.Solver.Common
import InitECandidate.Solver.Words
import InitECandidate.Solver.Ranges
/-! Integer LongDiv encoder-correctness case for the reduced branch. The original
RISC-V configuration rejects LongDiv in asm_ok; the original FP rejected case is
absent because riscv-mi removes the `FP` instruction constructor. The
contradiction is derived from the actual source asmStep seventh conjunct; it is
not a new rejection premise. The full existential/interference/assertion
conclusion is retained exactly. The proof does not execute an instruction.
Whole encoder/compiler correctness remains separate assembling work. -/
namespace Flapjack.RiscV.TargetProof.Bounded
set_option linter.unusedSimpArgs false
open Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target
/-- Original LongDiv637-642: all five registers remain arbitrary; the actual
source step is impossible under the reviewed RISC-V ISA configuration. -/
theorem riscv_encoder_correct_longdiv_bounded (r1 r2 r3 r4 r5 : Nat) (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.inst (.arith (.longDiv r1 r2 r3 r4 r5))) s2 ∧ targetStateRel riscvTarget s1 ms) :
    ∃ n : Nat, n + 1 ≤ (riscvTarget.config.encode (.inst (.arith (.longDiv r1 r2 r3 r4 r5)))).length / 4 ∧
      ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (riscvTarget.proj s1.memDomain) →
      let pcs := allPcs (riscvTarget.config.encode (.inst (.arith (.longDiv r1 r2 r3 r4 r5)))).length s1.pc
      asserts n (fun k s => env (n-k) (riscvTarget.next s)) ms
        (fun ms' => riscvTarget.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
          riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
        (fun ms' => targetStateRel riscvTarget s2 ms') ∧
      asserts2 (n+1) (fun k => env (n+1-k)) riscvTarget.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x) := by
  have good := h.1.2.2.2.2.2.2
  simp [riscvTarget,riscvConfig,asmOkExact,asmInstOkExact,asmArithOkExact] at good

end Flapjack.RiscV.TargetProof.Bounded
