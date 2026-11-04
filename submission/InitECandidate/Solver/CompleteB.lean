import Flapjack.RiscV.CorrectnessEncoding.TargetOk
import InitECandidate.Solver.SkipBounded
import InitECandidate.Solver.ConstAssertionsBounded
import InitECandidate.Solver.BinopB
import InitECandidate.Solver.ShiftB
import InitECandidate.Solver.DivBounded
import InitECandidate.Solver.LongMulB
import InitECandidate.Solver.RejectedB
import InitECandidate.Solver.AddCarryBounded
import InitECandidate.Solver.AddOverflowBounded
import InitECandidate.Solver.SubOverflowBounded
import InitECandidate.Solver.MemoryAssertionsBounded
import InitECandidate.Solver.JumpB
import InitECandidate.Solver.JumpCmpB
import InitECandidate.Solver.CallB
import InitECandidate.Solver.JumpRegBounded
import InitECandidate.Solver.LocB
import Flapjack.Compiler.Encoders.AsmProps.EncoderCorrect
import InitECandidate.Solver.EncoderDef

/-! Full native encoder correctness for the original complete assembler carrier.
All seventeen HOL constructor groups are assembled without extra hypotheses.
The native model retains the reviewed reals_as_rational_cuts assurance limit
(SOUNDNESS section 8); this theorem does not establish production compiler
routing or the whole Pancake-to-RISC-V correctness result. -/
namespace Flapjack.RiscV.TargetProof.Bounded
open Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 Compiler.Encoders.Asm Compiler.Encoders.AsmProps
  Compiler.Encoders.RiscV.Target
set_option autoImplicit false

/-- Original unconditional encoder_correct riscv_target, including target_ok,
every source instruction, every interference environment and both assertions.
The component proofs derive native fetch/decode/Run/Next from the actual emitted
bytes. Inherits reals_as_rational_cuts (SOUNDNESS section 8). -/
theorem riscv_encoder_correct_bounded : encoderCorrectBounded riscvTarget := by
  refine ⟨riscv_target_ok, ?_⟩
  intro s1 i s2 ms h
  cases i with
  | inst value =>
    cases value with
    | skip => exact riscv_encoder_correct_skip_bounded s1 s2 ms h
    | const r c => exact riscv_encoder_correct_const_bounded r c s1 s2 ms h
    | arith a =>
      cases a with
      | binop op r t right => exact riscv_encoder_correct_binop_bounded op r t right s1 s2 ms h
      | shift op r t right => exact riscv_encoder_correct_shift_bounded op r t right s1 s2 ms h
      | div r t u => exact riscv_encoder_correct_div_bounded r t u s1 s2 ms h
      | longMul r t u v => exact riscv_encoder_correct_longmul_bounded r t u v s1 s2 ms h
      | longDiv r t u v q => exact riscv_encoder_correct_longdiv_bounded r t u v q s1 s2 ms h
      | addCarry r t u v => exact riscv_encoder_correct_addcarry_bounded r t u v s1 s2 ms h
      | addOverflow r t u v => exact riscv_encoder_correct_addoverflow_bounded r t u v s1 s2 ms h
      | subOverflow r t u v => exact riscv_encoder_correct_suboverflow_bounded r t u v s1 s2 ms h
    | mem m r address =>
      cases address with
      | addr base w => exact riscv_encoder_correct_mem_bounded m r base w s1 s2 ms h
  | jump c => exact riscv_encoder_correct_jump_bounded c s1 s2 ms h
  | jumpCmp c r right a => exact riscv_encoder_correct_jumpCmp_bounded c r right a s1 s2 ms h
  | call c => exact riscv_encoder_correct_call_bounded c s1 s2 ms h
  | jumpReg r => exact riscv_encoder_correct_jumpReg_bounded r s1 s2 ms h
  | loc r c => exact riscv_encoder_correct_loc_bounded r c s1 s2 ms h

end Flapjack.RiscV.TargetProof.Bounded
