import Flapjack.RiscV.CorrectnessEncoding.Length
import Flapjack.RiscV.CorrectnessEncoding.TargetOk

/-! Word count of an encoded ASM instruction (EVM.fast K certificate, route 1). -/
namespace Flapjack.RiscV.TargetProof.Bounded
open Flapjack Compiler.Encoders.Asm Compiler.Encoders.RiscV.Target

theorem words_eq (i : HolAsm 64) :
    (riscvTarget.config.encode i).length / 4 = (riscvAst i).length := by
  change (riscvEnc i).length / 4 = _
  rw [Flapjack.RiscV.TargetProof.riscvEnc_length_eq]
  omega

end Flapjack.RiscV.TargetProof.Bounded
