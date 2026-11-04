import Flapjack.RiscV.CorrectnessEncoding.Length
import Flapjack.RiscV.CorrectnessEncoding.TargetOk

/-! Shared length facts for the step-bounded RISC-V encoder cases (EVM.fast K certificate, route 1). -/
namespace Flapjack.RiscV.TargetProof.Bounded
open Flapjack Compiler.Encoders.Asm Compiler.Encoders.RiscV.Target

/-- Every encoded ASM instruction has at least one 4-byte word. -/
theorem one_le_words (i : HolAsm 64) : 0 + 1 ≤ (riscvTarget.config.encode i).length / 4 := by
  change 0 + 1 ≤ (riscvEnc i).length / 4
  have h := (Flapjack.RiscV.TargetProof.riscv_encoding i)
  have hpos : 0 < (riscvEnc i).length := List.length_pos_iff.mpr h.2
  omega

end Flapjack.RiscV.TargetProof.Bounded
