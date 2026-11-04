import Flapjack.Compiler.Encoders.RiscV.Target

/-! Signed-range guards of the RISC-V lowering as integer comparisons (EVM.fast K, route 1). -/
namespace Flapjack.RiscV.TargetProof.Bounded
open Flapjack Compiler.Encoders.RiscV.Target

theorem inSignedRange_eq (lo hi a : BitVec 64) :
    inSignedRange lo hi a = decide (lo.toInt ≤ a.toInt ∧ a.toInt ≤ hi.toInt) := by
  simp [inSignedRange, BitVec.sle_eq_decide, Bool.decide_and]

theorem toInt_jlo : (18446744073708503040#64).toInt = -1048576 := by decide
theorem toInt_jhi : (1048575#64).toInt = 1048575 := by decide
theorem toInt_clo : (18446744073709547524#64).toInt = -4092 := by decide
theorem toInt_clo' : (-4092 : BitVec 64).toInt = -4092 := by decide
theorem toInt_chi : (4095#64).toInt = 4095 := by decide
theorem toInt_jlo' : (-1048576 : BitVec 64).toInt = -1048576 := by decide

theorem toInt_jhi' : (1048575 : BitVec 64).toInt = 1048575 := by decide
theorem toInt_chi' : (4095 : BitVec 64).toInt = 4095 := by decide

end Flapjack.RiscV.TargetProof.Bounded
