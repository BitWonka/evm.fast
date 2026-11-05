import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.Common
import InitECandidate.Solver.EncoderDef

/-! Step-bounded `compile_correct` statement for LabToTarget (EVM.fast K certificate).
Every lab line occupies at most `4 * W` bytes of target code; then a lab run with clock `c` is matched
by a target run within `W * c` evaluator steps. -/
namespace Flapjack.Compiler.Backend.LabToTarget.Bounded
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Backend.LabToTarget

/-- Every target line is at most `4 * W` bytes. -/
def LinesWithin {width : Nat} [NeZero width] (W : Nat) (code2 : LabProgHOL width) : Prop :=
  ∀ pc, posVal (pc + 1) 0 code2 ≤ posVal pc 0 code2 + 4 * W

def CompileCorrectForB {width : Nat} [NeZero width] (W : Nat) (S Q : Type) {F : Type}
    (s1 : LabSem.State width Config F) : Prop :=
  ∀ (res : MachineResult) (mc : MachineConfig width S Q) (s2 : LabSem.State width Config F)
    (code2 : LabProgHOL width) (labs : Spt (Spt Nat)) (t1 : AsmState width) (ms1 : S)
    (p : BitVec width),
    oracleTie mc ms1 s1 ∧ evaluate s1 = (res, s2) ∧ res ≠ .error ∧
      encoderCorrectBounded mc.target ∧ stateRel (mc, code2, labs, p) s1 t1 ms1 ∧
      LinesWithin W code2 →
    ∃ k ms2, s1.clock + k ≤ (W + 1) * s1.clock ∧
      evaluateTargetHOL mc s1.ffi (s1.clock + k) ms1 = (res, ms2, s2.ffi)

theorem compileCorrect_stepB {width : Nat} [NeZero width] {S Q F : Type} {W : Nat}
    {mc : MachineConfig width S Q} {code2 : LabProgHOL width} {labs : Spt (Spt Nat)}
    {p : BitVec width} {s1 s1' s2 : LabSem.State width Config F} {t1' : AsmState width}
    {ms1 ms2 : S} {res : MachineResult} {l : Nat}
    (ht : oracleTie mc ms1 s1) (hec : encoderCorrectBounded mc.target) (hclock : s1.clock ≠ 0)
    (hlines : LinesWithin W code2) (hlW : l ≤ W)
    (hl : ∀ k, evaluateTargetHOL mc s1.ffi (k + l) ms1 =
        evaluateTargetHOL (shiftInterfer l mc) s1.ffi k ms2 ∧
      findNextInterference mc s1.ffi (k + l) ms1 =
        findNextInterference (shiftInterfer l mc) s1.ffi k ms2)
    (hl0 : l ≠ 0)
    (hs' : s1'.clock = s1.clock - 1 ∧ s1'.ffi = s1.ffi ∧ s1'.ioRegs = s1.ioRegs ∧
      s1'.ioFpRegs = s1.ioFpRegs ∧ s1'.ccRegs = s1.ccRegs ∧ s1'.ccFpRegs = s1.ccFpRegs)
    (hrel' : stateRel (shiftInterfer l mc, code2, labs, p) s1' t1' ms2)
    (hev : evaluate s1' = (res, s2)) (hres : res ≠ .error)
    (ih : CompileCorrectForB W S Q s1') :
    ∃ k ms3, s1.clock + k ≤ (W + 1) * s1.clock ∧
      evaluateTargetHOL mc s1.ffi (s1.clock + k) ms1 = (res, ms3, s2.ffi) := by
  obtain ⟨hc, hffi, hio, hiofp, hcc, hccfp⟩ := hs'
  have ht' : oracleTie (shiftInterfer l mc) ms2 s1' :=
    oracleTie_step mc ms1 ms2 s1 s1' l ⟨ht, fun k => (hl k).2, hio, hiofp, hcc, hccfp, hffi⟩
  obtain ⟨k', ms3, hk'le, hk⟩ := ih res (shiftInterfer l mc) s2 code2 labs t1' ms2 p
    ⟨ht', hev, hres, hec, hrel', hlines⟩
  refine ⟨k' + l - 1, ms3, ?_, ?_⟩
  · have hmul : (W + 1) * s1'.clock + (W + 1) = (W + 1) * s1.clock := by
      rw [hc, ← Nat.mul_succ]; congr 1; omega
    omega
  · rw [show s1.clock + (k' + l - 1) = (s1'.clock + k') + l by omega, (hl _).1, ← hffi]
    exact hk

end Flapjack.Compiler.Backend.LabToTarget.Bounded
