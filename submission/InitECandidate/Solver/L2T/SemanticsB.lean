import Flapjack.Compiler.Backend.LabToTarget.MachineSemantics
import InitECandidate.Solver.L2T.AssemblyB

/-! Semantics-level corollary of the step-bounded LabToTarget simulation (EVM.fast K certificate):
a lab run that halts at clock `c` is matched by a target halt within `(W + 1) * c` evaluator steps. -/
namespace Flapjack.Compiler.Backend.LabToTarget.Bounded
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabToTarget

theorem lab_halt_within {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (p : BitVec width) (ms : S)
    (s : LabSem.State width Config F) (W c : Nat) (o : HolOutcome) (s2 : LabSem.State width Config F)
    (henc : encoderCorrectBounded mc.target)
    (hinit : initOk (mc, p) s ms)
    (hlines : ∀ code2 labs t1, stateRel (mc, code2, labs, p) s t1 ms → LinesWithin W code2)
    (hni : NoInstall s.code)
    (hev : evaluate { s with clock := c } = (.halt o, s2)) :
    ∃ ms2, evaluateTargetHOL mc s.ffi ((W + 1) * c) ms = (.halt o, ms2, s2.ffi) := by
  obtain ⟨code2, labs, t1, hrel, htie⟩ := hinit
  obtain ⟨k, ms2, hk, hrun⟩ := compileCorrectFor_allB (S := S) (Q := Q) W { s with clock := c } hni
    (.halt o) mc s2 code2 labs t1 ms p
    ⟨oracleTie_clock mc ms s c htie, hev, by simp, henc,
      stateRelClock (mc, code2, labs, p) s t1 ms c hrel, hlines code2 labs t1 hrel⟩
  refine ⟨ms2, ?_⟩
  have hmore := evaluateTargetAddClock mc s.ffi (c + k) ms ((W + 1) * c - (c + k)) _ _ _ hrun
    (by simp)
  simp only at hk
  rw [show c + k + ((W + 1) * c - (c + k)) = (W + 1) * c by omega] at hmore
  exact hmore

end Flapjack.Compiler.Backend.LabToTarget.Bounded
