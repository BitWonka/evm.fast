import Flapjack.Compiler.Backend.LabToTarget.Initialization.InitialStateContracts
import Flapjack.Compiler.Backend.LabToTarget.PositionOrder
import InitECandidate.Solver.L2T.SemanticsB

/-!
Draft, not Lean-checked. It keeps the same bounded Lab-to-target theorem and
replaces the unnecessarily universal line-size premise by an existential
initializer witness that includes its own line bound. No baseline initialization,
line bound, source execution bound, or finite certificate is proved here.
-/

namespace Flapjack.Compiler.Backend.LabToTarget.Bounded

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabToTarget

/-- A whole-program byte bound gives a conservative bound for every line.
This draft uses the upstream monotonicity and end-position theorems; it still
needs Lean checking and the actual baseline byte-length premise. -/
theorem linesWithin_of_total_bytes {width : Nat} [NeZero width]
    (cfg : AsmConfigExact width) (labs : Spt (Spt Nat))
    (ffis : List HolFfiName) (validPos : Nat) (code : LabProgHOL width) (W : Nat)
    (hAll : allEncOk cfg labs ffis validPos code) (hEnc : encOk cfg)
    (hSize : (progToBytes code).length ≤ 4 * W) : LinesWithin W code := by
  intro pc
  have hend := posVal_numPcs cfg labs ffis validPos code 0 hAll
  by_cases hlt : pc + 1 < numPcs code
  · have hmono := posVal_mono (pc + 1) 0 code (numPcs code) validPos cfg labs ffis
      ⟨hlt, le_refl _, hAll, hEnc⟩
    omega
  · have hlim : numPcs code ≤ pc + 1 := by omega
    have hsat := posVal_geNumPcs (pc + 1) 0 code hlim
    omega

/-- The original state relation already bounds the whole code below the
address space and records the encoding invariants. Any `W` whose fourfold
value covers that space gives a line bound, without an instruction scan.
Still uncompiled. -/
theorem linesWithin_of_stateRel {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (code : LabProgHOL width)
    (labs : Spt (Spt Nat)) (p : BitVec width) (s : LabSem.State width Config F)
    (t : AsmState width) (ms : S) (W : Nat) (hfit : 2 ^ width ≤ 4 * W)
    (hrel : stateRel (mc, code, labs, p) s t ms) : LinesWithin W code := by
  have henc : encOk mc.target.config := by
    dsimp only [stateRel] at hrel
    tauto
  have hall : allEncOk mc.target.config labs
      (mc.ffiNames.take (holThe (mmioPcsMinIndex mc.ffiNames))) 0 code := by
    dsimp only [stateRel] at hrel
    tauto
  have hsize : (progToBytes code).length + s.codeBuffer.buffer.length +
      s.codeBuffer.spaceLeft < 2 ^ width := by
    dsimp only [stateRel] at hrel
    tauto
  apply linesWithin_of_total_bytes mc.target.config labs
    (mc.ffiNames.take (holThe (mmioPcsMinIndex mc.ffiNames))) 0 code W hall henc
  omega

/-- For the challenge's 64-bit target, `4 * 2^62 = 2^64`. -/
theorem linesWithin_of_stateRel64 {S Q F : Type}
    (mc : MachineConfig 64 S Q) (code : LabProgHOL 64)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (s : LabSem.State 64 Config F)
    (t : AsmState 64) (ms : S)
    (hrel : stateRel (mc, code, labs, p) s t ms) : LinesWithin (2 ^ 62) code := by
  apply linesWithin_of_stateRel mc code labs p s t ms (2 ^ 62) _ hrel
  norm_num

theorem lab_halt_within_of_bounded_init {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (p : BitVec width) (ms : S)
    (s : LabSem.State width Config F) (W c : Nat) (o : HolOutcome)
    (s2 : LabSem.State width Config F)
    (henc : encoderCorrectBounded mc.target)
    (hinit : ∃ code2 labs t1, stateRel (mc, code2, labs, p) s t1 ms ∧
      oracleTie mc ms s ∧ LinesWithin W code2)
    (hni : NoInstall s.code)
    (hev : evaluate { s with clock := c } = (.halt o, s2)) :
    ∃ ms2, evaluateTargetHOL mc s.ffi ((W + 1) * c) ms = (.halt o, ms2, s2.ffi) := by
  obtain ⟨code2, labs, t1, hrel, htie, hlines⟩ := hinit
  obtain ⟨k, ms2, hk, hrun⟩ := compileCorrectFor_allB (S := S) (Q := Q) W { s with clock := c } hni
    (.halt o) mc s2 code2 labs t1 ms p
    ⟨oracleTie_clock mc ms s c htie, hev, by simp, henc,
      stateRelClock (mc, code2, labs, p) s t1 ms c hrel, hlines⟩
  refine ⟨ms2, ?_⟩
  have hmore := evaluateTargetAddClock mc s.ffi (c + k) ms ((W + 1) * c - (c + k)) _ _ _ hrun
    (by simp)
  simp only at hk
  rw [show c + k + ((W + 1) * c - (c + k)) = (W + 1) * c by omega] at hmore
  exact hmore

/-- Conditional on the existing bounded encoder and NoInstall results, use
the state relation's address-space bound as a universal Lab line bound. -/
theorem lab_halt_within_address_space {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (p : BitVec width) (ms : S)
    (s : LabSem.State width Config F) (c : Nat) (o : HolOutcome)
    (s2 : LabSem.State width Config F)
    (henc : encoderCorrectBounded mc.target) (hinit : initOk (mc, p) s ms)
    (hni : NoInstall s.code) (hev : evaluate { s with clock := c } = (.halt o, s2)) :
    ∃ ms2, evaluateTargetHOL mc s.ffi ((2 ^ width + 1) * c) ms = (.halt o, ms2, s2.ffi) := by
  apply lab_halt_within mc p ms s (2 ^ width) c o s2 henc hinit
  · intro code labs t hrel
    exact linesWithin_of_stateRel mc code labs p s t ms (2 ^ width) (by omega) hrel
  · exact hni
  · exact hev

/-- Specialized 64-bit version with a four-times-smaller conservative factor. -/
theorem lab_halt_within_address_space64 {S Q F : Type}
    (mc : MachineConfig 64 S Q) (p : BitVec 64) (ms : S)
    (s : LabSem.State 64 Config F) (c : Nat) (o : HolOutcome)
    (s2 : LabSem.State 64 Config F)
    (henc : encoderCorrectBounded mc.target) (hinit : initOk (mc, p) s ms)
    (hni : NoInstall s.code) (hev : evaluate { s with clock := c } = (.halt o, s2)) :
    ∃ ms2, evaluateTargetHOL mc s.ffi ((2 ^ 62 + 1) * c) ms = (.halt o, ms2, s2.ffi) := by
  apply lab_halt_within mc p ms s (2 ^ 62) c o s2 henc hinit
  · intro code labs t hrel
    exact linesWithin_of_stateRel64 mc code labs p s t ms hrel
  · exact hni
  · exact hev

end Flapjack.Compiler.Backend.LabToTarget.Bounded
