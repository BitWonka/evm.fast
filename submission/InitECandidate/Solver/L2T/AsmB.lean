import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.Step
import InitECandidate.Solver.L2T.StepB
import Flapjack.Compiler.Backend.LabToTarget.InstLemma
import Flapjack.Compiler.Backend.LabToTarget.AlignedPosVal
import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.Asm
import InitECandidate.Solver.L2T.StepB

/-! `Asm` cases of the original `compile_correct`
(lab_to_targetProofScript.sml:7560-7717): `Asmi (Inst i)` and
`Asmi (JumpReg r)`. Hypotheses are the source theorem's together with exactly
the `evaluate_ind` induction hypothesis of the instruction's recursive call. -/
namespace Flapjack.Compiler.Backend.LabToTarget.Bounded
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Encoders Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.AsmSem Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileCorrect_asmInstB {width : Nat} [NeZero width] {S Q F : Type} {W : Nat}
    (s1 : Flapjack.Compiler.Backend.LabSem.State width Config F) (i : HolInst width) (bytes : List (BitVec 8)) (n : Nat)
    (hclock : s1.clock ≠ 0) (hfetch : asmFetch s1 = some (.asm (.asmi (.inst i)) bytes n))
    (ih : ¬ (asmInst i s1).failed → CompileCorrectForB W S Q (incPc (decClock (asmInst i s1)))) :
    CompileCorrectForB W S Q s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨ht, hev, hres, hecB, hrel, hlines⟩
  have hec := encoderCorrect_of_bounded hecB
  rw [evaluate] at hev
  simp only [hclock, ↓reduceIte, hfetch] at hev
  by_cases hf : (asmInst i s1).failed = true
  · simp only [hf, ↓reduceIte, Prod.mk.injEq] at hev; exact absurd hev.1.symm hres
  · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hev
    obtain ⟨bytes', len', hok, hmem, hpos, hdis⟩ :=
      fetchedAsmLine hrel hfetch (by intro op re a h; cases h)
    simp only [lineOk, cbwToAsmHOL] at hok
    obtain ⟨htf, hout, hpost⟩ := instLemma i s1 mc code2 labs p t1 ms1 bytes' ms1
      ⟨hf, hrel, hpos⟩
    obtain ⟨l, ms2, hlb, hl⟩ := stepNopOfLineB s1.ffi hrel hecB (.inst i) bytes' hmem hok.1 hok.2.2 hdis
      (by simpa [asmUpd, AsmSem.updPc] using htf)
      (fun a ha => by simpa [asmUpd, AsmSem.updPc] using hout a ha) (by intro x h; cases h)
    have hrel1 := (instLemma i s1 mc code2 labs p t1 ms1 bytes' ms2 ⟨hf, hrel, hpos⟩).2.2
      (hl 0).2.2.1
    have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l hrel1
    obtain ⟨hpc, hcode, hcl, hffi, hio, hiofp, hcc, hccfp, -⟩ := asmInstConsts i s1
    exact compileCorrect_stepB (s1' := incPc (decClock (asmInst i s1))) ht hecB hclock hlines (by have := hlines s1.pc; omega)
      (fun k => ⟨(hl k).1, (hl k).2.1⟩) (hl 0).2.2.2
      ⟨by simp [incPc, decClock, hcl], hffi, hio, hiofp, hcc, hccfp⟩ hrel' hev hres (ih hf)

/-- Aligned words sum to an aligned word; Flapjack infrastructure for HOL's
`aligned_add_sub_cor`. -/
theorem holAligned_add {width : Nat} [NeZero width] (a : Nat) (x y : BitVec width)
    (hx : holAligned a x = true) (hy : holAligned a y = true) : holAligned a (x + y) = true := by
  rw [holAligned_iff] at hx hy ⊢
  rw [BitVec.toNat_add]
  rcases Nat.le_total a width with h | h
  · rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h), Nat.add_mod, hx, hy]; simp
  · have hx0 : x.toNat = 0 := by
      have := x.isLt
      have : x.toNat < 2 ^ a := lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) h)
      rw [Nat.mod_eq_of_lt this] at hx; exact hx
    have hy0 : y.toNat = 0 := by
      have := y.isLt
      have : y.toNat < 2 ^ a := lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) h)
      rw [Nat.mod_eq_of_lt this] at hy; exact hy
    simp [hx0, hy0]

/-- The `state_rel` mask form of code-base alignment; Flapjack infrastructure
for HOL's `aligned_bitwise_and`. -/
theorem holAligned_of_and_mask {width : Nat} [NeZero width] (a : Nat) (p : BitVec width)
    (h : (p &&& BitVec.ofNat width (2 ^ a - 1)) = 0) : holAligned a p = true := by
  rw [holAligned_iff]
  have h' := congrArg BitVec.toNat h
  rw [BitVec.toNat_and, BitVec.toNat_ofNat] at h'
  have h0 : (0 : BitVec width).toNat = 0 := by simp
  rw [h0] at h'
  rcases Nat.le_total a width with ha | ha
  · rw [Nat.mod_eq_of_lt (lt_of_lt_of_le (Nat.sub_lt (Nat.two_pow_pos a) (by decide))
      (Nat.pow_le_pow_right (by decide) ha)), Nat.and_two_pow_sub_one_eq_mod] at h'
    exact h'
  · have hm : (2 ^ a - 1) % 2 ^ width = 2 ^ width - 1 := by
      obtain ⟨c, hc⟩ : 2 ^ width ∣ 2 ^ a := Nat.pow_dvd_pow 2 ha
      have hpos : 0 < c := by
        rcases Nat.eq_zero_or_pos c with h0 | h0
        · rw [h0, Nat.mul_zero] at hc; exact absurd hc (Nat.two_pow_pos a).ne'
        · exact h0
      rw [hc]
      have hw := Nat.two_pow_pos width
      rw [show 2 ^ width * c - 1 = 2 ^ width * (c - 1) + (2 ^ width - 1) by
        have hle := Nat.le_mul_of_pos_right (2 ^ width) hpos
        rw [Nat.mul_sub_one]; omega]
      rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (by omega)
    rw [hm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt p.isLt] at h'
    simp [h']

/-- Every code position relative to the code base is an aligned jump
target; Flapjack infrastructure for the `JumpReg` alignment obligation. -/
theorem stateRel_aligned_target {width : Nat} [NeZero width] {S Q F : Type}
    {mc : MachineConfig width S Q} {code2 : LabProgHOL width} {labs : Spt (Spt Nat)}
    {p : BitVec width} {s1 : LabSem.State width Config F} {t1 : AsmState width} {ms1 : S}
    (hrel : stateRel (mc, code2, labs, p) s1 t1 ms1) (hec : encoderCorrect mc.target)
    (pc : Nat) :
    holAligned mc.target.config.codeAlignment (p + BitVec.ofNat width (posVal pc 0 code2)) =
      true := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, c42, -, -, c45, -, c47, -⟩ := hrel
  rw [c45] at c42
  refine holAligned_add _ _ _ (holAligned_of_and_mask _ _ c42) ?_
  exact allEncOk_aligned_posVal mc labs code2 pc _ ⟨c47, fun ho =>
    hasOddInst_alignment _ labs _ 0 code2 ⟨hec.1.1, c47, ho⟩, hec⟩

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileCorrect_jumpRegB {width : Nat} [NeZero width] {S Q F : Type} {W : Nat}
    (s1 : Flapjack.Compiler.Backend.LabSem.State width Config F) (r : Nat) (bytes : List (BitVec 8)) (n : Nat)
    (hclock : s1.clock ≠ 0) (hfetch : asmFetch s1 = some (.asm (.asmi (.jumpReg r)) bytes n))
    (ih : ∀ n1 n2 pc, s1.regs r = .loc n1 n2 → locToPc n1 n2 s1.code = some pc →
      CompileCorrectForB W S Q (updPc pc (decClock s1))) :
    CompileCorrectForB W S Q s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨ht, hev, hres, hecB, hrel, hlines⟩
  have hec := encoderCorrect_of_bounded hecB
  rw [evaluate] at hev
  simp only [hclock, ↓reduceIte, hfetch] at hev
  cases hr : s1.regs r with
  | word _ => simp only [hr, Prod.mk.injEq] at hev; exact absurd hev.1.symm hres
  | loc n1 n2 =>
    simp only [hr] at hev
    cases hpc : locToPc n1 n2 s1.code with
    | none => simp only [hpc, Prod.mk.injEq] at hev; exact absurd hev.1.symm hres
    | some pc =>
      simp only [hpc] at hev
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
        c28, c29, c30, c31, -, -, -, -, -, -, -, ht1f, -, -, -, -, -, c45, -⟩ := id hrel
      have hreg : t1.regs r = p + BitVec.ofNat width (posVal pc 0 code2) := by
        have := c30 r
        rw [hr] at this
        simp only [wordLocVal, c28 n1 n2 pc hpc, Option.some.injEq] at this
        exact this.symm
      obtain ⟨bytes', len', hok, hmem, hpos, hdis⟩ :=
        fetchedAsmLine hrel hfetch (by intro op re a h; cases h)
      simp only [lineOk, cbwToAsmHOL] at hok
      have hal := stateRel_aligned_target hrel hec pc
      obtain ⟨l, ms2, hlb, hl⟩ := stepOfLineB s1.ffi hrel hecB _ bytes' hmem hok.1 hok.2.2 hdis
        (by simp [asmUpd, AsmSem.updPc, AsmSem.assertState, AsmSem.readReg, hreg, c45, hal, ht1f])
      have htrel := (hl 0).2.2.1
      simp only [asmUpd, AsmSem.updPc, AsmSem.assertState, AsmSem.readReg, hreg, c45, hal,
        Bool.not_true, Bool.false_or, ht1f] at htrel
      have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l
        (stateRel_frame hrel s1.regs s1.fpRegs s1.memory pc (s1.clock - 1) t1.regs t1.fpRegs
          t1.mem _ htrel c30 c29 (fun x hx => (c31 x hx).2.2) (fun _ _ => rfl) rfl)
      exact compileCorrect_stepB (s1' := LabSem.updPc pc (decClock s1)) ht hecB hclock hlines (by have := hlines s1.pc; omega)
        (fun k => ⟨(hl k).1, (hl k).2.1⟩) (hl 0).2.2.2
        ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ hrel' hev hres (ih n1 n2 pc hr hpc)

end Flapjack.Compiler.Backend.LabToTarget.Bounded
