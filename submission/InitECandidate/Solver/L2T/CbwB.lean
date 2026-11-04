import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.Step
import InitECandidate.Solver.L2T.StepB
import Flapjack.Compiler.Backend.LabToTarget.InstMem
import Flapjack.Compiler.Backend.LabToTarget.Memory
import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.Cbw
import InitECandidate.Solver.L2T.StepB

/-! `Asm (Cbw r1 r2)` case of the original `compile_correct`
(lab_to_targetProofScript.sml:7719-7827): the code-buffer write is simulated
by a byte store to the target address just past the buffer, which lies outside
the source memory domain. Hypotheses are the source theorem's together with
exactly the `evaluate_ind` induction hypothesis of the case. -/
namespace Flapjack.Compiler.Backend.LabToTarget.Bounded
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Encoders Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.AsmSem Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang

/-- Distinct in-range offsets give distinct addresses; Flapjack word
arithmetic infrastructure (HOL `word_add_n2w` with `n2w_11`). -/
theorem add_ofNat_ne {width : Nat} (a : BitVec width) (n m : Nat) (hn : n < 2 ^ width)
    (hm : m < 2 ^ width) (h : n ≠ m) : a + BitVec.ofNat width n ≠ a + BitVec.ofNat width m := by
  intro e
  have e' := congrArg BitVec.toNat ((BitVec.add_right_inj a).mp e)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] at e'
  exact h e'

/-- The complete relation after the code-buffer write: the source buffer
gains the byte `b` and the target stores `b` at the address just past the
buffer. This is the `state_rel` part of the original CBW case (the
`bytes_in_mem_UPDATE`, `bytes_in_mem_APPEND` and space-shift subgoals). -/
theorem stateRel_cbw {width : Nat} [NeZero width] {S Q F : Type}
    {mc : MachineConfig width S Q} {code2 : LabProgHOL width} {labs : Spt (Spt Nat)}
    {p : BitVec width} {s1 : LabSem.State width Config F} {t1 : AsmState width} {ms1 ms2 : S}
    (h : stateRel (mc, code2, labs, p) s1 t1 ms1) (b : BitVec 8)
    (hsp : 0 < s1.codeBuffer.spaceLeft) (tpc : BitVec width)
    (htrel : targetStateRel mc.target
      { t1 with
        mem := fun x => if x = s1.codeBuffer.position +
          BitVec.ofNat width s1.codeBuffer.buffer.length then b else t1.mem x
        pc := tpc } ms2)
    (hpc : tpc = p + BitVec.ofNat width (posVal (s1.pc + 1) 0 code2)) :
    stateRel (mc, code2, labs, p)
      (incPc (decClock { s1 with
        codeBuffer := ⟨s1.codeBuffer.position, s1.codeBuffer.buffer ++ [b],
          s1.codeBuffer.spaceLeft - 1⟩ }))
      { t1 with
        mem := fun x => if x = s1.codeBuffer.position +
          BitVec.ofNat width s1.codeBuffer.buffer.length then b else t1.mem x
        pc := tpc } ms2 := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18,
    c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36,
    c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53⟩ := h
  have hw0 := c32 0 hsp
  simp only [Nat.add_zero] at hw0
  have hupd := fun (a : BitVec width) (xs : List (BitVec 8))
      (hne : ∀ n, n < xs.length → a + BitVec.ofNat width n ≠
        s1.codeBuffer.position + BitVec.ofNat width s1.codeBuffer.buffer.length)
      (hb : bytesInMemHOL a xs t1.mem t1.memDomain (fun a => s1.memDomain a = true)) =>
    bytesInMem_update xs a t1.mem t1.memDomain (fun a => s1.memDomain a = true) _ b ⟨hne, hb⟩
  refine ⟨htrel, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18,
    c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, ?_, ?_, ?_, c34, ?_, ?_,
    ?_, c38, c39, c40, hpc, c42, c43, c44, c45, c46, c47, c48, c49,
    shareMemStateRel_of_ffi mc s1 _ t1 ms1 _ ms2 rfl c50, c51, c52, c53⟩
  all_goals simp only [incPc, decClock]
  · intro a ha
    obtain ⟨h1, h2, h3⟩ := c31 a ha
    have hne : a ≠ s1.codeBuffer.position + BitVec.ofNat width s1.codeBuffer.buffer.length :=
      fun e => hw0.2 (e ▸ h2)
    exact ⟨h1, h2, by simpa [hne] using h3⟩
  · intro n hn
    have := c32 (n + 1) (by omega)
    simp only [List.length_append, List.length_singleton]
    rw [show s1.codeBuffer.buffer.length + 1 + n = s1.codeBuffer.buffer.length + (n + 1) by
      omega]
    exact this
  · refine hupd p _ (fun n hn => ?_) c33
    rw [c34, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact add_ofNat_ne p _ _ (by omega) (by omega) (by omega)
  · rw [bytesInMem_append]
    refine ⟨hupd _ _ (fun n hn => add_ofNat_ne _ _ _ (by omega) (by omega) (by omega)) c35, ?_⟩
    exact ⟨hw0.1, hw0.2, by simp, trivial⟩
  · simp only [List.length_append, List.length_singleton]; omega
  · intro bn hbn
    exact c37 bn (by simp only [List.length_append, List.length_singleton] at hbn; omega)

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileCorrect_cbwB {width : Nat} [NeZero width] {S Q F : Type} {W : Nat}
    (s1 : Flapjack.Compiler.Backend.LabSem.State width Config F) (r1 r2 : Nat)
    (bytes : List (BitVec 8)) (n : Nat)
    (hclock : s1.clock ≠ 0) (hfetch : asmFetch s1 = some (.asm (.cbw r1 r2) bytes n))
    (ih : ∀ w1 w2 newCb, s1.regs r1 = .word w1 → s1.regs r2 = .word w2 →
      wordSemBufferWrite s1.codeBuffer w1 (w2.setWidth 8) = some newCb →
      CompileCorrectForB W S Q (incPc (decClock { s1 with codeBuffer := newCb }))) :
    CompileCorrectForB W S Q s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨ht, hev, hres, hecB, hrel, hlines⟩
  have hec := encoderCorrect_of_bounded hecB
  rw [evaluate] at hev
  simp only [hclock, ↓reduceIte, hfetch] at hev
  cases hr1 : s1.regs r1 with
  | loc _ _ => simp only [hr1] at hev; exact absurd (Prod.mk.inj hev).1.symm hres
  | word w1 =>
  cases hr2 : s1.regs r2 with
  | loc _ _ => simp only [hr1, hr2] at hev; exact absurd (Prod.mk.inj hev).1.symm hres
  | word w2 =>
  simp only [hr1, hr2] at hev
  cases hbw : wordSemBufferWrite s1.codeBuffer w1 (w2.setWidth 8) with
  | none => simp only [hbw] at hev; exact absurd (Prod.mk.inj hev).1.symm hres
  | some newCb =>
  simp only [hbw] at hev
  have hbw' := hbw
  simp only [wordSemBufferWrite] at hbw'
  split at hbw'
  case isFalse => cases hbw'
  case isTrue hcond =>
  cases hbw'
  obtain ⟨haddr, hsp⟩ := hcond
  have haddr' : w1 = s1.codeBuffer.position + BitVec.ofNat width s1.codeBuffer.buffer.length := by
    rw [← haddr]; simp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, c30, -, c32, -, c34, -, c36, -, -, ht1f, -, htpc, -, -, -, -, -, c47, -⟩ := id hrel
  have htr1 : t1.regs r1 = w1 := by
    have := c30 r1; rw [hr1] at this; simpa [wordLocVal] using this.symm
  have htr2 : t1.regs r2 = w2 := by
    have := c30 r2; rw [hr2] at this; simpa [wordLocVal] using this.symm
  have hw0 := c32 0 hsp
  simp only [Nat.add_zero] at hw0
  obtain ⟨bytes', len', hok, hmem, hpos, hdis⟩ :=
    fetchedAsmLine hrel hfetch (by intro op re a h; cases h)
  simp only [lineOk, cbwToAsmHOL] at hok
  have hA : AsmSem.addrHOL (.addr r1 0#width) t1 = w1 := by
    simp [AsmSem.addrHOL, AsmSem.readReg, htr1]
  have hdom : t1.memDomain w1 := haddr' ▸ hw0.1
  have hupd : AsmSem.instUpd (.mem .store8 r2 (.addr r1 0#width)) t1 =
      { t1 with mem := fun x => if x = w1 then w2.setWidth 8 else t1.mem x } := by
    simp only [AsmSem.instUpd, AsmSem.memOp, asm_memStore_eq, hA,
      holLOG2_one, holAligned_zero, Nat.sub_self, BitVec.add_zero, ite_self, rmwOk,
      hdom, decide_true, Bool.and_true, wmwMem, AsmSem.readReg, htr2]
    simp [AsmSem.assertState, ht1f]
  have hupd' : AsmSem.instUpd (.mem .store8 r2 (.addr r1 (0 : BitVec width))) t1 =
      { t1 with mem := fun x => if x = w1 then w2.setWidth 8 else t1.mem x } := hupd
  -- the line itself is below the code-buffer address
  have hbound := posVal_bound (s1.pc + 1) 0 code2 _ labs _ 0 c47
  rw [hpos] at hbound
  have hb2 : bytesInMemHOL (p + BitVec.ofNat width (posVal s1.pc 0 code2)) bytes'
      (fun x => if x = w1 then w2.setWidth 8 else t1.mem x) t1.memDomain
      (fun a => s1.memDomain a = true) := by
    refine bytesInMem_update _ _ _ _ _ _ _ ⟨fun k hk => ?_, hmem⟩
    rw [haddr', c34, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    exact add_ofNat_ne p _ _ (by omega) (by omega) (by omega)
  obtain ⟨l, ms2, hlb, hl⟩ := stepNopOfLineMemB s1.ffi hrel hecB _ bytes' hmem hok.1 hok.2.2 hdis
    (by simp [asmUpd, AsmSem.updPc, hupd, ht1f])
    (by
      simp only [asmUpd, AsmSem.updPc, hupd']
      rw [htpc]; exact bytesInMem_impliesMemory _ _ _ _ _ hb2)
    (by intro x h; cases h)
  have htrel := (hl 0).2.2.1
  simp only [asmUpd, AsmSem.updPc, hupd', haddr'] at htrel
  have hrel1 := stateRel_cbw hrel (w2.setWidth 8) hsp _ htrel
    (by rw [htpc, BitVec.add_assoc, ← BitVec.ofNat_add, hpos])
  have hrel' := stateRel_shiftInterfer _ _ _ _ _ _ _ l hrel1
  exact compileCorrect_stepB (s1' := incPc (decClock { s1 with
      codeBuffer := ⟨s1.codeBuffer.position, s1.codeBuffer.buffer ++ [w2.setWidth 8],
        s1.codeBuffer.spaceLeft - 1⟩ })) ht hecB hclock hlines (by have := hlines s1.pc; omega)
    (fun k => ⟨(hl k).1, (hl k).2.1⟩) (hl 0).2.2.2
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ hrel' hev hres (ih w1 w2 _ hr1 hr2 hbw)

end Flapjack.Compiler.Backend.LabToTarget.Bounded
