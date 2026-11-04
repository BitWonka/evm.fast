import Flapjack.Compiler.Backend.LabToTarget.NopEncoding
import Flapjack.Compiler.Backend.LabToTarget.Interference
import Flapjack.Compiler.Backend.Semantics.TargetProps.AsmStepEvaluate
import Flapjack.Compiler.Encoders.AsmProps.AsmConsts
import Flapjack.Compiler.Backend.LabToTarget.NopSteps
import InitECandidate.Solver.AsmStepEvaluateB

/-! Original NOP-padded assembly-step simulation (lab_to_targetProofScript.sml
115-345). All original encoder, domain, FFI-entry disjointness, interference,
memory, assembly and target-relation hypotheses are retained; the conclusions
keep the existential shifted-clock witness and target relation. Only the
polymorphic word dimension translates to positive-width BitVec. Through the
assembly semantics these inherit the reviewed rational-cut real translation
(reals_as_rational_cuts, docs/SOUNDNESS.md item 8). -/
namespace Flapjack.Compiler.Backend.LabToTarget.Bounded
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.Semantics.TargetProps.Bounded
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Backend.Semantics.TargetProps

/-- Wrapped address reassociation; Flapjack word arithmetic infrastructure. -/
private theorem pcAddAdd {width : Nat} (a : BitVec width) (m n : Nat) :
    a + BitVec.ofNat width m + BitVec.ofNat width n = a + BitVec.ofNat width (m + n) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Shifting the interference oracle preserves projection-invariance;
Flapjack infrastructure (HOL unfolds `shift_seq_def`). -/
private theorem interferenceOk_shift {width : Nat} [NeZero width] {S Q : Type}
    (c : MachineConfig width S Q) (l : Nat) (proj : S → Q)
    (h : interferenceOk c.nextInterfer proj) :
    interferenceOk (shiftInterfer l c).nextInterfer proj := by
  intro i ms
  exact h (i + l) ms

/-- FFI-entry disjointness of a suffix region after advancing the PC;
Flapjack infrastructure for the original disjointness subgoals. -/
private theorem ffiEntryPcsDisjoint_advance {width : Nat} [NeZero width] {S Q : Type}
    (c : MachineConfig width S Q) (c' : MachineConfig width S Q) (s s' : AsmState width)
    (m n : Nat) (hpcs : c'.ffiEntryPcs = c.ffiEntryPcs)
    (hpc : s'.pc = s.pc + BitVec.ofNat width m)
    (h : ffiEntryPcsDisjoint c s (m + n)) : ffiEntryPcsDisjoint c' s' n := by
  rintro address ⟨hmem, off, hoff, heq⟩
  refine h address ⟨hpcs ▸ hmem, m + off, by omega, ?_⟩
  rw [heq, hpc, pcAddAdd]

/-- `asm (Inst Skip)` only sets the PC; Flapjack infrastructure. -/
private theorem asmUpd_skip {width : Nat} [NeZero width] (pc : BitVec width)
    (s : AsmState width) : asmUpd (.inst .skip) pc s = updPc pc s := rfl

/-- The two orientations of the original optional link-register guard agree;
Flapjack infrastructure. -/
private theorem linkGuard_swap {width : Nat} [NeZero width] (c : AsmConfigExact width)
    (s : AsmState width)
    (h : match c.linkReg with
      | none => True
      | some r => s.lr = r) :
    match c.linkReg with
    | some r => s.lr = r
    | none => True := by
  revert h; cases c.linkReg <;> exact id

private theorem asmOk_skip {width : Nat} [NeZero width] (c : AsmConfigExact width) :
    asmOkExact (.inst .skip) c = true := by
  simp [asmOkExact, asmInstOkExact]

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateNopStepsB {width : Nat} [NeZero width] {S Q : Type} {σ : Type}
    (io : HolFfiState σ) (n : Nat) (s1 : AsmState width) (ms1 : S)
    (c : MachineConfig width S Q)
    (h : encoderCorrectBounded c.target ∧ c.progAddresses = s1.memDomain ∧
      ffiEntryPcsDisjoint c s1 (n * (c.target.config.encode (.inst .skip)).length) ∧
      interferenceOk c.nextInterfer (c.target.proj s1.memDomain) ∧
      bytesInMemoryHOL s1.pc
        (List.replicate n (c.target.config.encode (.inst .skip))).flatten s1.mem
        s1.memDomain ∧
      (match c.target.config.linkReg with
       | none => True
       | some r => s1.lr = r) ∧
      s1.be = c.target.config.bigEndian ∧
      s1.align = c.target.config.codeAlignment ∧ ¬ s1.failed ∧
      targetStateRel c.target s1 ms1) :
    ∃ l ms2, l ≤ n * ((c.target.config.encode (.inst .skip)).length / 4) ∧ ∀ k,
      evaluateTargetHOL c io (k + l) ms1 = evaluateTargetHOL (shiftInterfer l c) io k ms2 ∧
      findNextInterference c io (k + l) ms1 =
        findNextInterference (shiftInterfer l c) io k ms2 ∧
      targetStateRel c.target
        (updPc (s1.pc + BitVec.ofNat width
          (n * (c.target.config.encode (.inst .skip)).length)) s1) ms2 := by
  induction n generalizing s1 ms1 c with
  | zero =>
    refine ⟨0, ms1, by simp, fun k => ?_⟩
    rw [shiftInterfer_zero]
    refine ⟨rfl, rfl, ?_⟩
    have : updPc (s1.pc + BitVec.ofNat width (0 * (c.target.config.encode (.inst .skip)).length))
        s1 = s1 := by
      cases s1; simp [updPc]
    rw [this]; exact h.2.2.2.2.2.2.2.2.2
  | succ n ih =>
    obtain ⟨henc, hdm, hdis, hint, hbytes, hlr, hbe, halign, hfail, hrel⟩ := h
    set len := (c.target.config.encode (.inst .skip)).length with hlen
    rw [List.replicate_succ, List.flatten_cons, bytesInMemory_append] at hbytes
    have hstep := asmStepImpEvaluateBounded c s1 ms1 io (.inst .skip)
      ⟨henc, hdm, ffiEntryPcsDisjoint_shorter c s1 _ _ ⟨hdis, by
          rw [Nat.succ_mul]; omega⟩, hint,
        ⟨hbytes.1, linkGuard_swap _ _ hlr, hbe, halign, rfl, by simpa [asmUpd_skip, updPc] using hfail,
          asmOk_skip _⟩, hrel⟩
    obtain ⟨l, ms2, hlb, hl⟩ := hstep
    rw [asmUpd_skip] at hl
    have ih' := ih (updPc (s1.pc + BitVec.ofNat width len) s1) ms2 (shiftInterfer l c)
      ⟨henc, hdm, ffiEntryPcsDisjoint_advance c _ s1 _ len (n * len) rfl rfl (by
          rw [Nat.succ_mul, Nat.add_comm] at hdis; exact hdis),
        interferenceOk_shift c l _ hint, hbytes.2, hlr, hbe, halign, hfail, (hl 0).2.2.1⟩
    obtain ⟨l', ms3, hlb', hl'⟩ := ih'
    change l' ≤ n * (len / 4) at hlb'
    refine ⟨l + l', ms3, by rw [Nat.succ_mul]; omega, fun k => ?_⟩
    have h1 := hl (k + l')
    have h2 := hl' k
    rw [shiftInterfer_twice] at h2
    have htgt : (shiftInterfer l c).target = c.target := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [show k + (l + l') = k + l' + l by omega, h1.1]; exact h2.1
    · rw [show k + (l + l') = k + l' + l by omega, h1.2.1]; exact h2.2.1
    · have h3 := h2.2.2
      simp only [htgt, ← hlen, updPc] at h3 ⊢
      rw [pcAddAdd, show len + n * len = (n + 1) * len by rw [Nat.succ_mul]; omega] at h3
      exact h3

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem asmStepImpEvaluateStepNopB {width : Nat} [NeZero width] {S Q : Type} {σ : Type}
    (c : MachineConfig width S Q) (s1 : AsmState width) (ms1 : S) (io : HolFfiState σ)
    (i : HolAsm width) (s2 : AsmState width) (bytes : List (BitVec 8))
    (h : encoderCorrectBounded c.target ∧ c.progAddresses = s1.memDomain ∧
      ffiEntryPcsDisjoint c s1 bytes.length ∧
      interferenceOk c.nextInterfer (c.target.proj s1.memDomain) ∧
      bytesInMemoryHOL s1.pc bytes s2.mem s1.memDomain ∧
      asmStepNop bytes c.target.config s1 i s2 ∧
      s2 = asmUpd i (s1.pc + BitVec.ofNat width bytes.length) s1 ∧
      targetStateRel c.target s1 ms1 ∧
      (∀ x, i ≠ .call x)) :
    ∃ l ms2, l ≤ bytes.length / 4 ∧ ∀ k,
      evaluateTargetHOL c io (k + l) ms1 = evaluateTargetHOL (shiftInterfer l c) io k ms2 ∧
      findNextInterference c io (k + l) ms1 =
        findNextInterference (shiftInterfer l c) io k ms2 ∧
      targetStateRel c.target s2 ms2 ∧ l ≠ 0 := by
  obtain ⟨henc, hdm, hdis, hint, hbytes2, hnop, hs2, hrel, hcall⟩ := h
  obtain ⟨hbytes1, hwith, hlr, hbe, halign, -, hfail, hok⟩ := hnop
  obtain ⟨n, rfl⟩ := (encWithNop_iff _ _ _).mp hwith
  set enc := c.target.config.encode i with henc_def
  set skip := c.target.config.encode (.inst .skip) with hskip
  have hflat : (List.replicate n skip).flatten.length = n * skip.length := by simp
  have hblen : (enc ++ (List.replicate n skip).flatten).length = enc.length + n * skip.length := by
    rw [List.length_append, hflat]
  rw [bytesInMemory_append] at hbytes1 hbytes2
  have hfail' : ¬ (asmUpd i (s1.pc + BitVec.ofNat width enc.length) s1).failed := by
    rw [asm_failed_ignore_new_pc i
      (s1.pc + BitVec.ofNat width (enc ++ (List.replicate n skip).flatten).length), ← hs2]
    exact hfail
  obtain ⟨l, ms2, hlb, hl⟩ := asmStepImpEvaluateBounded c s1 ms1 io i
    ⟨henc, hdm, ffiEntryPcsDisjoint_shorter c s1 _ _ ⟨hdis, by
        rw [hblen]; simp only [← henc_def]; omega⟩, hint,
      ⟨hbytes1.1, linkGuard_swap _ _ hlr, hbe, halign, rfl, hfail', hok⟩, hrel⟩
  -- The jumps ignore the supplied next PC.
  have hjump : (∃ w, i = .jump w) ∨
      (∃ cmp r ri w, i = .jumpCmp cmp r ri w ∧ wordCmpHOL cmp (readReg r s1) (regImm ri s1)) ∨
      (∃ r, i = .jumpReg r) → s2 = asmUpd i (s1.pc + BitVec.ofNat width enc.length) s1 := by
    rintro (⟨w, rfl⟩ | ⟨cmp, r, ri, w, rfl, hc⟩ | ⟨r, rfl⟩)
    · rw [hs2]; rfl
    · rw [hs2]; simp [asmUpd, hc]
    · rw [hs2]; rfl
  by_cases hj : (∃ w, i = .jump w) ∨
      (∃ cmp r ri w, i = .jumpCmp cmp r ri w ∧ wordCmpHOL cmp (readReg r s1) (regImm ri s1)) ∨
      (∃ r, i = .jumpReg r)
  · refine ⟨l, ms2, by rw [hblen]; simp only [← henc_def] at hlb; omega, fun k => ?_⟩
    rw [hjump hj]; exact hl k
  -- Otherwise the step falls through to the padding NOPs.
  set s := asmUpd i (s1.pc + BitVec.ofNat width enc.length) s1 with hs
  have hspc : s.pc = s1.pc + BitVec.ofNat width enc.length := by
    rw [hs]
    cases i with
    | inst _ => rfl
    | jump w => exact absurd (Or.inl ⟨w, rfl⟩) hj
    | jumpCmp cmp r ri w =>
      simp only [asmUpd]
      split
      · next hc => exact absurd (Or.inr (Or.inl ⟨cmp, r, ri, w, rfl, hc⟩)) hj
      · rfl
    | call x => exact absurd rfl (hcall x)
    | jumpReg r => exact absurd (Or.inr (Or.inr ⟨r, rfl⟩)) hj
    | loc _ _ => rfl
  have hupd : ∀ x, updPc x s = asmUpd i x s1 := by
    intro x
    rw [hs]
    cases i with
    | inst _ => rfl
    | jump w => exact absurd (Or.inl ⟨w, rfl⟩) hj
    | jumpCmp cmp r ri w =>
      simp only [asmUpd]
      split
      · next hc => exact absurd (Or.inr (Or.inl ⟨cmp, r, ri, w, rfl, hc⟩)) hj
      · rfl
    | call x => exact absurd rfl (hcall x)
    | jumpReg r => exact absurd (Or.inr (Or.inr ⟨r, rfl⟩)) hj
    | loc _ _ => rfl
  have hcs := asm_consts i (s1.pc + BitVec.ofNat width enc.length) s1
  have hmem : s.mem = s2.mem := by
    rw [hs, hs2]; exact asm_mem_ignore_new_pc _ _ _ _
  obtain ⟨l', ms3, hlb', hl'⟩ := evaluateNopStepsB io n s ms2 (shiftInterfer l c)
    ⟨henc, by rw [hcs.2.2.2]; exact hdm,
      ffiEntryPcsDisjoint_advance c _ s1 s enc.length _ rfl hspc (by
        rw [hblen] at hdis; exact hdis),
      by rw [hcs.2.2.2]; exact interferenceOk_shift c l _ hint,
      by rw [hspc, hmem, hcs.2.2.2]; exact hbytes2.2,
      by rw [hcs.2.1]; exact hlr, by rw [hcs.1]; exact hbe, by rw [hcs.2.2.1]; exact halign,
      hfail', (hl 0).2.2.1⟩
  have hmd : n * (skip.length / 4) ≤ n * skip.length / 4 := Nat.mul_div_le_mul_div_assoc n skip.length 4
  change l' ≤ n * (skip.length / 4) at hlb'
  simp only [← henc_def] at hlb
  refine ⟨l + l', ms3, by rw [hblen]; omega, fun k => ?_⟩
  have h1 := hl (k + l')
  have h2 := hl' k
  rw [shiftInterfer_twice] at h2
  have htgt : (shiftInterfer l c).target = c.target := rfl
  refine ⟨?_, ?_, ?_, by omega⟩
  · rw [show k + (l + l') = k + l' + l by omega, h1.1]; exact h2.1
  · rw [show k + (l + l') = k + l' + l by omega, h1.2.1]; exact h2.2.1
  · have h3 := h2.2.2
    simp only [htgt, ← hskip] at h3
    rw [hupd, hspc, pcAddAdd, ← hblen] at h3
    rw [hs2]; exact h3

end Flapjack.Compiler.Backend.LabToTarget.Bounded
