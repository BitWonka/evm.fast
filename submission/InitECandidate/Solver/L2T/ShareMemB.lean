import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.Step
import InitECandidate.Solver.L2T.StepB
import Flapjack.Compiler.Backend.LabToTarget.InstMem
import Flapjack.Compiler.Backend.LabToTarget.CodeSafetyFacts
import Flapjack.Compiler.Backend.Semantics.TargetProps.NextSharedMem
import Flapjack.Misc.FindIndex.Bounds
import Flapjack.Misc.FindIndex.SuccessfulMembership
import Flapjack.Misc.BytesInMemory.Domain
import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.ShareMem
import InitECandidate.Solver.L2T.StepB

/-! `Asm (ShareMem m r a)` case of the original `compile_correct`
(lab_to_targetProofScript.sml:7829-7965): the source shared-memory operation
is simulated by the target's mapped-memory FFI entry at the instruction's
own PC. Hypotheses are the source theorem's together with exactly the
`evaluate_ind` induction hypothesis of the case. -/
namespace Flapjack.Compiler.Backend.LabToTarget.Bounded
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Encoders Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.AsmSem Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang

/-- The complete relation after a returning shared-memory FFI call: the
source takes the FFI state `newFfi` reached by one call, possibly updates
registers, advances the PC and clock and shifts its I/O oracles; the target
takes the related registers and the next PC, and the machine configuration
consumes one FFI interference oracle. This is the `state_rel` part of the
original ShareMemOp case. -/
theorem stateRel_shareMem {width : Nat} [NeZero width] {S Q F : Type}
    {mc : MachineConfig width S Q} {code2 : LabProgHOL width} {labs : Spt (Spt Nat)}
    {p : BitVec width} {s1 : LabSem.State width Config F} {t1 : AsmState width} {ms1 ms2 : S}
    (h : stateRel (mc, code2, labs, p) s1 t1 ms1) (newFfi : HolFfiState F)
    (hffi : callFFIRelHOL s1.ffi newFfi)
    (regs : Nat → WordLocW width) (ioRegs : Nat → HolFfiName → Nat → Option (BitVec width))
    (ioFpRegs : Nat → Nat → BitVec 64)
    (tregs : Nat → BitVec width) (tpc : BitVec width)
    (htrel : targetStateRel mc.target { t1 with regs := tregs, pc := tpc } ms2)
    (hregs : ∀ r, wordLocVal p labs (regs r) = some (tregs r))
    (hpc : tpc = p + BitVec.ofNat width (posVal (s1.pc + 1) 0 code2)) :
    stateRel ({ mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer }, code2, labs, p)
      { s1 with ffi := newFfi, regs := regs, pc := s1.pc + 1, clock := s1.clock - 1,
                ioRegs := ioRegs, ioFpRegs := ioFpRegs }
      { t1 with regs := tregs, pc := tpc } ms2 := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18,
    c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36,
    c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53⟩ := h
  refine ⟨htrel, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, ?_, c17, c18,
    c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, hregs, c31, c32, c33, c34, c35, c36,
    c37, c38, c39, c40, hpc, c42, c43, c44, c45, c46, c47, c48, c49, ?_, c51, c52, c53⟩
  · intro ms k index newBytes t bytes bytes2 st newSt i ⟨hi, hix, hrd, hst, hcall, hdom, hts, hal⟩
    exact c16 ms (k + 1) index newBytes t bytes bytes2 st newSt i
      ⟨hi, hix, hrd, Relation.ReflTransGen.head hffi hst, hcall, hdom, hts, hal⟩
  · refine ⟨fun ms k index newBytes t nb ad offs re pc' ad' st newSt i
      ⟨hi, hle, hlt, hst, hlk, hdom, had, hts⟩ => ?_, c50.2⟩
    exact c50.1 ms (k + 1) index newBytes t nb ad offs re pc' ad' st newSt i
      ⟨hi, hle, hlt, Relation.ReflTransGen.head hffi hst, hlk, hdom, had, hts⟩

/-- HOL `word_to_bytes_aux` as an indexed map; Flapjack byte infrastructure. -/
theorem wordToBytesAux_eq_map {width : Nat} [NeZero width] (n : Nat) (v : BitVec width)
    (be : Bool) :
    HolByte.wordToBytesAux n v be =
      (List.range n).map fun i => HolByte.getByte (BitVec.ofNat width i) v be := by
  induction n with
  | zero => rfl
  | succ n ih => simp [HolByte.wordToBytesAux, ih, List.range_succ]

/-- The source's shared-memory byte rendering is HOL `word_to_bytes w F`. -/
theorem sharedMemoryWordBytes_eq {width : Nat} [NeZero width] (v : BitVec width) :
    sharedMemoryWordBytes v = HolByte.wordToBytes v false := by
  simp [sharedMemoryWordBytes, HolByte.wordToBytes, wordToBytesAux_eq_map, getByteHOL8_eq]

/-- `TAKE k (word_to_bytes w F) = word_to_bytes_aux k w F` for `k` within the
word; the original proves the three instances `k = 1, 2, 4` inline. -/
theorem take_wordToBytes {width : Nat} [NeZero width] (k : Nat) (v : BitVec width)
    (hk : k ≤ width / 8) :
    (HolByte.wordToBytes v false).take k = HolByte.wordToBytesAux k v false := by
  simp [HolByte.wordToBytes, wordToBytesAux_eq_map, ← List.map_take, List.take_range,
    Nat.min_eq_left hk]

/-- The source and target byte decoders agree. -/
theorem wordOfBytesHOL8_eq {width : Nat} [NeZero width] (be : Bool) (a : BitVec width)
    (bs : List (BitVec 8)) : wordOfBytesHOL8 be a bs = HolByte.wordOfBytes be a bs := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih => simp [wordOfBytesHOL8, HolByte.wordOfBytes, ih, setByteHOL8_eq]

/-- Both natural-key association-list lookups read the first equal key. -/
theorem sptAListLookup_eq_lookup {α : Type} (key : Nat) (entries : List (Nat × α)) :
    sptAListLookup key entries = entries.lookup key := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨k, value⟩
    by_cases h : key = k
    · simp [sptAListLookup, List.lookup, h]
    · cases hb : (key == k) with
      | false => simp [sptAListLookup, List.lookup, h, hb, ih]
      | true => exact False.elim (h (by simpa only [beq_iff_eq] using hb))

/-- Every shared-memory operation is a load or a store of size 0, 1, 2 or 4
whose `get_memop_info` size byte and mapped-access validity match the
instruction; the original obtains these facts by `Cases_on m`. -/
theorem shareMemOp_load_or_store {width : Nat} [NeZero width] (m : HolMemop) :
    (∃ size, (size = 0 ∨ size = 1 ∨ size = 2 ∨ size = 4) ∧
      getMemopInfo m = (.mappedRead, BitVec.ofNat 8 size) ∧
      (∀ {C F : Type} r (ad : HolAddr width) (s : LabSem.State width C F),
        shareMemOp m r ad s = shareMemLoad r ad s size) ∧
      (∀ {S Q : Type} (pc : BitVec width) r ad (pc' : BitVec width) (tg : HolAsmTarget width S Q)
        (ms : S) (dom : BitVec width → Prop),
        isValidMappedRead pc (BitVec.ofNat 8 size) ad r pc' tg ms dom ↔
          bytesInMemoryHOL pc (tg.config.encode (.inst (.mem m r ad))) (tg.getByte ms) dom)) ∨
    (∃ size, (size = 0 ∨ size = 1 ∨ size = 2 ∨ size = 4) ∧
      getMemopInfo m = (.mappedWrite, BitVec.ofNat 8 size) ∧
      (∀ {C F : Type} r (ad : HolAddr width) (s : LabSem.State width C F),
        shareMemOp m r ad s = shareMemStore r ad s size) ∧
      (∀ {S Q : Type} (pc : BitVec width) r ad (pc' : BitVec width) (tg : HolAsmTarget width S Q)
        (ms : S) (dom : BitVec width → Prop),
        isValidMappedWrite pc (BitVec.ofNat 8 size) ad r pc' tg ms dom ↔
          bytesInMemoryHOL pc (tg.config.encode (.inst (.mem m r ad))) (tg.getByte ms) dom)) := by
  cases m
  · exact .inl ⟨0, by simp, rfl, fun _ _ _ => rfl, by intros; simp [isValidMappedRead]⟩
  · exact .inl ⟨1, by simp, rfl, fun _ _ _ => rfl, by intros; simp [isValidMappedRead]⟩
  · exact .inl ⟨2, by simp, rfl, fun _ _ _ => rfl, by intros; simp [isValidMappedRead]⟩
  · exact .inl ⟨4, by simp, rfl, fun _ _ _ => rfl, by intros; simp [isValidMappedRead]⟩
  · exact .inr ⟨0, by simp, rfl, fun _ _ _ => rfl, by intros; simp [isValidMappedWrite]⟩
  · exact .inr ⟨1, by simp, rfl, fun _ _ _ => rfl, by intros; simp [isValidMappedWrite]⟩
  · exact .inr ⟨2, by simp, rfl, fun _ _ _ => rfl, by intros; simp [isValidMappedWrite]⟩
  · exact .inr ⟨4, by simp, rfl, fun _ _ _ => rfl, by intros; simp [isValidMappedWrite]⟩

/-- One target step at a valid mapped-read FFI entry: the FFI call is made
and, on return, the run continues after one FFI interference. The target
semantics' own case, unfolded once (`evaluate_def` in the original). -/
theorem evaluateTarget_mappedRead {width : Nat} [NeZero width] {S Q σ : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (c : Nat) (ms : S) (index : Nat)
    (nb : BitVec 8) (base re : Nat) (off pc' : BitVec width)
    (hn : ¬ (mc.progAddresses (mc.target.getPc ms) ∧ mc.target.getPc ms ∉ mc.ffiEntryPcs))
    (hh : mc.target.getPc ms ≠ mc.haltPc) (hc : mc.target.getPc ms ≠ mc.ccachePc)
    (hi : Misc.findIndex (mc.target.getPc ms) mc.ffiEntryPcs 0 = some index)
    (he : holEl index mc.ffiNames = .sharedMem .mappedRead)
    (hm : sptAListLookup index mc.mmioInfo = some (nb, .addr base off, re, pc'))
    (hal : nb = 0 → (mc.target.getReg ms base + off).toNat % (width / 8) = 0)
    (hsh : mc.sharedAddresses (mc.target.getReg ms base + off))
    (hv : isValidMappedRead (mc.target.getPc ms) nb (.addr base off) re pc' mc.target ms
      mc.progAddresses) :
    evaluateTargetHOL mc ffi (c + 1) ms =
      match callFFIHOL ffi (.sharedMem .mappedRead) [nb]
          (HolByte.wordToBytes (mc.target.getReg ms base + off) false) with
      | .final e => (.halt (.ffiOutcome e), ms, ffi)
      | .ret newFfi newBytes =>
          evaluateTargetHOL { mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer } newFfi c
            (mc.ffiInterfer 0 (index, newBytes, ms)) := by
  have hcond : (if nb = 0 then (mc.target.getReg ms base + off).toNat % (width / 8) = 0
      else True) := by
    split
    · exact hal ‹_›
    · trivial
  simp only [evaluateTargetHOL, hn, ↓reduceIte, hh, hc, hi, he, hm, applyOracleHOL]
  rw [if_pos ⟨hcond, hsh, hv⟩]
  rfl

/-- One target step at a valid mapped-write FFI entry (`evaluate_def`). -/
theorem evaluateTarget_mappedWrite {width : Nat} [NeZero width] {S Q σ : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (c : Nat) (ms : S) (index : Nat)
    (nb : BitVec 8) (base re : Nat) (off pc' : BitVec width)
    (hn : ¬ (mc.progAddresses (mc.target.getPc ms) ∧ mc.target.getPc ms ∉ mc.ffiEntryPcs))
    (hh : mc.target.getPc ms ≠ mc.haltPc) (hc : mc.target.getPc ms ≠ mc.ccachePc)
    (hi : Misc.findIndex (mc.target.getPc ms) mc.ffiEntryPcs 0 = some index)
    (he : holEl index mc.ffiNames = .sharedMem .mappedWrite)
    (hm : sptAListLookup index mc.mmioInfo = some (nb, .addr base off, re, pc'))
    (hal : nb = 0 → (mc.target.getReg ms base + off).toNat % (width / 8) = 0)
    (hsh : mc.sharedAddresses (mc.target.getReg ms base + off))
    (hv : isValidMappedWrite (mc.target.getPc ms) nb (.addr base off) re pc' mc.target ms
      mc.progAddresses) :
    evaluateTargetHOL mc ffi (c + 1) ms =
      match callFFIHOL ffi (.sharedMem .mappedWrite) [nb]
          ((if nb = 0 then HolByte.wordToBytes (mc.target.getReg ms re) false
            else HolByte.wordToBytesAux nb.toNat (mc.target.getReg ms re) false) ++
            HolByte.wordToBytes (mc.target.getReg ms base + off) false) with
      | .final e => (.halt (.ffiOutcome e), ms, ffi)
      | .ret newFfi newBytes =>
          evaluateTargetHOL { mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer } newFfi c
            (mc.ffiInterfer 0 (index, newBytes, ms)) := by
  have hcond : (if nb = 0 then (mc.target.getReg ms base + off).toNat % (width / 8) = 0
      else True) := by
    split
    · exact hal ‹_›
    · trivial
  simp only [evaluateTargetHOL, hn, ↓reduceIte, hh, hc, hi, he, hm, applyOracleHOL]
  rw [if_pos ⟨hcond, hsh, hv⟩]
  rfl

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compileCorrect_shareMemB {width : Nat} [NeZero width] {S Q F : Type} {W : Nat}
    (s1 : Flapjack.Compiler.Backend.LabSem.State width Config F) (m : HolMemop) (r : Nat)
    (ad : HolAddr width) (bytes : List (BitVec 8)) (n : Nat)
    (hclock : s1.clock ≠ 0) (hfetch : asmFetch s1 = some (.asm (.shareMem m r ad) bytes n))
    (ih : ∀ ffi' bs s', shareMemOp m r ad s1 = some (.ret ffi' bs, s') →
      CompileCorrectForB W S Q { s' with
        ioRegs := holShiftSeq 1 s'.ioRegs
        ioFpRegs := holShiftSeq 1 s'.ioFpRegs }) :
    CompileCorrectForB W S Q s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨ht, hev, hres, hecB, hrel, hlines⟩
  have hec := encoderCorrect_of_bounded hecB
  obtain ⟨c1, c2, c3, -, -, -, -, -, -, -, -, -, -, -, c15, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, c30, -, -, c33, -, -, -, -, -, -, -, c41, -, -, -, -, -, c47, -, c49, c50, c51, c52,
    -⟩ := id hrel
  obtain ⟨base, off⟩ := ad
  obtain ⟨bytes', hf2, henc, hbm, -, hpos, hok⟩ :=
    imp_bytesInMemory_shareMem mc labs _ s1 code2 p t1 m r (.addr base off) bytes n
      ⟨hfetch, c49, c47, c33⟩
  obtain ⟨i, hi, -⟩ := c15
  obtain ⟨index, hle, hfi, hinfo⟩ := c51.1 s1.pc m r (.addr base off) bytes' bytes'.length i
    ⟨hf2, hi⟩
  have hpc : mc.target.getPc ms1 = p + BitVec.ofNat width (posVal s1.pc 0 code2) :=
    c1.2.1.trans c41
  rw [← hpc] at hfi
  have hlt : index < mc.ffiNames.length := by
    have := (Misc.findIndexLessLength _ _ _ _ hfi).2
    rw [c52]; omega
  have hn : ¬ (mc.progAddresses (mc.target.getPc ms1) ∧
      mc.target.getPc ms1 ∉ mc.ffiEntryPcs) :=
    fun h => h.2 (Misc.findIndex_isMem _ _ _ _ hfi)
  obtain ⟨hcc, hhalt⟩ := ffiEntryPcs_not_ccache_or_halt _ mc index
    ⟨hfi, (c50.2 index i ⟨hi, hlt, hle⟩).1, (c50.2 index i ⟨hi, hlt, hle⟩).2⟩
  have hentry : holEl index mc.ffiEntryPcs = t1.pc := by
    have := (findIndex_holEl _ _ 0 index hfi).2
    rw [Nat.sub_zero] at this
    rw [this, c1.2.1]
  have hts0 : targetStateRel mc.target { t1 with pc := holEl index mc.ffiEntryPcs } ms1 := by
    rw [hentry]; exact c1
  -- registers read by the target instruction
  simp only [asmOkExact, asmInstOkExact, asmRegOkExact, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at hok
  have hgr : ∀ x, x < mc.target.config.regCount →
      mc.target.config.avoidRegs.contains x = false → mc.target.getReg ms1 x = t1.regs x :=
    fun x h1 h2 => c1.2.2.2.1 x ⟨h1, h2⟩
  have htreg : ∀ x w, s1.regs x = .word w → t1.regs x = w := by
    intro x w hx
    have := c30 x; rw [hx] at this; simpa [wordLocVal] using this.symm
  -- the encoded instruction is in target memory at the entry PC
  have henc' : bytesInMemoryHOL (mc.target.getPc ms1)
      (mc.target.config.encode (.inst (.mem m r (.addr base off)))) (mc.target.getByte ms1)
      mc.progAddresses := by
    obtain ⟨cnt, hcnt⟩ := (encWithNop_iff _ _ _).mp henc
    rw [hcnt, bytesInMemory_append] at hbm
    rw [hpc, c3]
    refine bytesInMemory_changeMem _ _ t1.mem _ _ ⟨hbm.1, fun k hk => ?_⟩
    exact (c1.2.2.1 _ (bytesInMemoryInDomain _ _ _ _ k ⟨hbm.1, hk⟩)).symm
  have hshared : ∀ v, s1.sharedMemDomain (holByteAlign v) = true →
      mc.sharedAddresses v := by
    intro v hv
    rw [c51.2.2.2]; exact c51.2.2.1 v hv
  have hshared0 : ∀ v, s1.sharedMemDomain v = true → mc.sharedAddresses v := by
    intro v hv; rw [c51.2.2.2]; exact hv
  have hwidth : 4 ≤ width / 8 := by rcases c2 with h | h <;> simp [h]
  rw [evaluate] at hev
  simp only [hclock, ↓reduceIte, hfetch] at hev
  obtain ⟨x, next, hso⟩ : ∃ x next, shareMemOp m r (.addr base off) s1 = some (x, next) := by
    split at hev
    · exact absurd (Prod.mk.inj hev).1.symm hres
    · exact ⟨_, _, ‹_›⟩
    · exact ⟨_, _, ‹_›⟩
  -- the target FFI entry simulates the source operation
  have hcore :
      (∀ c, evaluateTargetHOL mc s1.ffi (c + 1) ms1 =
        match x with
        | .final e => (.halt (.ffiOutcome e), ms1, s1.ffi)
        | .ret f bs => evaluateTargetHOL { mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer }
            f c (mc.ffiInterfer 0 (index, bs, ms1))) ∧
      (∀ e, x = .final e → next = s1) ∧
      (∀ f bs, x = .ret f bs →
        nextInterference mc s1.ffi ms1 = some
          (.ffiApp index bs ms1 (mc.ffiInterfer 0 (index, bs, ms1)),
            { mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer }, f) ∧
        callFFIRelHOL s1.ffi f ∧
        ∃ tregs regs, targetStateRel mc.target
            { t1 with regs := tregs, pc := p + BitVec.ofNat width (posVal (s1.pc + 1) 0 code2) }
            (mc.ffiInterfer 0 (index, bs, ms1)) ∧
          (∀ y, wordLocVal p labs (regs y) = some (tregs y)) ∧
          next = { s1 with ffi := f, regs := regs, pc := s1.pc + 1, clock := s1.clock - 1 }) := by
    have hgb : ∀ wb, s1.regs base = .word wb → mc.target.getReg ms1 base = wb :=
      fun wb hb => (hgr base hok.1.2.1 hok.1.2.2).trans (htreg base wb hb)
    rcases shareMemOp_load_or_store (width := width) m with
      ⟨size, hsz, hgi, hop, hvalid⟩ | ⟨size, hsz, hgi, hop, hvalid⟩
    all_goals
      rw [hgi] at hinfo
      obtain ⟨he, hlk⟩ := hinfo
      have hm := (sptAListLookup_eq_lookup index mc.mmioInfo).trans hlk
      have hsize0 : BitVec.ofNat 8 size = 0 ↔ size = 0 := by
        rcases hsz with rfl | rfl | rfl | rfl <;> decide
      have hv := (hvalid (mc.target.getPc ms1) r (.addr base off)
        (p + BitVec.ofNat width (posVal s1.pc 0 code2 + bytes'.length)) mc.target ms1
        mc.progAddresses).2 henc'
      rw [hop] at hso
    · -- loads
      simp only [shareMemLoad, addrValue] at hso
      cases hb : s1.regs base with
      | loc _ _ => simp [hb] at hso
      | word wb =>
      simp only [hb] at hso
      by_cases hcond : (if size = 0 then
          ((wb + off).toNat % (width / 8) == 0 && s1.sharedMemDomain (wb + off))
        else s1.sharedMemDomain (riscvByteAlignHOL (wb + off))) = true
      swap
      · rw [if_neg hcond] at hso; cases hso
      rw [if_pos hcond] at hso
      have hal : BitVec.ofNat 8 size = 0 →
          (mc.target.getReg ms1 base + off).toNat % (width / 8) = 0 := by
        intro h0
        rw [hsize0] at h0
        rw [if_pos h0] at hcond
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        rw [hgb wb hb]; exact hcond.1
      have hsh : mc.sharedAddresses (mc.target.getReg ms1 base + off) := by
        rw [hgb wb hb]
        by_cases h0 : size = 0
        · rw [if_pos h0] at hcond
          simp only [Bool.and_eq_true] at hcond
          exact hshared0 _ hcond.2
        · rw [if_neg h0, riscvByteAlignHOL_eq c2] at hcond
          exact hshared _ hcond
      have hstep := fun c => evaluateTarget_mappedRead mc s1.ffi c ms1 index _ base r off _
        hn hhalt hcc hfi he hm hal hsh hv
      have hcallT : HolByte.wordToBytes (mc.target.getReg ms1 base + off) false =
          sharedMemoryWordBytes (wb + off) := by
        rw [hgb wb hb, sharedMemoryWordBytes_eq]
      rw [hcallT] at hstep
      cases hcall : callFFIHOL s1.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 size]
          (sharedMemoryWordBytes (wb + off)) with
      | final e =>
        rw [hcall] at hso hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hso
        obtain ⟨rfl, rfl⟩ := hso
        exact ⟨hstep, fun _ _ => rfl, fun _ _ h => by cases h⟩
      | ret f bs =>
        rw [hcall] at hso hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hso
        obtain ⟨rfl, rfl⟩ := hso
        refine ⟨hstep, (fun _ h => by cases h), fun f' bs' h => ?_⟩
        cases h
        obtain ⟨op, hop', hmatch⟩ := c50.1 ms1 0 index bs t1 (BitVec.ofNat 8 size) base off r _
          (mc.target.getReg ms1 base + off) s1.ffi f i
          ⟨hi, hle, hlt, .refl, hlk, c3, rfl, hts0⟩
        rw [he] at hop'
        cases hop'
        have htrel := hmatch ⟨by split; exact hal ‹_›; trivial, hsh, hv, by
          rw [hcallT]; exact hcall⟩
        refine ⟨nextInterferenceSharedMem mc s1.ffi ms1 index base r _ off _ .mappedRead bs f
            ⟨hn, hhalt, hcc, hfi, he, hm, hal, hsh, fun _ => ⟨hv, by rw [he, hcallT]; exact hcall⟩,
              fun h => by cases h⟩,
          ⟨_, _, _, _, hcall⟩, fun n => if n = r then HolByte.wordOfBytes false 0 bs else t1.regs n,
          _, ?_, ?_, rfl⟩
        · rw [hpos]; exact htrel
        · intro y
          by_cases hy : y = r
          · simp [hy, wordLocVal, wordOfBytesHOL8_eq]
          · simpa [hy] using c30 y
    · -- stores
      simp only [shareMemStore, addrValue] at hso
      cases hw : s1.regs r with
      | loc _ _ => simp [hw] at hso
      | word w =>
      cases hb : s1.regs base with
      | loc _ _ => simp [hw, hb] at hso
      | word wb =>
      simp only [hw, hb] at hso
      by_cases hcond : (if size = 0 then
          ((wb + off).toNat % (width / 8) == 0 && s1.sharedMemDomain (wb + off))
        else s1.sharedMemDomain (riscvByteAlignHOL (wb + off))) = true
      swap
      · rw [if_neg hcond] at hso; cases hso
      rw [if_pos hcond] at hso
      have hal : BitVec.ofNat 8 size = 0 →
          (mc.target.getReg ms1 base + off).toNat % (width / 8) = 0 := by
        intro h0
        rw [hsize0] at h0
        rw [if_pos h0] at hcond
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        rw [hgb wb hb]; exact hcond.1
      have hsh : mc.sharedAddresses (mc.target.getReg ms1 base + off) := by
        rw [hgb wb hb]
        by_cases h0 : size = 0
        · rw [if_pos h0] at hcond
          simp only [Bool.and_eq_true] at hcond
          exact hshared0 _ hcond.2
        · rw [if_neg h0, riscvByteAlignHOL_eq c2] at hcond
          exact hshared _ hcond
      have hstep := fun c => evaluateTarget_mappedWrite mc s1.ffi c ms1 index _ base r off _
        hn hhalt hcc hfi he hm hal hsh hv
      have hgw : mc.target.getReg ms1 r = w :=
        (hgr r hok.1.1.1 hok.1.1.2).trans (htreg r w hw)
      have hcallT : ((if BitVec.ofNat 8 size = 0 then
            HolByte.wordToBytes (mc.target.getReg ms1 r) false
          else HolByte.wordToBytesAux (BitVec.ofNat 8 size).toNat (mc.target.getReg ms1 r) false) ++
          HolByte.wordToBytes (mc.target.getReg ms1 base + off) false) =
          ((if size = 0 then sharedMemoryWordBytes w
            else (sharedMemoryWordBytes w).take size) ++ sharedMemoryWordBytes (wb + off)) := by
        rw [hgb wb hb, hgw, sharedMemoryWordBytes_eq, sharedMemoryWordBytes_eq]
        rcases hsz with rfl | rfl | rfl | rfl
        · rfl
        all_goals
          simp only [BitVec.ofNat_eq_ofNat, show ¬ ((1 : Nat) = 0) from by decide,
            show ¬ ((2 : Nat) = 0) from by decide, show ¬ ((4 : Nat) = 0) from by decide,
            ↓reduceIte]
          rw [take_wordToBytes _ _ (by omega)]
          rfl
      rw [hcallT] at hstep
      cases hcall : callFFIHOL s1.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 size]
          ((if size = 0 then sharedMemoryWordBytes w
            else (sharedMemoryWordBytes w).take size) ++ sharedMemoryWordBytes (wb + off)) with
      | final e =>
        rw [hcall] at hso hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hso
        obtain ⟨rfl, rfl⟩ := hso
        exact ⟨hstep, fun _ _ => rfl, fun _ _ h => by cases h⟩
      | ret f bs =>
        rw [hcall] at hso hstep
        simp only [Option.some.injEq, Prod.mk.injEq] at hso
        obtain ⟨rfl, rfl⟩ := hso
        refine ⟨hstep, (fun _ h => by cases h), fun f' bs' h => ?_⟩
        cases h
        obtain ⟨op, hop', hmatch⟩ := c50.1 ms1 0 index bs t1 (BitVec.ofNat 8 size) base off r _
          (mc.target.getReg ms1 base + off) s1.ffi f i
          ⟨hi, hle, hlt, .refl, hlk, c3, rfl, hts0⟩
        rw [he] at hop'
        cases hop'
        have htrel := hmatch ⟨by split; exact hal ‹_›; trivial, hsh, hv, by
          rw [hcallT]; exact hcall⟩
        refine ⟨nextInterferenceSharedMem mc s1.ffi ms1 index base r _ off _ .mappedWrite bs f
            ⟨hn, hhalt, hcc, hfi, he, hm, hal, hsh, (fun h => by cases h),
              fun _ => ⟨hv, by rw [he, hcallT]; exact hcall⟩⟩,
          ⟨_, _, _, _, hcall⟩, t1.regs, s1.regs, ?_, c30, rfl⟩
        rw [hpos]; exact htrel
  obtain ⟨hstep, hfinal, hret⟩ := hcore
  have hclk : ∀ k, s1.clock + k = (s1.clock - 1 + k) + 1 := fun k => by omega
  split at hev
  · exact absurd (Prod.mk.inj hev).1.symm hres
  · -- final outcome
    rename_i outcome next' hshare
    rw [hso] at hshare
    simp only [Option.some.injEq, Prod.mk.injEq] at hshare
    obtain ⟨rfl, rfl⟩ := hshare
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
    refine ⟨0, ms1, by rw [Nat.add_mul, Nat.one_mul]; omega, ?_⟩
    rw [hclk, hstep]
    dsimp only
    rw [hfinal _ rfl]
  · -- returning call
    rename_i f bs next' hshare
    have hshare' := hshare
    rw [hso] at hshare'
    simp only [Option.some.injEq, Prod.mk.injEq] at hshare'
    obtain ⟨rfl, rfl⟩ := hshare'
    obtain ⟨hnext, hffi, tregs, regs, htrel, hregs, hnexteq⟩ := hret f bs rfl
    subst hnexteq
    have hrel' := stateRel_shareMem hrel f hffi regs (holShiftSeq 1 s1.ioRegs)
      (holShiftSeq 1 s1.ioFpRegs) tregs _ htrel hregs rfl
    obtain ⟨k, ms2, hkb, hk⟩ := ih f bs _ hshare res _ s2 code2 labs _ _ p
      ⟨oracleTie_ffiNext mc ms1 s1 _ index bs ms1 _ _ f ⟨ht, hnext, rfl, rfl, rfl, rfl, rfl⟩,
        hev, hres, hecB, hrel', hlines⟩
    refine ⟨k, ms2, by
      have hc : (W + 1) * (s1.clock - 1) + (W + 1) = (W + 1) * s1.clock := by
        rw [← Nat.mul_succ]; congr 1; omega
      simp only at hkb
      omega, ?_⟩
    rw [hclk, hstep]
    exact hk

end Flapjack.Compiler.Backend.LabToTarget.Bounded
