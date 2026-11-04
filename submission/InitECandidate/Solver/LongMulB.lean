import InitECandidate.Solver.DivBounded
import Flapjack.RiscV.CorrectnessEncoding.DecodeLongMul
import Flapjack.RiscV.CorrectnessEncoding.InstructionStep
import Flapjack.RiscV.CorrectnessEncoding.Arithmetic
import Flapjack.RiscV.L3.Step.MulHStep
import Flapjack.RiscV.L3.Step.MulDivStep
import InitECandidate.Solver.Common
import InitECandidate.Solver.Words
import InitECandidate.Solver.Ranges
namespace Flapjack.RiscV.TargetProof.Bounded
set_option linter.unusedSimpArgs false
open Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.RiscV.Target
  Compiler.Encoders.Asm Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
/-- Local Run composition needed by the full original LongMul constructor.
The original targetStateRel supplies riscvOk; the source asm_ok supplies rd!=0.
No separate HOL declaration is claimed by this helper. -/
private theorem longMulHighRun (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (ok : riscvOk s = true) (nz : rd ≠ 0#5) :
    Run (.MulDiv (.MULHU (rd, rs1, rs2))) s =
      «write'GPR» (RiscV.L3.holWordExtract 64 127 64
        ((GPR rs1 s).setWidth 128 * (GPR rs2 s).setWidth 128), rd) s := by
  have arch := ((riscvOk_iff s).mp ok).2.1
  have invalid : (s.c_MCSR s.procID).mcpuid.ArchBase ≠ 1#2 := by simp [arch]
  have step := dfnMULHU rd rs1 rs2 s invalid nz
  let a : BitVec 128 :=
    if (s.c_MCSR s.procID).mcpuid.ArchBase = 0 then
      (RiscV.L3.holWordExtract 32 31 0
        (if rs1 = 0 then 0 else s.c_gpr s.procID rs1)).setWidth 128
    else (if rs1 = 0 then 0 else s.c_gpr s.procID rs1).setWidth 128
  let b : BitVec 128 :=
    if (s.c_MCSR s.procID).mcpuid.ArchBase = 0 then
      (RiscV.L3.holWordExtract 32 31 0
        (if rs2 = 0 then 0 else s.c_gpr s.procID rs2)).setWidth 128
    else (if rs2 = 0 then 0 else s.c_gpr s.procID rs2).setWidth 128
  change «dfn'MULHU» (rd, rs1, rs2) s =
    {s with
      c_gpr := holUpdate s.procID
        (holUpdate rd
          (if (s.c_MCSR s.procID).mcpuid.ArchBase = 0 then
            (RiscV.L3.holWordExtract 32 63 32 (a * b)).setWidth 64
           else RiscV.L3.holWordExtract 64 127 64 (a * b))
          (s.c_gpr s.procID)) s.c_gpr} at step
  change «dfn'MULHU» (rd, rs1, rs2) s = _
  rw [step]
  simp [a, b, arch, «write'GPR», «write'gpr», nz, GPR, gpr]
/-- Native low-product Run equation derived from the delivered original MUL
step theorem; arbitrary register zero reads and aliases are preserved. -/
private theorem longMulLowRun (rd rs1 rs2 : BitVec 5) (s : riscv_state)
    (nz : rd ≠ 0#5) :
    Run (.MulDiv (.MUL (rd, rs1, rs2))) s =
      «write'GPR» (GPR rs1 s * GPR rs2 s, rd) s := by
  change «dfn'MUL» (rd, rs1, rs2) s = _
  have step := dfnMUL rd rs1 rs2 s nz
  simpa [«write'GPR», «write'gpr», nz, GPR, gpr] using step
private theorem reg_nonzero (r : Nat) (guard : asmRegOkExact r riscvConfig = true) :
    BitVec.ofNat 5 r ≠ 0#5 := by
  have g : r < 32 ∧ r ≠ 0 := by
    have g := guard
    simp [asmRegOkExact, riscvConfig] at g
    exact ⟨of_decide_eq_true g.1, g.2.1⟩
  intro eq
  have n := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat] at n
  norm_num at n
  rw [Nat.mod_eq_of_lt g.1] at n
  exact g.2 n

private theorem reg_read (r : Nat) (s : AsmState 64) (ms : riscv_state)
    (guard : asmRegOkExact r riscvConfig = true)
    (rel : targetStateRel riscvTarget s ms) :
    GPR (BitVec.ofNat 5 r) ms = readReg r s := by
  have g : r < riscvConfig.regCount ∧ riscvConfig.avoidRegs.contains r = false := by
    simpa [asmRegOkExact] using guard
  have before := rel.2.2.2.1 r g
  change ms.c_gpr ms.procID (BitVec.ofNat 5 r) = s.regs r at before
  simpa [GPR, gpr, reg_nonzero r guard, readReg] using before

private def longMulInstruction (high : Bool) (rd rs1 rs2 : BitVec 5) : instruction :=
  if high then .MulDiv (.MULHU (rd, rs1, rs2)) else .MulDiv (.MUL (rd, rs1, rs2))

private def longMulWord (high : Bool) (rd rs1 rs2 : BitVec 5) : BitVec 32 :=
  Encode (longMulInstruction high rd rs1 rs2)

private def longMulValue (high : Bool) (a b : BitVec 64) : BitVec 64 :=
  if high then BitVec.ofNat 64 ((a.toNat * b.toNat) / 2 ^ 64) else a * b

private theorem longMulHighValue (a b : BitVec 64) :
    RiscV.L3.holWordExtract 64 127 64 (a.setWidth 128 * b.setWidth 128) =
      BitVec.ofNat 64 ((a.toNat * b.toNat) / 2 ^ 64) := by
  change _ = BitVec.ofNat 64 ((a.toNat * b.toNat) / 18446744073709551616)
  rw [mul_long]
  apply BitVec.eq_of_toNat_eq
  simp [RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]

private theorem longMulLowValue (a b : BitVec 64) :
    BitVec.ofNat 64 (a.toNat * b.toNat) = a * b := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul]

/-- Local native byte-fetch/decode/Run/Next composition; its Run equation is
derived internally from the delivered original Step theorems. Not a separate
HOL declaration or a successful-target-execution premise. -/
private theorem longMulNext (high : Bool) (rd rs1 rs2 : Nat)
    (s : AsmState 64) (ms : riscv_state)
    (guards : asmRegOkExact rd riscvConfig = true ∧
      asmRegOkExact rs1 riscvConfig = true ∧ asmRegOkExact rs2 riscvConfig = true)
    (rel : targetStateRel riscvTarget s ms)
    (bytes : bytesInMemoryHOL s.pc
      (riscvEncode (longMulInstruction high (BitVec.ofNat 5 rd)
        (BitVec.ofNat 5 rs1) (BitVec.ofNat 5 rs2))) s.mem s.memDomain) :
    riscvTarget.next ms = writePost ms (BitVec.ofNat 5 rd)
      (longMulValue high (readReg rs1 s) (readReg rs2 s)) := by
  have hb := bytes
  change bytesInMemoryHOL s.pc
    [RiscV.L3.holWordExtract 8 7 0 (longMulWord high (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) (BitVec.ofNat 5 rs2)),
     RiscV.L3.holWordExtract 8 15 8 (longMulWord high (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) (BitVec.ofNat 5 rs2)),
     RiscV.L3.holWordExtract 8 23 16 (longMulWord high (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) (BitVec.ofNat 5 rs2)),
     RiscV.L3.holWordExtract 8 31 24 (longMulWord high (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) (BitVec.ofNat 5 rs2))] s.mem s.memDomain at hb
  have b := bytes_in_memory_thm () s ms _ _ _ _ ⟨rel, hb⟩
  have left := reg_read rs1 s ms guards.2.1 rel
  have right := reg_read rs2 s ms guards.2.2 rel
  let fetched : riscv_state := {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}
  have fetchedOk : riscvOk fetched = true := by
    have ok : riscvOk ms = true := rel.1
    simpa [riscvOk, fetched] using ok
  have nz := reg_nonzero rd guards.1
  have run : Run (longMulInstruction high (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) (BitVec.ofNat 5 rs2)) fetched =
      «write'GPR» (longMulValue high (readReg rs1 s) (readReg rs2 s), BitVec.ofNat 5 rd) fetched := by
    cases high
    · simpa [longMulInstruction, longMulValue, fetched, GPR, gpr, ← left, ← right]
        using longMulLowRun (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) (BitVec.ofNat 5 rs2) fetched nz
    · simpa [longMulInstruction, longMulValue, longMulHighValue, fetched, GPR, gpr, ← left, ← right]
        using longMulHighRun (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) (BitVec.ofNat 5 rs2) fetched fetchedOk nz
  have decode : DecodeAny (.Word (longMulWord high (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) (BitVec.ofNat 5 rs2))) =
      longMulInstruction high (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) (BitVec.ofNat 5 rs2) := by
    cases high
    · exact decode_encode_mul _ _ _
    · exact decode_encode_mulhu _ _ _
  have low : (longMulWord high (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) (BitVec.ofNat 5 rs2)).getLsbD 0 = true ∧
      (longMulWord high (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) (BitVec.ofNat 5 rs2)).getLsbD 1 = true := by
    cases high <;> simp only [longMulWord, longMulInstruction, Bool.false_eq_true,
      ↓reduceIte, Encode, Rtype, opc, BitVec.setWidth_eq, BitVec.getLsbD_append] <;> simp
  have next := write_next ms _ _ (BitVec.ofNat 5 rd) _ nz rel.1 decode run low.1 low.2
    b.2.2.2.2.2.1 b.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.2.1
  change holThe (NextRISCV ms) = _
  rw [next]
  rfl
/-- Full original LongMul encoder constructor630-634. Only original asmStep
and initial targetStateRel are premises; actual encoded MULHU then MUL derive
all existential environment/interference/asserts/asserts2 obligations. Original
asm_ok supplies high/source nonoverlap; other aliases remain unrestricted.
Broad native Run/target closure inherits reals_as_rational_cuts, SOUNDNESS8. -/
theorem riscv_encoder_correct_longmul_bounded (hi lo rs1 rs2 : Nat) (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.inst (.arith (.longMul hi lo rs1 rs2))) s2 ∧
      targetStateRel riscvTarget s1 ms) :
    ∃ n : Nat, n + 1 ≤ (riscvTarget.config.encode (.inst (.arith (.longMul hi lo rs1 rs2)))).length / 4 ∧
      ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (riscvTarget.proj s1.memDomain) →
      let pcs := allPcs (riscvTarget.config.encode (.inst (.arith (.longMul hi lo rs1 rs2)))).length s1.pc
      asserts n (fun k s => env (n - k) (riscvTarget.next s)) ms
        (fun ms' => riscvTarget.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
          riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
        (fun ms' => targetStateRel riscvTarget s2 ms') ∧
      asserts2 (n + 1) (fun k => env (n + 1 - k)) riscvTarget.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x) := by
  have hs := h.1
  change asmStep riscvConfig s1 (.inst (.arith (.longMul hi lo rs1 rs2))) s2 at hs
  have guards : asmRegOkExact hi riscvConfig = true ∧
      asmRegOkExact lo riscvConfig = true ∧ asmRegOkExact rs1 riscvConfig = true ∧
      asmRegOkExact rs2 riscvConfig = true ∧ hi ≠ rs1 ∧ hi ≠ rs2 := by
    simpa [asmOkExact, asmInstOkExact, asmArithOkExact,
      riscvConfig, Bool.and_eq_true, and_assoc] using hs.2.2.2.2.2.2
  have boundHi : hi < 32 := by
    have g := guards.1
    simp [asmRegOkExact, riscvConfig] at g
    exact of_decide_eq_true g.1
  have boundLo : lo < 32 := by
    have g := guards.2.1
    simp [asmRegOkExact, riscvConfig] at g
    exact of_decide_eq_true g.1
  let high := longMulValue true (readReg rs1 s1) (readReg rs2 s1)
  let low := longMulValue false (readReg rs1 s1) (readReg rs2 s1)
  let firstInst := longMulInstruction true (BitVec.ofNat 5 hi) (BitVec.ofNat 5 rs1) (BitVec.ofNat 5 rs2)
  let secondInst := longMulInstruction false (BitVec.ofNat 5 lo) (BitVec.ofNat 5 rs1) (BitVec.ofNat 5 rs2)
  let mid := updPc (s1.pc + 4) (updReg hi high s1)
  have source : s2 = updPc (s1.pc + 8) (updReg lo low (updReg hi high s1)) := by
    simpa [asmUpd, instUpd, arithUpd, riscvConfig, riscvEnc_length_eq,
      riscvAst, high, low, longMulValue, longMulLowValue] using hs.2.2.2.2.1.symm
  have hb := hs.1
  change bytesInMemoryHOL s1.pc (riscvEncode firstInst ++ riscvEncode secondInst) s1.mem s1.memDomain at hb
  have pair := (bytesInMemory_append _ _ _ _ _).mp hb
  have secondBytes : bytesInMemoryHOL (s1.pc + 4) (riscvEncode secondInst) s1.mem s1.memDomain := by
    simpa [riscvEncode] using pair.2
  have firstNext := longMulNext true hi rs1 rs2 s1 ms
    ⟨guards.1, guards.2.2.1, guards.2.2.2.1⟩ h.2 pair.1
  have firstPure := write_post_rel s1 ms hi high boundHi h.2
  have left : readReg rs1 mid = readReg rs1 s1 := by
    simp [readReg, mid, updPc, updReg, Ne.symm guards.2.2.2.2.1]
  have right : readReg rs2 mid = readReg rs2 s1 := by
    simp [readReg, mid, updPc, updReg, Ne.symm guards.2.2.2.2.2]
  refine ⟨1, by
    first
    | (rw [Flapjack.RiscV.TargetProof.Bounded.words_eq]; simp_all [riscvAst]; done)
    | (rw [Flapjack.RiscV.TargetProof.Bounded.words_eq]
       simp only [riscvAst, Flapjack.RiscV.TargetProof.Bounded.inSignedRange_eq, Flapjack.RiscV.TargetProof.Bounded.toInt_jlo, Flapjack.RiscV.TargetProof.Bounded.toInt_jhi, Flapjack.RiscV.TargetProof.Bounded.toInt_clo, Flapjack.RiscV.TargetProof.Bounded.toInt_clo', Flapjack.RiscV.TargetProof.Bounded.toInt_chi, Flapjack.RiscV.TargetProof.Bounded.toInt_jlo', Flapjack.RiscV.TargetProof.Bounded.toInt_jhi', Flapjack.RiscV.TargetProof.Bounded.toInt_chi', decide_eq_true_eq]
       split <;> first | omega | (simp_all; done) | (cases c <;> simp_all)), ?_⟩
  intro env interference
  let firstMs := env 0 (writePost ms (BitVec.ofNat 5 hi) high)
  have firstRel : targetStateRel riscvTarget mid firstMs := by
    exact (riscv_target_ok.2 firstMs (writePost ms (BitVec.ofNat 5 hi) high) mid
      (interference 0 _)).1.mpr firstPure
  have secondBytesMid : bytesInMemoryHOL mid.pc (riscvEncode secondInst) mid.mem mid.memDomain := by
    simpa [mid, updPc, updReg] using secondBytes
  have secondNext := longMulNext false lo rs1 rs2 mid firstMs
    ⟨guards.2.1, guards.2.2.1, guards.2.2.2.1⟩ firstRel secondBytesMid
  rw [left, right] at secondNext
  have finalSource : updPc (mid.pc + 4) (updReg lo low mid) = s2 := by
    rw [source]
    simp [mid, updPc, updReg, BitVec.add_assoc]
  have secondPure := write_post_rel mid firstMs lo low boundLo firstRel
  have finalRel : targetStateRel riscvTarget s2 (env 1 (writePost firstMs (BitVec.ofNat 5 lo) low)) := by
    rw [← finalSource]
    exact (riscv_target_ok.2 _ _ (updPc (mid.pc + 4) (updReg lo low mid))
      (by simpa [mid, updPc, updReg] using interference 1 (writePost firstMs (BitVec.ofNat 5 lo) low))).1.mpr secondPure
  have encodedLength : (riscvTarget.config.encode (.inst (.arith (.longMul hi lo rs1 rs2)))).length = 8 := by
    simp [riscvTarget, riscvConfig, riscvEnc_length_eq, riscvAst]
  constructor
  · simp only [asserts]
    rw [firstNext]
    change (riscvTarget.stateOk firstMs = true ∧
      (∀ pc, pc ∈ allPcs _ s1.pc 0 → riscvTarget.getByte firstMs pc = riscvTarget.getByte ms pc) ∧
      riscvTarget.getPc firstMs ∈ allPcs _ s1.pc riscvTarget.config.codeAlignment) ∧
      targetStateRel riscvTarget s2 (env 1 (riscvTarget.next firstMs))
    constructor
    · refine ⟨firstRel.1, ?_, ?_⟩
      · intro pc covered
        have domain := bytesInMemory_allPcs _ _ _ _ 0 hs.1 covered
        exact (firstRel.2.2.1 pc domain).trans (h.2.2.2.1 pc domain).symm
      · change firstMs.c_PC firstMs.procID ∈ _
        have pcEq : firstMs.c_PC firstMs.procID = s1.pc + 4 := firstRel.2.1
        rw [pcEq, encodedLength, allPcs_eq]
        exact ⟨1, by decide, rfl⟩
    · rw [secondNext]
      exact finalRel
  · simp only [asserts2]
    rw [firstNext]
    refine ⟨fun _ _ => rfl, ?_⟩
    change (∀ x, ¬ s1.memDomain x → riscvTarget.getByte firstMs x = riscvTarget.getByte (riscvTarget.next firstMs) x) ∧ True
    rw [secondNext]
    exact ⟨fun _ _ => rfl, trivial⟩

end Flapjack.RiscV.TargetProof.Bounded
