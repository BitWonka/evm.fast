import Flapjack.RiscV.CorrectnessEncoding.RorExecution
import InitECandidate.Solver.ConstAssertionsBounded
import Flapjack.RiscV.CorrectnessEncoding.ShiftRun
import Flapjack.RiscV.CorrectnessEncoding.Arithmetic
import InitECandidate.Solver.Common
import InitECandidate.Solver.Words

namespace Flapjack.RiscV.TargetProof.Bounded
open Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

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


private theorem reg_scratch (r : Nat) (guard : asmRegOkExact r riscvConfig = true) :
    BitVec.ofNat 5 r ≠ 31#5 := by
  have g := guard
  simp [asmRegOkExact, riscvConfig] at g
  intro eq
  have n := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat] at n
  norm_num at n
  rw [Nat.mod_eq_of_lt (of_decide_eq_true g.1)] at n
  exact g.2.2.2.2.2 n

/-- Native five-instruction Ror arithmetic, including the original zero count.
No named HOL port is claimed for this masked-count composition. -/
private theorem masked_ror (w c : BitVec 64) (bound : c.toNat < 64) :
    (w <<< ((RiscV.L3.holWordExtract 6 5 0 ((64#64)-c)).setWidth 64).toNat) |||
      (w >>> ((RiscV.L3.holWordExtract 6 5 0 c).setWidth 64).toNat) =
      w.rotateRight c.toNat := by
  have mask (x : BitVec 64) :
      ((RiscV.L3.holWordExtract 6 5 0 x).setWidth 64).toNat = x.toNat % 64 := by
    simp [RiscV.L3.holWordExtract,BitVec.toNat_setWidth]
    omega
  have le : c ≤ (64#64) := by
    change c.toNat ≤ (64#64).toNat
    norm_num
    omega
  rw [mask,mask,BitVec.toNat_sub_of_le le,Nat.mod_eq_of_lt bound]
  norm_num only [BitVec.toNat_ofNat,Nat.reduceMod]
  by_cases zero : c.toNat = 0
  · simp [zero,BitVec.rotateRight,BitVec.rotateRightAux]
  · rw [Nat.mod_eq_of_lt (show 64-c.toNat < 64 by omega)]
    exact ror w c.toNat bound

private theorem guards (rd rs rc : Nat) (s1 s2 : AsmState 64)
    (hs : asmStep riscvConfig s1 (.inst (.arith (.shift .ror rd rs (.reg rc)))) s2) :
    asmRegOkExact rd riscvConfig = true ∧ asmRegOkExact rs riscvConfig = true ∧
    asmRegOkExact rc riscvConfig = true := by
  simpa [asmOkExact,asmInstOkExact,asmArithOkExact,asmRegImmOkExact,riscvConfig,
    Bool.and_eq_true,and_assoc] using hs.2.2.2.2.2.2

private theorem kinds (rd rs rc : Nat) :
    ∀ i ∈ riscvAst (.inst (.arith (.shift .ror rd rs (.reg rc)))), RorInstruction i := by
  intro i hi
  simp [riscvAst] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · exact .prior _ (.ori _ _ _)
  · exact .sub _ _ _
  · exact .sll _ _ _
  · exact .srl _ _ _
  · exact .prior _ (.or _ _ _)

/-- Local full source/native postrelation assembly. No named HOL original is
claimed for this intermediate consequence; the full case theorem supplies
original interference and both assertion predicates separately. -/
private theorem pure_relation (rd rs rc : Nat) (s1 s2 : AsmState 64)
    (ms : riscv_state)
    (hs : asmStep riscvConfig s1 (.inst (.arith (.shift .ror rd rs (.reg rc)))) s2)
    (rel : targetStateRel riscvTarget s1 ms) :
    targetStateRel riscvTarget s2
      ((riscvAst (.inst (.arith (.shift .ror rd rs (.reg rc))))).foldl
        (fun s i => rorStep i s) ms) := by
  have g := guards rd rs rc s1 s2 hs
  have rn := reg_nonzero rd g.1
  have rsn := reg_nonzero rs g.2.1
  have rd31 := reg_scratch rd g.1
  have rs31 := reg_scratch rs g.2.1
  have bound : rd < 32 := by
    have a := g.1
    simp [asmRegOkExact,riscvConfig] at a
    exact of_decide_eq_true a.1
  have source : s2 = updPc (s1.pc + 20) (updReg rd ((readReg rs s1).rotateRight (readReg rc s1).toNat) s1) := by
    rw [shift_source_post .ror rd rs (.reg rc) s1 s2 hs]
    rfl
  have frame := ror_step_list_frame _ (kinds rd rs rc) ms rel.1
  dsimp only at frame
  have arch := ((riscvOk_iff ms).mp rel.1).2.1
  have countBound : (readReg rc s1).toNat < 64 :=
    of_decide_eq_true (shift_source_count .ror rd rs (.reg rc) s1 s2 hs)
  have rcn := reg_nonzero rc g.2.2
  have rc31 := reg_scratch rc g.2.2
  have right : ms.c_gpr ms.procID (BitVec.ofNat 5 rc) = readReg rc s1 := by
    simpa [GPR,gpr,rcn] using reg_read rc s1 ms g.2.2 rel
  have left : ms.c_gpr ms.procID (BitVec.ofNat 5 rs) = readReg rs s1 := by
    simpa [GPR,gpr,rsn] using reg_read rs s1 ms g.2.1 rel
  let final := (riscvAst (.inst (.arith (.shift .ror rd rs (.reg rc))))).foldl (fun s i => rorStep i s) ms
  rw [source]
  refine ⟨frame.1,?_,?_,?_,?_⟩
  · dsimp only [riscvTarget, updPc, updReg]
    rw [frame.2.2.2]
    simpa [riscvAst,riscvTarget] using rel.2.1
  · intro a domain
    dsimp only [riscvTarget, updPc, updReg]
    rw [frame.2.2.1]
    exact rel.2.2.1 a domain
  · intro i hi
    have ibound : i < 32 := hi.1
    have avoid := hi.2
    change [0,2,3,4,31].contains i = false at avoid
    simp at avoid
    have scratch : BitVec.ofNat 5 i ≠ 31#5 := by
      intro e
      have n := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat] at n
      norm_num at n
      rw [Nat.mod_eq_of_lt ibound] at n
      exact avoid.2.2.2.2 n
    have before := rel.2.2.2.1 i hi
    change ms.c_gpr ms.procID (BitVec.ofNat 5 i) = s1.regs i at before
    dsimp only [riscvTarget, updPc, updReg]
    by_cases eq : i = rd
    · subst i
      simp [riscvAst,List.foldl,rorStep,constStep,Run,«dfn'ORI»,«dfn'SUB»,«dfn'SLL»,«dfn'SRL»,«dfn'OR»,
        in32BitMode,curArch,architecture,MCSR,arch,GPR,gpr,«write'GPR»,«write'gpr»,holUpdate,
        rn,rsn,rcn,rd31,Ne.symm rs31,Ne.symm rc31,left,right]
      rw [BitVec.or_comm]
      simpa only [BitVec.toNat_setWidth] using masked_ror (readReg rs s1) (readReg rc s1) countBound
    · have ne : BitVec.ofNat 5 rd ≠ BitVec.ofNat 5 i := by
        intro e
        have n := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat] at n
        rw [Nat.mod_eq_of_lt bound,Nat.mod_eq_of_lt ibound] at n
        exact eq n.symm
      simp [riscvAst,List.foldl,rorStep,constStep,Run,«dfn'ORI»,«dfn'SUB»,«dfn'SLL»,«dfn'SRL»,«dfn'OR»,
        in32BitMode,curArch,architecture,MCSR,arch,GPR,gpr,«write'GPR»,«write'gpr»,holUpdate,
        rn,rsn,rcn,rd31,Ne.symm rs31,Ne.symm rc31,Ne.symm scratch,ne,eq,before]
  · intro i hi
    change i < 0 at hi
    omega


private theorem nonzero (rd rs rc : Nat)
    (guard : asmRegOkExact rd riscvConfig = true) :
    ∀ i ∈ riscvAst (.inst (.arith (.shift .ror rd rs (.reg rc)))), rorDestination i ≠ 0#5 := by
  intro i member
  simp [riscvAst] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · simp [rorDestination,constDestination]
  · simp [rorDestination]
  · simp [rorDestination]
  · simpa [rorDestination] using reg_nonzero rd guard
  · simpa [rorDestination,constDestination] using reg_nonzero rd guard

private theorem bytes_from_domain (pc : BitVec 64) (bs : List (BitVec 8))
    (m1 m2 : BitVec 64 → BitVec 8) (d : BitVec 64 → Prop)
    (bytes : bytesInMemoryHOL pc bs m1 d)
    (agree : ∀ a, d a → m2 a = m1 a) : bytesInMemoryHOL pc bs m2 d := by
  induction bs generalizing pc with
  | nil => trivial
  | cons b bs ih =>
    exact ⟨(agree pc bytes.2.1).trans bytes.1, bytes.2.1,
      ih (pc + 1) bytes.2.2⟩

/-- Full original Shift Reg/Ror constructor (560-620), including the actual five-instruction ORI31/SUB31/SLL31/SRLrd/ORrd lowering. Source count/avoid-register guards, every fetch/Next, scratch effect, PC coverage and both full original assertions are derived. This case inherits reals_as_rational_cuts, SOUNDNESS8. riscv_encoder_correct_shift_bounded (Shift.lean) assembles the full Shift constructor; whole-encoder and compiler assembly is separate. Original source step and initial target
relation only; every original environment and both assertion predicates retained. -/
theorem riscv_encoder_correct_shiftRorRegister_bounded (rd rs rc : Nat)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.inst (.arith (.shift .ror rd rs (.reg rc)))) s2 ∧
      targetStateRel riscvTarget s1 ms) :
    ∃ n : Nat, n + 1 ≤ (riscvTarget.config.encode (.inst (.arith (.shift .ror rd rs (.reg rc))))).length / 4 ∧
      ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (riscvTarget.proj s1.memDomain) →
      let pcs := allPcs (riscvTarget.config.encode (.inst (.arith (.shift .ror rd rs (.reg rc))))).length s1.pc
      asserts n (fun k s => env (n - k) (riscvTarget.next s)) ms
        (fun ms' => riscvTarget.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
          riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
        (fun ms' => targetStateRel riscvTarget s2 ms') ∧
      asserts2 (n + 1) (fun k => env (n + 1 - k)) riscvTarget.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x) := by
  let is := riscvAst (.inst (.arith (.shift .ror rd rs (.reg rc))))
  have nonempty : is ≠ [] := by simp [is,riscvAst]
  have positive : 0 < is.length := List.length_pos_iff.mpr nonempty
  refine ⟨is.length - 1, by
    rw [Flapjack.RiscV.TargetProof.Bounded.words_eq]
    exact (by omega : is.length - 1 + 1 ≤ is.length), ?_⟩
  intro env interference
  have hs : asmStep riscvConfig s1 (.inst (.arith (.shift .ror rd rs (.reg rc)))) s2 := h.1
  have kinds : ∀ i ∈ is, RorInstruction i := Bounded.kinds rd rs rc
  have nonzero : ∀ i ∈ is, rorDestination i ≠ 0#5 :=
    Bounded.nonzero rd rs rc (guards rd rs rc s1 s2 hs).1
  have pcEq : ms.c_PC ms.procID = s1.pc := h.2.2.1
  have sourceBytes : bytesInMemoryHOL s1.pc (is.flatMap riscvEncode) s1.mem s1.memDomain := hs.1
  have bytes := bytes_from_domain _ _ _ ms.MEM8 _ sourceBytes h.2.2.2.1
  rw [← pcEq] at bytes
  have projection := ror_native_execute_projection s1.memDomain is kinds nonzero env 0 ms h.2.1 bytes interference
  have pureRel := pure_relation rd rs rc s1 s2 ms hs h.2
  have finalRel : targetStateRel riscvTarget s2 (constNativeExecute env 0 is ms) :=
    (riscv_target_ok.2 _ _ s2 (by
      simpa only [shift_source_post .ror rd rs (.reg rc) s1 s2 hs, updPc, updReg, riscvTarget, is] using projection)).1.mpr pureRel
  constructor
  · let P := fun ms' => riscvTarget.stateOk ms' = true ∧
        (∀ pc, pc ∈ allPcs (riscvTarget.config.encode (.inst (.arith (.shift .ror rd rs (.reg rc))))).length s1.pc 0 →
          riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
        riscvTarget.getPc ms' ∈ allPcs (riscvTarget.config.encode (.inst (.arith (.shift .ror rd rs (.reg rc))))).length
          s1.pc riscvTarget.config.codeAlignment
    have mid : ∀ j, 0 < j → j < is.length → P (constNativeExecute env 0 (is.take j) ms) := by
      intro j lower upper
      have prefixKinds : ∀ i ∈ is.take j, RorInstruction i :=
        fun i member => kinds i (List.mem_of_mem_take member)
      have prefixNonzero : ∀ i ∈ is.take j, rorDestination i ≠ 0#5 :=
        fun i member => nonzero i (List.mem_of_mem_take member)
      have prefixBytes : bytesInMemoryHOL (ms.c_PC ms.procID)
          ((is.take j).flatMap riscvEncode) ms.MEM8 s1.memDomain := by
        have allBytes := bytes
        rw [← List.take_append_drop j is, List.flatMap_append, bytesInMemory_append] at allBytes
        exact allBytes.1
      have prefixFrame := ror_native_execute_frame s1.memDomain (is.take j)
        prefixKinds prefixNonzero env 0 ms h.2.1 prefixBytes interference
      dsimp only at prefixFrame
      refine ⟨prefixFrame.1, ?_, ?_⟩
      · intro a covered
        have domain := bytesInMemory_allPcs _ _ _ _ 0 hs.1 covered
        exact prefixFrame.2.2 a domain
      · dsimp only [P, riscvTarget]
        rw [prefixFrame.2.1, pcEq, allPcs_eq]
        refine ⟨j, ?_, ?_⟩
        · change j * 4 < (riscvEnc (.inst (.arith (.shift .ror rd rs (.reg rc))))).length
          rw [riscvEnc_length_eq]
          dsimp only [is] at upper
          omega
        · simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt upper)]
          change s1.pc + BitVec.ofNat 64 (4 * j) = s1.pc + BitVec.ofNat 64 (j * 4)
          rw [Nat.mul_comm]
    simpa only [Nat.zero_add] using
      const_asserts_of_prefixes is nonempty env 0 ms P _ mid finalRel
  · have memoryFrame := ror_native_asserts2 s1.memDomain is kinds nonzero env 0 ms h.2.1 bytes interference
    have count : is.length - 1 + 1 = is.length := by omega
    simpa only [count, Nat.zero_add, riscvTarget] using memoryFrame

end Flapjack.RiscV.TargetProof.Bounded
