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

private theorem guards (rd rs : Nat) (c : BitVec 64) (s1 s2 : AsmState 64)
    (hs : asmStep riscvConfig s1 (.inst (.arith (.shift .ror rd rs (.imm c)))) s2) :
    asmRegOkExact rd riscvConfig = true ∧ asmRegOkExact rs riscvConfig = true ∧
    c.toNat < 64 ∧ 0 < c.toNat := by
  have g := hs.2.2.2.2.2.2
  simp [asmOkExact, asmInstOkExact, asmArithOkExact, riscvConfig,
    Bool.and_eq_true, and_assoc] at g
  refine ⟨g.1,g.2.1,g.2.2.2,?_⟩
  have nonzero := g.2.2.1
  by_contra h
  have zero : c = 0 := BitVec.eq_of_toNat_eq (by simp; omega)
  exact nonzero zero

private theorem kinds (rd rs : Nat) (c : BitVec 64) :
    ∀ i ∈ riscvAst (.inst (.arith (.shift .ror rd rs (.imm c)))), RorInstruction i := by
  intro i hi
  simp [riscvAst] at hi
  rcases hi with rfl | rfl | rfl
  · exact .srli _ _ _
  · exact .prior _ (.slli _ _ _)
  · exact .prior _ (.or _ _ _)

/-- Local full source/native postrelation assembly. No named HOL original is
claimed for this intermediate consequence; the full case theorem supplies
original interference and both assertion predicates separately. -/
private theorem pure_relation (rd rs : Nat) (c : BitVec 64) (s1 s2 : AsmState 64)
    (ms : riscv_state)
    (hs : asmStep riscvConfig s1 (.inst (.arith (.shift .ror rd rs (.imm c)))) s2)
    (rel : targetStateRel riscvTarget s1 ms) :
    targetStateRel riscvTarget s2
      ((riscvAst (.inst (.arith (.shift .ror rd rs (.imm c))))).foldl
        (fun s i => rorStep i s) ms) := by
  have g := guards rd rs c s1 s2 hs
  have rn := reg_nonzero rd g.1
  have rsn := reg_nonzero rs g.2.1
  have rd31 := reg_scratch rd g.1
  have rs31 := reg_scratch rs g.2.1
  have bound : rd < 32 := by
    have a := g.1
    simp [asmRegOkExact,riscvConfig] at a
    exact of_decide_eq_true a.1
  have source : s2 = updPc (s1.pc + 12) (updReg rd ((readReg rs s1).rotateRight c.toNat) s1) := by
    rw [shift_source_post .ror rd rs (.imm c) s1 s2 hs]
    rfl
  have frame := ror_step_list_frame _ (kinds rd rs c) ms rel.1
  dsimp only at frame
  have arch := ((riscvOk_iff ms).mp rel.1).2.1
  have count : (BitVec.ofNat 6 c.toNat).toNat = c.toNat := by
    simp [Nat.mod_eq_of_lt g.2.2.1]
  have complement : (BitVec.ofNat 6 (64-c.toNat)).toNat = 64-c.toNat := by
    simp [Nat.mod_eq_of_lt (show 64-c.toNat < 64 by omega)]
  have left : ms.c_gpr ms.procID (BitVec.ofNat 5 rs) = readReg rs s1 := by
    simpa [GPR,gpr,rsn] using reg_read rs s1 ms g.2.1 rel
  let final := (riscvAst (.inst (.arith (.shift .ror rd rs (.imm c))))).foldl (fun s i => rorStep i s) ms
  rw [source]
  refine ⟨frame.1,?_,?_,?_,?_⟩
  · change final.c_PC final.procID = s1.pc+12
    rw [frame.2.2.2]
    simpa [riscvAst,riscvTarget] using rel.2.1
  · intro a domain
    change final.MEM8 a = s1.mem a
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
    change final.c_gpr final.procID (BitVec.ofNat 5 i) =
      if i = rd then (readReg rs s1).rotateRight c.toNat else s1.regs i
    by_cases eq : i = rd
    · subst i
      simp [final,riscvAst,List.foldl,rorStep,constStep,Run,«dfn'SRLI»,«dfn'SLLI»,«dfn'OR»,
        in32BitMode,curArch,architecture,MCSR,arch,GPR,gpr,«write'GPR»,«write'gpr»,holUpdate,
        rn,rsn,rd31,Ne.symm rs31,complement,left,Nat.mod_eq_of_lt g.2.2.1,ror _ _ g.2.2.1]
    · have ne : BitVec.ofNat 5 rd ≠ BitVec.ofNat 5 i := by
        intro e
        have n := congrArg BitVec.toNat e
        simp only [BitVec.toNat_ofNat] at n
        rw [Nat.mod_eq_of_lt bound,Nat.mod_eq_of_lt ibound] at n
        exact eq n.symm
      simp [final,riscvAst,List.foldl,rorStep,constStep,Run,«dfn'SRLI»,«dfn'SLLI»,«dfn'OR»,
        in32BitMode,curArch,architecture,MCSR,arch,GPR,gpr,«write'GPR»,«write'gpr»,holUpdate,
        rn,rsn,rd31,Ne.symm rs31,Ne.symm scratch,ne,eq,before]
  · intro i hi
    change i < 0 at hi
    omega


private theorem nonzero (rd rs : Nat) (c : BitVec 64)
    (guard : asmRegOkExact rd riscvConfig = true) :
    ∀ i ∈ riscvAst (.inst (.arith (.shift .ror rd rs (.imm c)))), rorDestination i ≠ 0#5 := by
  intro i member
  simp [riscvAst] at member
  rcases member with rfl | rfl | rfl
  · simp [rorDestination]
  · simpa [rorDestination,constDestination] using reg_nonzero rd guard
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

/-- Full original Shift Imm/Ror constructor (560-620), including the actual three-instruction SRLI31/SLLIrd/ORrd lowering. Source count/avoid-register guards, every fetch/Next, scratch effect, PC coverage and both full original assertions are derived. This case inherits reals_as_rational_cuts, SOUNDNESS8. The Reg/Ror case is riscv_encoder_correct_shiftRorRegister_bounded, and riscv_encoder_correct_shift_bounded (Shift.lean) assembles every Shift case.: original source step and initial target
relation only; every original environment and both assertion predicates retained. -/
theorem riscv_encoder_correct_shiftRorImmediate_bounded (rd rs : Nat) (c : BitVec 64)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.inst (.arith (.shift .ror rd rs (.imm c)))) s2 ∧
      targetStateRel riscvTarget s1 ms) :
    ∃ n : Nat, n + 1 ≤ (riscvTarget.config.encode (.inst (.arith (.shift .ror rd rs (.imm c))))).length / 4 ∧
      ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (riscvTarget.proj s1.memDomain) →
      let pcs := allPcs (riscvTarget.config.encode (.inst (.arith (.shift .ror rd rs (.imm c))))).length s1.pc
      asserts n (fun k s => env (n - k) (riscvTarget.next s)) ms
        (fun ms' => riscvTarget.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
          riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
        (fun ms' => targetStateRel riscvTarget s2 ms') ∧
      asserts2 (n + 1) (fun k => env (n + 1 - k)) riscvTarget.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x) := by
  let is := riscvAst (.inst (.arith (.shift .ror rd rs (.imm c))))
  have nonempty : is ≠ [] := by simp [is,riscvAst]
  have positive : 0 < is.length := List.length_pos_iff.mpr nonempty
  refine ⟨is.length - 1, by
    rw [Flapjack.RiscV.TargetProof.Bounded.words_eq]
    exact (by omega : is.length - 1 + 1 ≤ is.length), ?_⟩
  intro env interference
  have hs : asmStep riscvConfig s1 (.inst (.arith (.shift .ror rd rs (.imm c)))) s2 := h.1
  have kinds : ∀ i ∈ is, RorInstruction i := Bounded.kinds rd rs c
  have nonzero : ∀ i ∈ is, rorDestination i ≠ 0#5 :=
    Bounded.nonzero rd rs c (guards rd rs c s1 s2 hs).1
  have pcEq : ms.c_PC ms.procID = s1.pc := h.2.2.1
  have sourceBytes : bytesInMemoryHOL s1.pc (is.flatMap riscvEncode) s1.mem s1.memDomain := hs.1
  have bytes := bytes_from_domain _ _ _ ms.MEM8 _ sourceBytes h.2.2.2.1
  rw [← pcEq] at bytes
  have projection := ror_native_execute_projection s1.memDomain is kinds nonzero env 0 ms h.2.1 bytes interference
  have pureRel := pure_relation rd rs c s1 s2 ms hs h.2
  have finalRel : targetStateRel riscvTarget s2 (constNativeExecute env 0 is ms) :=
    (riscv_target_ok.2 _ _ s2 (by
      simpa only [shift_source_post .ror rd rs (.imm c) s1 s2 hs, updPc, updReg, riscvTarget, is] using projection)).1.mpr pureRel
  constructor
  · let P := fun ms' => riscvTarget.stateOk ms' = true ∧
        (∀ pc, pc ∈ allPcs (riscvTarget.config.encode (.inst (.arith (.shift .ror rd rs (.imm c))))).length s1.pc 0 →
          riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
        riscvTarget.getPc ms' ∈ allPcs (riscvTarget.config.encode (.inst (.arith (.shift .ror rd rs (.imm c))))).length
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
      · change (constNativeExecute env 0 (is.take j) ms).c_PC
          (constNativeExecute env 0 (is.take j) ms).procID ∈ _
        rw [prefixFrame.2.1, pcEq, allPcs_eq]
        refine ⟨j, ?_, ?_⟩
        · change j * 4 < (riscvEnc (.inst (.arith (.shift .ror rd rs (.imm c))))).length
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
