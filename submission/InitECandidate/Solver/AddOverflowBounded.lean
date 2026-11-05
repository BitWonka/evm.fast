import Flapjack.RiscV.CorrectnessEncoding.AddOverflow.Post
import InitECandidate.Solver.ConstAssertionsBounded
import InitECandidate.Solver.Common
import InitECandidate.Solver.Words
namespace Flapjack.RiscV.TargetProof.Bounded
open Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps Compiler.Encoders.RiscV.Target AddOverflow
set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
private theorem bytes_from_domain (pc : BitVec 64) (bs : List (BitVec 8))
    (m1 m2 : BitVec 64 → BitVec 8) (d : BitVec 64 → Prop)
    (bytes : bytesInMemoryHOL pc bs m1 d)
    (agree : ∀ a, d a → m2 a = m1 a) : bytesInMemoryHOL pc bs m2 d := by
  induction bs generalizing pc with
  | nil => trivial
  | cons b bs ih =>
    exact ⟨(agree pc bytes.2.1).trans bytes.1, bytes.2.1,
      ih (pc + 1) bytes.2.2⟩

/-- Full original six-instruction AddOverflow constructor: original source step and initial target
relation only; every original environment and both assertion predicates retained.
The XOR/XORI/ADD/XOR/AND/SRLI list retains source aliases, including r1=r4.
This native closure inherits the reviewed rational-cut limitation of the broad
RISC-V target model (SOUNDNESS section8), as the other full native encoder cases. -/
theorem riscv_encoder_correct_addoverflow_bounded (r1 r2 r3 r4 : Nat)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.inst (.arith (.addOverflow r1 r2 r3 r4))) s2 ∧
      targetStateRel riscvTarget s1 ms) :
    ∃ n : Nat, n + 1 ≤ (riscvTarget.config.encode (.inst (.arith (.addOverflow r1 r2 r3 r4)))).length / 4 ∧
      ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (riscvTarget.proj s1.memDomain) →
      let pcs := allPcs (riscvTarget.config.encode (.inst (.arith (.addOverflow r1 r2 r3 r4)))).length s1.pc
      asserts n (fun k s => env (n - k) (riscvTarget.next s)) ms
        (fun ms' => riscvTarget.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
          riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
        (fun ms' => targetStateRel riscvTarget s2 ms') ∧
      asserts2 (n + 1) (fun k => env (n + 1 - k)) riscvTarget.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x) := by
  let is := riscvAst (.inst (.arith (.addOverflow r1 r2 r3 r4)))
  have nonempty : is ≠ [] := by simp [is,riscvAst]
  have positive : 0 < is.length := List.length_pos_iff.mpr nonempty
  refine ⟨is.length - 1, by
    rw [Flapjack.RiscV.TargetProof.Bounded.words_eq]
    exact (by omega : is.length - 1 + 1 ≤ is.length), ?_⟩
  intro env interference
  have hs : asmStep riscvConfig s1 (.inst (.arith (.addOverflow r1 r2 r3 r4))) s2 := h.1
  have kinds : ∀ i ∈ is, Family i := program_family _ _ _ _
  have guards : asmRegOkExact r1 riscvConfig = true ∧ asmRegOkExact r2 riscvConfig = true ∧
      asmRegOkExact r3 riscvConfig = true ∧ asmRegOkExact r4 riscvConfig = true ∧
      r1 ≠ r3 := by
    simpa [asmOkExact,asmInstOkExact,asmArithOkExact,riscvConfig,Bool.and_eq_true,and_assoc]
      using hs.2.2.2.2.2.2
  have nz1 := (guard r1 guards.1).2.1
  have nz4 := (guard r4 guards.2.2.2.1).2.1
  have nonzero : ∀ i ∈ is, destination i ≠ 0#5 := by
    intro i member
    change i ∈ program (BitVec.ofNat 5 r1) (BitVec.ofNat 5 r2)
      (BitVec.ofNat 5 r3) (BitVec.ofNat 5 r4) at member
    simp only [program,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [destination]
    all_goals first | exact nz1 | exact nz4 | decide
  have pcEq : ms.c_PC ms.procID = s1.pc := h.2.2.1
  have sourceBytes : bytesInMemoryHOL s1.pc (is.flatMap riscvEncode) s1.mem s1.memDomain := hs.1
  have bytes := bytes_from_domain _ _ _ ms.MEM8 _ sourceBytes h.2.2.2.1
  rw [← pcEq] at bytes
  have projection := execute_projection s1.memDomain is kinds nonzero env 0 ms h.2.1 bytes interference
  have pureRel := post_relation r1 r2 r3 r4 s1 s2 ms hs h.2
  have finalRel : targetStateRel riscvTarget s2 (constNativeExecute env 0 is ms) :=
    (riscv_target_ok.2 _ _ s2 (by
      simpa only [source_post r1 r2 r3 r4 s1 s2 hs, updPc, updReg, riscvTarget, is, riscvAst, program] using projection)).1.mpr pureRel
  constructor
  · let P := fun ms' => riscvTarget.stateOk ms' = true ∧
        (∀ pc, pc ∈ allPcs (riscvTarget.config.encode (.inst (.arith (.addOverflow r1 r2 r3 r4)))).length s1.pc 0 →
          riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
        riscvTarget.getPc ms' ∈ allPcs (riscvTarget.config.encode (.inst (.arith (.addOverflow r1 r2 r3 r4)))).length
          s1.pc riscvTarget.config.codeAlignment
    have mid : ∀ j, 0 < j → j < is.length → P (constNativeExecute env 0 (is.take j) ms) := by
      intro j lower upper
      have prefixKinds : ∀ i ∈ is.take j, Family i :=
        fun i member => kinds i (List.mem_of_mem_take member)
      have prefixNonzero : ∀ i ∈ is.take j, destination i ≠ 0#5 :=
        fun i member => nonzero i (List.mem_of_mem_take member)
      have prefixBytes : bytesInMemoryHOL (ms.c_PC ms.procID)
          ((is.take j).flatMap riscvEncode) ms.MEM8 s1.memDomain := by
        have allBytes := bytes
        rw [← List.take_append_drop j is, List.flatMap_append, bytesInMemory_append] at allBytes
        exact allBytes.1
      have prefixFrame := execute_frame s1.memDomain (is.take j)
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
        · change j * 4 < (riscvEnc (.inst (.arith (.addOverflow r1 r2 r3 r4)))).length
          rw [riscvEnc_length_eq]
          dsimp only [is] at upper
          omega
        · simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt upper)]
          change s1.pc + BitVec.ofNat 64 (4 * j) = s1.pc + BitVec.ofNat 64 (j * 4)
          rw [Nat.mul_comm]
    simpa only [Nat.zero_add] using
      const_asserts_of_prefixes is nonempty env 0 ms P _ mid finalRel
  · have memoryFrame := native_asserts2 s1.memDomain is kinds nonzero env 0 ms h.2.1 bytes interference
    have count : is.length - 1 + 1 = is.length := by omega
    simpa only [count, Nat.zero_add, riscvTarget] using memoryFrame

end Flapjack.RiscV.TargetProof.Bounded
