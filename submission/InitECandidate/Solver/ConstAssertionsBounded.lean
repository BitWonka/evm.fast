import Flapjack.RiscV.CorrectnessEncoding.TargetOk
import Flapjack.RiscV.CorrectnessEncoding.ConstRelation
import Flapjack.Compiler.Encoders.AsmProps.PcCoverage
import InitECandidate.Solver.Common
import InitECandidate.Solver.Words

namespace Flapjack.RiscV.TargetProof.Bounded
open Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 Compiler.Encoders.Asm Compiler.Encoders.AsmSem
  Compiler.Encoders.AsmProps Compiler.Encoders.RiscV.Target
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

private theorem const32_dest_nonzero (r : BitVec 5) (c : BitVec 32)
    (rn : r ≠ 0#5) : ∀ i ∈ riscvConst32 r c, constDestination i ≠ 0#5 := by
  simp only [riscvConst32]
  split
  all_goals
    intro i member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simpa only [constDestination] using rn

/-- Every emitted Const destination is nonzero, derived from original asm_ok.
All original lowering branches and constants are retained. Untagged infrastructure. -/
theorem const_dest_nonzero (r : Nat) (c : BitVec 64)
    (ok : asmOkExact (.inst (.const r c)) riscvConfig = true) :
    ∀ i ∈ riscvAst (.inst (.const r c)), constDestination i ≠ 0#5 := by
  have guard : r < 32 ∧ r ≠ 0 := by
    have g := ok
    simp only [asmOkExact, asmInstOkExact, asmRegOkExact, Bool.and_eq_true] at g
    have avoid := g.2
    simp [riscvConfig] at avoid
    exact ⟨of_decide_eq_true g.1, avoid.1⟩
  have rn : BitVec.ofNat 5 r ≠ 0#5 := by
    intro e
    have n := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at n
    norm_num at n
    rw [Nat.mod_eq_of_lt guard.1] at n
    exact guard.2 n
  simp only [riscvAst]
  split
  · intro i member
    simp only [List.mem_singleton] at member
    subst i
    exact rn
  · split
    · exact const32_dest_nonzero _ _ rn
    · split
      all_goals
        intro i member
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with (member | member) | (rfl | rfl)
        · exact const32_dest_nonzero _ _ (by decide) i member
        · exact const32_dest_nonzero _ _ rn i member
        · exact rn
        · exact rn

/-- Generic assertion-counter assembly for the actual native iterator. Prefix
properties and the final property are supplied by separate execution proofs;
this untagged logical lemma is not a correctness port or a target-run assumption. -/
theorem const_asserts_of_prefixes (is : List instruction)
    (nonempty : is ≠ []) (env : Nat → riscv_state → riscv_state)
    (index : Nat) (ms : riscv_state) (P Q : riscv_state → Prop)
    (mid : ∀ j, 0 < j → j < is.length →
      P (constNativeExecute env index (is.take j) ms))
    (final : Q (constNativeExecute env index is ms)) :
    asserts (is.length - 1)
      (fun k s => env (index + (is.length - 1) - k) (riscvTarget.next s)) ms P Q := by
  induction is generalizing index ms with
  | nil => exact (nonempty rfl).elim
  | cons i is ih =>
    by_cases empty : is = []
    · subst is
      simpa [asserts, constNativeExecute] using final
    · have positive : 0 < is.length := List.length_pos_iff.mpr empty
      have first := mid 1 (by omega) (by simp only [List.length_cons]; omega)
      have tailMid : ∀ j, 0 < j → j < is.length →
          P (constNativeExecute env (index + 1) (is.take j)
            (env index (riscvTarget.next ms))) := by
        intro j pos bound
        have prefixResult := mid (j + 1) (by omega) (by simp only [List.length_cons]; omega)
        simpa only [List.take_succ_cons, constNativeExecute] using prefixResult
      have tailFinal : Q (constNativeExecute env (index + 1) is
          (env index (riscvTarget.next ms))) := by
        simpa only [constNativeExecute] using final
      have tail := ih empty (index + 1) _ tailMid tailFinal
      have length : (i :: is).length - 1 = (is.length - 1) + 1 := by
        simp only [List.length_cons]
        omega
      have counter : index + 1 + (is.length - 1) = index + (is.length - 1 + 1) := by omega
      rw [length, asserts]
      have firstIndex : index + (is.length - 1 + 1) - (is.length - 1 + 1) = index := by omega
      rw [firstIndex]
      refine ⟨?_, ?_⟩
      · simpa only [List.take_succ_cons, List.take_zero, constNativeExecute] using first
      · simpa only [counter] using tail

private theorem bytes_from_domain (pc : BitVec 64) (bs : List (BitVec 8))
    (m1 m2 : BitVec 64 → BitVec 8) (d : BitVec 64 → Prop)
    (bytes : bytesInMemoryHOL pc bs m1 d)
    (agree : ∀ a, d a → m2 a = m1 a) : bytesInMemoryHOL pc bs m2 d := by
  induction bs generalizing pc with
  | nil => trivial
  | cons b bs ih =>
    exact ⟨(agree pc bytes.2.1).trans bytes.1, bytes.2.1,
      ih (pc + 1) bytes.2.2⟩

/-- Full original Const constructor: original source step and initial target
relation only; every original environment and both assertion predicates retained. -/
theorem riscv_encoder_correct_const_bounded (r : Nat) (c : BitVec 64)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.inst (.const r c)) s2 ∧
      targetStateRel riscvTarget s1 ms) :
    ∃ n : Nat, n + 1 ≤ (riscvTarget.config.encode (.inst (.const r c))).length / 4 ∧
      ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (riscvTarget.proj s1.memDomain) →
      let pcs := allPcs (riscvTarget.config.encode (.inst (.const r c))).length s1.pc
      asserts n (fun k s => env (n - k) (riscvTarget.next s)) ms
        (fun ms' => riscvTarget.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
          riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
        (fun ms' => targetStateRel riscvTarget s2 ms') ∧
      asserts2 (n + 1) (fun k => env (n + 1 - k)) riscvTarget.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x) := by
  let is := riscvAst (.inst (.const r c))
  have nonempty : is ≠ [] := const_register_nonempty r c
  have positive : 0 < is.length := List.length_pos_iff.mpr nonempty
  refine ⟨is.length - 1, by
    rw [Flapjack.RiscV.TargetProof.Bounded.words_eq]
    exact (by omega : is.length - 1 + 1 ≤ is.length), ?_⟩
  intro env interference
  have hs : asmStep riscvConfig s1 (.inst (.const r c)) s2 := h.1
  have kinds : ∀ i ∈ is, ConstRegisterInstruction i := const_register_family r c
  have nonzero : ∀ i ∈ is, constDestination i ≠ 0#5 :=
    const_dest_nonzero r c hs.2.2.2.2.2.2
  have pcEq : ms.c_PC ms.procID = s1.pc := h.2.2.1
  have sourceBytes : bytesInMemoryHOL s1.pc (is.flatMap riscvEncode) s1.mem s1.memDomain := hs.1
  have bytes := bytes_from_domain _ _ _ ms.MEM8 _ sourceBytes h.2.2.2.1
  rw [← pcEq] at bytes
  have projection := const_native_execute_projection s1.memDomain is kinds nonzero env 0 ms h.2.1 bytes interference
  have pureRel := const_step_post_relation r c s1 s2 ms hs h.2
  have finalRel : targetStateRel riscvTarget s2 (constNativeExecute env 0 is ms) :=
    (riscv_target_ok.2 _ _ s2 (by
      simpa only [const_source_post r c s1 s2 hs, updPc, updReg, riscvTarget, is] using projection)).1.mpr pureRel
  constructor
  · let P := fun ms' => riscvTarget.stateOk ms' = true ∧
        (∀ pc, pc ∈ allPcs (riscvTarget.config.encode (.inst (.const r c))).length s1.pc 0 →
          riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
        riscvTarget.getPc ms' ∈ allPcs (riscvTarget.config.encode (.inst (.const r c))).length
          s1.pc riscvTarget.config.codeAlignment
    have mid : ∀ j, 0 < j → j < is.length → P (constNativeExecute env 0 (is.take j) ms) := by
      intro j lower upper
      have prefixKinds : ∀ i ∈ is.take j, ConstRegisterInstruction i :=
        fun i member => kinds i (List.mem_of_mem_take member)
      have prefixNonzero : ∀ i ∈ is.take j, constDestination i ≠ 0#5 :=
        fun i member => nonzero i (List.mem_of_mem_take member)
      have prefixBytes : bytesInMemoryHOL (ms.c_PC ms.procID)
          ((is.take j).flatMap riscvEncode) ms.MEM8 s1.memDomain := by
        have allBytes := bytes
        rw [← List.take_append_drop j is, List.flatMap_append, bytesInMemory_append] at allBytes
        exact allBytes.1
      have prefixFrame := const_native_execute_frame s1.memDomain (is.take j)
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
        · change j * 4 < (riscvEnc (.inst (.const r c))).length
          rw [riscvEnc_length_eq]
          dsimp only [is] at upper
          omega
        · simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt upper)]
          change s1.pc + BitVec.ofNat 64 (4 * j) = s1.pc + BitVec.ofNat 64 (j * 4)
          rw [Nat.mul_comm]
    simpa only [Nat.zero_add] using
      const_asserts_of_prefixes is nonempty env 0 ms P _ mid finalRel
  · have memoryFrame := const_native_asserts2 s1.memDomain is kinds nonzero env 0 ms h.2.1 bytes interference
    have count : is.length - 1 + 1 = is.length := by omega
    simpa only [count, Nat.zero_add, riscvTarget] using memoryFrame

end Flapjack.RiscV.TargetProof.Bounded
