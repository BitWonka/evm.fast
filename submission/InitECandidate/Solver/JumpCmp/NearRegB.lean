import Flapjack.RiscV.CorrectnessEncoding.JumpCmp.Comparison
import Flapjack.RiscV.CorrectnessEncoding.JumpCmp.Arithmetic
import InitECandidate.Solver.Common
import InitECandidate.Solver.Words
import InitECandidate.Solver.Ranges

/-! Near Reg assembly for the six non-Test comparison forms. This helper
retains the complete original existential/allenv/bothasserts conclusion, but
takes the original proof branch guards. It remains untagged; the full case
will discharge those guards and include Test/NotTest, Imm and far lowering.
Native target statements inherit reals_as_rational_cuts (SOUNDNESS section 8). -/
namespace Flapjack.RiscV.TargetProof.Bounded.JumpCmp
set_option linter.unusedSimpArgs false
open Flapjack.RiscV.TargetProof.JumpCmp Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target
theorem near_reg_simple (cmp : Cmp) (r1 r2 : Nat) (a : BitVec 64)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.jumpCmp cmp r1 (.reg r2) a) s2 ∧ targetStateRel riscvTarget s1 ms)
    (range : -4092 ≤ a.toInt ∧ a.toInt ≤ 4095)
    (simple : cmp ≠ .test ∧ cmp ≠ .notTest) :
    ∃ n : Nat, n + 1 ≤ (riscvTarget.config.encode (.jumpCmp cmp r1 (.reg r2) a)).length / 4 ∧
      ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (riscvTarget.proj s1.memDomain) →
      let pcs := allPcs (riscvTarget.config.encode (.jumpCmp cmp r1 (.reg r2) a)).length s1.pc
      asserts n (fun k s => env (n-k) (riscvTarget.next s)) ms
        (fun ms' => riscvTarget.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
          riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
        (fun ms' => targetStateRel riscvTarget s2 ms') ∧
      asserts2 (n+1) (fun k => env (n+1-k)) riscvTarget.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x) := by
  have hs : asmStep riscvConfig s1 (.jumpCmp cmp r1 (.reg r2) a) s2 := h.1
  have guard := source_guard cmp r1 (.reg r2) a hs.2.2.2.2.2.2
  have g2 : asmRegOkExact r2 riscvConfig = true := by
    simpa [asmRegImmOkExact] using guard.2.2.2
  have read1 := reg_read r1 s1 ms guard.2.2.1 h.2
  have read2 := reg_read r2 s1 ms g2 h.2
  have offset : ((a.sshiftRight 1).setWidth 12).signExtend 64 <<< (1 : Nat) = a := by
    simpa using near_offset_prefix0 a range guard.2.1
  have bounds : (18446744073709547524#64).sle a = true ∧ a.sle (4095#64) = true := by
    simp only [BitVec.sle_eq_decide,decide_eq_true_eq]
    exact range
  have enc : riscvConfig.encode (.jumpCmp cmp r1 (.reg r2) a) =
      riscvEncode (simple_branch cmp (BitVec.ofNat 5 r1) (BitVec.ofNat 5 r2) ((a.sshiftRight 1).setWidth 12)) := by
    cases cmp
    case test => exact False.elim (simple.1 rfl)
    case notTest => exact False.elim (simple.2 rfl)
    all_goals simp [riscvConfig,riscvEnc,riscvAst,inSignedRange,bounds.1,bounds.2,simple_branch]
  have hb := hs.1
  rw [enc] at hb
  have bytes := bytes_in_memory_thm () s1 ms _ _ _ _ ⟨h.2,hb⟩
  have pc := h.2.2.1
  change ms.c_PC ms.procID = s1.pc at pc
  have hn := simple_branch_next cmp (BitVec.ofNat 5 r1) (BitVec.ofNat 5 r2)
    ((a.sshiftRight 1).setWidth 12) ms h.2.1 simple
    ⟨bytes.2.2.2.2.2.1,bytes.2.2.2.2.2.2.1,
      bytes.2.2.2.2.2.2.2.1,bytes.2.2.2.2.2.2.2.2.1⟩
  let dest := if wordCmpHOL cmp (readReg r1 s1) (readReg r2 s1) then s1.pc+a else s1.pc+4
  have next : riscvTarget.next ms = Jump.branchPost ms dest := by
    change holThe (NextRISCV ms) = _
    rw [hn,offset,pc,read1,read2]
    rfl
  have initial_aligned : holAligned 2 s1.pc = true := by
    simpa [pc] using (riscvOk_iff ms).mp h.2.1 |>.2.2.2.2
  have aligned : holAligned 2 dest = true := by
    dsimp [dest]
    split
    · exact Jump.aligned_add s1.pc a initial_aligned guard.2.1
    · exact Jump.aligned_add s1.pc 4 initial_aligned (by decide)
  have post : s2 = updPc dest s1 := by
    have original := source_post cmp r1 (.reg r2) a s1 s2 hs
    rw [enc] at original
    dsimp [dest]
    split <;> rename_i chosen
    all_goals simpa [riscvEncode,regImm,chosen] using original
  have hp := Jump.branch_post_rel s1 ms dest h.2 aligned
  rw [← post] at hp
  refine ⟨0, Flapjack.RiscV.TargetProof.Bounded.one_le_words _, ?_⟩
  intro env interference
  have projection := interference 0 (Jump.branchPost ms dest)
  have transport := (riscv_target_ok.2 (env 0 (Jump.branchPost ms dest))
    (Jump.branchPost ms dest) s2
    (by simpa [post,updPc] using projection)).1
  constructor
  · simpa [asserts,next] using transport.mpr hp
  · simp only [asserts2]
    rw [next]
    exact ⟨fun _ _ => rfl,trivial⟩

end Flapjack.RiscV.TargetProof.Bounded.JumpCmp
