import InitECandidate.Proofs.BootstrapAsmComposition
import InitECandidate.Solver.CompleteB
import InitECandidate.Solver.AsmStepEvaluateB

/-! Bounded bootstrap clock (EVM.fast K certificate, route 1).
The original `checked_trace_evaluator` returns an existential clock `count` with only a lower bound.
Here every assembler step uses the step-bounded encoder correctness, so `count` is bounded by the
total number of 4-byte words of the executed instruction list. -/
namespace InitECandidate.Proofs.Bounded
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps
open InitECandidate.Proofs.BootstrapSteps InitECandidate.Proofs.BootstrapCopy
open InitECandidate.Proofs.BootstrapAsmComposition

/-- Total encoded words of an instruction list: the machine-step budget of its straight-line run. -/
def words (code : List (HolAsm 64)) : Nat := (code.map fun i => (riscvEnc i).length / 4).sum

theorem step_evaluator_bounded {σ : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (s : AsmState 64) (ms : riscv_state) (io : HolFfiState σ) (i : HolAsm 64)
    (target : mc.target = riscvTarget)
    (domain : mc.progAddresses = s.memDomain)
    (disjoint : ffiEntryPcsDisjoint mc s (riscvEnc i).length)
    (interference : interferenceOk mc.nextInterfer (mc.target.proj s.memDomain))
    (step : asmStep riscvConfig s i (after s i))
    (related : targetStateRel riscvTarget s ms) :
    ∃ l ms2, l ≤ (riscvEnc i).length / 4 ∧
      (∀ k, evaluateTargetHOL mc io (k + l) ms =
        evaluateTargetHOL (shiftInterfer l mc) io k ms2) ∧
      targetStateRel riscvTarget (after s i) ms2 ∧ l ≠ 0 := by
  have h := Bounded.asmStepImpEvaluateOnlyBounded mc s ms io i
    ⟨by rw [target]; exact Flapjack.RiscV.TargetProof.Bounded.riscv_encoder_correct_bounded,
      domain, by simpa only [target, riscvTarget, riscvConfig_encode] using disjoint, interference,
      by simpa only [target, riscvTarget, riscvConfig_encode, after] using step, by simpa [target] using related⟩
  simpa only [target, riscvTarget, riscvConfig_encode, after] using h

theorem checked_trace_evaluator_bounded {σ : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (target : mc.target = riscvTarget)
    (identity : mc.nextInterfer = fun _ state => state)
    (code : List (HolAsm 64)) (s : AsmState 64)
    (checks : Checked code s) (guards : EvaluatorGuards mc code s)
    (ms : riscv_state) (io : HolFfiState σ)
    (related : targetStateRel riscvTarget s ms) :
    ∃ count post, count ≤ words code ∧
      (∀ clock, evaluateTargetHOL mc io (count + clock) ms =
        evaluateTargetHOL mc io clock post) ∧
      targetStateRel riscvTarget (run code s) post := by
  induction code generalizing s ms with
  | nil =>
    exact ⟨0, ms, Nat.zero_le _, fun _ => by simp only [Nat.zero_add], related⟩
  | cons i rest ih =>
    have interference : interferenceOk mc.nextInterfer (mc.target.proj s.memDomain) := by
      intro index state
      rw [identity]
    obtain ⟨firstCount, middle, firstLe, firstRun, middleRelated, _⟩ :=
      step_evaluator_bounded mc s ms io i target guards.1 guards.2.1 interference checks.1 related
    have shiftEq := shiftInterfer_identity mc identity firstCount
    simp only [shiftEq] at firstRun
    obtain ⟨restCount, post, restLe, restRun, postRelated⟩ :=
      ih (after s i) checks.2 guards.2.2 middle middleRelated
    refine ⟨firstCount + restCount, post, ?_, ?_, postRelated⟩
    · simp only [words, List.map_cons, List.sum_cons] at restLe ⊢
      omega
    · intro clock
      rw [show firstCount + restCount + clock = (restCount + clock) + firstCount by omega,
        firstRun, restRun]

end InitECandidate.Proofs.Bounded
