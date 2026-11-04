import Flapjack.RiscV.CorrectnessEncoding.MemoryFetch
import Flapjack.RiscV.CorrectnessEncoding.MemoryRelation
import Flapjack.RiscV.CorrectnessEncoding.MemoryFrame
import Flapjack.RiscV.CorrectnessEncoding.TargetOk
import Flapjack.Compiler.Encoders.AsmProps.Assertions
import InitECandidate.Solver.Common

namespace Flapjack.RiscV.TargetProof.Bounded
open Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmSem Compiler.Encoders.AsmProps Compiler.Encoders.RiscV.Target
set_option autoImplicit false

/-- Source memory operations preserve their domain even when an assertion fails.
Local frame infrastructure; no separately named HOL declaration is claimed. -/
theorem memory_source_post_domain (m : HolMemop) (r base : Nat) (w : BitVec 64)
    (s s' : AsmState 64)
    (step : asmStep riscvConfig s (.inst (.mem m r (.addr base w))) s') :
    s'.memDomain = s.memDomain := by
  rw [memory_source_post m r base w s s' step]
  change (memOp m r (.addr base w) s).memDomain = s.memDomain
  cases m
  all_goals simp only [memOp]
  all_goals first
    | exact (source_memload_frame _ _ _ _).2.1
    | exact (source_memstore_frame _ _ _ _).1

/-- Full original Mem constructor over the actual native Next evaluator.
Both original assertion predicates and every projection-preserving environment
are retained. The native RISC-V model inherits the rational-cut rendering
limitation recorded in SOUNDNESS section 8. -/
theorem riscv_encoder_correct_mem_bounded (m : HolMemop) (r base : Nat) (w : BitVec 64)
    (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.inst (.mem m r (.addr base w))) s2 ∧
      targetStateRel riscvTarget s1 ms) :
    ∃ n : Nat, n + 1 ≤ (riscvTarget.config.encode (.inst (.mem m r (.addr base w)))).length / 4 ∧
      ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (riscvTarget.proj s1.memDomain) →
      let pcs := allPcs (riscvTarget.config.encode (.inst (.mem m r (.addr base w)))).length s1.pc
      asserts n (fun k s => env (n - k) (riscvTarget.next s)) ms
        (fun ms' => riscvTarget.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
          riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
        (fun ms' => targetStateRel riscvTarget s2 ms') ∧
      asserts2 (n + 1) (fun k => env (n + 1 - k)) riscvTarget.next ms
        (fun before after => ∀ x, ¬ s1.memDomain x →
          riscvTarget.getByte before x = riscvTarget.getByte after x) := by
  refine ⟨0, Flapjack.RiscV.TargetProof.Bounded.one_le_words _, ?_⟩
  intro env interference
  have step : asmStep riscvConfig s1 (.inst (.mem m r (.addr base w))) s2 := h.1
  let native : instruction := match riscvMemop m with
    | .inl f => .Load (f (BitVec.ofNat 5 r, BitVec.ofNat 5 base, w.setWidth 12))
    | .inr f => .Store (f (BitVec.ofNat 5 base, BitVec.ofNat 5 r, w.setWidth 12))
  have emitted : native ∈ riscvAst (.inst (.mem m r (.addr base w))) := by
    cases m <;> simp [native, riscvAst, riscvMemop]
  have kind : MemoryInstruction native := by
    cases m <;> simp only [native, riscvMemop] <;> constructor
  have next : riscvTarget.next ms = memoryStep native ms := by
    change holThe (NextRISCV ms) = _
    rw [memory_source_next m r base w s1 s2 ms native step h.2 emitted]
    rfl
  have pureRelation := memory_step_post_relation m r base w s1 s2 ms native step h.2 emitted
  have domain := memory_source_post_domain m r base w s1 s2 step
  have projection : riscvTarget.proj s2.memDomain (env 0 (memoryStep native ms)) =
      riscvTarget.proj s2.memDomain (memoryStep native ms) := by
    rw [domain]
    exact interference 0 _
  have finalRelation : targetStateRel riscvTarget s2 (env 0 (memoryStep native ms)) :=
    (riscv_target_ok.2 _ _ s2 projection).1.mpr pureRelation
  constructor
  · simpa only [asserts, Nat.sub_self, next] using finalRelation
  · simp only [asserts2, next, and_true]
    intro x outside
    change ms.MEM8 x = (memoryStep native ms).MEM8 x
    rw [(memory_step_data_frame native kind ms h.2.1).1]
    exact (memory_run_outside_source_domain m r base w s1 s2 ms native
      step h.2 emitted x outside).symm

end Flapjack.RiscV.TargetProof.Bounded
