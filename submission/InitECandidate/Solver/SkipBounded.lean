import Flapjack.Compiler.Encoders.AsmProps.EncoderCorrect
import Flapjack.RiscV.CorrectnessEncoding.BytesInMemory
import Flapjack.RiscV.CorrectnessEncoding.TargetOk
import Flapjack.RiscV.L3.Step.Evaluation
import Flapjack.RiscV.L3.Step.FetchTheorems
import InitECandidate.Solver.Common

/-! Full native Skip case of the original encoder correctness proof. Native
byte fetch, complete decoder and Run are used directly; no target run is assumed. -/
namespace Flapjack.RiscV.TargetProof.Bounded
open Flapjack.RiscV.TargetProof
open Flapjack RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target

/-- Actual emitted native Skip bytes; Flapjack infrastructure. -/
private theorem skip_encoding : riscvEnc (.inst .skip) = [19, 0, 0, 0] := by
  decide

/-- Native constant opcode reduction through the entire original decoder. -/
private theorem skip_decode : DecodeAny (.Word 19) = .ArithI (.ADDI (0, 0, 0)) := by
  decide

/-- Full original native Run leaves the state unchanged for the Skip opcode. -/
private theorem skip_run (ms : riscv_state) : Run (.ArithI (.ADDI (0, 0, 0))) ms = ms := by
  simp [Run, «dfn'ADDI», «write'GPR»]

/-- Full byte-fetch reduction from original bare-VM and four literal bytes. -/
private theorem skip_fetch (ms : riscv_state)
    (vm : (ms.c_MCSR ms.procID).mstatus.VM = 0)
    (b0 : ms.MEM8 (ms.c_PC ms.procID) = 19)
    (b1 : ms.MEM8 (ms.c_PC ms.procID + 1) = 0)
    (b2 : ms.MEM8 (ms.c_PC ms.procID + 2) = 0)
    (b3 : ms.MEM8 (ms.c_PC ms.procID + 3) = 0) :
    Fetch ms = (.Word 19, {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}) := by
  change ms.MEM8 (ms.c_PC ms.procID + 1#64) = 0#8 at b1
  change ms.MEM8 (ms.c_PC ms.procID + 2#64) = 0#8 at b2
  change ms.MEM8 (ms.c_PC ms.procID + 3#64) = 0#8 at b3
  rw [fetch_bare ms vm]
  simp [rawReadInst, boolify8, b0, b1, b2, b3, «write'Skip»]

/-- Full native post-record for actual Skip execution, with all other fields retained. -/
private def skipPost (ms : riscv_state) : riscv_state :=
  { ms with
    c_Skip := holUpdate ms.procID 4 ms.c_Skip
    c_PC := holUpdate ms.procID (ms.c_PC ms.procID + 4) ms.c_PC }

/-- Actual native Next result derived from source validity and four emitted bytes. -/
private theorem skip_next (ms : riscv_state) (ok : riscvOk ms = true)
    (b0 : ms.MEM8 (ms.c_PC ms.procID) = 19)
    (b1 : ms.MEM8 (ms.c_PC ms.procID + 1) = 0)
    (b2 : ms.MEM8 (ms.c_PC ms.procID + 2) = 0)
    (b3 : ms.MEM8 (ms.c_PC ms.procID + 3) = 0) :
    NextRISCV ms = some (skipPost ms) := by
  have fields := (riscvOk_iff ms).mp ok
  have hf := skip_fetch ms fields.1 b0 b1 b2 b3
  have hn := nextRISCV ms (.Word 19)
    {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}
    (.ArithI (.ADDI (0, 0, 0)))
    {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip}
    ⟨hf, skip_decode, skip_run _, fields.2.2.2.1, fields.2.2.1⟩
  simpa [update_pc, «write'PC», Skip, PC, holUpdate, skipPost] using hn

/-- Flapjack source-alignment arithmetic used only to discharge post-state validity. -/
private theorem aligned_add_four (pc : BitVec 64) (h : holAligned 2 pc = true) :
    holAligned 2 (pc + 4) = true := by
  have he := congrArg BitVec.toNat (of_decide_eq_true h)
  rw [holAlign_eq_div] at he
  simp only [BitVec.toNat_ofNat] at he
  change decide (holAlign 2 (pc + 4) = pc + 4) = true
  apply decide_eq_true
  apply BitVec.eq_of_toNat_eq
  rw [holAlign_eq_div]
  simp only [BitVec.toNat_ofNat, BitVec.toNat_add]
  have four : (4 : BitVec 64).toNat = 4 := by decide
  rw [four]
  norm_num at *
  have bound := pc.isLt
  omega

/-- Flapjack intermediate native post-relation, derived rather than assumed. -/
private theorem skip_post_rel (s : AsmState 64) (ms : riscv_state)
    (hr : targetStateRel riscvTarget s ms) :
    targetStateRel riscvTarget (updPc (s.pc + 4) s) (skipPost ms) := by
  rcases hr with ⟨ok, pc, mem, regs, fp⟩
  have fields := (riscvOk_iff ms).mp ok
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply (riscvOk_iff _).mpr
    simpa [skipPost, holUpdate] using
      ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1,
       aligned_add_four _ fields.2.2.2.2⟩
  · change (skipPost ms).c_PC (skipPost ms).procID = s.pc + 4
    change ms.c_PC ms.procID = s.pc at pc
    simp [skipPost, holUpdate, pc]
  · exact mem
  · exact regs
  · intro i hi
    change i < 0 at hi
    omega

/-- Full Skip constructor case under the original source-step hypotheses.
The intermediate assertion is retained even though the original zero witness
makes its recursive base use only the final relation, as in the original next_tac
Skip case. Full source comparison: asmProps encoder_correct_def117-133 and
riscv_targetProofScript512-530; native validity, domain, arbitrary state fields,
all environments, original code-byte/PC assertion, and outside-domain memory
conclusion are retained. No target evaluation is assumed. -/
theorem riscv_encoder_correct_skip_bounded (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.inst .skip) s2 ∧
      targetStateRel riscvTarget s1 ms) :
    ∃ n : Nat, n + 1 ≤ (riscvTarget.config.encode (.inst .skip)).length / 4 ∧
      ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (riscvTarget.proj s1.memDomain) →
      let pcs := allPcs (riscvTarget.config.encode (.inst .skip)).length s1.pc
      asserts n (fun k s => env (n - k) (riscvTarget.next s)) ms
        (fun ms' => riscvTarget.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
          riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
        (fun ms' => targetStateRel riscvTarget s2 ms') ∧
      asserts2 (n + 1) (fun k => env (n + 1 - k)) riscvTarget.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x) := by
  have hs := h.1
  change asmStep riscvConfig s1 (.inst .skip) s2 at hs
  have enc : riscvConfig.encode (.inst .skip) = [19, 0, 0, 0] := skip_encoding
  have hb := hs.1
  rw [enc] at hb
  have bytes := bytes_in_memory_thm () s1 ms 19 0 0 0 ⟨h.2, hb⟩
  have hn := skip_next ms h.2.1 bytes.2.2.2.2.2.1
    bytes.2.2.2.2.2.2.1 bytes.2.2.2.2.2.2.2.1 bytes.2.2.2.2.2.2.2.2.1
  have next : riscvTarget.next ms = skipPost ms := by
    change holThe (NextRISCV ms) = skipPost ms
    rw [hn]
    rfl
  have he : s2 = updPc (s1.pc + 4) s1 := by
    have step := hs.2.2.2.2.1
    rw [enc] at step
    simpa [asmUpd, instUpd] using step.symm
  subst s2
  refine ⟨0, Flapjack.RiscV.TargetProof.Bounded.one_le_words _, ?_⟩
  intro env interference
  have hp := skip_post_rel s1 ms h.2
  have projection := interference 0 (skipPost ms)
  have transport := (riscv_target_ok.2 (env 0 (skipPost ms)) (skipPost ms)
    (updPc (s1.pc + 4) s1) projection).1
  constructor
  · simpa [asserts, next] using transport.mpr hp
  · simp only [asserts2]
    rw [next]
    exact ⟨fun _ _ => rfl, trivial⟩

end Flapjack.RiscV.TargetProof.Bounded
