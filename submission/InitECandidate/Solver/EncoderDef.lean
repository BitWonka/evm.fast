import Flapjack.Compiler.Encoders.AsmProps.EncoderCorrect

/-! Step-bounded encoder correctness (EVM.fast K certificate, route 1).
Identical to flapjack's `encoderCorrect`, except that the machine-step witness `n` of each ASM
instruction is bounded by the number of 4-byte words of its encoding. -/
namespace Flapjack.Compiler.Encoders.AsmProps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem

noncomputable def encoderCorrectBounded {width : Nat} [NeZero width] {β γ : Type}
    (t : HolAsmTarget width β γ) : Prop :=
  targetOk t ∧
    ∀ (s1 : AsmState width) (i : HolAsm width) (s2 : AsmState width) (ms : β),
      asmStep t.config s1 i s2 ∧ targetStateRel t s1 ms →
      ∃ n : Nat, n + 1 ≤ (t.config.encode i).length / 4 ∧
        ∀ env : Nat → β → β,
        interferenceOk env (t.proj s1.memDomain) →
        let pcs := allPcs (t.config.encode i).length s1.pc
        asserts n (fun k s => env (n - k) (t.next s)) ms
            (fun ms' => t.stateOk ms' = true ∧
              (∀ pc, pc ∈ pcs 0 → t.getByte ms' pc = t.getByte ms pc) ∧
              t.getPc ms' ∈ pcs t.config.codeAlignment)
            (fun ms' => targetStateRel t s2 ms') ∧
          asserts2 (n + 1) (fun k => env (n + 1 - k)) t.next ms
            (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x → t.getByte ms1 x = t.getByte ms2 x)

theorem encoderCorrect_of_bounded {width : Nat} [NeZero width] {β γ : Type}
    {t : HolAsmTarget width β γ} (h : encoderCorrectBounded t) : encoderCorrect t := by
  refine ⟨h.1, ?_⟩
  intro s1 i s2 ms hs
  obtain ⟨n, _, hn⟩ := h.2 s1 i s2 ms hs
  exact ⟨n, hn⟩

end Flapjack.Compiler.Encoders.AsmProps
