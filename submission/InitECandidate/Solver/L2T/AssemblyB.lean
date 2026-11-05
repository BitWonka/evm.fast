import Flapjack.Compiler.Backend.LabToTarget.CompileCorrect.Assembly
import InitECandidate.Solver.L2T.AsmB
import InitECandidate.Solver.L2T.ControlB
import InitECandidate.Solver.L2T.CbwB
import InitECandidate.Solver.L2T.CallFfiB
import InitECandidate.Solver.L2T.ShareMemB

/-! Step-bounded `compile_correct` for LabToTarget (EVM.fast K certificate): for lab code without
`Install` lines whose target lines are at most `4 * W` bytes, a lab run with clock `c` is matched by
a target run within `(W + 1) * c` evaluator steps. Strong induction on the lab clock, as in the
original `compileCorrectFor_all`. -/
namespace Flapjack.Compiler.Backend.LabToTarget.Bounded
open Flapjack Flapjack.Compiler.Encoders Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.AsmSem Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabToTarget

/-- The lab code never fetches an `Install` line (true of Pancake output). -/
def NoInstall {width : Nat} [NeZero width] (code : LabProgHOL width) : Prop :=
  ∀ pc w bytes n, asmFetchAux pc code ≠ some (.labAsm .install w bytes n)

theorem shareMemLoad_ret_code {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (address : HolAddr width)
    (state next : LabSem.State width C F)
    (size : Nat) (ffi : HolFfiState F) (bytes : List (BitVec 8))
    (h : shareMemLoad register address state size = some (.ret ffi bytes, next)) :
    next.code = state.code := by
  unfold shareMemLoad at h
  repeat' first | split at h | simp_all
  all_goals exact (congrArg (fun s : LabSem.State width C F => s.code) h.2).symm

theorem shareMemStore_ret_code {width : Nat} [NeZero width] {C F : Type}
    (register : Nat) (address : HolAddr width)
    (state next : LabSem.State width C F)
    (size : Nat) (ffi : HolFfiState F) (bytes : List (BitVec 8))
    (h : shareMemStore register address state size = some (.ret ffi bytes, next)) :
    next.code = state.code := by
  unfold shareMemStore at h
  repeat' first | split at h | simp_all [incPc, decClock]
  all_goals exact (congrArg (fun s : LabSem.State width C F => s.code) h.2).symm

theorem shareMemOp_ret_code {width : Nat} [NeZero width] {C F : Type}
    (operator : HolMemop) (register : Nat) (address : HolAddr width)
    (state next : LabSem.State width C F)
    (ffi : HolFfiState F) (bytes : List (BitVec 8))
    (h : shareMemOp operator register address state = some (.ret ffi bytes, next)) :
    next.code = state.code := by
  cases operator <;> simp only [shareMemOp] at h
  all_goals first
    | exact shareMemLoad_ret_code _ _ _ _ _ _ _ h
    | exact shareMemStore_ret_code _ _ _ _ _ _ _ h

theorem compileCorrect_errorB {width : Nat} [NeZero width] {S Q F : Type} {W : Nat}
    (s1 : LabSem.State width Config F) (h : evaluate s1 = (.error, s1)) :
    CompileCorrectForB W S Q s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨-, hev, hres, -, -, -⟩
  rw [h] at hev
  exact absurd (Prod.mk.inj hev).1.symm hres

theorem compileCorrect_timeOutB {width : Nat} [NeZero width] {S Q F : Type} {W : Nat}
    (s1 : LabSem.State width Config F) (hc : s1.clock = 0) :
    CompileCorrectForB W S Q s1 := by
  rintro res mc s2 code2 labs t1 ms1 p ⟨-, hev, -, -, -, -⟩
  rw [evaluate, if_pos hc] at hev
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hev
  exact ⟨0, ms1, by rw [hc]; simp, by rw [hc]; rfl⟩

theorem compileCorrectFor_allB {width : Nat} [NeZero width] {S Q F : Type} (W : Nat)
    (s1 : LabSem.State width Config F) (hni : NoInstall s1.code) :
    CompileCorrectForB W S Q s1 := by
  induction hcl : s1.clock using Nat.strong_induction_on generalizing s1 with
  | _ c ihc =>
  have IH : ∀ s' : LabSem.State width Config F, s'.clock < s1.clock → s'.code = s1.code →
      CompileCorrectForB W S Q s' := fun s' hs hcode =>
    ihc _ (hcl ▸ hs) s' (by rw [hcode]; exact hni) rfl
  by_cases hc : s1.clock = 0
  · exact compileCorrect_timeOutB s1 hc
  have herr : ∀ (h : evaluate s1 = (.error, s1)), CompileCorrectForB W S Q s1 :=
    compileCorrect_errorB s1
  cases hf : asmFetch s1 with
  | none => exact herr (by rw [evaluate]; simp [hc, hf])
  | some line =>
  cases line with
  | label => exact herr (by rw [evaluate]; simp [hc, hf])
  | asm a bytes n =>
    cases a with
    | asmi i =>
      cases i with
      | inst ins =>
        exact compileCorrect_asmInstB s1 ins bytes n hc hf fun _ => IH _ (by
          obtain ⟨-, -, hcl', -⟩ := asmInstConsts ins s1
          simp [incPc, decClock, hcl']; omega) (by
          obtain ⟨-, hcode, -⟩ := asmInstConsts ins s1
          simp [incPc, decClock, hcode])
      | jumpReg r =>
        exact compileCorrect_jumpRegB s1 r bytes n hc hf fun _ _ _ _ _ => IH _ (by
          simp [LabSem.updPc, decClock]; omega) (by simp [LabSem.updPc, decClock])
      | _ => exact herr (by rw [evaluate]; simp [hc, hf])
    | cbw r1 r2 =>
      exact compileCorrect_cbwB s1 r1 r2 bytes n hc hf fun _ _ _ _ _ _ => IH _ (by
        simp [incPc, decClock]; omega) (by simp [incPc, decClock])
    | shareMem m r ad =>
      exact compileCorrect_shareMemB s1 m r ad bytes n hc hf fun ffi' bs s' hs => IH _ (by
        have := shareMemOp_ret_clock m r ad s1 s' ffi' bs hs
        simp only; omega) (by
        have := shareMemOp_ret_code m r ad s1 s' ffi' bs hs
        simp only; exact this)
  | labAsm a w bytes n =>
    cases a with
    | jump jt =>
      exact compileCorrect_jumpB s1 jt w bytes n hc hf fun _ _ => IH _ (by
        simp [LabSem.updPc, decClock]; omega) (by simp [LabSem.updPc, decClock])
    | jumpCmp cmp rr ri jt =>
      exact compileCorrect_jumpCmpB s1 cmp rr ri jt w bytes n hc hf
        (fun _ => IH _ (by simp [incPc, decClock]; omega) (by simp [incPc, decClock]))
        (fun _ _ _ => IH _ (by simp [LabSem.updPc, decClock]; omega)
          (by simp [LabSem.updPc, decClock]))
    | call lab =>
      exact compileCorrect_callB s1 lab w bytes n hc hf fun _ _ _ _ => IH _ (by
        simp [LabSem.updPc, decClock, LabSem.updReg]; omega)
        (by simp [LabSem.updPc, decClock, LabSem.updReg])
    | locValue reg lab =>
      exact compileCorrect_locValueB s1 reg lab w bytes n hc hf fun _ => IH _ (by
        simp [incPc, decClock, LabSem.updReg]; omega) (by simp [incPc, decClock, LabSem.updReg])
    | install =>
      exact absurd hf (hni s1.pc w bytes n)
    | callFFI name =>
      exact compileCorrect_callFFIB s1 name w bytes n hc hf
        fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => IH _ (by simp only; omega) rfl
    | halt => exact compileCorrect_haltB s1 w bytes n hc hf

end Flapjack.Compiler.Backend.LabToTarget.Bounded
