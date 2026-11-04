import Flapjack.Compiler.Backend.StackToLab.Proofs.NoInstall
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoInstallTop
import Flapjack.Pancake.Proofs.PanToTarget.WordToWordNoInstall
import Flapjack.Pancake.Proofs.PanToWord.NoInstallCode
import Flapjack.Compiler.Backend.RegAlloc.Executable
import Flapjack.Compiler.Backend.LabFilter.Proofs.PcAdjustment
import InitECandidate.Solver.L2T.AssemblyB
import InitECandidate.Proofs.BackendStages.Sections
import InitECandidate.Proofs.BackendStages.Filtered
import InitECandidate.Proofs.BackendStages.Function64
import InitECandidate.Proofs.ArtifactComposition

/-!
Draft bridge for EVM.fast, pinned to flapjack 034bb5a and L6 e2888857.
Not compiled or checked by Lean. This does not prove that the baseline
StackLang program satisfies the source hypothesis or establish any cost bound.
Move into the allowed Solver namespace only after checking on the pinned
Linux build environment.
-/

namespace InitECandidate.Solver.NoInstallBridge

open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabFilter Flapjack.Compiler.Backend.LabFilter.Proofs
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip

set_option maxRecDepth 1000000

/-- First generated body: a proposed kernel reduction, still uncompiled. -/
theorem generatedBody64_noInstall :
    StackProps.noInstall InitECandidate.Proofs.BackendStages.stackBody64_682 = true := by
  decide

/-- The two fetched-instruction predicates have the same definition. -/
theorem boundedNoInstall_of_labNoInstall {width : Nat} [NeZero width]
    (code : LabSem.LabProgHOL width) (h : LabProps.noInstall code) :
    LabToTarget.Bounded.NoInstall code := by
  exact h

/-- Transfer the upstream stack-to-lab result to the bounded lab evaluator. -/
theorem boundedNoInstall_of_stack_compile {width : Nat} [NeZero width]
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config}
    {maxHeap sp : Nat} {offset : BitVec width × BitVec width}
    (prog : List (Nat × StackLang.HolProg width))
    (compiled : LabSem.LabProgHOL width)
    (noInstall : ∀ ap ∈ prog, StackProps.noInstall ap.2 = true)
    (hcompile : StackToLab.compile stackConf dataConf maxHeap sp offset prog = compiled) :
    LabToTarget.Bounded.NoInstall compiled := by
  apply boundedNoInstall_of_labNoInstall
  exact StackToLab.Proofs.NoInstall.compileNoInstall prog compiled ⟨noInstall, hcompile⟩

/-- Isolate the generated function bodies from the two fixed native stubs. -/
theorem baselineNativeNoInstall_of_bodies
    (h : ∀ ap ∈ InitECandidate.Proofs.BackendStages.Native.bodies0,
      StackProps.noInstall ap.2 = true) :
    ∀ ap ∈ InitECandidate.Proofs.BackendStages.Native.stack,
      StackProps.noInstall ap.2 = true := by
  intro ap hap
  simp only [InitECandidate.Proofs.BackendStages.Native.stack, List.mem_cons] at hap
  rcases hap with rfl | rfl | hap
  · simp [WordToStack.Native.raiseStubNative, StackProps.noInstall]
  · simp [WordToStack.Native.storeConstsStubNative, StackProps.noInstall]
  · exact h ap hap

/-- Specialize using the baseline's existing Stack-to-Lab equality.
The remaining hypothesis must be proved for every entry, including stubs. -/
theorem baselineLabNoInstall
    (noInstall : ∀ ap ∈ InitECandidate.Proofs.BackendStages.Native.stack,
      StackProps.noInstall ap.2 = true) :
    LabToTarget.Bounded.NoInstall InitECandidate.Proofs.BackendStages.Sections.program := by
  exact boundedNoInstall_of_stack_compile
    InitECandidate.Proofs.BackendStages.Native.stack
    InitECandidate.Proofs.BackendStages.Sections.program noInstall
    InitECandidate.Proofs.BackendStages.Sections.compile_eq

/-- Reduce the concrete Lab precondition to all generated native bodies. -/
theorem baselineLabNoInstall_of_bodies
    (h : ∀ ap ∈ InitECandidate.Proofs.BackendStages.Native.bodies0,
      StackProps.noInstall ap.2 = true) :
    LabToTarget.Bounded.NoInstall InitECandidate.Proofs.BackendStages.Sections.program :=
  baselineLabNoInstall (baselineNativeNoInstall_of_bodies h)

/-- Reuse the upstream whole-program theorem, including both injected stubs.
The WordLang code-map guard and distinct identifiers still need independent
proof for the concrete baseline. -/
theorem baselineLabNoInstall_of_word
    (distinct : (InitECandidate.Proofs.BackendStages.Native.programs0.map Prod.fst).Nodup)
    (guard : WordProps.noInstallCode
      (sptFromAList InitECandidate.Proofs.BackendStages.Native.programs0)) :
    LabToTarget.Bounded.NoInstall InitECandidate.Proofs.BackendStages.Sections.program := by
  apply baselineLabNoInstall
  have safe := WordToStack.Native.wordToStackCompileNoInstall
    Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig
    InitECandidate.Proofs.BackendStages.Native.programs0
    InitECandidate.Proofs.BackendStages.Native.bitmaps
    InitECandidate.Proofs.BackendStages.Native.wordConfig
    (0 :: InitECandidate.Proofs.BackendStages.Native.frames0)
    InitECandidate.Proofs.BackendStages.Native.stack
    distinct guard InitECandidate.Proofs.BackendStages.Native.native_eq
  intro ap hap
  exact (List.all_eq_true.mp safe) ap hap

/-- Connect the two generic compiler safety results to the checked baseline
frontend and optimizer. Both lists' identifier uniqueness is still required.
This is a draft: no Lean or axiom check has been run. -/
theorem baselineLabNoInstall_of_distinct
    (frontendDistinct :
      (InitECandidate.Proofs.FrontendStages.pass5.map Prod.fst).Nodup)
    (optimizedDistinct :
      (InitECandidate.Proofs.BackendStages.Native.programs0.map Prod.fst).Nodup) :
    LabToTarget.Bounded.NoInstall InitECandidate.Proofs.BackendStages.Sections.program := by
  let front := InitECandidate.Proofs.FrontendStages.pass5
  let optimized := InitECandidate.Proofs.BackendStages.Native.programs0
  let target := Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig
  have frontNoInstall : WordProps.noInstallCode (sptFromAList front) := by
    exact PanToWord.pan_to_word_compile_prog_no_install_code target.isa InitE.sourceDeclarations front
      InitECandidate.Proofs.FrontendStages.frontend_eq
  have frontNoMt : WordProps.noMtCode (sptFromAList front) := by
    exact PanToWord.pan_to_word_compile_prog_no_mt_code target.isa InitE.sourceDeclarations front
      InitECandidate.Proofs.FrontendStages.frontend_eq
  have allocatorEq : RegAlloc.regAllocExecutable = RegAlloc.regAlloc := by
    funext algorithm costs limit moves tree forced stackOnly
    exact RegAlloc.regAllocExecutable_eq algorithm costs limit moves tree forced stackOnly
  have optimizedExecutable : WordToWord.compileWith RegAlloc.regAllocExecutable
      InitE.baselineCompilerConfig.wordToWordConf target front = ([], optimized) := by
    change WordToWord.compileWith RegAlloc.regAllocExecutable InitECandidate.Proofs.WordBackend.config
      target InitECandidate.Proofs.WordBackend.inputs = ([], optimized)
    rw [InitECandidate.Proofs.WordBackend.compileWith_eq,
      InitECandidate.Proofs.WordBackend.StackAgreement.outputs_eq]
    apply congrArg (fun xs => ([], xs))
    exact InitECandidate.Proofs.BackendStages.Native.programs_eq.symm
  have optimizedTheorem : WordToWord.compile InitE.baselineCompilerConfig.wordToWordConf
      target front = ([], optimized) := by
    exact (WordToWord.compileWith_eq_compile RegAlloc.regAllocExecutable allocatorEq
      InitE.baselineCompilerConfig.wordToWordConf target front).symm.trans optimizedExecutable
  have optimizedNoInstall : WordProps.noInstallCode (sptFromAList optimized) :=
    (PanToTarget.word_to_word_compile_no_install_no_alloc
      InitE.baselineCompilerConfig.wordToWordConf target front [] optimized
      ⟨optimizedTheorem, frontendDistinct, frontNoMt, frontNoInstall⟩).1
  exact baselineLabNoInstall_of_word optimizedDistinct optimizedNoInstall

/-- Candidate kernel reductions for the two concrete ID lists. The static
inventory found both lists equal to 64..877, but Lean has not checked this. -/
theorem frontendIdentifiersDistinct :
    (InitECandidate.Proofs.FrontendStages.pass5.map Prod.fst).Nodup := by
  have ids : InitECandidate.Proofs.FrontendStages.pass5.map Prod.fst =
      List.range' 64 814 := by decide
  rw [ids]
  exact List.nodup_range' 1

theorem optimizedIdentifiersDistinct :
    (InitECandidate.Proofs.BackendStages.Native.programs0.map Prod.fst).Nodup := by
  have ids : InitECandidate.Proofs.BackendStages.Native.programs0.map Prod.fst =
      List.range' 64 814 := by decide
  rw [ids]
  exact List.nodup_range' 1

/-- Intended closed NoInstall result for the baseline Lab program. This is
uncompiled draft code, not a verified theorem or finite-step certificate. -/
theorem baselineLabNoInstall_closed :
    LabToTarget.Bounded.NoInstall InitECandidate.Proofs.BackendStages.Sections.program :=
  baselineLabNoInstall_of_distinct frontendIdentifiersDistinct optimizedIdentifiersDistinct

/-- Every PC of the skip-filtered program has an original PC whose adjustment
is that PC. Relies on the upstream skipped-prefix and fetch correspondence. -/
theorem adjustPc_surjective {width : Nat} [NeZero width]
    (code : LabSem.LabProgHOL width) : ∀ q, ∃ p, adjustPc p code = q := by
  intro q
  induction q with
  | zero => exact ⟨0, by rw [adjustPc.eq_def]; simp⟩
  | succ q ih =>
      obtain ⟨p, hp⟩ := ih
      obtain ⟨count, _, skipped⟩ := asmFetchAuxEq p code
      refine ⟨p + count + 1, ?_⟩
      rw [← adjustPcAllSkips count p code skipped, hp]

/-- Skip filtering cannot create an Install instruction. -/
theorem noInstall_filterSkip {width : Nat} [NeZero width]
    (code : LabSem.LabProgHOL width) (safe : LabToTarget.Bounded.NoInstall code) :
    LabToTarget.Bounded.NoInstall (filterSkip code) := by
  intro pc w bytes len fetch
  obtain ⟨p, hp⟩ := adjustPc_surjective code pc
  obtain ⟨count, sameFetch, _⟩ := asmFetchAuxEq p code
  apply safe (p + count) w bytes len
  rw [sameFetch, hp, fetch]

/-- Intended no-Install conclusion for the baseline's filtered Lab program. -/
theorem baselineFilteredNoInstall_closed :
    LabToTarget.Bounded.NoInstall InitECandidate.Proofs.BackendStages.Filtered.program := by
  rw [← InitECandidate.Proofs.BackendStages.Filtered.compile_eq]
  exact noInstall_filterSkip _ baselineLabNoInstall_closed

end InitECandidate.Solver.NoInstallBridge
