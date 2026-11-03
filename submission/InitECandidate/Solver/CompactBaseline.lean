import InitECandidate.Solver.CompactInstallationFacts
import InitECandidate.Solver.FiniteBoundReduction
import InitECandidate.Solver.BootstrapClockBound
import InitECandidate.Proofs.PanInstallationCore
import InitECandidate.Proofs.BaselineInstallationFacts
import InitECandidate.Proofs.InstallationTransport
import InitECandidate.Proofs.CompilerFacts
import InitECandidate.Proofs.CompilerOracles
import InitE.SourceCodeFacts
import InitECandidate.Proofs.AllocationFacts
import InitECandidate.Proofs.StackLayout
import InitECandidate.Proofs.SourceStackCertificate
import InitECandidate.Proofs.StartupEnvironment
import InitECandidate.Proofs.BootstrapTrace
import InitECandidate.Proofs.BootstrapComposition
import InitE.TargetTotality

/-! Compact top-level baseline certificate chain replacing the 14 `decide_cbv`
obligations across `PanInstallation`, `BaselineCertificate`, `BaselineCorrectness`,
and `OracleBaselineCorrectness` with `kernel_rfl` / `of_decide_eq_true (by kernel_rfl)`,
deduplicating `StackNames.findNameSpt` and `installedLimits` stack-bound proofs,
and bypassing `FullBaseline` / `NativeBaseline` / `BaselineCertificate` / `PanInstallation`
in the exported `lean4export` / `comparator` constant closure. -/

namespace InitECandidate.Solver

open InitE InitECandidate.Proofs
open Flapjack Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Basis.Pure.MlString

/-- `baselineMmio` is defined as `baselineConfig.labConf.shmemExtra` (marked `@[irreducible]`),
so unfolding `baselineMmio` proves projection equality by `rfl` without `decide_cbv`. -/
theorem compact_mmio_projection :
    baselineConfig.labConf.shmemExtra = baselineMmio := by
  unfold baselineMmio
  rfl

/-- Compact replacement for `PanInstallation.baseline_pan_installed_metadata`,
avoiding both `decide_cbv` calls (`baseline_mmio_projection` and `hregs`). -/
theorem compact_pan_installed_metadata :
    panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      baselineConfig.labConf.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig baselineConfig.labConf.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ sourceMemory) ordinaryDomain sharedDomain :=
  panInstalled_metadata_congr _ _ _ _ _ (some baselineNames) _ (11, 13)
    _ _ baselineMmio _ _ (wlabWlocExact ∘ sourceMemory) _ ordinaryDomain _ sharedDomain
    baseline_installation_metadata.1 compact_heapRegs compact_mmio_projection
    rfl rfl rfl baseline_pan_installed_core

/-- Compact replacement for `PanInstallation.baseline_pan_installed`. -/
theorem compact_pan_installed (input : Guest.InputBlob) :
    panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      baselineConfig.labConf.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig baselineConfig.labConf.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ (sourceInitialState input).memory)
      (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs :=
  panInstalled_metadata_congr _ _ _ _ _ baselineConfig.labConf.ffiNames
    _ (heapRegs pancakeRiscVBackendConfig.stackConf.regNames) _ _ baselineConfig.labConf.shmemExtra
    _ _ (wlabWlocExact ∘ sourceMemory) _ ordinaryDomain _ sharedDomain
    rfl rfl rfl rfl (source_memory_domain input) rfl compact_pan_installed_metadata

/-- Compact replacement for `BaselineCorrectness.baseline_behaviour_eq`. -/
theorem compact_baseline_behaviour_eq (input : Guest.InputBlob) (out : RiscV.NativeSource.Output)
    (compiled : out.declarations = sourceDeclarations ∧
      out.artifact = compileProgAsmFast baselineCompilerConfig riscvConfig sourceDeclarations)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (ms : RiscV.L3.riscv_state) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (c : Backend.Config) (heapLen : Nat) (adj2 adj4 : BitVec 64)
    (cbspace dataSp : Nat)
    (installed : CompactBaselineInstallation input out mc ms bytes bitmaps c heapLen adj2 adj4 cbspace dataSp)
    (nonfail : sourceBehaviour input ≠ HolBehaviour.fail) :
    ∀ behaviour, machineSemHOL mc (sourceFfi input) ms behaviour →
      behaviour = sourceBehaviour input :=
  compact_baseline_behaviour_eq_of_oracles WordBackend.oracles input out compiled
    sourceLogicalStackBound_bounded mc ms bytes bitmaps c heapLen adj2 adj4
    cbspace dataSp installed nonfail

/-- Compact replacement for `BaselineCertificate.baseline_installation`:
discharges all 10 numeric and register-name obligations via `CompactInstallationFacts`
(`kernel_rfl` / `of_decide_eq_true (by kernel_rfl)`) with zero `decide_cbv` calls. -/
theorem compact_baseline_installation (input : Guest.InputBlob)
    (memory : panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      baselineConfig.labConf.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig baselineConfig.labConf.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ (sourceInitialState input).memory)
      (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs) :
    CompactBaselineInstallation input baselineOutput baselineMachineConfig baselineInstalledState
      InitECandidate.nativeCode InitECandidate.bitmaps baselineConfig compactHeapLen
      compactAdj2 compactAdj4 3788 0 := by
  refine ⟨baseline_machine_isRiscv, baseline_artifact_complete,
    compact_sourceBase_pos, compact_sourceBase_lt_stackStart, rfl,
    compact_heapLen_eq, compact_heapEnd_eq, compact_globalsWords_le_heapLen,
    rfl, compact_stack_diff_aligned, rfl, rfl,
    compact_adj2_le_stackStart, compact_stackStart_le_adj4,
    compact_stack_diff_le_maxHeap, rfl, memory, ?_⟩
  simp only [readLimits, compact_stack_name_2, compact_stack_name_3, compact_stack_name_4]
  rfl

/-- Compact replacement for `BaselineCertificate.baseline_installation_transport`:
reuses `compact_stack_name_2/3/4` directly instead of recomputing `decide_cbv`. -/
theorem compact_baseline_installation_transport (input : Guest.InputBlob)
    (ms : RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm ms)
    (installed : CompactBaselineInstallation input baselineOutput baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      baselineConfig compactHeapLen compactAdj2 compactAdj4 3788 0) :
    CompactBaselineInstallation input baselineOutput baselineMachineConfig ms
      InitECandidate.nativeCode InitECandidate.bitmaps baselineConfig compactHeapLen
      compactAdj2 compactAdj4 3788 0 := by
  have agreement := baseline_endpoint_agreement ms related
  have r11 := agreement.regs 11 (by decide)
  have r12 := agreement.regs 12 (by decide)
  have r13 := agreement.regs 13 (by decide)
  have limits : readLimits baselineMachineConfig.target.config pancakeRiscVBackendConfig
      baselineMachineConfig ms = readLimits baselineMachineConfig.target.config
        pancakeRiscVBackendConfig baselineMachineConfig baselineInstalledState := by
    simp only [readLimits, compact_stack_name_2, compact_stack_name_3, compact_stack_name_4,
      r11, r12, r13]
  have rlen : baselineMachineConfig.target.getReg ms baselineMachineConfig.lenReg =
      baselineMachineConfig.target.getReg baselineInstalledState baselineMachineConfig.lenReg := r11
  have rptr : baselineMachineConfig.target.getReg ms baselineMachineConfig.ptr2Reg =
      baselineMachineConfig.target.getReg baselineInstalledState baselineMachineConfig.ptr2Reg := r12
  have rlen2 : baselineMachineConfig.target.getReg ms baselineMachineConfig.len2Reg =
      baselineMachineConfig.target.getReg baselineInstalledState baselineMachineConfig.len2Reg := r13
  rcases installed with ⟨hmc, hart, hpositive, hsplit, hbase, hlen, htop, hglobals,
    hdomain, haligned, hadj2, hadj4, hleft, hright, hmax, hendian, hmemory, hlimits⟩
  have memory := panInstalled_transport agreement hmemory
  unfold CompactBaselineInstallation
  simp only [rlen, rptr, rlen2, limits]
  exact ⟨hmc, hart, hpositive, hsplit, hbase, hlen, htop, hglobals, hdomain,
    haligned, hadj2, hadj4, hleft, hright, hmax, hendian, memory, hlimits⟩

/-- Compact replacement for `NativeBaseline.native_baseline_correct`. -/
theorem compact_native_baseline_correct (input : Guest.InputBlob)
    (ms : RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm ms)
    (nonfail : sourceBehaviour input ≠ HolBehaviour.fail) :
    ∀ behaviour, machineSemHOL baselineMachineConfig (sourceFfi input) ms behaviour →
      behaviour = sourceBehaviour input :=
  compact_baseline_behaviour_eq input baselineOutput baseline_ast_compilation
    baselineMachineConfig ms InitECandidate.nativeCode InitECandidate.bitmaps
    baselineConfig compactHeapLen compactAdj2 compactAdj4 3788 0
    (compact_baseline_installation_transport input ms related
      (compact_baseline_installation input (compact_pan_installed input))) nonfail

/-- Compact replacement for `FullBaseline.full_baseline_correct`. -/
theorem compact_full_baseline_correct (input : Guest.InputBlob)
    (nonfail : sourceBehaviour input ≠ HolBehaviour.fail) :
    ∀ behaviour,
      machineSemHOL baselineMachineConfig (sourceFfi input)
        (baselineInitialState input) behaviour →
      behaviour = sourceBehaviour input := by
  obtain ⟨count, post, shift, related⟩ := BootstrapTrace.full_evaluator
    (sourceFfi input) (baselineInitialState input) (baselineInitialState_related input)
  exact Bootstrap.behavior_property_from_clock_shift (sourceFfi input) shift
    (fun behaviour => behaviour = sourceBehaviour input)
    (compact_native_baseline_correct input post related nonfail)

end InitECandidate.Solver
