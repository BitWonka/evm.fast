import InitE.Parameters
import InitE.SourceCodeFacts
import InitE.MachineInitialization
import InitE.TargetTotality
import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.CompilerOracles
import InitECandidate.Proofs.AllocationFacts
import InitECandidate.Proofs.PanInstallationConstructor
import InitECandidate.Proofs.BootstrapComposition
import Flapjack.Compiler.Backend.RiscVConfig.Executable
import Flapjack.Compiler.Backend.BackendProof.ConfigOk
import Flapjack.Compiler.Backend.BackendProof.MachineInit
import Flapjack.Compiler.Backend.BackendProof.ReadLimits
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitLimits
import Flapjack.Compiler.Encoders.RiscV.Target
import Flapjack.Pancake.Proofs.PanToTarget
import Flapjack.Pancake.Proofs.PanToTarget.PanInstalled
import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileProgMaxAsmWith
import Flapjack.RiscV.NativeSource

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitECandidate.Solver

open InitE
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Basis.Pure.MlString

def compactHeapLen : Nat := (stackStart - sourceBase) / 8

def compactAdj2 : BitVec 64 := BitVec.ofNat 64 sourceBase +
  (8 : BitVec 64) * BitVec.ofNat 64 StackRemove.maxStackAlloc

def compactAdj4 : BitVec 64 := BitVec.ofNat 64 ramEnd -
  (8 : BitVec 64) * BitVec.ofNat 64 StackRemove.maxStackAlloc

def compactInstalledLimits : Nat × Nat :=
  StackRemove.Proofs.InitLimits.getStackHeapLimit
    (2 * DataToWord.maxHeapLimit 64 pancakeRiscVBackendConfig.dataConf - 1)
    (BitVec.ofNat 64 sourceBase, BitVec.ofNat 64 stackStart, BitVec.ofNat 64 ramEnd)

theorem compact_heapRegs :
    heapRegs pancakeRiscVBackendConfig.stackConf.regNames = (11, 13) := by
  unfold pancakeRiscVBackendConfig
  rw [riscvBackendConfig_eq_executable]
  kernel_rfl

theorem compact_stack_names_spt :
    (StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 2,
     StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 3,
     StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 4) =
      (11, 12, 13) := by
  unfold pancakeRiscVBackendConfig
  rw [riscvBackendConfig_eq_executable]
  kernel_rfl

theorem compact_stack_name_2 :
    StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 2 = 11 :=
  congrArg Prod.fst compact_stack_names_spt

theorem compact_stack_name_3 :
    StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 3 = 12 :=
  congrArg (fun p => p.2.1) compact_stack_names_spt

theorem compact_stack_name_4 :
    StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 4 = 13 :=
  congrArg (fun p => p.2.2) compact_stack_names_spt

theorem compact_sourceBase_pos :
    (0 : BitVec 64) < BitVec.ofNat 64 sourceBase :=
  of_decide_eq_true (by kernel_rfl)

theorem compact_sourceBase_lt_stackStart :
    BitVec.ofNat 64 sourceBase < BitVec.ofNat 64 stackStart :=
  of_decide_eq_true (by kernel_rfl)

theorem compact_heapLen_eq :
    compactHeapLen =
      (BitVec.ofNat 64 stackStart + -1 * BitVec.ofNat 64 sourceBase).toNat / (64 / 8) := by
  kernel_rfl

theorem compact_heapEnd_eq :
    BitVec.ofNat 64 heapEnd =
      BitVec.ofNat 64 sourceBase +
        (wordSemBytesInWord : BitVec 64) * BitVec.ofNat 64 compactHeapLen -
          BitVec.ofNat 64 (globalsWords * 64 / 8) := by
  kernel_rfl

theorem compact_globalsWords_le_heapLen :
    globalsWords ≤ compactHeapLen :=
  of_decide_eq_true (by kernel_rfl)

theorem compact_stack_diff_aligned :
    holAligned (wordShiftAmount 64 + 1)
      (BitVec.ofNat 64 stackStart + -1 * BitVec.ofNat 64 sourceBase) = true := by
  kernel_rfl

theorem compact_adj2_le_stackStart :
    compactAdj2 ≤ BitVec.ofNat 64 stackStart :=
  of_decide_eq_true (by kernel_rfl)

theorem compact_stackStart_le_adj4 :
    BitVec.ofNat 64 stackStart ≤ compactAdj4 :=
  of_decide_eq_true (by kernel_rfl)

theorem compact_stack_diff_le_maxHeap :
    (BitVec.ofNat 64 stackStart + -1 * BitVec.ofNat 64 sourceBase).toNat ≤
      (wordSemBytesInWord : BitVec 64).toNat *
        (2 * DataToWord.maxHeapLimit 64 pancakeRiscVBackendConfig.dataConf - 1) := by
  unfold pancakeRiscVBackendConfig
  rw [riscvBackendConfig_eq_executable]
  exact of_decide_eq_true (by kernel_rfl)

theorem compact_stack_bound_fits :
    7480 < compactInstalledLimits.1 := by
  unfold compactInstalledLimits pancakeRiscVBackendConfig
  rw [riscvBackendConfig_eq_executable]
  exact of_decide_eq_true (by kernel_rfl)

/-- Installation obligations for the oracle-configured compiler theorem,
using `compactInstalledLimits` (`kernel_rfl`) instead of `decide_cbv`. -/
def CompactOracleInstallation (input : Guest.InputBlob)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (ms : RiscV.L3.riscv_state) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (c : Backend.Config) (heapLen : Nat) (adj2 adj4 : BitVec 64)
    (cbspace dataSp : Nat) : Prop :=
  let s := sourceInitialState input
  isRiscvMachineConfig mc ∧
  (0 : BitVec 64) < mc.target.getReg ms mc.lenReg ∧
  mc.target.getReg ms mc.lenReg < mc.target.getReg ms mc.ptr2Reg ∧
  mc.target.getReg ms mc.lenReg = s.baseAddr ∧
  heapLen = (mc.target.getReg ms mc.ptr2Reg + -1 * s.baseAddr).toNat / (64 / 8) ∧
  s.topAddr = s.baseAddr + (wordSemBytesInWord : BitVec 64) * BitVec.ofNat 64 heapLen -
    BitVec.ofNat 64 (globalsWords * 64 / 8) ∧
  globalsWords ≤ heapLen ∧
  s.memaddrs = StackRemove.addresses (mc.target.getReg ms mc.lenReg) (heapLen - globalsWords) ∧
  holAligned (wordShiftAmount 64 + 1)
    (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg) = true ∧
  adj2 = mc.target.getReg ms mc.lenReg +
    (wordSemBytesInWord : BitVec 64) * BitVec.ofNat 64 StackRemove.maxStackAlloc ∧
  adj4 = mc.target.getReg ms mc.len2Reg -
    (wordSemBytesInWord : BitVec 64) * BitVec.ofNat 64 StackRemove.maxStackAlloc ∧
  adj2 ≤ mc.target.getReg ms mc.ptr2Reg ∧
  mc.target.getReg ms mc.ptr2Reg ≤ adj4 ∧
  (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg).toNat ≤
    (wordSemBytesInWord : BitVec 64).toNat *
      (2 * DataToWord.maxHeapLimit 64 pancakeRiscVBackendConfig.dataConf - 1) ∧
  mc.target.config.bigEndian = s.be ∧
  panInstalled bytes cbspace bitmaps dataSp c.labConf.ffiNames
    (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
    mc c.labConf.shmemExtra ms (wlabWlocExact ∘ s.memory) s.memaddrs s.shMemaddrs ∧
  (readLimits mc.target.config pancakeRiscVBackendConfig mc ms).1 = compactInstalledLimits.1

/-- Compact replacement for `OracleBaselineCorrectness.oracle_baseline_behaviour_eq`,
using `compact_stack_bound_fits` (`kernel_rfl`) instead of `decide_cbv`. -/
theorem compact_oracle_baseline_behaviour_eq (oracles : List (Option (Spt Nat)))
    (input : Guest.InputBlob)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (ms : RiscV.L3.riscv_state) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (c : Backend.Config) (depth heapLen : Nat) (adj2 adj4 : BitVec 64)
    (cbspace dataSp : Nat)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (bytes, bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (installed : CompactOracleInstallation input mc ms bytes bitmaps c heapLen adj2 adj4 cbspace dataSp)
    (nonfail : sourceBehaviour input ≠ HolBehaviour.fail) :
    ∀ behaviour, machineSemHOL mc (sourceFfi input) ms behaviour →
      behaviour = sourceBehaviour input := by
  obtain ⟨hmc, hpositive, hsplit, hbase, hlen, htop, hglobals, hdomain,
    haligned, hadj2, hadj4, hleft, hright, hmax, hendian, hinstalled, hlimits⟩ := installed
  have correct := panToTargetCompileSemanticsOraclesRiscVSource oracles mc
    (Guest.Software.guestAst.map Pancake.PanLang.declToHOL) bytes bitmaps c (some depth)
    (sourceInitialState input) ms globalsWords heapLen adj2 adj4
    (sourceFfi input) cbspace dataSp (ofString "main") hmc sourceHasMain
    ⟨compiled, sourceGoodCode, sourceDistinctParams, sourceDistinctFunctions,
      rfl, rfl, rfl, sourceExceptionBound, rfl,
      hpositive, by simpa only [sourceDeclarations, globalsWords] using sourceGlobalsSize.symm,
      hsplit, hbase, source_globals_allocatable input,
      hlen, htop, hglobals, hdomain, haligned, hadj2, hadj4, hleft, hright, hmax,
      rfl, hendian, hinstalled, rfl, nonfail⟩
  have hprecise : optionLt (some depth)
      (some (readLimits mc.target.config (oracleCompilerConfig oracles) mc ms).1) = true := by
    change optionLt (some depth)
      (some (readLimits mc.target.config pancakeRiscVBackendConfig mc ms).1) = true
    rw [hlimits]
    simpa only [optionLt, decide_eq_true_eq] using
      (Nat.lt_of_le_of_lt depthBound compact_stack_bound_fits)
  intro behaviour hbehaviour
  have h := correct behaviour hbehaviour
  simpa only [SemanticsPropsHOL.extendWithResourceLimitPrimeHOL, hprecise, if_true,
    sourceBehaviour] using h

/-- Installation obligations including the compiler artifact equality. -/
def CompactBaselineInstallation (input : Guest.InputBlob)
    (out : RiscV.NativeSource.Output)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (ms : RiscV.L3.riscv_state) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (c : Backend.Config) (heapLen : Nat) (adj2 adj4 : BitVec 64)
    (cbspace dataSp : Nat) : Prop :=
  let s := sourceInitialState input
  isRiscvMachineConfig mc ∧
  out.artifact = some (bytes, bitmaps, c) ∧
  (0 : BitVec 64) < mc.target.getReg ms mc.lenReg ∧
  mc.target.getReg ms mc.lenReg < mc.target.getReg ms mc.ptr2Reg ∧
  mc.target.getReg ms mc.lenReg = s.baseAddr ∧
  heapLen = (mc.target.getReg ms mc.ptr2Reg + -1 * s.baseAddr).toNat / (64 / 8) ∧
  s.topAddr = s.baseAddr + (wordSemBytesInWord : BitVec 64) * BitVec.ofNat 64 heapLen -
    BitVec.ofNat 64 (globalsWords * 64 / 8) ∧
  globalsWords ≤ heapLen ∧
  s.memaddrs = StackRemove.addresses (mc.target.getReg ms mc.lenReg) (heapLen - globalsWords) ∧
  holAligned (wordShiftAmount 64 + 1)
    (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg) = true ∧
  adj2 = mc.target.getReg ms mc.lenReg +
    (wordSemBytesInWord : BitVec 64) * BitVec.ofNat 64 StackRemove.maxStackAlloc ∧
  adj4 = mc.target.getReg ms mc.len2Reg -
    (wordSemBytesInWord : BitVec 64) * BitVec.ofNat 64 StackRemove.maxStackAlloc ∧
  adj2 ≤ mc.target.getReg ms mc.ptr2Reg ∧
  mc.target.getReg ms mc.ptr2Reg ≤ adj4 ∧
  (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg).toNat ≤
    (wordSemBytesInWord : BitVec 64).toNat *
      (2 * DataToWord.maxHeapLimit 64 pancakeRiscVBackendConfig.dataConf - 1) ∧
  mc.target.config.bigEndian = s.be ∧
  panInstalled bytes cbspace bitmaps dataSp c.labConf.ffiNames
    (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
    mc c.labConf.shmemExtra ms (wlabWlocExact ∘ s.memory) s.memaddrs s.shMemaddrs ∧
  (readLimits mc.target.config pancakeRiscVBackendConfig mc ms).1 = compactInstalledLimits.1

/-- Parameterized compact replacement for `BaselineCorrectness.baseline_behaviour_eq`. -/
theorem compact_baseline_behaviour_eq_of_oracles
    (oracles : List (Option (Spt Nat)))
    (input : Guest.InputBlob) (out : RiscV.NativeSource.Output)
    (compiled : out.declarations = sourceDeclarations ∧
      out.artifact = compileProgAsmFast (oracleCompilerConfig oracles) riscvConfig sourceDeclarations)
    (hstack : ∃ depth,
      (compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig sourceDeclarations).2 =
        some depth ∧ depth ≤ 7480)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (ms : RiscV.L3.riscv_state) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (c : Backend.Config) (heapLen : Nat) (adj2 adj4 : BitVec 64)
    (cbspace dataSp : Nat)
    (installed : CompactBaselineInstallation input out mc ms bytes bitmaps c heapLen adj2 adj4 cbspace dataSp)
    (nonfail : sourceBehaviour input ≠ HolBehaviour.fail) :
    ∀ behaviour, machineSemHOL mc (sourceFfi input) ms behaviour →
      behaviour = sourceBehaviour input := by
  obtain ⟨hmc, hart, hpositive, hsplit, hbase, hlen, htop, hglobals, hdomain,
    haligned, hadj2, hadj4, hleft, hright, hmax, hendian, hinstalled, hlimits⟩ := installed
  obtain ⟨depth, hdepth, hbound⟩ := hstack
  have hcomp : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (bytes, bitmaps, c), some depth) := by
    apply Prod.ext
    · have ha := hart
      rw [compiled.2, compileProgAsmFast_eq_fst] at ha
      exact ha
    · exact hdepth
  exact compact_oracle_baseline_behaviour_eq oracles input mc ms bytes bitmaps c
    depth heapLen adj2 adj4 cbspace dataSp hcomp hbound
    ⟨hmc, hpositive, hsplit, hbase, hlen, htop, hglobals, hdomain,
      haligned, hadj2, hadj4, hleft, hright, hmax, hendian, hinstalled, hlimits⟩ nonfail

#print axioms compact_heapRegs
#print axioms compact_stack_names_spt
#print axioms compact_stack_diff_le_maxHeap
#print axioms compact_stack_bound_fits
#print axioms compact_oracle_baseline_behaviour_eq
#print axioms compact_baseline_behaviour_eq_of_oracles

end InitECandidate.Solver
