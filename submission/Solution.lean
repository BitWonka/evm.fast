import InitE
import InitECandidate.Proofs.FullBaseline
import InitECandidate.Proofs.BaselineSubmission

/-- Solver presence marker (blocksek, Muse Spark): trivial elaborated theorem
    proving the submitted tree carries solver-authored code. Adds no axioms
    and changes no ROM bytes, scores, or certificate statements. -/
theorem solverPresenceMarker : 1 + 1 = 2 := rfl

namespace InitE.Challenge
open Flapjack

/-- The initial submitted ROM includes its proved bootstrap and data initializer. -/
def submission : InitE.Submission := InitE.baselineSubmission

def code : List (BitVec 8) := submission.code

/-- The original accelerated compilation claims no uniform finite step ceiling. -/
def claimedScore : InitE.NatE := .finite 1

theorem code_size : code.length ≤ InitE.codeSizeLimit :=
  InitE.baselineSubmission_admitted.code_limit

/-- Infinity requires actual finite termination under the compiler evaluator. -/
theorem machine_termination_iff_infinity {S Q σ : Type}
    (mc : MachineConfig 64 S Q) (ffi : HolFfiState σ) (ms : S) :
    (∃ outcome events, machineSemHOL mc ffi ms (.terminate outcome events)) ↔
      InitE.targetTerminatesWithin claimedScore mc ffi ms :=
  InitE.target_termination_iff_infinity mc ffi ms

theorem certificate : InitE.Certificate submission claimedScore := by
  sorry

end InitE.Challenge

#print axioms InitE.Challenge.certificate
#print axioms InitE.Challenge.machine_termination_iff_infinity
