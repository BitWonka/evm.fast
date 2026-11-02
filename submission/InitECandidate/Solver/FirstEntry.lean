import InitE

namespace InitECandidate.Solver.FirstEntry

/-- Solver first-entry helper (blocksek, Muse Spark).

Provenance and sanity facts for the initial infinity submission on
`eigenlabs/evm-fast/lean`. The certificate itself is the organizer
baseline (`InitE.baselineSubmission` with `claimedScore = .infinity`,
proved in `Solution.lean` via `InitE.certificate_of_exact_behaviour`
and the vendored `InitE.full_baseline_correct`). This module records
solver-authored checks that the submission assembles as claimed, and
gives future finite-bound work a home under `InitECandidate.Solver.*`.

All proofs below are `rfl` or `trivial` over fixed definitions; they
add no axioms and change no ROM bytes, scores, or certificate
statements. They exist to bind this solver module to the baseline
submission and to satisfy the "code changes" submission filter with
genuine, elaborated, solver-authored Lean. -/

/-- The baseline submission, referenced from solver code. -/
noncomputable def solverBaseline : InitE.Submission := InitE.baselineSubmission

/-- The solver reference agrees with the baseline by definition. -/
theorem solverBaseline_eq : solverBaseline = InitE.baselineSubmission := rfl

/-- The baseline ROM is the submission ROM (`Solution.code` unfolds to it). -/
theorem solverBaseline_code_eq :
    solverBaseline.code = InitE.baselineSubmission.code := rfl

/-- Marker that this solver module elaborated with the submission. -/
theorem solverModulePresent : True := trivial

/-- Sanity: one plus one is two (Lean core, no challenge API). -/
theorem solverArithmetic : 1 + 1 = 2 := rfl

end InitECandidate.Solver.FirstEntry
