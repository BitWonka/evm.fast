# Kernel-checked computation benchmarks

For a step-by-step workflow for bounded experiments, see the
[comparator speedup guide](COMPARATOR-SPEEDUP-GUIDE.md).

Run from `init-e` after building the helper modules:

```sh
lake build InitECandidate.Proofs.KernelComputation InitE.MetadataComputation InitE.NameComputation InitECandidate.Proofs.CompilerComputation
python3 tools/bench-lean-computation.py --family utf8 --sizes 256 1024 4096 16384 --timeout 30
python3 tools/bench-lean-computation.py --family lexer --sizes 1 4 16 --timeout 20
python3 tools/bench-lean-computation.py --family parser --sizes 1 4 16 --timeout 30
python3 tools/bench-lean-computation.py --family metadata --sizes 8 32 128 --depth 128 --timeout 30
python3 tools/bench-lean-computation.py --family distinct --sizes 64 128 256 --depth 0 --timeout 30
python3 tools/bench-lean-computation.py --family compiler --sizes 1 4 16 --timeout 60 --setup .lake/build/ir/InitECandidate/Proofs/ArtifactFacts.setup.json
```

The runner writes the generated Lean fixtures, logs, timings and incremental
`results.json` under `work/lean-perf/`. Cases run sequentially on one logical CPU
with identical imports in both variants. It obtains the Lake environment once,
then times Lean directly; timing the `lake env` wrapper loses child CPU/RSS
accounting when a timeout kills it. The timeout is per experimental fixture;
full verifier builds use 16 logical CPUs, at most 16 active Lean compilers,
112 GiB with zero swap, and an eight-hour limit per build/comparison step. Exit status is nonzero
if any fixture fails, times out or reports additional axioms. A timeout is an
unfinished proof, never a success. Wall/CPU time and peak RSS include imports,
elaboration and kernel checking, and can vary with other host activity.

## Byte conversion measurements

Measured on 2026-10-05, Lean 4.33.1 and Flapjack
`7981f765cdadecf9b2857f326a65bae47371ab15`:

| ASCII bytes | Ordinary reduction | Verified shortcut | Shortcut peak RSS |
| ---: | ---: | ---: | ---: |
| 256 | 20.33 s (9.81 s CPU) | 0.72 s | 1,577 MiB |
| 1,024 | unfinished at 30 s | 0.88 s | 1,621 MiB |
| 4,096 | unfinished at 30 s | 1.53 s | 1,808 MiB |
| 16,384 | unfinished at 30 s | 4.84 s | 2,556 MiB |

Both successful variants report exactly `propext` and `Quot.sound`.
Retained raw results: `work/lean-perf/scaled-utf8-direct/results.json`.

`InitECandidate.Proofs.KernelComputation.byteArray_toList` proves equivalence between the
byte-array loop and its underlying array's list. The scoped simplifier proposes
a byte-list literal and returns that proved equality. Native computation only
constructs the proposed term; the kernel checks its relationship to the source
string. Enable the rule with `open scoped InitECandidate.Proofs.KernelComputation`.
ASCII and multibyte UTF-8 probes have also passed. This targets byte conversion,
not the whole parser or compiler.

## Other bottlenecks and current scope

Parser equality on 1, 4 and 16 tiny functions remained unfinished at 30 seconds,
with or without faster byte conversion. Lexing these programs also exceeded a
20-second cap. Deferring partially applied grammar rules did not resolve the
problem and was not retained as a production optimization. The AST-based
challenge removes parser agreement from required certificate dependencies.

`InitE.MetadataComputation.functionNames_toHOL` proves that extracting function
names commutes with AST-to-HOL conversion. Its scoped rule defers evaluation of
function-record fields until metadata projections need them. The original
shallow fixture (32 expression levels, identical bodies) passed in about one
second in both variants, so it did not establish a speedup. The runner now uses
distinct bodies to avoid misleading sharing and accepts `--depth` for stronger
examples. All successful metadata probes use only the three standard axioms.

With 128 distinct bodies at depth 128, ordinary name projection took 16.74 s
and the proved projection took 14.23 s. This is a modest gain, not a full
solution. Numeric fingerprints reduce quadratic byte-string comparison:
64 common-prefix names took 29.29 s with ordinary distinctness and 5.21 s
with numeric fingerprints. Sorting fingerprints and checking adjacent strict
order passed at 256 names in 19.03 s; 512 and 1,024 remained unfinished at
the 30-second cap. Literal-codec shortcuts did not materially improve these
fixtures. These results point to additional costs in symbolic proof reduction.

## Small AST compilation

Reference byte lengths are obtained by native execution only to propose the
literal target. They are then proved by Lean. The baseline executable allocator
hits the fixture's recursion limit; enabling its proved equality with the pure
allocator produces successful kernel-checked proofs:

| Functions | Byte-length proof time | Peak RSS |
| ---: | ---: | ---: |
| 1 | 27.21 s | 5,763 MiB |
| 4 | 27.99 s | 5,892 MiB |
| 16 | 30.72 s | 6,311 MiB |
| 64 | 44.98 s | 8,475 MiB |

All passing proofs report only the three standard axioms. The helper is scoped
as `InitECandidate.Proofs.CompilerComputation`; it changes proof evaluation, not the compiler's
output. Two identical proofs took 40.93 s / 5,947 MiB with asynchronous
elaboration and 39.94 s / 5,785 MiB with serial elaboration, so this fixture
shows no large concurrency effect within one module. The full source and
artifact modules are nevertheless sequenced to avoid their simultaneous
memory peaks. Source checks also use serial elaboration as a conservative
memory bound.

Compact measurement records are retained in
[benchmarks/lean-computation-2026-10-05.json](benchmarks/lean-computation-2026-10-05.json).
The last two 512-name cases in the first fingerprint experiment were invalidated
by rebuilding the imported helper during the run; they are excluded from
performance conclusions. Later completed runs used stable helpers.

The full baseline still needs fast, kernel-checked artifact and stack-bound
proofs. The last complete isolated attempt exhausted 64 GiB before comparison;
these small successes do not imply that the full verifier passes.

The source facts are now split into sequential compilation units. In the first
outside-isolation run, parameter uniqueness took 37 seconds, function-name
uniqueness 40 seconds, struct/global shapes 56 seconds, exception bounds 28
seconds, main membership 17 seconds, and source good-code checking 55 seconds.
Stack analysis and the full compiler artifact equality remain pending.
`ImageComputation.initialMemory_eq` uses proved region lengths to select the
prefix, native code, or suffix before inspecting bytes. With this rewrite,
`BootstrapCodeFacts` passed in 5.5 seconds; the former direct check reached its
recursion limit after 60 seconds. A literal compiler-metadata probe also passed
with only the three standard axioms after unfolding irreducible finite bounds.

The suffix-only bitmap check with repeated word indexing was still unfinished
at its five-minute exploratory limit. `BitmapComputation.range_bytes_eq` proves
that this indexed definition equals a linear traversal emitting eight bytes
per word. Rewriting with that lemma let the full `BitmapImageFacts` module
build outside isolation in 39 seconds. The lemma's axiom closure is
`propext, Quot.sound`; no generated index or extra axiom is needed.

A proved frame-only stack analyzer avoids native body construction when only
frame sizes are needed. On a 16-function constant-body fixture, the original
analyzer proof took 11.79 seconds and the frame-only version 12.22 seconds;
both passed using exactly the three standard axioms. This does not establish
a useful performance improvement, so the full guest's running stack proof
has not been replaced on this evidence.

`SourceStackFacts.lean` remains the long-running module: its one proof computes
source lowering, Word optimization/allocation, frame sizing and call-graph
depth. Source lowering and Word optimization are also computed by artifact
certification. `Tools.GenWordStages` prototypes proposed literals and separate
per-function optimizer equalities at `WordToWord.fullCompileSingleWith`.
The first complete lowered-function literal (466,748 bytes) typechecked.
No generated stage data is a proof until its compiler equality is checked;
the stage split has not yet replaced the running full stack proof.

For actual guest function 65 (52,788 bytes of lowered Word syntax), the full
optimizer proof without an oracle did not finish within 120 seconds. A native
proposal for the allocator's coloring was accepted by `oracleColourOk`.
The corresponding kernel proof that oracle-based optimization yields the same
proposed optimized Word program passed with exactly `propext`,
`Classical.choice`, and `Quot.sound`. This is an experimental compiler input;
the default-config challenge certificate still needs either cached stage
proofs or a derived correctness wrapper for explicit allocation oracles.

## Baseline metadata certificate

`InitE.baseline_finite_facts` previously ended in `decide_cbv`, which embedded a
large reduction proof in the exported environment. After unfolding the same
definitions, the proof now converts a kernel-checked Boolean equality with
`of_decide_eq_true (by kernel_rfl)`. The theorem statement and finite metadata
values are unchanged.

The bounded benchmark targets only this theorem and uses the verifier's actual
declaration comparison, primitive comparison, axiom audit, and independent
kernel replay. Two alternating trials produced:

| Metric | `decide_cbv` control | Compact proof |
| --- | ---: | ---: |
| Median comparator wall time | 18.09 s | 11.55 s |
| Median kernel replay | 4.491 s | 2.204 s |
| Solution export | 65.35 MB | 34.01 MB |
| Fixture `.olean` | 30.59 MB | 32.95 KB |
| Peak comparator RSS | 1,987,446 KiB | 1,691,230 KiB |

Both variants were accepted and depend only on `propext`, `Classical.choice`,
and `Quot.sound`. Direct builds of `CompilerInstallationMetadata.lean` and
`BootstrapCopyGuards.lean` passed after the change. No whole-submission
comparator was run, so the effect on total verifier wall time remains unknown.
Reproduce the fragment experiment with
`tools/certificate-bench/metadata.py`; portable results are in
[metadata-results.json](../tools/certificate-bench/metadata-results.json).


## Compiler-pass checkpoints and dead-code subterms

The eight-function allocation-oracle sample certifies functions 65–71 using only
`propext`, `Classical.choice`, and `Quot.sound`. Function 65 took 47 seconds;
functions 66–71 took 8.5–17 seconds in that concurrent run. Function 64 did not
finish within the four-minute experiment limit. A direct kernel-reduction
experiment on function 65 also exceeded its one-minute limit.

Splitting function 64 at pass boundaries isolated dead-code elimination: its
first three pass proofs completed in 5.5, 3.2, and 5.4 seconds, while the fourth
pass did not finish within the remaining four-minute experiment budget.
A structural-recursion mirror of that pass is proved equal to Flapjack's pass
in `submission/InitECandidate/Proofs/DeadComputation.lean`, with only `propext` and `Quot.sound`, but the
structural-only and sequence-constructor experiments also exceeded their
120-second and 90-second limits. These are not successful verification results.

The next certificate splits dead-code elimination into individual program
subterms, following the suggestion to keep intermediates nonreducible and apply
explicit equations. `Tools/GenWordStages.lean --dead-checkpoints` produces 1,493
nodes for function 64. Both `irreducible` and `cbv_opaque` are necessary: `cbv`
otherwise expands irreducible definitions. Each node's equation rewrites its
certified child equations and performs only the local computation. Literal
register-set contexts are shared across nodes. The current certificate remains
an experiment until its build and the input/output bridges pass.

Generated stage proposals do not establish compiler correctness by themselves.
The full compiler-artifact equality, source stack bound, and isolated verification
still need to pass. Do not run all proposed optimizer modules concurrently: the
largest unsplit proof already exceeds tens of GiB.


The subterm cache now uses `InitECandidate.Proofs.ComputationCache.boxedValue`: an opaque
function returning a subtype containing its checked defining equation. Its
body and equation are kernel checked, and `boxedValue_eq` depends on no axioms.
This prevents even full-transparency kernel reduction from reopening a cached
program tree. Input/output bridges must use the explicit defining equations;
definitional equality alone cannot open these caches. This is stronger than
marking ordinary definitions `irreducible` or `cbv_opaque`, which only controls
meta-level reduction. The generated certificate is split into groups of 32 nodes
and remains pending until all groups and both literal bridges finish.


The sealed certificate now passes all 1,493 nodes and its input/output bridges
for the original `WordAlloc.removeDeadProg pass64_2 = pass64_3` proposition.
The complete certificate run took 106.3 seconds and peaked at 3,417,508 KiB;
that run ended with a small root-context alias mismatch in the final bridge.
After explicitly normalizing its three empty contexts, the bridge module built
successfully in 6.1 seconds. Its axiom closure is exactly `propext` and
`Quot.sound`. The cache equation itself uses no axioms.

The formerly growing late certificate files now consistently take 1.8–2.1
seconds, including the files that previously took 22–39 seconds. This certifies
one compiler pass on the real largest-function sample; it does **not** establish
that the full challenge or isolated verification has passed. The remaining
passes and full compiler linkage still need measurement and certification.


All eleven optimizer pass proofs for function 64 now pass. The remaining
passes after dead-code removal took 19, 11, 2.0, 3.9, 8.5, 14, and 2.1 seconds.
The complete `fullCompileSingleWith` theorem is assembled from these equations
in `submission/InitECandidate/Proofs/WordStages/Optimize64.lean`; it built in 1.8 seconds (2.62 seconds
including Lake), with the exact three standard axioms. The older single
computation of the same theorem did not finish in four minutes. These module
timings use already-built dependencies and do not claim a cold whole-project
build under twenty minutes.


Frontend checkpoints exposed a separate large-value problem: even the combined
18 MB data declaration exceeded a 45-second data-only experiment. The initial
eight declaration-sized simplification proofs passed in 1.3–1.8 seconds, but
most were tiny globals, so a second sample selected large function bodies.
The largest declaration (index 721) had about 9 MB each of original and
simplified literal text. Sharing explicitly typed `Prog (BitVec 64)` subterms
reduced both together to a 296,517-byte data module with 2,684 subdefinitions.
That data module built successfully in 9.5 seconds. Its transformation proof
is measured separately; successful data elaboration alone is not compiler
correctness. The generator supports `--frontend-declarations --largest
--data-dag` for reproducibility.

The largest frontend declaration (721) also passed its simplification proof in
4.0 seconds using only `propext`, `Classical.choice`, and `Quot.sound`. All 928
source declarations have now been generated as shared typed subterms. Sixteen
dependency lanes bound concurrent frontend proof elaboration; the aggregate
frontend build is being measured before integration into the stack certificate.

The complete AST/simplification aggregate now passes: 928 AST agreement
theorems and 928 simplification theorems compose into `sourceDeclarations_eq`
and `panSimpSource_eq`. The corrected run took 5:08.66 wall time on 16 CPUs
with dependency caching from the earlier trial; it is not a cold full verifier
measurement. The aggregate module itself took 25 seconds and peak per-process
RSS was 7,583,460 KiB. Both aggregate theorems use exactly the three standard
axioms. Log: `work/lean-perf/word-stages/frontend-source-build.log`.

The largest declaration also passed struct lowering for arbitrary contexts in
7.24 seconds. `StructComputation.compileTop_identity` composes these independent
certificates into the original struct compiler evaluator, using only `propext`
and `Quot.sound`. Whole-source struct composition is the next check.

All 928 context-general struct declaration certificates passed. Their first
aggregate run (1:54.89) reached only a composition step limit; after a local
simplifier limit and empty-list endpoint fix, the composition took 2.6 seconds.
The integrated `FrontendStages.Pass0` and `Pass1` wrappers each build in about
1.4 seconds and print only the three standard axioms.

Shared typed Word subterms reduced the largest input, function 713, from
37,689,622 bytes to about 1 MiB. Its data-only module builds in 13 seconds,
peak RSS 3,315,864 KiB. Its first two exact compiler passes passed: expression
simplification 66 seconds (6,828,120 KiB), instruction selection 49 seconds
(4,241,616 KiB). Both pass theorems use only `propext` and `Quot.sound`. These
are bounded stage measurements, not a complete compiler or verifier pass.

Global lowering of the largest frontend declaration (721), including exact
function-name permutation and the compiler's finite-map context for all 93
globals, passed in 17 seconds; standard axioms only. Its generated source
shares typed program nodes and is 363,077 bytes. Log:
`work/lean-perf/word-stages/frontend-globals721-build.log`.

The largest Word SSA conversion (713/pass2) exceeded the bounded 120-second
experiment. It is now being measured with a 600-second limit, while opaque
dead-code checkpoints are generated separately. The full proof budget has
not yet been demonstrated.

The largest SSA conversion passed in 198 seconds (3:19.67 including Lake)
with standard axioms. The 1493-node sealed dead-code example, rebatched from
32 to 256 nodes per module, passed in 1:18.10 including its exact pass bridge,
peak RSS 3,405,608 KiB; the previous 32-node run took about 106 seconds for
checkpoints alone. The largest dead-code proposal contains 17,409 nodes.
`tools/rechunk-dead-proofs.py` rebatches these without repeating native
generation.

The first all-functions global-lowering run took 5:06.48 and failed on
generated multiline record layout in several small functions; it is not
a pass. The generator and affected files have been corrected for a retry.

All 825 global-lowering function certificates and their exact
`compileFunctionDeclarations_eq` composition have now passed; the composition
module took 38 seconds. The aggregate retry reached the final source ordering
lemma after 8:21.55 but failed because its restricted simplifier omitted Boolean
filter/list concatenation rules. This last lemma is being retried separately.

The Word data layout experiment showed that naming every tiny node adds
elaboration overhead. `tools/compact-word-data.py` retains shared/large nodes
and inlines single-use subterms up to 1024 bytes and depth 32. Function 713's
first pass data module then built in 15 seconds instead of 61 seconds; the
compiler equality is being checked against the compact layout separately.

The final global source ordering lemma now passes in 5.7 seconds with the
three standard axioms. All 825 global function certificates, their compiler
composition, and the exact source resorting agreement are checked.

Function 713's compact first-pass theorem passed in 50 seconds, using only
`propext` and `Quot.sound`. Its independently scheduled CSE theorem passed in
563 seconds (9:39.77 including concurrent input/output data builds), peak RSS
21,953,792 KiB, with the same two axioms. Data-only CSE input/output modules
each took 14 seconds. The dense input/output scheduling experiment hit its
180-second bound; it did not constitute a compiler pass.

The largest dead-code proof reached node 13,823 before exposing a two-layer
opaque branch alias. `DeadBranchComputation.removeDeadStructural_ite_eq`
replaces constructor matching by checked Boolean shape facts, without changing
the compiler definition or invalidating earlier checkpoints. The repaired
256-node chunk passed in 10 seconds, using only `propext` and `Quot.sound`.
Remaining chunks and later independent compiler passes are being checked.

All 17,409 sealed dead-code checkpoints and the original exact pass equality
for function 713 now pass with only `propext` and `Quot.sound`. The dense
input/output bridge module took 363 seconds, with its generated data included;
the last resumed run took 8:46.24 and peaked at 14,288,364 KiB. These resumed
timings do not demonstrate a cold complete compiler build under 20 minutes.
The bridge should be split/compacted next.

The later compact, independent function-713 pass group passed in 4:57.20:
copy propagation 235s, three-to-two conversion 1.7s, unreachable elimination
42s, second dead pass 192s, checked allocation oracle 283s, and must-terminate
removal 3.5s. The allocator peak was 28,986,656 KiB; every pass printed only
standard axioms.

Source-derived global initializer context and the initializer/exception
compiler fragments have passed. A generic first-function lookup equation now
passes in 0.8s with standard axioms; a name-only tactic macro exposes the
pinned private evaluator's defining equation. This prevents deep kernel
unfolding of the complete declaration projection during top-stage composition.
The concrete whole-global-stage composition is being retried separately.

The complete global-stage composition now passes in 1.5 seconds, using only
`propext`, `Classical.choice`, and `Quot.sound`. The earlier concrete proof
exceeded its 120-second experiment bound. `GlobalsTopComposition` proves
renaming, three-list compilation, and top-level assembly with abstract source
and intermediate lists. `FrontendStages.Pass2` applies these equations to the
checked concrete facts; it never unfolds every program body during composition.
The incremental Lake run took 3.54 seconds, peak RSS 5,092,556 KiB. Log:
`work/lean-perf/word-stages/frontend-stage2-abstract-build.log`.

Function 713's complete optimization theorem now composes all eleven checked
passes in 2.3 seconds. `Sparse713.Agreement3` checks that the compact dead-code
DAG equals the original checked output. `Optimize713` reuses that agreement
and the existing compact later-stage proofs; it defines the allocation oracle
explicitly and disables implicit theorem parameters. The incremental Lake run
took 3.22 seconds, peak RSS 4,135,012 KiB, with exactly the three standard
axioms. Log: `work/lean-perf/word-stages/optimize713-compose-build.log`.
These are composition timings with cached prerequisites. They do not establish
a cold complete build under 20 minutes or a successful isolated verifier run.

The dead-code bridge for function 713 has also been split into 34,818 small
node agreement lemmas (17,409 input and 17,409 output), in 69 modules.
`tools/split-checkpoint-agreements.py` uses text hashes only to propose matching
DAG nodes; each match is proved by explicit child equations and kernel-checked
reflexivity. All agreements pass with no axioms or `propext` only. The first
chunk took 2.6s; later chunks took 2.6–3.5s. The independent dense SSA data
module took 98s. An initial 2:26.91 run reached chunk 053 but failed because a
redundant tactic followed an already closed alias proof; that is not a pass.
The corrected remaining group, final bridge, and optimization composition
passed in 1:33.56, peak RSS 12,533,896 KiB. The final bridge itself took 38s;
optimization composition took 2.4s. Logs:
`work/lean-perf/word-stages/checkpoint-agreement713-first-build.log`,
`work/lean-perf/word-stages/checkpoint-agreement713-all-build.log`, and
`work/lean-perf/word-stages/optimize713-node-bridge-build.log`.

A largest-function cold-root benchmark now uses an independent `buildDir`,
`enableArtifactCache = false`, affinity to 16 logical CPUs, and a 1200-second
time bound. Pinned dependency artifacts are retained, as in the verifier.
Lake otherwise restores offline artifacts even into a fresh build directory;
the 0.92-second cache-control run is not a cold build. The actual cold-root
benchmark log is `work/lean-perf/word-stages/optimize713-cold-build.log`; its
final result passed in **14:05.37**. The build recompiled the entire root-module
dependency closure of `InitECandidate.Proofs.WordStages.Optimize713`, with 16 logical CPUs
and offline artifact restoration disabled. User CPU time was 3325.01s, system
time 100.23s, and peak single-process RSS 28,986,804 KiB. The largest CSE
proof took 633s, SSA 259s, allocation 294s, and the complete optimization
composition 2.4s; the final theorem printed exactly the three standard axioms.
This demonstrates the under-20-minute target for the largest representative
optimization proof, not the full challenge/submission build or isolated verifier.

`tools/split-dead-checkpoints.py` separates each sealed checkpoint module into
cache data/shape equations, independent conditional computation theorems, and
closed composition. A conditional theorem explicitly takes the exact child
conclusions as arguments; composition supplies the already proved children.
The resulting root theorem has no premises and uses only standard axioms.
The 1493-node function-64 checkpoint root passed in **40.44s**, peak RSS
2,687,432 KiB, with 16 logical CPUs. This timing excludes its complete
compiler-pass input/output bridge; the earlier 78.10s timing included that
bridge. Log: `work/lean-perf/word-stages/dead64-parallel-build.log`.

The same split for all 17,409 function-713 checkpoints passed in **7:43.99**,
peak single-process RSS 6,271,972 KiB. Data chunks took about 6–7s, conditional
proof chunks about 5–6s, and composition chunks about 2s. The final closed
root theorem printed only `propext` and `Quot.sound`. Its exact compiler-pass
bridge and all 34,818 data agreements also passed in 3:57.08 with data and
conditional computation prerequisites cached; the final bridge took 38s.
Peak RSS was 12,641,800 KiB. The optimization certificate now uses this
parallel checkpoint implementation. This incremental timing does not replace
the earlier 14:05.37 cold measurement of the previous implementation. Log:
`work/lean-perf/word-stages/dead713-parallel-build.log`.

The native-only `--word-largest` report identifies 826 functions. Function
713 has 14,331 source Word nodes; the next largest, 240, has 4,215. Reports
only propose sizes and data; every compiler equality still requires a checked
proof. The generic per-declaration Pancake-to-Crep composition equations
(`CrepComputation`) pass with `propext` and `Quot.sound`; concrete frontend
outputs and the complete pipeline remain to be certified.

The parallel compiler-pass bridge log is
`work/lean-perf/word-stages/dead713-parallel-bridge-build.log`. No source AST,
compiler pass, native byte, score, or runtime memory-layout change is involved
in this proof scheduling change.

After selecting the parallel checkpoint bridge, `Optimize713` was rechecked
and passed in 2.5s (3.42s including Lake), with exactly `propext`,
`Classical.choice`, and `Quot.sound`. The corresponding log is
`work/lean-perf/word-stages/optimize713-parallel-compose-build.log`.

The frontend declaration data now imports only the AST computation helpers;
AST agreement imports `Guest.Ast`, and the whole-list aggregate imports
`SourceDeclarationsCore`. Compiler-correctness imports remain at their actual
consumers. The first representative thin-import build (declaration 0 and Crep
metadata context) passed in 9.52s with 109 jobs, versus the earlier large
dependency graph. This is an incremental import check, not a cold full build.
Log: `work/lean-perf/word-stages/frontend-thin-imports-first-build.log`.

Structural identity lemmas now prove the empty-map Crep inline pass preserves
every program, without evaluating a concrete whole-program AST. The generic
module passed in 1.1s; all three lemmas print only `propext` and `Quot.sound`.
Log: `work/lean-perf/word-stages/crep-inline-empty-build.log`.

Global output AST values are separated into `Globals/OutputN` modules;
`TranslateN` retains the original exact equality proofs and sixteen proof
lanes. Run `tools/split-global-outputs.py` after regenerating global outputs.
Crep translation consumes the output module directly. The largest Crep
translation (649, original declaration 721) now passes in 9.1s with exactly
the three standard axioms. The incremental output plus proof build took
15.74s, peak RSS 3,501,580 KiB. Its prerequisite AST simplification modules
were cached by a preceding 180-second bounded run, so this is not a cold
whole-frontend measurement. Log:
`work/lean-perf/word-stages/frontend-crep649-output-build.log`.

After the import/output split, the whole frontend through global lowering and
Crep metadata agreement passed. The first bounded rebuild timed out at 600s
with 47 of 5,722 jobs remaining, without proof errors. Resuming checked modules
completed in 4:15.18, peak single-process RSS 9,861,448 KiB. The global function
aggregate took 37s, header facts 73s, initializers 11s, complete global stage
1.2s, and Crep metadata agreement 84s. All printed only the standard three
axioms. This two-run incremental result is not a cold full challenge build.
Logs: `frontend-crep-context-thin-build.log` and
`frontend-crep-context-resume-build.log` under `work/lean-perf/word-stages/`.
The generic checked-output composition lemma (`CrepComposition`) also passed
in 1.4s, using only `propext`.

All 826 Pancake-to-Crep function certificates and their checked-output
composition passed in 5:49.47 with 16 logical CPUs and frontend prerequisites
cached. Peak single-process RSS was 5,173,184 KiB. The aggregate theorem took
2.6s and printed exactly the standard three axioms. Logs:
`work/lean-perf/word-stages/frontend-crep-functions-build.log`.
`tools/compose-crep-proofs.py` generates sixteen dependency lanes and composes
only explicit checked per-function equations. Full challenge/submission timing
and isolated verification remain pending.

The complete Pancake-to-Crep stage (`FrontendStages.Pass3`) passed in 2.7s
(4.03s including Lake) after component prerequisites were checked. Both the
raw Crep-output theorem and the complete empty-inline stage theorem print
exactly `propext`, `Classical.choice`, and `Quot.sound`. Peak RSS was
5,446,192 KiB. Log: `work/lean-perf/word-stages/frontend-stage3-build.log`.

The largest representative Crep-to-Loop function (649) passed in 33s; its
compact Loop DAG data compiled in 17s and shared metadata context in 5.9s.
Total incremental build time was 56.86s, peak RSS 5,953,304 KiB, with exactly
the standard three axioms. The native proposal uses explicit width-64 AST
quoting because generic ToExpr deriving cannot quote the proof-valued NeZero
parameter; that generator is outside the proof boundary, and the literal is
checked against the original exact compiler definition. Log:
`work/lean-perf/word-stages/frontend-loop649-build.log`.

The concrete Crep-to-Loop function-map agreement passed in 67s (1:10.53
including Lake), peak RSS 9,775,872 KiB. It compares names, function labels,
and parameter counts while leaving bodies unused. Both metadata theorems
print only the standard three axioms. The generic Loop compiler
decomposition and map-congruence module passed in 1.3s. Log:
`work/lean-perf/word-stages/frontend-loop-context-build.log`.

All 826 exact Crep-to-Loop function certificates passed in 7:22.14 with
16 logical CPUs, peak single-process RSS 6,362,972 KiB, and frontend
prerequisites cached. The function aggregate took 4.7s. The complete
whole-program Crep-to-Loop stage (`Pass4`) then passed in 2.3s (8.25s
including an aggregate recheck and Lake), peak RSS 7,610,268 KiB. Both
aggregate and full-stage theorems print exactly the three standard axioms.
Logs: `frontend-loop-functions-build.log` and `frontend-stage4-build.log`
under `work/lean-perf/word-stages/`.

The monolithic largest Loop-to-Word function equality (649) hit its
180-second timeout, reaching roughly 49 GiB RSS during an observation.
Separating its assigned-variable set, remaining variables, and register
context succeeded in 4.1s (4.92s including Lake), peak RSS 3,132,656 KiB;
all three equations print only `propext` and `Quot.sound`. The bottleneck
is therefore body compilation, which is being split into local compiler
equations with opaque compiled-output checkpoints. Logs:
`frontend-word649-build.log` and `frontend-word649-context-build.log`
under `work/lean-perf/word-stages/`.

The generic sequence, branch, loop, and mark compiler equations
(`LoopWordComputation`) passed in 908ms. They take exact child compiler
results as hypotheses and derive the parent result without reducing the
child output programs. Each prints only `propext` and `Quot.sound`; closed
checkpoint composition still needs to supply all child equations and connect
the root to the supplied Word literal. Log:
`work/lean-perf/word-stages/loop-word-local-equations-build.log`.

For the largest Loop-to-Word body, the checkpoint generator proposes 10,764
compiled-output caches in 144 groups of 75. Input nodes are the existing Loop
DAG definitions. Each conditional proof takes the exact child compiler results;
closed composition supplies them. Separate output equations connect the opaque
values to the supplied Word DAG. The first 75 checkpoints passed in 3.22s
with cache data already checked, peak RSS 2,978,300 KiB. Closed computation
proofs printed `propext` and `Quot.sound`; the printed output-source agreement
uses no axioms. Whole-body verification is still pending this measurement.
Log: `work/lean-perf/word-stages/frontend-word649-checkpoints-first-build.log`.

All 10,764 largest-function Loop-to-Word checkpoints and Word-source
agreements passed in 3:07.81 with prerequisites cached and 16 logical CPUs.
Peak single-process RSS was 3,091,148 KiB, compared with roughly 49 GiB
observed during the monolithic proof that timed out at 180s. User CPU time
was 508.44s and system time 227.43s. The closed body certificate printed
only `propext` and `Quot.sound`, with no child premises remaining. The final
printed output-source agreement uses no axioms. This is a complete body
certificate; the final tuple and whole frontend still need composition. Log:
`work/lean-perf/word-stages/frontend-word649-checkpoints-build.log`.

The complete largest Loop-to-Word tuple equality (`Word.Translate649`)
passed in 3.5s (4.29s including Lake) after composing metadata and the closed
checkpoint body certificate; it prints only `propext` and `Quot.sound`.
The second-largest Word-source example (index176, label240, 4,215 Word nodes)
also timed out monolithically at 120s; an observation at 90s showed roughly
32 GiB RSS. This motivates output checkpoints for additional functions rather
than treating the first large example as the only slow case. Logs:
`frontend-word649-composed-build.log` and `frontend-word176-build.log` under
`work/lean-perf/word-stages/`.

Grouping the same 10,764 local equations into 384-node groups reduced the
largest full Loop-to-Word certificate build to 1:18.18 (from 3:07.81 for
75-node groups), with prerequisites cached. Peak RSS was 3,930,820 KiB;
user CPU time 224.56s, system 47.79s. The closed body and complete tuple
equalities still print only `propext` and `Quot.sound`. There are 29 active
groups, and the superseded small-group source files were removed. Log:
`work/lean-perf/word-stages/frontend-word649-checkpoints384-build.log`.

The second-largest Word function (index176, label240) now has a closed
3,740-node body certificate and Word-data agreements. All component checks
completed in a 32.45s run; the final tuple initially needed its function label
exposed before rewriting. After that correction, the full tuple passed in
1.6s (2.42s including Lake), peak RSS 3,144,104 KiB, with only `propext` and
`Quot.sound`. Logs: `frontend-word176-checkpoints-build.log` and
`frontend-word176-composed-build.log` under `work/lean-perf/word-stages/`.

### Third opaque Loop-to-Word example and full-stage assembly

Function index 766 (label 830, 4,167 Word nodes) passed the complete
checkpoint/body/tuple certificate in 31.02 seconds with prerequisites cached
(`frontend-word766-checkpoints-build.log`, exit 0; peak individual process
RSS 3,260,620 KiB). Its proof uses only standard axioms. This is a third
representative function, not a complete challenge build.

The large-function proposal batch completed for the measured top thirty
functions. The complete Word frontend now assembles all 826 certificates in
sixteen dependency lanes. Its first bounded build exposed an elaboration issue
at loop nodes: anonymous live-set arguments cannot always be inferred backwards
from already-computed cutsets. The generator now supplies both original live
sets explicitly and checks cutset computation with proof-producing `cbv`,
keeping the compiled child opaque. A four-loop pilot passed in 4.02 seconds
(3.2 seconds for the file) with standard axioms and no extra assumptions.
The full stage and the complete verifier remain pending.

### Complete exact frontend certified

All 826 Loop-to-Word function equations and the aggregate map equation now
pass. `InitECandidate.Proofs.FrontendStages.Pass5.frontend_eq` certifies the original
`panToWordCompileProgHOL riscvConfig.isa sourceDeclarations` against the
supplied per-function Word literals, composing all six frontend stages. Its
printed axiom set is exactly `propext`, `Classical.choice`, and `Quot.sound`.

The first full Word-stage build took 5:16.24 and exposed 39 loop-argument
elaboration failures. A proof-only migration supplied the original live sets;
the repaired run took 2:02.88 and completed all function certificates and their
aggregate (4.9 seconds), leaving only the final compiler composition to fix.
That composition needed explicit reduction of nested let-bindings and the
`globalStart = ofString "main"` equation. The final build succeeded in 4.26
seconds (2.3 seconds for Pass5), peak individual process RSS 8,845,784 KiB.
Logs: `frontend-word-full-build.log`,
`frontend-word-full-repaired-build.log`, and `frontend-word-composed-build.log`.
These are incremental runs with earlier frontend prerequisites cached, not a
cold full challenge build or an isolated verifier result.

The proposal generator can now replace an optimizer literal with a shared DAG
without rewriting a certified frontend literal (`--optimized-only`). Function
240's optimizer output proposal is about 264 KB rather than its previous
multi-megabyte printed tree, and eleven pass proposals permit separate bounded
measurements. Those backend equations are still pending kernel verification.

The second-largest Word optimizer example (label 240) now has checked pass
0 (expression simplification, 19 seconds), pass 1 (instruction selection,
12 seconds), and pass 2 (SSA, 32 seconds). The bounded dependency build
completed in 1:04.26, peak individual RSS 5,255,584 KiB, exit 0; all three
printed axiom sets are `propext` and `Quot.sound`. Its earlier prerequisites
were cached. Log: `optimizer240-first-three-passes-build.log`. Dead-code
removal and the remaining optimizer stages are still pending.

Label 240's monolithic dead-code removal did not complete within the
three-minute limit (exit 124, `optimizer240-dead-pass-build.log`). A process
sample at 2:05 showed 30,698,644 KiB RSS. The timeout wrapper's `time -v`
maximum RSS does not include the terminated Lean child correctly, so it is
not a meaningful memory measure for this failed run. This smaller example
reproduces the largest function's bottleneck. The next proposed proof replaces
whole-tree reduction with opaque input/output checkpoints, small conditional
lemmas, and a closed composition of child certificates.

All 4,745 opaque dead-code checkpoints for label 240, including their closed
root composition, passed in 1:56.21 with prerequisites cached. Peak individual
RSS was 3,298,916 KiB; the root axiom set is `propext`, `Quot.sound`. Log:
`optimizer240-dead-parallel-build.log`, exit 0. The graph contains nineteen
data/conditional/composition groups. Another 9,490 small node-agreement
lemmas connect it to the supplied pass-2/pass-3 ASTs; the full pass bridge
is being checked separately and is not implied by the checkpoint timing.

The literal bridge for label 240's dead-code pass also passed: all 9,490
node agreements plus the final bridge completed in 1:16.67 with checkpoint
prerequisites cached, peak individual RSS 5,172,708 KiB. The final pass
theorem took 9.4 seconds and its axiom set is `propext`, `Quot.sound`.
Log: `optimizer240-dead-bridge-build.log`, exit 0. Thus the complete
checkpoint-and-agreement sequence took 3:12.88 across two runs, and the
complete dead-code pass has a closed standard-axiom certificate. The
monolithic three-minute attempt had failed while reaching roughly 29 GiB
in an observed sample. This comparison does not establish the cold complete
optimizer or full challenge build time; the remaining backend passes, stack
bound, artifact encoding and isolated verifier are still pending.

### Complete second-largest optimizer and stack-computation links

`InitECandidate.Proofs.WordStages.Optimize240.optimize240_eq` now passes with exactly
`propext`, `Classical.choice`, and `Quot.sound`. All eleven pass equations
and their composition are closed. With passes 0--4 and the dead-code graph
previously cached, the remaining pass/composition build took 3:29.94, peak
individual RSS 9,415,336 KiB. Newly checked passes took 56 seconds (copy),
14 seconds (register conversion), 18 seconds (unreachable code), 44 seconds
(second dead removal), 61 seconds (oracle-validated allocation), 7.4 seconds
(must-terminate removal), and 6.8 seconds (composition). This is incremental
evidence, not a cold complete optimizer or challenge build. Log:
`optimizer240-complete-build.log`, exit 0. Its CSE pass separately passed in
1:49.69 (108 seconds for the file), peak RSS 7,425,948 KiB, standard axioms
(`optimizer240-cse-pass-build.log`).

All other optimizer output proposals were compacted into shared Word AST DAGs
without rewriting certified frontend literals. Labels 64, 240, and 713 were
preserved. These other output proposals are not certified by native execution.
The measured large functions now have eleven separately proposed pass equations
and composed optimizer proofs; their remaining kernel checks are pending.
`--large-only` filters functions with at least 1,000 measured Word nodes.

`InitECandidate.Proofs.WordBackendComputation` provides checked structural composition of
per-function optimizer equations and consumes the provided oracle list using
a generic length theorem, rather than computing its coloring values again.
Both generic lemmas use only standard axioms.

The actual source stack analyzer is now factored through `analyzeWordStack`.
`analyzeSourceStack_fixed_eq` reuses the complete frontend equality via
`congrArg`, and `compilerDepthStack_eq` identifies exactly the compiler
correctness theorem's depth calculation. Both links pass with standard axioms
(3.6 seconds for `SourceStackComputation`; total dependency build 50.93 seconds,
including uncached upstream proof modules). The numeric bound 538 and the
complete verifier remain pending. Log: `source-stack-frontend-link-build.log`.

A further large example, label 830 (4,167 source Word nodes), passed its
first three optimizer equations in 1:01.43 total with prerequisites cached:
18 seconds for simplification, 11 seconds for instruction selection, and
31 seconds for SSA. Peak individual RSS was 5,215,632 KiB; all three use
`propext`, `Quot.sound`. Log: `optimizer830-first-three-passes-build.log`,
exit 0. Native proposal generation ran concurrently on the same sixteen
affined CPUs, so this is not an exclusive-machine timing measurement.
The remaining native large-function checkpoint batch is still running; its
results require the separately prepared kernel-checking graph and literal
bridges before being used in the complete compiler certificate.

The native large-function batch completed: 28 functions, 55,390 dead-code
checkpoints. Preparation is reproducible with
`tools/prepare-large-dead-checkpoints.py`. Discarded intermediate outputs
need not correspond to nodes in the final AST, so agreement generation now
follows only the input/output roots' explicit dependencies. All computation
checkpoints remain in the closed root computation proof. Deep root dependency
traversal uses an iterative worklist. Hashes select proposed AST matches only;
Lean proves the resulting equalities.

Two new complete dead-code certificates passed together in 2:11.13:
label 121 exercises discarded intermediate outputs, and label 830 is the
third-largest measured source Word function. Peak individual RSS 5,159,376
KiB, standard axioms only; final bridges took 4.3 and 9.3 seconds. Earlier
compiler prerequisites and label 830's first three passes were cached. Log:
`optimizer-large-dead-two-examples-build.log`, exit 0. The complete 28-function
dead-code batch is now being checked with a 20-minute limit and 16 affined
CPUs; remaining optimizer, stack-bound, artifact, and full verifier gates
are still pending.

### All measured large-function first dead-code passes certified

All 28 large-function dead-code certificates now pass with exactly
`propext`, `Quot.sound`. This includes all 55,390 computation checkpoints,
root-reachable literal agreements, and closed final pass bridges. The initial
16-CPU dependency build took 12:23.26 and exposed 40 loop-context rewrite
failures, with peak individual RSS 24,669,192 KiB. The loop child uses a cached
context list while its parent constructs the equivalent list literally; a
transparency setting alone did not fix rewriting. The checked repair supplies
explicit context/empty-store equations, then rewrites the child certificate.
A pilot passed, and `tools/fix-dead-loop-contexts.py` migrated the remaining
39 cases without changing any program data. New native proposals emit the
corrected equations directly.

The repaired build completed in 1:17.19, peak individual RSS 6,557,412 KiB,
exit 0. All 28 final pass axiom prints contain only `propext`, `Quot.sound`.
Logs: `optimizer-large-dead-full-build.log` (first run, exit 1),
`optimizer-large-dead-repaired-build.log` (successful repair), and
`optimizer-loop-context-pilot-build.log`. These are incremental dependency
checks with earlier frontend/compiler prerequisites cached, not the cold
complete challenge build. The complete optimizer certificates for these 28
functions are now under a separate 20-minute bounded check.

### Complete large optimizer batch and allocation microbenchmarks

The complete 28-function optimizer batch reached its 20-minute limit
(exit 124; `optimizer-large-complete-build.log`). It certified 13 complete
optimizers before timeout, including label 830; this is not a passing full
challenge build. Label 874's allocation equation alone took 675 seconds in
that concurrent batch. Small label 65's complete optimizer passed in 53.67
seconds with prerequisites cached.

Five separate label-874 checks isolate allocation work. Coloring application
passed in 8.80 seconds total (8.0 seconds in the proof module); even coloring,
forced endpoints, and stack-variable constraints passed in about two seconds
per module. The stack probe initially had an unnecessary `unfold colour` and
was corrected before passing. The combined clash-tree construction/check
reached a 180-second timeout while its Lean process had consumed over 150 CPU
seconds. The timeout wrapper's reported RSS/CPU omit the terminated child,
so those numbers are not useful peak measurements. These checks depend only
on `propext`, `Quot.sound`. Logs: `allocation-probe874-*.log` and
`allocation-composition-build.log`.

`AllocationComputation.wordAllocWith_eq_of_checks` now combines separate
certificates for the oracle, even colors, clash validation, applying colors,
stack constraints, and forced endpoints. It avoids evaluating the unused
allocator branch and repeating the colored program. This generic lemma passes
in 696 milliseconds with `propext`, `Quot.sound`
(`allocation-composition-repaired-build.log`). An opaque clash-checkpoint
generator is being tested; its proposed data is not trusted without the
resulting kernel certificates. Full artifact, numeric stack-bound, outside
build timing, and isolated verifier checks remain pending.

### Opaque allocation checkpoints integrated; faster clash validator certified

Label 874 now uses a closed allocation certificate in the actual optimizer.
The checkpoint graph has 1,157 traversal nodes, each with a checked defining
equation and result equation. Conditional chunks take child results as explicit
arguments; final composition supplies all children, leaving no root premise.
Sharing complete live-set literals reduced data from 14,427,431 to 2,680,797
bytes. Sharing their constructor subtrees further reduced it to 917,890 bytes.
No candidate output or challenge semantics changed.

The first closed parallel traversal build took 2:14.38 and passed all traversal
chunks; its final bridge needed an explicit equation identifying the cached
empty live sets with `.ln`. The corrected allocation composition passed in
3.01 seconds with traversal prerequisites cached. Axiom audit: clash certificate
`propext`, `Quot.sound`; exact allocation/optimizer equations standard three
(including `Classical.choice` through the executable allocator argument).

`ClashComputation.checkColSorted_eq` proves an unconditional equivalent validator
using merge sort and a linear adjacent-order check, replacing quadratic
`Pairwise` reduction. Both acceptance and rejection agree with Flapjack's
checker; no validator condition is weakened. The theorem passes with
`propext`, `Quot.sound`. The identical unsplit clash microbenchmark now passes
in 50.43 seconds total (49-second proof module), versus its previous 180-second
timeout. Log: `allocation-probe874-Clash-sorted.log`, exit 0.

Combining the sorted validator and shared live-set subtrees, the actual
`Optimize874` dependency build passed in 1:10.25, peak individual RSS 3,489,420
KiB. Data took 35 seconds; conditional chunks 1.4–11 seconds; final allocation
pass bridge 1.2 seconds. Earlier frontend and passes 0–8 were cached; the new
allocation graph and final passes were rebuilt. Log:
`optimizer874-sorted-checkpoints-build.log`, exit 0, standard axioms only.
The earlier monolithic allocation proof alone took 675 seconds in the
concurrent large-function batch; this is a qualified incremental comparison,
not a cold whole-challenge timing claim.

Reproduction: `GenWordStages --allocation-checkpoints` proposes data;
`tools/split-clash-checkpoints.py` prepares independent checks and closed
composition; `tools/compose-allocation-proofs.py --install` installs the exact
optimizer bridge. `tools/enable-clash-computation.py` locally enables the proved
faster checker in remaining monolithic optimizer proofs. All 826 Word outputs
and structural oracle consumption are now under a single twenty-minute,
sixteen-CPU `WordBackend.FunctionsFacts` check. Numeric stack bounds, artifact
composition, full outside build, and the isolated verifier remain pending.

Stack-frame projection lemmas are now certified in `StackFrameComputation`: the
compiler's sparse frame map equals argument/max-register analysis alone.
`StackDepthComputation.depth_eq_of_word_compile` then rewrites the compiler's
exact stack-depth result through a checked Word compilation equation, avoiding
stack body and bitmap generation. Both modules pass with the standard three
axioms; projection module 1.6 seconds, depth bridge 3.6 seconds (excluding
replayed or rebuilt upstream prerequisites). Logs:
`stack-frame-projection-repaired-build.log`,
`stack-depth-word-output-link-repaired-build.log`. This does not yet certify
the numeric 538 bound.

A further isolated small example tests opaque boundaries between all eleven
optimizer passes in one source module (`Fused65`). It leaves the active full
backend files unchanged. A copied monolithic counterpart (`Monolithic65`)
provides the same source/oracle/output comparison with cached prerequisites.
Both have bounded one-CPU builds; results are pending.

The label-65 opaque-pass comparison passed after removing a redundant final
`rfl` (all eleven step certificates already passed on the first run). The
monolithic counterpart passed in 1:50.89 wall / 52.43 user seconds, peak
5,321,180 KiB; the fused version passed in 3:07.23 wall / 85.78 user seconds,
peak 4,070,420 KiB. Both were affined to one CPU while the larger backend
batch shared those CPUs, so wall times include contention. Standard axioms
only. Root pass boundaries in one module do not improve this example; its
much larger intermediate literal data costs more than it saves. This variant
is retained as an isolated experiment rather than installed into production.
Logs: `optimizer65-monolithic-comparison-build.log`,
`optimizer65-fused-repaired-build.log`.

The full backend run also observed a SIGTERM (exit 143) for allocation label
233, without a proof error identifying a cause. Its original native clash
proposal generator reached a 180-second timeout because it recomputed whole
subtree results at each traversal node. The generator now caches already
computed child results and evaluates only the local checker step. This is
proposal generation only; kernel validation remains mandatory. A bounded
label-233 regeneration is in progress.

The all-function Word backend check reached its twenty-minute limit
(exit 124; `word-backend-full-sorted-build.log`). It checked 410 new complete
optimizers before timeout; root backend composition remains unchecked. Two
allocation workers (233 and sparse 713) exited on SIGTERM without a logical
proof error identifying the reason. Peak individual RSS 30,195,244 KiB,
aggregate CPU utilization 1229%; prerequisites included previously checked
frontend and large-function stages. This is not a passing twenty-minute full
build or isolated verifier run.

After caching child results, native label-233 clash proposal generation
completed (1,515 nodes), while its previous repeated-subtree implementation
had timed out at 180 seconds. The closed allocation certificate is now under
a separate five-minute, sixteen-CPU check after the full backend timeout.

Label 233 closed allocation certificates passed in 1:53.36 wall,
398.86 user seconds, peak 4,836,680 KiB, standard axioms only.
The installed exact allocation bridge then passed the complete optimizer
in 14.97 seconds with its prerequisites cached (13.36 user seconds,
peak 3,168,488 KiB). This removes its previously monolithic allocation
check; it is not a cold full-project timing. Logs:
`allocation-clash233-complete-build.log`,
`optimizer233-allocation-integrated-build.log`.

Sparse label 713 now has 12,035 native-proposed clash checkpoints,
split into 126 conditional proof chunks. Its complete allocation
certificate is under a bounded four-CPU kernel check; no pass is claimed yet.

The generic CompilerArtifactComputation.artifact_of_stages certificate
passed in 839 ms (standard three axioms). It preserves the executable
compiler API behavior of passing the original configuration to fromStack.

A controlled sparse-713 literal-data comparison replaced only the broad
CompilerComputation import with RegAlloc.ClashTree and renamed its namespace.
The identical 8.2 MB values passed in 2:13.35 wall / 119.53 user / 13.70
system seconds, on one CPU; peak RSS 11,192,600 KiB. The original broader
import version had already used more than 4.5 minutes of CPU without finishing.
Log: clash713-minimal-data-build.log. This motivates reducing generated data
imports; it does not establish the final allocation certificate or full verifier.

Production sparse-713 Data with narrow imports passed in 112 seconds.
Its first conditional proof chunk then passed in 2.3 seconds (2.83 total
wall, peak 1,775,912 KiB). Precise TotalColour imports and removal of
optional linter settings were needed after removing the broad compiler
import. The repaired complete allocation batch is pending.

Static exploration of the lowered guest graph reports 826 function keys,
2,995 edges, all targets present, no SCC/self cycles, max rank 39 and
max frame 92. This is proposal evidence only. A generic ranked stack-bound
proof is being developed to avoid expanding 1,293,289 evaluator contexts;
the exact numeric 538 proof and the final bound are not certified yet.

Sparse-713 repaired closed allocation passed: 3:51.78 wall, 505.37
user seconds, four-CPU affinity, all 126 conditional/composition chunks
checked, standard axioms only. This timing uses the already certified
minimal-import Data module (112 seconds separately). The closed certificate
has been installed into Sparse713.Proof9; the complete optimizer check
is running. Log: allocation-clash713-minimal-import-repaired-build.log.

WordBackend.StackAgreement64 proved independent stack-analysis literal
agreement with the checked optimized function by rfl, without axioms,
in 1.2 seconds. This permits staged analysis before optimizer closure
finishes without trusting independently generated data.

StackAnalysis.Closed.depth_bounded PASSED (final module 8.2 seconds):
`∃ d, depthOfWordOutputs outputs = some d ∧ d ≤ 7480`. Axioms exactly
`propext`, `Quot.sound`. All 826 frame/slim/rank certificates were checked.
The rank theorem follows the original evaluator, including deletion,
tail recursion shortcuts, exceptions and Option failure cases. The closed
optimizer-output agreement and baseline compiler integration remain pending.

Function 713 integrated optimizer first reached a 180-second bound while
rebuilding earlier passes and unrelated scheduling-lane dependencies. The
large staged functions 240/713 now omit those artificial imports. Independent
713 recheck certified copy propagation (pass5) in 250 seconds, standard two
axioms; common-subexpression elimination (pass4) remains under a 300-second
probe and has a separate checkpoint optimization task.

An independent 713 optimizer check reached its 300-second bound while
common-subexpression elimination was still running. Copy propagation
passed in 250 seconds. The checkpoint bridge additionally hit an evicted
global Lake artifact path for Pass713_1, despite its local artifact being
present. With LAKE_ARTIFACT_CACHE=false it passed in 41.42 seconds,
standard two axioms. The outside build helper now uses stable local
artifact paths. Sparse713 literal agreement with independent stack
analysis passed by rfl in 1.3 seconds, without axioms. Logs:
`sparse713-from-checkpoints-local-cache-build.log`,
`stack-analysis713-agreement-build.log`.

The sparse-713 CSE and copy passes now use independent literal modules and
lazy kernel reduction. CSE passed in 126 seconds and copy propagation in
54 seconds, each with propext and Quot.sound. Their main optimizer bridges
passed; the cached full Optimize713 check took 4.58 seconds, standard three
axioms. These figures do not include rebuilding the already checked earlier
passes or allocation checkpoints.

The same isolated CSE method certified function 700 in 8.47 wall seconds,
11.22 user seconds, peak RSS 2.32 GB. Complete optimizers 700, 783 and 808
passed after checkpoint integration. The 300-second cohort reached its bound
while function 875 allocation remained unfinished; its pass8 passed in 185
seconds. Allocation875 is being split into independent checkpoints.

Compact small-function certificates were compared with the original
monolithic optimizer on function 163. Including generation, data parsing,
eight boundaries, composition and literal agreement, the compact version
used 56.41 CPU seconds and 28.60 wall seconds on four CPUs, with maximum
individual RSS 3.58 GB. The original used 58.28 CPU seconds, 55.63 wall
seconds and 10.35 GB peak RSS. Aggregate concurrent memory was not measured.
New missing-function tests 191, 207 and 214 also passed exact original
equality with standard axioms; broad integration is pending.

All 826 native function translations have been kernel checked.
BackendStages.Native.native_eq composes their exact Native.compileNative
result; its final aggregate module took 3.20 seconds. Native.bitmaps_eq
certifies agreement with the submitted 4,613-word bitmap list in 2.85 seconds
using only propext. Raw-call lowering and the subsequent assembler stages,
compiler integration, and the full outside/verifier builds remain pending.

The five compact optimizer bridges (191,207,214,223,230) passed their real
Lake build: 2:40.86 wall / 366.25 user / 31.11 system seconds on four CPUs,
maximum individual RSS 7.17 GB. This rebuilt compact modules previously
checked directly with Lean; their main wrappers each took 2.2–4.6 seconds.
All five depend only on the standard three axioms. Log:
`compact-five-integrated-build.log`.

SourceStackStages now links the ranked bound through an exact word stage
to compileProgMaxAsmExecutable, the compiler-correctness evaluator. Both
conditional composition theorems passed, standard three axioms; final
module 4.0 seconds, cached whole build 8.13 seconds. The exact stage
premise still awaits full optimizer closure and output-literal agreement.
The first group of 16 optimizer/stack literal agreements passed in 1.8
seconds; 52 small groups and their explicit list composition are prepared.
Logs: `source-stack-stages-final-build.log`,
`stack-agreement-chunk64-build.log`.

Allocation875 closed with all 27 conditional/composition chunks checked,
standard three axioms. Its integrated full optimizer then passed. The
allocation apply-color obligation took 245 seconds under four-CPU contention;
the endpoint took 1.2 seconds. CompilerOracles also passed its real Lake
build in 6.55 seconds, certifying use of checked allocation proposals through
the general correctness theorem.

All 397 remaining compact small-function proposals were prepared in 6:02.33
wall / 1419.66 CPU seconds with four generation workers; no failures,
maximum child RSS 2.19 GB. Their original main-module literals are retained,
and wrappers now refer to exact compact certificates. These bulk proofs
remain pending kernel checks. The bounded Lake wave driver checks at most
two candidate graphs at once, retaining normal build traces; a 16-logical-CPU,
20-minute outside cohort is running. This avoids starting thousands of
independent split-proof processes through an aggregate root import.

OracleBaselineCorrectness passed, final module 2.3 seconds, standard three
axioms. It specializes compiler correctness for the fixed source using an
exact oracle compilation result and any finite depth at most7480; concrete
installation and source nonfailure then imply machine/source behavior
agreement. The resource-limit relaxation is eliminated using the separately
checked7480-word fit, without computing exact538. AllocationFacts now
imports SourceCodeFacts directly so its proof avoids the old stack evaluator.

The project-local Lean admission launcher preserves the real compiler,
githash and module cache traces, and holds flock slots across exec before
loading proof environments. Twelve real Lean requests peaked at four active
processes with four slots; eight fake requests with two slots measured exact
peak two. Cache and nested-limit smoke checks passed. The focused remote
branch perf/lean-process-limit at3ff1141362d80ad32c5a1c701c40f9706b48ca37
contains only the launcher sources and usage documentation; the shared
checkout/index was not switched. Its scripts do not require RTK at runtime.

The verifier stages and hashes these trusted sources and invokes the limiter
inside isolation for both audit and comparator, with explicit .lake storage,
16 active compiler slots and16,384 waiting-process/thread capacity. Its
16-CPU/112GiB/eight-hour bounds remain. Log capture retains the final4MiB
with an explicit truncation marker, so a large build cannot silently drop
the final axiom manifest. Fifteen verifier Python tests passed, including
12MiB output draining/manifest retention and staged source/hash sensitivity.
Full PrivatePIDs proof verification remains pending.

The first bounded two-function wave cohort checked44 complete waves (88
compact optimizers) and stopped at its20-minute overall bound without proof
errors. It consumed3342.32 user and459.95 system seconds, only316% average
CPU use: the slowest leaf in each wave left other CPUs idle.

The tested admission launcher then completed the actual all-function
WordBackend.FunctionsFacts Lake build in19:18.57 wall /14676.09 user /2054.66
system seconds,16active compiler slots and16logical CPUs. The final
compileWith_eq depends on exactly the standard three axioms. This run reused
the already checked frontend, many previous optimizers and those88new compact
certificates; it is not a cold full challenge build. Maximum individual
worker RSS was21,945,644KiB; no aggregate memory peak was collected for this
run. Log: word-backend-limited-full-build.log.

The outside build helper now uses the admission launcher by default and has
--constrained mode for an enforced112GiB cgroup, zero swap,30logical CPUs,
30active compilers and an eight-hour timeout without private namespaces.
Its warm CompilerOracles smoke passed in1.432service seconds,2.350CPU seconds,
271.8MiB aggregate cgroup peak. Concrete source stack closure is now being
checked under those enforced caps. The user's final goal is completion under
these resource caps with measured timing and a generous timeout, rather than
a fixed20-minute cold-build deadline.

A small actual compiler proof also passed inside mandatory PrivatePIDs
isolation using the staged launcher. The explicit
INIT_E_LIMITED_SANDBOX_SMOKE marker was retained. This is an isolation/launcher
smoke, not a full verification pass. Log: limited-sandbox-smoke.log.

The concrete source-stack linkage passed under the enforced resource caps in
47.742 service seconds, 51.193 CPU seconds and 3 GiB aggregate peak memory.
Its 52 literal agreement chunks feed an axiom-free aggregate;
`sourceLogicalStackBound_bounded` depends on the three standard axioms. An
initial aggregate failed because `congrArg2` was unavailable; replacing it
with a small proved list-cons congruence lemma fixed the check. Log:
`source-stack-certificate-constrained-repaired-build.log`.

`BaselineCorrectness` and `CheckedCompilerConfig` then passed the same
constrained build in 27.742 service seconds, 31.797 CPU seconds and 2.8 GiB
aggregate peak memory. These runs reused the already checked optimizer and
frontend; they do not measure a cold full submission. Log:
`baseline-correctness-constrained-build.log`. Final artifact composition and
full isolated verification remain pending.

The standalone challenge definition also passed the enforced resource caps:
7.433 service seconds, 11.838 CPU seconds, 911.8 MiB aggregate memory peak,
zero swap. This incremental build covered `InitE.Challenge` and its changed
source semantics, observations, machine initialization, oracle replay and
submission model dependencies. It does not certify the baseline submission.
Log: `challenge-constrained-build.log`.

`InitE.baseline_artifact_of_backend` in `ArtifactComposition.lean`
now checks the composition of certified frontend, allocation tape, optimized
program agreement and native lowering. Its final backend equality is an
explicit premise that `BackendStages.Artifact` will discharge; no baseline
certificate assumes it. The composition theorem has exactly the standard
three axioms. Log: `artifact-composition-check.log`.

The complete raw-call stage is now certified: all 826 functions and 52
composition chunks feed `InitECandidate.Proofs.BackendStages.Raw.compile_eq`, whose axiom
closure is `propext` and `Quot.sound`. The final aggregate checked in 3.78
seconds. The resumed raw service completed successfully with 2,145,898,496
bytes aggregate peak memory and 573.514 CPU seconds; it reused 710 checked
functions, so these are not cold full-stage timings.

The remaining backend and target queues run as persistent user services with
file logging and retained exit/resource status. This avoids losing active
work when tool sessions end. The target queue covers all 832 sections, both
encoding phases and available origin bridges, using four workers on CPUs 0–3.
After the corrected suffix queue completed, the backend queues were expanded
to eight shared compiler slots on CPUs 4–11. Each group has a
32 GiB cap, zero swap and an eight-hour runtime limit. The final full build
and verifier still use the requested 112 GiB and 16-compiler caps.

Allocation lowering is also complete: all 826 per-function certificates,
chunk compositions and `InitECandidate.Proofs.BackendStages.Alloc.compile_eq` pass with the
three standard axioms. Later removal, naming, section and byte stages remain
in the persistent bounded queues.

The first target-phase aggregate exposed a proposal-generation error:
section-label scanning and re-encoding advance separate positions when a
branch encoding grows. Four phase-0 sections (595, 597, 692, 862) have different
next positions. Each original leaf equation is sound in isolation, but its
encoding position cannot be propagated through the full pass. Corrected
intermediate modules preserve the original live inputs and track both
positions explicitly; chunk generation now rejects discontinuities. A
corrected 594–598 example passed both phases, covering the first two changes.
Full corrected composition and origin agreement remain pending.

The corrected 594–598 example also passes exact append composition for both
encoding phases, and all five corrected phase-1 output literals are
kernel-equal to the existing final-phase proposals. Only sections 596–889
need corrected leaf proofs; earlier original contracts remain valid. The
full corrected proposal generation completed with 284.419 CPU seconds and
1,530,286,080 bytes aggregate peak memory. A separate four-worker queue checks
those 294 affected sections, leaving the original live queue untouched.

Bounded 32-section encoding, label-map and origin chunks pass using only
standard axioms. Their persistent aggregate and origin queues each use one
worker. Together with the two-worker metadata task and other queues, the
maximum active compiler count is 16. Whole phase/metadata/byte endpoints are
still pending; these intermediate successes are not full verification.

The focused target-stage snapshot is published on `perf/backend-target-checks`
at `c4e6c7843c7e7c1348fa92c18b0a67f5d750c1e4`, without changing the shared
checkout or index. Its leaf and composition proofs still require the final
combined source tree and complete verification. The upstream `riscv-im`
branch was rechecked and remains at the pinned
`7981f765cdadecf9b2857f326a65bae47371ab15` revision.

All 294 corrected suffix sections now pass. The whole phase-0 and phase-1
encoding equations checked in 3.63 and 4.32 seconds, with peak process RSS of
3.20 and 3.68 GiB. The phase-1 label equation checked in 30.89 seconds and
6.15 GiB RSS. These endpoints use only `propext` and `Quot.sound`.

An attempted agreement with every old phase-1 output exposed one stale
output alias in section 648. The earlier position error can change cached
branch bytes even when the final encoding length is unchanged. That false
shortcut is being removed: final assembly inputs use the corrected phase-1
outputs directly. This is a generated proof-input repair; the complete
artifact and verifier are still pending.

Parallel work is preserved in scoped remote branches without changing the
shared checkout or the draft PR head:

- `perf/backend-artifact-stages` at
  `2f29a8789b307129c2545b17ae95c06ea41b5021`: backend intermediate literals,
  equations, composition helpers and preparation scripts; excludes target
  checks and metadata. This checkpoint is not a completed artifact proof.
- `perf/backend-metadata` at
  `45b8daf3132cedf731cdd7fe8ac90dd89ac94ad2`: metadata literals, certificates,
  generator and its three preparation scripts. Checks continue against final
  backend inputs in the shared working tree.

These scoped branches depend on the combined standard-axiom source tree;
checking one branch alone is not equivalent to checking the final submission.
The final-stage pipeline measured approximately 9.5 seconds per section
serially (generation median 1.64 seconds; individual checks about 1.7–1.8
seconds). Independent final sections are being parallelized behind the
existing shared compiler admission limit, preserving exact section positions.

The original target queue ended at 828/832 checks. Its four failures are old
phase-1 cached-output aliases for sections 648, 671, 683 and 684; all four
corrected contracts are included in the successful 294-section suffix.
The full aggregate queue passed all 108 modules. Both encoding equations and
both label maps are certified; the phase-0 label map checked in 28.67 seconds
(30.96 CPU seconds, 6.07 GiB process RSS), using `propext` and `Quot.sound`.
The label endpoint wrapper also passed. Initial-origin agreement still waits
for the remaining encoded-section certificates.

The corrected target snapshot is now published on `perf/backend-target-checks`
at `fde986f5a0c00556c9b40f217afa51042872aaf1`. It removes the unsafe output
alias optimization and the rejected agreement bridge while retaining the
kernel-checked corrected equations. Diagnostic logs preserve the failed
shortcuts. No additional axioms or omitted required premises resolve these
failures.

The four obsolete phase-1 output aliases were repaired after their original
readers stopped. Their eight old encoding/phase endpoints now pass through
the existing shared admission lock, with only `propext` and `Quot.sound`.
Original failure logs remain separate from repair results. Canonical full
composition continues to use the corrected intermediate modules. The updated
target branch is `ba72d737fea985d064a32563a12a041a42b5e84a`.

Root-owned frontend, optimizer, stack, challenge and verifier integration work
is preserved on `perf/standard-axiom-integration` at
`c1684cc7144c03457ed9ac6198f5757f132e48a2`. It excludes all backend-owned stages,
metadata and target generation. The shared index and checkout were unchanged;
the draft PR still separates its old published certificate from current WIP.

After the original target queue ended, backend admission expanded to twelve
compiler slots on CPUs 0–11. Two aggregate/origin slots and two metadata slots
keep the total ceiling at sixteen. Final-section, byte, zero-label and
byte-fragment checks use independent workers behind that shared admission.
Measured catch-up throughput was approximately 0.94 seconds per final-label
section and 1.49 seconds per byte-agreement section (previously 3.84 seconds
serial); final padding progressed at about 2.66 seconds per section.

All 832 final alignment/re-encoding/padding, byte, zero-label and final-label
leaf checks pass. Whole final composition checked in 3.50 seconds. Two small
terminal glue failures were repaired using explicit reduction of the empty
tail and the existing zero-validity theorem. Successful `Bytes.compile_eq`
and `ZeroLabels.valid` checks took 3.45 and 19.49 seconds and report exactly
`propext` and `Quot.sound`; failed recovery logs are not certification evidence.
`BytePieces.nativeCode_eq` checked in 2.90 seconds using `propext` alone,
certifying the full submitted 904,056-byte native literal. The complete
source-to-artifact composition and full verification are still pending.

The complete parametric `Artifact.fromStack_eq` now passes in 10.15 seconds
with exactly the three standard axioms. The source-to-artifact integration
`baseline_compiler_artifact_eq` also passes in 32.99 seconds (33.081 CPU
seconds): cgroup peak 4,769,820,672 bytes, individual process maximum RSS
37,685,644 KiB, including shared mapped imports. All generators are terminal
and proof sources frozen. These are direct kernel checks with cached imports;
backend direct checks did not produce Lake traces.

The actual full outside build is running as the persistent
`init-e-outside-full-standard3.service`, invocation
`83e73ad32c9b471280eed47d041ccd1f`, targeting `InitE`, `Submission` and
`InitECandidate.Proofs.Audit`. It enforces 112 GiB, zero swap, CPUs 0–15, sixteen compiler
slots and an eight-hour runtime. Logs are
`work/lean-perf/outside-full-standard3-build.log`; final wall/CPU measurements
will be in the matching `.time` file and retained service resource status.
It reuses existing frontend/optimizer caches; a complete pass remains pending.

Final backend and metadata snapshots are pushed at
`643559785120fd67fc604b912fc21c14c5e6f4fe` and
`35eeaafcd2066c55a56aaddf378e6decbd6bf55a`, respectively. Their completed
proof interfaces now support the prepared root artifact composition.

Verifier cache staging now excludes the eight namespaces already discarded by
`clear_artifacts`, only at the workspace Lean/IR artifact roots. Upstream
packages, Tools, configuration and other artifacts remain independent copies.
The measured live cache contains approximately 131 GiB of discarded artifacts;
selective staging avoids that temporary copy, but the ensuing cold workspace
rebuild will still require substantial disk space. A regression test checks
namespace boundaries, dependency preservation and independent copied files.
All 16 verifier tests passed in 13.038 seconds. The full isolated run remains
pending; these tests establish staging behavior, not proof acceptance.

A follow-up symlink audit found two generated limiter launcher links into the
mutable host cache. Staging now omits `.lake/lean-limit` and
`.lake/metadata-limit`; the project-local limiter recreates its binary,
virtual toolchain and locks before use. The remaining retained links resolve
within copied dependencies or to the pinned, read-only elan toolchain. The
regression test covers omission of both host-linked launcher trees. All 16
verifier tests passed again after this fix in 12.044 seconds.

Before the fresh isolated run, three inactive generated `.lake` trees from
`host-upgrade-baseline-5`, `riscv-im-16cpu-1hour` and
`ast-16cpu-8hour-112gib` were removed after checking process references. Their
combined measured allocation was 49.71 GiB. Run sources, logs, configurations
and result records remain; this cleanup does not constitute a new verification
result. The active outside build and its cache were left running.

The first actual full outside build stopped after 1:03:56 (43,357.45 user and
12,693.55 system CPU seconds), cgroup peak 70,017,769,472 bytes, no swap.
Every compiler/artifact stage passed; `BaselineInstallationFacts` then failed
after 165 seconds because `baseline_literal_layout` recomputed the full image
length with `decide_cbv` and hit maximum recursion depth. This is a failed
build, not certification evidence. The fix reuses the already checked
`LiteralFacts` chunk-length theorems; compiler installation metadata also
rewrites the native length before computation.

The incremental full continuation is live as
`init-e-outside-full-standard3-retry1.service`, invocation
`6953d6ccd9bf491a90cc1c4c2af52a72`, with the same targets and caps. Its logs
and measurements are `work/lean-perf/outside-full-standard3-retry1-build.log`
and `.time`. Both the first attempt and this continuation must be accounted
for when reporting the full build cost; the retry alone is not a cold build.

GitHub's `lake-build` workflow now runs only through `workflow_dispatch`.
Automatic PR and main-push triggers were removed in commit `535d76f`, since
the hosted runner budget does not accommodate this proof build.

The continuation passes `BaselineInstallationFacts`, compiler installation
metadata, `FullBaseline` and the actual `InitECandidate.Proofs.Audit` Lake target. Every root
printed by the audit has exactly the three standard axioms, including full
correctness, termination, final output, bootstrap evaluation and zero memory
after headers. The submission admission facts remain active; the full target
build and isolated verification are still pending.

The remaining admission proof continued running for more than twenty CPU
minutes. A scratch prototype keeps its public statement unchanged, extracts
the 13 MMIO records and 33 entry PCs into small literals once, derives the
length equation from existing facts, and splits the other conditions. Direct
`rw` of indexed goals initially failed because their bound proofs depended on
the rewritten list; the simplifier variant reached its 300-second timeout.
Explicit predicates over the lists make the dependent motives well typed.
`decide_cbv` on those small indexed predicates still hit recursion depth;
ordinary kernel `decide` passes.

The successful prototype checked in 31.07 seconds (24.89 user, 6.51 system),
cgroup peak 4,786,425,856 bytes, exactly the standard three axioms. This uses
cached imports and is a scratch check, not a full build. Source and logs are
`work/lean-perf/admission-facts-fallback-helpers.lean` and
`admission-facts-fallback-helpers3.{log,time}`; the source SHA256 is recorded
in BASELINE. Earlier failed experiments are not certification evidence. The
active full build and its original source are unchanged pending its terminal
result.

At the user's request, the obsolete admission run was superseded and the
verified small-list replacement installed in `submission/InitECandidate/Proofs/BaselineSubmissionFacts`.
Its public theorem statement is unchanged. The prior service's final live
resource snapshot is preserved in
`work/lean-perf/outside-full-standard3-retry1-superseded.json`; it is not a
completed build. The scoped replacement is published on `perf/admission-facts`
at `5a274ad3e38e4aabd0b94ebf8aace0064826cb64`.

The actual full-target continuation is now
`init-e-outside-full-standard3-retry2.service`, invocation
`b519198a606e42f49e5580f24adfd17f`, with unchanged 112 GiB, zero swap,
sixteen compiler slots, sixteen CPUs and eight-hour caps. Measurements and
logs use `work/lean-perf/outside-full-standard3-retry2-build.{time,log}`.

The complete actual outside continuation succeeds: all 53,272 Lake jobs,
including `Solution` and `InitECandidate.Proofs.Audit`, pass. The certificate and infinity
termination equivalence report exactly the three standard axioms. Continuation
wall time is 1:33.65, user/system CPU 87.37/13.72 seconds, cgroup peak
5,704,183,808 bytes, no swap. This incremental measurement includes the newly
installed admission proof and downstream targets; it does not describe a cold
build. The earlier 1:03:56 rebuild and superseded-run resource snapshot remain
part of the development cost.

Full isolated verification is now live in
`init-e-full-verifier-standard3.service`, invocation
`e971a80e80ed4dd68dee057b90644b50`, work directory
`verifier/runs/full-standard3-20261006`. Isolation preflight passed, and the
trusted audit is rebuilding workspace proofs inside PrivatePIDs. Upstream
package caches are copied independently; workspace proof artifacts are
omitted. Each inner build/comparison retains the eight-hour/112-GiB/16-slot
limits. The persistent outer unit permits eighteen hours for both steps plus
staging. Its log/time files are `work/lean-perf/full-verifier-standard3.*`;
outer CPU/RSS measurements do not include sibling sandbox-unit processes.
Only the verifier's final `verified` status will establish isolated acceptance.

The cold workspace trusted audit passed all 53,263 jobs with exactly
`propext`, `Classical.choice`, and `Quot.sound`. Wall time was
9,802.874 seconds (2h 43m 23s), CPU time 147,050.743 seconds,
and cgroup memory peak 117,086,064,640 bytes (109.0 GiB), with zero swap.
The memory peak includes charged file cache, not just compiler heaps.
Upstream dependencies and trusted tool caches were reused. The final comparator
is running separately inside PrivatePIDs with the same limits; trusted audit
success alone is not submission acceptance. Exact service accounting is retained
in `work/lean-perf/full-verifier-standard3-trusted-audit-result.json`.

### Comparator text-buffer experiment and transport adoption

The live full comparator reached its 112-GiB cap while exporting Solution.
The pinned comparator captures all stdout with `IO.Process.output`; Lean
reads it into one byte array before UTF-8 conversion and export parsing.
A separate prototype copies stdout to private temporary handles in 64-KiB
chunks and parses those handles after both exporters finish. The original run
was left unchanged until its actual OOM failure. The measured prototype used
`/tmp`, now confirmed to be tmpfs; the installed verifier instead requires a
private disk-backed directory outside the candidate’s writable Lake cache.

Synthetic ASCII producers were measured sequentially with one CPU, 2 GiB,
zero swap and a 600-second limit. Sampled anonymous memory includes the Lean
harness. Sampled file memory includes tmpfs/shmem and shared tool mappings;
the tmpfs portion is not reclaimable disk cache with zero swap. These tests
measure buffer elimination, not disk-spool I/O performance. RSS is not the
anonymous-memory measurement below.

| Output | Buffered wall / sampled anon | Spool wall / sampled anon |
| --- | --- | --- |
| 64 MiB | 1.68 s / 347.7 MiB | 1.10 s / 118.8 MiB |
| 256 MiB | 2.62 s / 1117.5 MiB | 1.31 s / 121.0 MiB |
| 512 MiB | OOM at 2 GiB (3.35 s) | 1.11 s / 121.2 MiB |

All 14 pinned comparator fixtures matched their expected results, including
full kernel acceptance of valid proofs and rejection of illegal theorem or
submission axioms, altered primitives, type mismatches and invalid kernel
terms. String/file parser agreement, malformed and truncated exports, UTF-8
chunk boundaries, exporter exit 7, write failure and large stderr were checked.
The prototype retains the original nanoda-enabled path unchanged; its
execution and full-size parser/kernel memory remain untested. The 512-MiB
buffered OOM is a measured transport failure, not proof acceptance.

Exact measurements, commands, source hashes and initial setup failures are
in `work/lean-perf/comparator-spool/experiment-results.json`; the proposed
patch is `spool.patch` in that directory (SHA256
`de157a76ea8749d19456b32b48fab4ba60cf2ac1615d907a0e395b75ac7d2d4a`). These are exploratory checks,
not the initial submission verification result.

The uninterrupted original comparator failed with an OOM kill after
9,594.844 seconds (2h 39m 55s), with 7,252.767 CPU seconds,
120,259,084,288 bytes peak (112 GiB), and zero swap. Its solution build passed
all 53,268 jobs before the buffered exporter failed; this is not acceptance.
The full outer attempt took 5h 24m 13s including the successful cold trusted
audit. Exact comparator accounting and journal are retained in
`work/lean-perf/full-verifier-standard3-comparator-result.{json,journal.json}`.

After that terminal failure, the reviewed transport patch was installed at
`verifier/patches/comparator-file-spool.patch`, hash-checked by setup. The
installed native comparator passes all 14 upstream fixtures. The verifier
creates a unique mode-0700 spool directory on disk outside the staged project,
passes it only to the comparator, and grants systemd write access only to that
directory in addition to the Lake cache. Candidate Landrun write permissions
remain restricted to the Lake cache. Tmpfs and ramfs are rejected. Final
full-size parsing and kernel replay still require the next isolated run.

The disk-spooling full retry is now live in
`init-e-full-verifier-spool-standard3.service`, invocation
`95281914a9f845369accdafc9ea6424b`, with frozen source snapshot `e6bb936d`.
It repeats the cold workspace trusted audit and full comparator under the same
112-GiB, zero-swap, 16-CPU/16-compiler-slot and eight-hour inner limits. The
outer allowance remains eighteen hours. All 21 verifier regression tests pass
in 7.733 seconds, and the real sandbox temporary-file probe confirms that Lean
uses the supplied private disk directory. Full acceptance remains pending.

### PR #14 ready for review; full comparator still running

At the user's request, PR #14 is ready for review while isolated comparator
acceptance remains pending. This readiness status does not certify completion
of the verifier. The current retry's cold trusted audit passed all 53,263 jobs
with exactly `propext`, `Classical.choice`, and `Quot.sound`: wall time
9,502.804642 seconds (2h 38m 23s), CPU time 143,573.824268 seconds,
peak memory 118,107,770,880 bytes (110.0 GiB), zero swap. Upstream dependencies
and trusted tool caches were reused. Exact terminal accounting is retained in
`work/lean-perf/full-verifier-spool-standard3-trusted-audit-result.json`.

The comparator is running in `init-e-verify-bed444a03767.service`, invocation
`bbefec5ce3e64843a60cd3c3f193354b`. At 2026-10-06T08:56:01.153250+00:00, the larger
private export file contained 49,470,701,568 bytes and comparator peak memory was
111,525,384,192 bytes (103.9 GiB), below the 112-GiB cap.
These are interim measurements; export, parsing, comparison and full kernel
replay must all finish before acceptance can be claimed. The exact snapshot is
`work/lean-perf/full-verifier-spool-standard3-pr14-status.json`.

A one-shot completion watcher,
`init-e-full-verifier-spool-standard3-waker.service`, checks the exact outer
verifier invocation and this session's herdr thread identity before prompting
it after success or failure. It does not interrupt or restart the verifier.
The Flapjack dependency remains pinned to `riscv-im` revision
`7981f765cdadecf9b2857f326a65bae47371ab15`; the user plans a separate repin PR
after merging PR #14.

### Old-pin retry superseded for the ISA-alignment repin

After PR #14 was merged, the user requested repinning Flapjack and stopping
the old full verifier. The outer run and comparator were stopped explicitly,
and the completion waker was disarmed first. This is a superseded run, not
full acceptance or an OOM failure. The comparator used 6,555.527439 CPU seconds
over 6,612.445188 wall seconds, with 111,525,384,192 bytes (103.9 GiB) peak
and zero swap. The passed trusted audit remains valid evidence for the old pin.
Terminal journal accounting is retained in
`work/lean-perf/full-verifier-spool-standard3-superseded.json`.

The stopped run's generated Lake cache and private spool files were reclaimed
after a process-reference audit found no users. Frozen sources and logs remain.
The new pin is `034bb5a1ed0b757082768d5406206bd2f8e31b7c`; its semantics
change requires a fresh isolated build and comparison. All 21 verifier
regression tests passed in 8.463 seconds.
The bounded compatibility build also passed all 3,616 jobs, including
`InitE.Challenge`, `InitECandidate.Proofs.MachineWordMemory`, and
`Flapjack.RiscV.L3.Step.NoCompressed`. Its log is
`work/lean-perf/flapjack-repin-034bb5a1-smoke.log`; it is not a full
initial-submission or isolated comparator check.

The fresh full verifier was started in
`init-e-full-verifier-riscv-im-034bb5a1.service`, invocation
`92688cf3b01a454d82aadb8e857bdeb4`, with source snapshot
`be28eb472322c3e0af7c420e6ffc4d5abb505293`. Its work directory is
`verifier/runs/full-riscv-im-034bb5a1-20261006`, with outer log/time files
`work/lean-perf/full-verifier-riscv-im-034bb5a1.{log,time}`. The same
112-GiB, zero-swap, 16-CPU/16-compiler-slot and eight-hour inner limits apply;
the outer allowance was eighteen hours. The session-specific herdr completion
waker was armed for this exact invocation. This run was subsequently stopped
at the user’s request, as recorded below; it did not establish full acceptance.


### Compact computation certificates (2026-10-06)

After PR #15 was merged, work moved to `perf/compact-computation-proofs`.
At the user's request, the current repin verifier and its exact completion
watcher were stopped before replacing the computation certificates. The stopped
run is not an acceptance result. Sources, journals and its pre-stop resource
snapshot are retained under `work/lean-perf/full-verifier-riscv-im-034bb5a1-*`.

`InitECandidate.Proofs.CompactComputation.kernel_rfl` submits an `Eq.refl` term without first
repeating the conversion check in the elaborator. Lean's kernel still checks
that the proposed result is definitionally equal to the computation. This
changes the certificate representation, not the trust level. The regression
module `Tools/KernelComputationCheck.lean` checks a real copy propagation and
requires the kernel to reject the false proposed equality `1 = 2`.

A 256-group changing-program copy-propagation fixture produced 892,468 distinct
proof-expression nodes with `cbv`, versus 16 using full-transparency reflexivity.
The complete dependency exports were 47,736,547 and 6,000,582 bytes respectively;
fresh kernel replay took 38.542 and 2.728 seconds. This fixture includes moves
between distinct allocator variables and returns rewritten to their copy
representatives. The short term alone does not remove the definitions and
input/output literals from the export. Exploratory wall measurements also
include shared compiler-slot waits and concurrent work.

Full guest-stage checks use the same 16-slot compiler admission and a 112-GiB,
zero-swap memory cap. Reference sizes below are cached old artifacts, not fresh
reruns of the old proof scripts. Each listed compact artifact passed a direct
Lean kernel check; this is not full isolated comparator acceptance.

| Full guest certificate | CPU seconds | Old `.olean` bytes | Compact `.olean` bytes |
| --- | ---: | ---: | ---: |
| Copy propagation `Pass875_5` | 67.31 | 810,526,280 | 28,441,056 |
| Common subexpression elimination `Pass875_4` | 35.25 | 702,656,080 | 29,044,720 |
| Complete optimizer `Optimize694` | 49.46 | 324,016,720 | 3,885,216 |
| Dead-code removal `Pass875_8` | 49.65 | 321,780,152 | 25,028,168 |
| SSA conversion `Pass713_2` | 113.58 | 197,057,048 | 49,146,064 |

All listed equations retain only a subset of `propext`, `Classical.choice` and
`Quot.sound`. The exact logs and resource measurements are recorded in
`work/lean-perf/compact-guest/root-full-stage-results.json`.

Closed definitional computations use compact reflexivity. For symbolic contexts
and computations that need equation lemmas, the proof first applies a shared
checked bridge. The Loop shrink pass now has a structurally recursive evaluator
and a live-set-size-bounded fixed-point evaluator, proved equal to the original
mutually well-founded definitions. Dead-code checkpoints retain cached child
and skip equations; clash checkpoints retain the original structural validator
and named child equations. A sorted-validator rewrite was tested but dropped:
its well-founded merge sort did not reduce definitionally in larger cases.
These shared equations keep each local computation small. The largest checked
Loop translation, `Translate649`, took 17.53 wall seconds and reduced its artifact
from 66,931,720 to 12,576 bytes; its shared evaluator helper is about 1.99 MB.
The largest frontend conditional checkpoint,
`Checkpoints811/Conditional/Chunk008`, also passed, reducing its artifact from
3,379,712 to 988,776 bytes.

The shared production-to-HOL codecs now have universally quantified equality
proofs for shapes, expressions, programs and declarations. These permit compact
frontend checks without reducing the original size-based recursion over string
payloads. The codec module itself checked in 4.13 CPU seconds with only the three
standard axioms. Full frontend leaf and aggregate checks remain separate work.

The broad build exposed SSA-stage reflexivity failures that were absent from
initial representative checks. Its expression traversal was inferred as
well-founded recursion and could remain stuck even on a variable expression.
`SmallSsaKernelComputation` proves the structural expression and program
traversals equal to the original SSA compiler, without additional premises.
The repaired `Pass875_2` checked in 65.80 wall seconds; the tiny failing
`Compact885/Pass2` artifact shrank from 11,155,720 to 12,576 bytes. Fused
optimizer proofs expose the pipeline before applying this bridge; proofs that
already compose checked stages only need the final tuple conversion.

The original bulk Word/Small and frontend discovery builds found these cases
and exited with errors; they are not acceptance results. The first full outside
integration pass also found staged optimizer tails that needed correction, plus
a brief disk-space failure. Two later import crashes came from truncated cached
artifacts (`Pass184_7.olean` and `Optimize189.olean`), rather than proof failures.
Regenerating those artifacts from unchanged source and refreshing their Lake
traces repaired both crashes.

The final full-target continuation, `lake build InitE Submission InitECandidate.Proofs.Audit`,
passed all **53,282 jobs**, including the full bootstrap/guest composition and
submission certificate. It took 814.024 wall seconds and 1,702.500 CPU seconds,
with a 32,581,480,448-byte (30.34-GiB) memory peak and zero swap. Earlier successful
stages were cached; this is the completed incremental outside build, not a cold
build timing. The audit and both submission theorems report exactly `propext`,
`Classical.choice` and `Quot.sound`. No additional outside rebuild is required.
Unit `init-e-compact-full-outside-retry2-20261006.service`, invocation
`a1c28505d6574a75bec188ea4ddeb8bf`, and its terminal journal are recorded in
`work/lean-perf/compact-guest/full-outside-retry2-build-result.json`.
Fresh isolated comparator acceptance remains pending.


The fresh isolated run started from commit
`1f8d0751a704daacaeeb7e39d1524469536275fb` in
`init-e-full-verifier-compact-5e0e78c2.service`, invocation
`c4626cb5d8ae43c6b326a84e09cfd02c`. Mandatory Linux isolation passed before
project staging. The run rebuilds the trusted challenge namespaces cold and
then exports/replays the candidate with the comparator. Its work directory is
`verifier/runs/full-compact-5e0e78c2-20261006`; outer log/time and exact launch
metadata are under `work/lean-perf/full-verifier-compact-5e0e78c2*`.
The limits remain 16 CPUs/compiler slots, 112 GiB, zero swap and eight hours
per phase, with eighteen hours for the outer runner. The herdr completion
watcher is armed for this exact invocation and session. Full isolated
acceptance remains pending.


### Remaining image computations: bounded comparator improvement (2026-10-06)

Two image certificates had retained large `decide_cbv` proof terms after the
compiler-stage compacting work: `InitE.bitmap_image_bytes` and
`InitECandidate.Proofs.BootstrapCopy.final_bitmap_word_image`. Their production
modules were approximately 80.4 and 108.6 MiB respectively.

The retained change uses the existing proved region/bitmap rewrites followed by
`kernel_rfl`. The final-word proof also uses a new `ImageComputation.suffix_getElem?_eq`:
it proves the length of the first ten suffix chunks once and then selects the
last chunk before indexing. This avoids eight traversals of the same 40 KiB
prefix. Its split and length equations are ordinary kernel-checked theorems.
The final two production modules are approximately 56 and 66 KiB.

The challenge, source program, ROM/bitmap literals, and all seven existing theorem
statements in the two edited certificate files are unchanged. The new certificates
have axiom closure exactly `propext, Quot.sound`.

The combined fragment benchmark checks both equations together, so shared
prerequisites are counted once. It reconstructs the original proof bodies even
after rollout and exports every used dependency. `CompareReplay.lean` calls the
pinned comparator's actual statement/definition comparison and axiom checker,
including its primitive targets, followed by ordinary `Environment.replay`.
Each command is capped at 180 seconds; the complete submission is never exported
or replayed by this harness.

Two alternating-order trials of each variant passed the actual comparator checks.
Medians (decimal MB for exports):

| Combined image fragment | Original | Compact |
| --- | ---: | ---: |
| Comparator process wall time | 107.03 s | 38.09 s |
| Parse both exports | 34.864 s | 5.776 s |
| Statement/axiom checks | 10.443 s | 0.210 s |
| Kernel replay | 60.660 s | 31.217 s |
| Proof build (one run) | 114.26 s | 5.65 s |
| Export generation (one run) | 15.29 s | 3.09 s |
| Solution export | 279.75 MB | 29.55 MB |

Comparator wall time improves **2.81×** on this fragment. Both
exports include the same two claims and all used data/helper dependencies.


The proof-build measurements use existing common imports. The updated shared
`ImageComputation` module separately built in 4.8 seconds; its entire used proof
closure is included in comparison. These are not cold whole-project timings.
The affected-module build passed 4,115 jobs and the bootstrap/bitmap-installation
consumer build passed 4,108 jobs, mostly cached. No full comparator was run, so
this establishes a local improvement, not an hours-to-minutes whole-solution
result.

Reproduce after building the affected modules and existing verifier tools:

```sh
python3 tools/certificate-bench/image.py \
  --work work/lean-perf/image-comparator-reproduction --trials 2 --timeout 180
```

Use `--family word` or `--family bitmap` for smaller individual fragments.
Portable measurements and source hashes are in
[image-results.json](../tools/certificate-bench/image-results.json); raw generated
fixtures, exports, timing files and logs are in
`work/lean-perf/image-comparator-final/`.

Other bounded experiments were not rolled out. Shared sequence/leaf proof
combinators on 256 real dead-code checkpoints changed median kernel replay from
842 to 813 ms, only a small gain. A proof-carrying instruction-encoding table on
3,277 ordinary assembly lines from seven real functions made replay worse,
1,462 to 2,147 ms, despite 1,100 distinct pairs. A shared compiler-pipeline
composition theorem on function 79 left complete-closure replay essentially
unchanged, 28.491 versus 28.521 seconds. Each used three replay trials. These
results favour measured computational shortcuts and compact checking over
unselective proof factoring or caching.

### Parallel kernel replay in pinned comparator (2026-11-01)

`verifier/patches/comparator-file-spool.patch` (SHA256
`880369b34e19efbc9dc2f35409dbde82cfdade00a3b3a70edc7ea9e9ab39f715`) replaces
single-threaded `Environment.replay'` in the pinned `comparator`
(`c0c5a52d2aff92b457c3e5ed4a68c1ebc5795809`, compiled with Lean `v4.33.1`) with
`Comparator.ParallelReplay.checkParallel` (default `6` threads; direct
`comparator` invocations also support `COMPARATOR_KERNEL_THREADS` or optional
`kernel_threads` in comparator JSON, whereas `verify.py` runs under `env -i`
with a fixed environment allowlist and an unmodified `verifier/comparator.json`
so official verifier runs always use the default `6` threads).
`compareAt`, `checkAxioms` (theorem and definition closures), `primitiveTargets`,
permitted axioms (`propext`, `Quot.sound`, `Classical.choice`), and disk-backed
export spooling remain unchanged.

In `checkParallel`, a single-threaded topological pass (`prepareAll`) rejects
unsafe/partial declarations, checks axioms and inductive/quotient declarations
sequentially through the stock kernel, inserts safe definitions, theorems, and
opaques via `addDeclWithoutChecking` while snapshotting each item's exact
pre-insertion `Kernel.Environment`, and compares postponed inductive,
constructor, recursor, and quotient constants with `==`. Dedicated worker tasks
then independently check every deferred declaration via stock
`Kernel.Environment.addDeclCore 0 0` against its pre-insertion environment
snapshot, require `actual == expected` on the added constant, and share an
`IO.CancelToken` for early cancellation on error.

Measured on a 32-vCPU, 128-GiB host (`CPUAffinity=0-29`, `MemoryMax=112 GiB`,
`MemorySwapMax=0`, `TasksMax=16384`) against prebuilt real exports so timings
isolate export spooling, stream parsing, declaration/primitive/axiom checks,
and full Lean kernel replay:

1. **`K=2` submission export** (`29 MiB` challenge export, `210 MiB` solution
   export):

   | Variant | Comparator wall | Peak cgroup memory | Outcome |
   | --- | ---: | ---: | --- |
   | Stock sequential | 194.825 s | — | Accepted |
   | Parallel `N=1` | 193.572 s | — | Accepted |
   | Parallel `N=4` | 76.059 s | — | Accepted |
   | Parallel `N=6` (default) | 59.833 s | — | Accepted |
   | Parallel `N=8` | 58.944 s | — | Accepted |
   | Parallel `N=12` | 60.306 s (268.194 CPU s) | 33.366 GiB | Accepted |

2. **Initial `K=infinity` submission export** (`29 MiB` challenge export,
   `6,104,551,435`-byte / `5.69 GiB` solution export). Because spooling and
   parsing the `5.69 GiB` export populates reclaimable page cache up to the
   `112 GiB` cgroup limit (`memory.peak = 112.0 GiB` with `oom_kill = 0`),
   1 Hz cgroup `memory.stat` sampling also records peak `anon` and
   `anon + kernel` memory:

   | Variant | Comparator wall | CPU seconds | Peak `anon + kernel` | Outcome |
   | --- | ---: | ---: | ---: | --- |
   | Stock sequential (2026-10-30 pilot on identical `015dc95d…` export) | ~17,242 s (4h 47m 22s) | — | — | Accepted |
   | Parallel `N=4` | 3,086.666 s (51m 27s) | 11,373.047 | 103.793 GiB | Accepted |
   | Parallel `N=6` (default) | 2,299.706 s (38m 20s) | 12,088.991 | 96.308 GiB | Accepted |
   | Parallel `N=8` | 1,921.128 s (32m 01s) | 12,888.340 | 107.337 GiB | Accepted |
   | Parallel `N=12` | 769.088 s (killed) | 6,347.323 | 111.438 GiB | SIGKILL (112 GiB cgroup OOM) |

`N=6` is selected as the default: it cuts `K=2` comparator wall time by **3.26×**
(`194.8 s` → `59.8 s`) and initial `K=infinity` comparator wall time by **~7.5×**
(`~17,242 s` → `2,299.7 s`, saving ~4h 09m), while retaining ~15.7 GiB of
anonymous+kernel headroom under the `112 GiB` zero-swap cap where `N=12` OOMs
and `N=8` leaves ~4.7 GiB. All 14 upstream comparator fixtures, 9 adversarial
integration fixtures (`adv_*`), and the direct `ConstantInfo` soundness suite
(`tests/soundness_replay.lean`) pass.
