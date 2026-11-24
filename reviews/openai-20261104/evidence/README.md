# November verification records

The records are separated by what was checked. `supplied-targets/` contains an unchanged copy of the earlier submission build and checks of OpenAI's own targets. `independent-checks/` contains the new compilation and axiom audit of the group's November adapters. The independent combined-target Comparator run has its own record, distinct from both.

## Group's independent checks

[`independent-checks/AxiomAudit.json`](independent-checks/AxiomAudit.json) records the successful compilation of 49 review modules against the November source build. It identifies the compiler, search path, source hashes, direct external import hashes, commands and individual logs. Its 95 axiom reports include both combined acceptance theorems, the public OS bridge and the projection to November's public existence conditions. All report only `propext`, `Classical.choice` and `Quot.sound`. The review modules produced no warnings.

The build driver reused already compiled review modules only when their recorded source and dependency fingerprints matched. The separate Comparator overlay starts without review build products, while reusing the already built submission and dependency libraries. Neither procedure is a new clean build of the whole submission.

[`independent-checks/port-audit.json`](independent-checks/port-audit.json) compares the 43 copied October files with the pinned baseline: 23 are byte-identical, nine differ only in the OS module import prefix, and 11 contain the recorded adapters or replacement endpoints. It checks that the seven central acceptance predicates are unchanged and that the OPE specification changes only its import and channel-field name. It also reports no admission, fresh axiom or `unsafe` tokens in the review code after removing comments and strings. This textual check complements the theorem-specific axiom audit; it does not replace kernel checking.

The import inventory does not reach `Comparators.Matching.Solution`. Shared construction libraries are still used where needed; the result is not a review of positive-order perturbative matching.

The new Comparator run freezes the two statements in [`comparator/NovemberChallenge.lean`](../comparator/NovemberChallenge.lean) and uses [`comparator/combined.json`](../comparator/combined.json), with no definition holes. The `sorry` placeholders occur only in the reference challenge, as intended by Comparator; the solution proofs are complete.

Both targets **passed on November 11, 2026**, in 1,020 seconds. [`combined-targets/combined-comparator.json`](combined-targets/combined-comparator.json) records the command, times, exit code and log hash. The [log](combined-targets/combined-comparator.log) ends with the Lean kernel accepting the solution and Comparator accepting it. [Prepared inputs](combined-targets/prepared-inputs.json) identify the tool revisions, binary hashes and every frozen review source. [Input stability](combined-targets/input-stability.json) confirms that the overlay inputs were unchanged and that all 37,673 original submission files still match the pinned manifest. Both tool binaries also match those used in the earlier successful November 10 supplied-target recheck.

This run used the upstream macOS development launcher and the Comparator built with Lean 4.34.0. It did not use Linux/Landrun isolation, an optional second kernel or Palomar.

## Earlier submission and supplied-target checks

The source repository's pinned review notes predate completion; the receipts copied into `supplied-targets/` record the later results.

The clean source build reported success in `supplied-targets/release-build.log`. Its outer macOS `/usr/bin/time -l` wrapper then failed while reading resource information, so the original `release-build.json` truthfully retains exit code 1. The direct `lake --no-cache --no-build build` follow-up returned zero; its log and receipt are included. This follow-up checks the completed build and is not a second clean compilation.

`patched-comparator-recheck.json` records successful replays of both supplied targets, ending on 10 November 2026. It identifies the source manifests before and after, tool revisions and binary hashes, exact commands, configuration hashes, log hashes and exit codes. The accompanying Existence and Matching logs and individual receipts are included unchanged.

The replays used Comparator `d03acab154d269c06e60e4de7e4cc85deebff94b` built with Lean 4.34.0, together with the Lean 4.32.0 exporter. The submission continued to use its own Lean 4.32.0 build toolchain. The label “patched” is inherited from the local records: it refers to the checker recheck, not edits to submitted Lean files.

Both separate axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`. The two supplied Comparator configurations are copied here as `Existence.json` and `Matching.json`.

These are macOS development-mode runs using the upstream `fake-landrun.sh` launcher. They do not provide Linux/Landrun isolation, an optional independent second-kernel check or a Palomar check. Matching's mechanical pass does not establish completion of our scientific matching review.

Recorded absolute paths identify the machine and workspace where the commands ran. To find a recorded log here, use its basename within `supplied-targets/`. The initial snapshot does not contain every intermediate log or the historical control experiments. It contains the final recheck, build evidence and theorem-specific axiom audits.

Run `python3 scripts/check_snapshot.py` from the repository root to verify the recorded artifact hashes and included receipt log hashes. Add `--source /path/to/submission` to check all 37,673 files listed in the received source manifest. This integrity check is not a proof replay. Commands for compiling the independent checks and rerunning their Comparator target are in [the port report](../docs/november-port.md#reproducing-the-checks).

## Perturbative reference investigation

[`matching/diagram-reference-audit.json`](matching/diagram-reference-audit.json) records two additional free-gauge-line theorems and inspection of twelve existing submitted bridge theorems. The run compiled with Lean 4.32.0, no warnings and fourteen axiom reports containing only the standard axioms. The accompanying log preserves the printed types and dependencies. This uses the previously built source library and is not another whole-submission build or Comparator run.

[`matching/independent-tests-build.json`](matching/independent-tests-build.json) and its log are unchanged copies of the earlier compilation of `IndependentMatchingTests.lean`. The successful finite algebra lemmas and adapter do not establish the proposed interacting-coefficient tests. Its recorded absolute paths point to the original local output directory; the copied source is now under `checks/matching/`.

[`matching/ghost-convention-check.json`](matching/ghost-convention-check.json) records five new proofs comparing the ghost lines and classical ghost–gluon vertex with explicit scalar-antighost formulas. [`matching/counterterm-audit.json`](matching/counterterm-audit.json) records type and axiom inspection of eight submitted theorems about an actual ghost-loop pole and its regulated complement. Both runs passed without warnings and with only standard axioms. The counterterm audit is not an independent loop calculation; neither run is a new Comparator run.

[`matching/ghost-loop-benchmark.json`](matching/ghost-loop-benchmark.json) records eighteen proved statements: the independent Gamma-function reference and its Laurent coefficients, the parameter weight, comparison of the actual submitted pole tensor, a negative control for a finite regulator term, the actual finite-reading bridge, scale dependence and reduction to one reference scale, and heat-dressing bounds and pointwise removal of the actual line cutoff. The build passed without warnings and reported only standard axioms. Its receipt explicitly separates these proofs from the then-unproved `SubmittedFinitePartTest` and from the unformalized dimensional integral reduction. It uses the existing submission libraries and is not a Comparator run.

[`matching/ghost-loop-finite-evaluation.json`](matching/ghost-loop-finite-evaluation.json) records 23 standard-axiom reports for the explicit finite calculation: the ordinary source force, source ghost-trace and radial-continuation reductions, scalar radial Gaussian integrals, the continued polynomial and local jet parameter, and exact finite parameter integrals. The run passed with no warnings. These results support the analytic calculation in Appendix C of the notes; the full submitted finite-value test was not yet proved at that stage. This is a local Lean check against the already built submission, not a Comparator run.

The [matching notes](../docs/matching/november-perturbative-matching.pdf) describe the source audit, its definition glossary and the supplied and independent test inventories. The source map pins each cited Lean source by hash. The review still requires validation of the ghost/source dictionary for renormalized insertions, the finite subtraction prescription and complete physical coefficients beyond calibration.

## Completed finite ghost-loop comparison (November 13)

[`matching/ghost-finite-build.json`](matching/ghost-finite-build.json) records a fresh build of all 15 review modules against the pinned, previously built November library. The final theorem is `YMReview.NovemberMatching.GhostSolution.acceptance : ∀ G, GhostLoop.SubmittedFinitePartTest G`. It has no extra finite-part assumption. The seven principal axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. One review-code warning suggests a simpler tactic sequence in `GhostLoopFlow.lean`; there are no errors. The earlier helper receipts above are preserved as records of their original scope, and this new receipt establishes the completed result.

[`matching/ghost-finite-comparator/`](matching/ghost-finite-comparator/) contains the successful frozen-target run. It finished in 146.94 seconds with both `Lean default kernel accepts the solution` and `Your solution is okay!`. The reference imports only the benchmark, not its proof; the configuration has no definition holes. `prepared-inputs.json` records review sources, generated project files, the build receipt hash, and tool revisions/binary hashes. `input-stability.json` records unchanged frozen inputs and the successful after-run check of all 37,673 submission files. Those files also passed the before-run check.

The run uses Comparator `d03acab154d269c06e60e4de7e4cc85deebff94b` (Lean 4.34.0) and lean4export `4e7915201d3f9f04470d9eae002fa695f7cdc589` (Lean 4.32.0). It is a macOS development-mode run with the upstream `fake-landrun.sh`, without Linux isolation, the optional second kernel, or Palomar. The log includes replayed submitted-module lint/deprecation warnings, the challenge's intentional theorem-placeholder warning, and the review-code style warning. The solution's proof does not depend on `sorryAx`.

The [finite-check guide](../docs/matching/ghost-finite-check.md) gives the formula, proof map and rerun commands. This pass concerns the full finite value of one gauge-dependent graph contribution, not independent validation of every perturbative matching coefficient.

## All-orders statement alignment (November 13)

[`matching/all-orders-statement.json`](matching/all-orders-statement.json) and [its log](matching/all-orders-statement.log) record the successful compilation of `YMReview.NovemberMatching.AllOrders.submitted` and the small-coupling lemma `coupling_zero`. Both axiom reports contain only `propext`, `Classical.choice` and `Quot.sound`; there were no warnings. The script checked all 37,673 submission files before compiling in a fresh overlay against the previously built source.

This theorem restates the core arbitrary-order correlation and whole-output OPE bounds with one shared construction, reference and calibrated measurement. It reuses the submitted graph reference and conversion. It is a check of statement alignment, not an independent validation of every graph rule. The [all-orders review](../docs/matching/all-orders-statement-review.md) identifies the remaining definition-level questions. This local audit is separate from the already completed Comparator runs for the supplied all-orders Matching target and the independent finite ghost-loop target.
