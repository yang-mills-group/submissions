# Full finite ghost-loop comparison

The independent finite ghost-loop target passed in Lean and Comparator on November 13, 2026. This checks the actual submitted graph, including its finite subtraction constants. It is one gauge-dependent contribution to the two-point amplitude, with the overall coupling factor omitted as in the submitted coefficient. It is not the sum of all one-loop diagrams or a full independent validation of perturbative matching.

## Exact statement

The proof is [`GhostSolution.acceptance`](../../checks/matching/GhostLoopSolution.lean), in namespace `YMReview.NovemberMatching`:

```lean
theorem acceptance (G : YM.Gauge) :
    GhostLoop.SubmittedFinitePartTest G
```

The predicate is defined in [`GhostLoopBenchmark.lean`](../../checks/matching/GhostLoopBenchmark.lean). For every gauge object satisfying `G.Simple`, every positive MS-bar scale, every nonzero physical momentum and all color/tensor components, it requires

\[
\lim_{s\to\infty} B^{ab}_{ij,s}(\bar\mu;p)
=\frac{C_A\delta^{ab}}{16\pi^2}
\left[
\frac{\delta_{ij}p^2}{12}
 \left(\log\frac{\bar\mu^2}{p^2}+\frac83\right)
+\frac{p_i p_j}{6}
 \left(\log\frac{\bar\mu^2}{p^2}+\frac53\right)
\right].
\]

Here `B` is the **actual** `Outlook.four` reading of `(TwoPoint.bubble G true true).instructions.renorm`, with `s` the logarithm of the retained infrared length. The scale coordinate supplied to the reader is `log mu_bar + (γ − log (4π))/2`. `C_A` is `G.casimir`, with the submission's color metric; no change to a textbook generator normalization is implicit. The graph sign and conventions are explained in Section 3.5 and Appendix C of the [matching notes](november-perturbative-matching.pdf).

The target assumes neither the finite answer nor a proposition saying it agrees with the reference. The independently entered right-hand side was already present in the benchmark before the new source-level proof. Its Gamma-function Laurent expansion and the pole comparison were established earlier. The reduction of the conventional dimensionally regulated Feynman integral to that Gamma expression remains a human calculation; the final Lean theorem proves that the submitted graph equals the displayed finite formula.

## How the proof reaches the submitted graph

| Files under `checks/matching/` | What is proved |
| --- | --- |
| [GhostLoopTrace](../../checks/matching/GhostLoopTrace.lean) | Contracts the submitted ghost vertices and selected lines in the auxiliary sectors; tracks the sign, color factors and lifted momenta. |
| [GhostLoopRadial](../../checks/matching/GhostLoopRadial.lean), [GhostLoopContinuation](../../checks/matching/GhostLoopContinuation.lean) | Evaluates the actual radial Gaussian integrals and continued source force, with integrability and integral-exchange justifications. |
| [GhostLoopJet](../../checks/matching/GhostLoopJet.lean) | Differentiates the actual local term in the regulator, proving `SubmittedRegulatorJetTest`. This retains the finite contribution that would be lost by dropping regulator-dependent numerator terms before pole subtraction. |
| [GhostLoopInfrared](../../checks/matching/GhostLoopInfrared.lean), [GhostLoopMellin](../../checks/matching/GhostLoopMellin.lean), [GhostLoopPrimitive](../../checks/matching/GhostLoopPrimitive.lean) | Evaluates the physical source force and proves the derivative and both endpoint limits of an explicit primitive. The small-argument constant retains the Euler constant and logarithms. |
| [GhostLoopFlow](../../checks/matching/GhostLoopFlow.lean), [GhostLoopUnit](../../checks/matching/GhostLoopUnit.lean) | Matches the actual amplitude's scale derivative and ultraviolet boundary to the explicit expression. Equality at every cutoff is proved before the infrared limit is taken. |
| [GhostLoopTensor](../../checks/matching/GhostLoopTensor.lean), [GhostLoopSolution](../../checks/matching/GhostLoopSolution.lean) | Extends the diagonal unit-momentum calculation to every tensor component and nonzero momentum, then applies the actual finite-reader bridge and the prescribed scale conversion. |

The proof uses established submitted lemmas for the reader, flow, covariance and color contraction. It does not replace the graph with a new definition that has the desired value. The frozen challenge imports the benchmark but does not import these proof modules. There are no permitted definition holes.

The prior [convention](../../checks/matching/GhostConventionCheck.lean), [benchmark](../../checks/matching/GhostLoopBenchmark.lean) and [elementary evaluation](../../checks/matching/GhostLoopFiniteEvaluation.lean) files remain unchanged. Some of their comments describe the incomplete stage at which they were written; the complete result is in `GhostLoopSolution.lean`.

## Verification and its scope

A [fresh 15-module review build](../../evidence/matching/ghost-finite-build.json) passed using the pinned, previously built November libraries. [`GhostFiniteAudit.lean`](../../checks/matching/GhostFiniteAudit.lean) prints seven principal axiom reports, including the final acceptance theorem; all contain only `propext`, `Classical.choice` and `Quot.sound`. One review-code warning recommends simpler tactic syntax. There are no build errors.

The [Comparator receipt](../../evidence/matching/ghost-finite-comparator/ghost-finite-comparator.json) and [full log](../../evidence/matching/ghost-finite-comparator/ghost-finite-comparator.log) record a pass in 146.94 seconds. Both `Lean default kernel accepts the solution` and `Your solution is okay!` appear. The [frozen inputs](../../evidence/matching/ghost-finite-comparator/prepared-inputs.json) and [stability record](../../evidence/matching/ghost-finite-comparator/input-stability.json) bind this pass to the target, proof sources and received submission. All 37,673 submission-file hashes were checked before and after.

Comparator was `d03acab154d269c06e60e4de7e4cc85deebff94b`, using the Lean 4.34.0 checking kernel. The export tool was `4e7915201d3f9f04470d9eae002fa695f7cdc589`, using Lean 4.32.0. The macOS run used upstream `fake-landrun.sh`; it did not provide Linux process isolation, the optional second kernel or Palomar. The intentional reference-theorem placeholder causes a challenge-build warning, but the solution does not depend on `sorryAx`. Replayed submission warnings and informational tactic suggestions are retained in the full log.

This is a completed test of the full finite graph value. It is not a new clean rebuild of the entire submission. Complete physical coefficient tests, renormalized composite-source conventions, and the general identification of conventional perturbation theory remain separate review items.

## Reproduce

Use the pinned submission checkout described in the [repository README](../../README.md#getting-the-source-and-checking-this-snapshot), and first build that submission according to its `NOTES.md`. Both commands below create a new overlay and leave the original source unchanged. Choose a fresh work directory for each run.

```sh
python3 scripts/check_snapshot.py --source vendor/OpenAI-Nov4/submission
python3 scripts/build_ghost_finite.py \
  --source vendor/OpenAI-Nov4/submission/lean \
  --work work-cache/ghost-finite-local-build
```

The build writes its receipt and module logs to the new work directory's `evidence/`. It does not overwrite the committed records. For Comparator, prepare and build `comparator/` and `lean4export/` at the revisions in the [port report](../november-port.md#reproducing-the-checks), under a common `tools/` directory, then run:

```sh
python3 scripts/run_ghost_finite_comparator.py \
  --source vendor/OpenAI-Nov4/submission/lean \
  --tools /path/to/tools \
  --work work-cache/ghost-finite-local-comparator
```

This runner requires the review source hashes to match the committed successful build receipt. It freezes the [challenge](../../comparator/GhostFiniteChallenge.lean), [configuration](../../comparator/ghost-finite.json) and proof modules, checks the tool revisions and submission manifest, runs Comparator, and checks input stability again. It saves the result under the new work directory's `evidence/`. Its launcher configuration reproduces the recorded macOS development run.
