# Independent checks on the November construction

The October review checks now compile against the November submission. The port proves a combined theorem containing November's complete public existence requirements together with our independent OS, Wilson-measure, Ward-identity, operator-content and leading-trace checks. It also retains the additional contact and calibration conclusions that were bundled into the October acceptance statement.

The [acceptance specification](../checks/NovemberAcceptanceSpec.lean) and [proof](../checks/NovemberCombined.lean) are the main entry points. The [checklist](checklist.md) distinguishes the compiled mathematical results from Comparator and human review. This is a verification report for the port, not a final assessment of the November submission or of perturbative matching.

## What the combined theorem says

The main theorem is:

```lean
YMReview.November.combined_acceptance
  (g : YangMills.GaugeGroup) (hg : g.IsSimple)
  (b : ℝ) (hb : 0 < b) :
  Nonempty (YMReview.November.ReviewedConstruction g hg b)
```

`ReviewedConstruction` retains the native Wilson family and fixes its construction penalty to the requested positive number `b`. It then fixes a Maxwell reference, the lattice data, the fixed-volume continuum correlation table and the cutoff trajectory. These choices precede the requested sequence of volumes. For every strictly increasing requested volume-index sequence, it supplies a refinement, a continuum table `S`, the native construction object `F : Final ... S`, and its OPE reader `Q`.

The continuum hierarchy is specifically `YangMills.hierarchy F Q`. The corresponding `CheckedRefinement` requires four things about these data:

1. November's full `Wilson.ContinuumLimit`, including lattice convergence, reconstruction, field and phase identifications, Ward and trace results, OPE conditions, and the all-radius, all-phase Maxwell ultraviolet limit.
2. Our `Acceptance.Accepted hg F`, whose independently stated requirements apply to that same `F` and its lattice family and table.
3. The independent OS axioms and growth condition for the selected centered stress-trace correlations of `hierarchy F Q` itself.
4. Our explicit-radius `OPE.CommonOPE` predicate for that hierarchy and its coefficients.

The theorem `YMReview.November.public_realizes` projects these data to a `Wilson.Construction` satisfying November's public `Realizes` predicate. Thus the new target contains the public existence conditions; it does not ask for a second, separately chosen theory to satisfy them.

We also prove `YMReview.Acceptance.combined_acceptance`, with the October-shaped `CombinedAcceptance g hg b` target. This retains its quantification over arbitrary input extraction orders, rather than replacing it with only the volume-sequence interface used by November's short public theorem.

## How the connection to the submitted construction is established

The short theorem `YangMills.jointExistence` returns an existentially quantified public construction. It does not expose all the native data needed by our checks. We therefore extend its proof assembly, using the same November results: `Independent.fundedRun`, `R2IGoals.fromFunded`, `LeanPointReturns.nativeReturns` and the refinement theorem. Instead of discarding the native `Final` and reader after building the public hierarchy, we retain them in `CheckedRefinement` and establish our additional clauses there.

This is a proof that the November construction method supplies a witness satisfying all the stated conditions. It is not a theorem that an arbitrary witness chosen from the short existential theorem has those extra properties. Nor does it identify November's chosen infinite-volume hierarchy with October's chosen hierarchy. Neither comparison requires, or establishes, uniqueness of the infinite-volume limit.

Within the independent acceptance record, the Wilson measure, UV convergence, extracted IR limit, phase-average identity, selected scalar family, stress tensor and local field spaces are all indexed by the same `F` and `S`. The public OPE check uses the stored reader `Q`. The retained legacy source bundle also quantifies auxiliary reconstruction, contact and scaling data over that same `F`; these auxiliary existential choices do not introduce another lattice family or continuum table.

## The OS comparison

The bridge uses the OSreconstruction axioms and arity-linear E0′ growth condition already used in the October review. The relevant declarations are `OsterwalderSchraderAxioms 3` and `OSArityLinearGrowthCondition 3`. Here `3` is the number of spatial dimensions; the test functions have four-dimensional Euclidean arguments.

For each arity, `publicSchwinger` integrates the public hierarchy's selected centered stress-trace kernel against a joint Schwartz test that is flat on every coincidence diagonal. The coordinate equivalence is explicit. [NovemberOS.lean](../checks/NovemberOS.lean) proves successively that the public centered trace is the native trace field, that its public correlation kernel is the kernel used by our OS bridge, and that the resulting Schwinger functions agree. `public_os` then supplies E0–E4 and E0′ for these exact functions.

The mathematical OS predicates and the growth predicate have not been weakened for November. The vendored modules have moved from `YangMills.OSRecon` to `NovemberOSRecon` to avoid a Lean module-search collision with the submission's own `YangMills` directory. This is an import-path change, not a change to the declarations.

This remains a comparison for the selected scalar stress-trace hierarchy. It does not independently establish OS positivity for every field in the full operator collection on unrestricted Euclidean contact extensions. The diagonal-flat tests cannot detect terms supported on coincidence diagonals. The separately retained contact-distribution existence result does not supply uniqueness or unrestricted contact-term positivity.

## What changed in the port

| October component | November treatment |
| --- | --- |
| `LatticeAndScale`, `PhaseAndOS`, `TranslationWard`, `OperatorContent`, `LeadingTrace` | Same predicate bodies; their generic proofs compile against November. |
| `Accepted` and `CombinedAcceptance` | Same record and quantifier structure. The imported source-conclusion wrapper is adapted explicitly below. |
| Standalone endpoints calling October's `Nonperturbative.continuum` | Removed from the adapters. Their generic proofs are retained and assembled on November's witness in `NovemberCombined`. |
| Public OPE channel field `actor` | Renamed to November's `channelField`. The explicit radius and state quantifiers in `CommonOPE` are unchanged. |
| October's four-field `Properties` wrapper | Reintroduced as `RetainedSource.Properties`, with Wilson convergence, reconstruction, OPE and trace fields using November's public definitions. November's trace predicate includes its additional trace requirements. |
| Contact-extension predicate and proof | Retained in `RetainedSourceSpec` and `RetainedContactProof`; the latter adapts October's `ContactBridge` argument using November lemmas. |
| Additional source conclusions | `RetainedSourceProof` assembles the contact, reconstruction, nested OPE and calibration results on the given November `F`. It also recovers the small `four_on` assembly lemma omitted from November. |

The old `SourceConclusions` was a bundle of submitted results, not an independent semantic validation of every source definition. Retaining it preserves those conclusions but does not change that status. In particular, the horizon-four calibration result retained here is not the new positive-order perturbative-matching claim.

[The baseline manifest](../provenance/october-checks.json) records the October check files and their hashes. The [port audit](../evidence/independent-checks/port-audit.json) records which files changed and checks the unchanged independent predicate bodies. Original source notices are retained; our small adaptations of October source proofs are identified in their comments.

## Verification and its limits

The compiler uses the November submission's Lean 4.32.0 toolchain and already built source/dependency libraries. Our modules are compiled separately. The successful audit covers 49 review modules and 95 axiom reports, including both combined theorems and the public OS and existence projections. Every reported dependency is among `propext`, `Classical.choice` and `Quot.sound`.

Both combined targets passed Comparator on November 11, 2026. The configuration freezes the statements and permits no definition holes. The run used Comparator `d03acab` with its Lean 4.34.0 checking kernel and the Lean 4.32.0 exporter. Its new overlay built the review modules from source while reusing the existing November and Mathlib builds. The original submission and frozen review inputs were checked before and after the run. See the [verification records](../evidence/README.md) for the receipts. Earlier passes of OpenAI's supplied targets are recorded separately.

These checks establish the formal implications stated in the targets. Human review must still decide whether the definitions express the intended physics. This port adds no claim of a mass gap, unique IR limit, intrinsic nonzero mass scale, unique Euclidean contact extension, or equivalence to a separately specified canonical Hilbert space. Positive-order perturbative matching and a new November-specific adversarial exercise remain separate review tasks.

## Reproducing the checks

Start with the pinned submission and its build instructions, as described in the [repository README](../README.md). Then run:

```sh
python3 scripts/build_checks.py --source /path/to/submission/lean --target AxiomAudit
```

This compiles the review modules and records source hashes, imported library hashes, commands, compiler output and axiom reports under `evidence/independent-checks/`. Add `--fresh` to recompile every review module. It does not rebuild the whole submission.

For the independent-target Comparator run, provide built checkouts of the pinned Comparator and exporter as sibling directories:

| Directory | Upstream repository | Revision | Toolchain |
| --- | --- | --- | --- |
| `tools/comparator` | [leanprover/comparator](https://github.com/leanprover/comparator) | `d03acab154d269c06e60e4de7e4cc85deebff94b` | Lean 4.34.0 |
| `tools/lean4export` | [leanprover/lean4export](https://github.com/leanprover/lean4export) | `4e7915201d3f9f04470d9eae002fa695f7cdc589` | Lean 4.32.0 |

Check out these revisions and run `lake build` in each tool directory. Then run the following from this verification repository:

```sh
python3 scripts/run_comparator.py \
  --source /path/to/submission/lean \
  --tools /path/to/tools \
  --work work-cache/my-combined-run
```

The script requires a successful current axiom audit. It checks the full received-file manifest, copies the audited review sources into a new overlay, runs Comparator, and checks the frozen inputs and submission again afterward. Each invocation requires a new work directory. On macOS this uses the upstream development launcher; it does not provide Linux/Landrun isolation, the optional second kernel or a Palomar run.
