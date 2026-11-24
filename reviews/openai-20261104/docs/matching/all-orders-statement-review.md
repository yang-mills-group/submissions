# Reviewing the all-orders matching statement

The finite ghost-loop calculation is one diagnostic of the conventions. The main review must also decide whether the **all-orders theorem states the intended comparison with Yang–Mills perturbation theory**. We do not need to calculate infinitely many diagrams individually. We do need to validate the definitions that generate every coefficient, the renormalization prescription, and the quantifiers connecting those coefficients to the constructed theory.

The source inspection below finds the required all-orders quantifier structure in the public target. The graph/flow uniqueness bridges provide an all-orders route to validating the reference. Endorsing their input operations and boundary conditions as the intended Yang–Mills prescription remains a mathematical review task. Passing a single graph benchmark does not settle that task.

## The intended mathematical statement

Fix the gauge group. There is one Wilson construction and one perturbative reference, chosen before the requested volume sequence. For each selected infinite-volume refinement, there is one calibrated field frame `J_r` and one measured coupling `g_X(r)`, shared by every perturbative order, arity, field tuple and phase of that hierarchy.

For every finite order `N`, derivative order `j`, collection of field degree cutoffs, and compact set `K` of separated shapes, the actual correlations satisfy

\[
\left\|D_x^\ell\left[
S_\sigma(J_r v_1,\ldots,J_r v_n;o+rx_1,\ldots,o+rx_n)
-\sum_{k=0}^{N} g_X(r)^k C^X_{n,k}(v;x)
\right]\right\|
\le A\prod_i\|v_i\|_{\rm coeff}\,|g_X(r)|^{N+1},
\qquad 0\le\ell\le j.
\]

The constant and small-radius threshold are chosen before the phase, center, field tuple and point in `K`. They may depend on `N`, `j`, the cutoffs and `K`. The reference coefficients are the graph coefficients after the fixed scheme conversion; they are not read off from the physical correlations being tested.

For each finite output cutoff `h`, the analogous OPE bound controls the **entire output field**, through order `N` in the same coupling and frame. The output cutoff and perturbative order are separate quantifiers. In particular, this is not merely a test of the identity coefficient or the vacuum expectation of the OPE.

This is an asymptotic statement at every fixed finite order. It does not require convergence of the infinite perturbative series, uniform bounds as `N` grows, Borel summability, contact-term matching, or uniqueness of the nonperturbative large-volume limit. The radius tends to zero in a fixed continuum hierarchy, after its construction limits have been taken.

## Informal–formal alignment

Source paths in this table are relative to the pinned November `submission/lean/` tree. Unprefixed filenames other than `MSConversion.lean` and `MSOrdinaryOPE.lean` are in `YangMills/PerturbativeMatching/`. The [source pin](../../provenance/submission.json) and [source map](source-map.json) identify that tree. “Statement checked” means that the declarations have the stated content and quantifier order; it does not certify the physical interpretation of all definitions they use.

| Requirement | Formal location | Review finding |
| --- | --- | --- |
| One construction, one lattice family, one reference before all requested volumes | `YangMills/PerturbativeMatching.lean`: `MatchedRun` | **Statement checked.** `reference`, `lattice` and `kernels` are fields outside `refinement`. Each refinement's `continuum` uses those same data and the run's chosen subsequence. |
| One coupling and field frame before every perturbative order | Same file: `MatchedRefinement`; `Measurement.lean`: `Measurement`, `FrameCalibration` | **Statement checked.** Both expansion propositions use the same measurement. Its frame is an isomorphism at each radius and degree, and calibration ties it to the physical position-normalized frame. |
| Every finite order, every arity and heterogeneous field degree | `Correlations.lean`: `CorrelationExpansion.shapeDerivatives` | **Statement checked.** `order : ℕ`, `n : ℕ` and `d : Fin n → ℕ` are unrestricted. There is no fixed maximum loop or field degree in this clause. |
| A genuine remainder estimate, not equality of formal symbols | Same clause; `Asymptotics.lean`: `ShapeDerivativeBound` | **Statement checked.** The norm is of derivatives of the actual correlation minus a finite sum, bounded by `A * product(coefficientNorm v_i) * abs(coupling r)^(order+1)`. Smoothness of both functions is required. |
| Uniformity over the mixed hierarchy and all its character phases | Same clause, with `phase : Option T.Character` | **Statement checked.** The eventual radius is before phase, fields, center and point. `none` is the mixed hierarchy. This is not a claim about every conceivable hierarchy unrelated to the run's chosen refinements. |
| A genuine small expansion parameter | `Measurement.lean`: `coupling_pos`, `oneLoop`; our `AllOrders.coupling_zero` | **Statement checked.** The positive measured coupling and its normalized logarithmic running law imply `g_X(r) → 0`. The new Lean check derives this consequence explicitly; the remainder cannot pass merely because the proposed expansion parameter stays large. |
| Nonarbitrary coupling and scheme conversion | `Measurement.lean`: `FrameCalibration`; `Calibration.lean`; `MSConversion.lean`: `ConversionValid` | **Statement checked.** A signed physical triangle measurement fixes the coupling. The free normalization menu and reference coefficients determine the formal coupling, field and inverse-field series. The smooth numerical adjustment is also specified. A human review must validate this prescription and its interpretation as the stated scheme. |
| Coefficients fixed independently of the interacting construction | `GraphCoefficients.lean`: `graphCorrelation`; `Reference.lean`: `msbarCoefficients`, `Reference` | **Statement checked.** The graph array takes the gauge group, labels, positions and order, with no physical hierarchy argument. The reference is a subsingleton once the stated calibration requirements hold. Independence does not by itself establish that the graph rules are correct. |
| Full OPE output through every finite dimension | `OperatorProducts.lean`: `measuredOPE`, `HasChannelBasis`, `OPEExpansion` | **Statement checked.** All channels through `h` are summed, form a basis of the output space, and are pulled back by the same frame. The coefficient norm separates output fields. Derivative tests range over the dual unit ball. |
| Reference OPE determined by arbitrary exterior fields | `Reference.lean`: `OPEIsDetermined`; `MSOrdinaryOPE.lean`: `Valid`, `Determined` | **Statement checked; proof connection traced.** Existence and uniqueness are required for the whole exterior-tested array. The interpretation and strength of the exterior tests need review; agreement of vacuum moments alone would not suffice. |
| Stress tensor matched in the same scheme | `Correlations.lean`: `stressExpansion`; `WardIdentities.lean`: `WardStress.Determined` | **Statement checked.** Every finite order is tested against the uniquely normalized Ward stress series. The stated remainder is little-o of `g_X^N`; it should not be advertised as the stronger derivative estimate used for general correlations. |
| Regulated graph limits actually exist | `YM/MS/Graphical/PricePin.lean`, `Panels.lean`; the named graph-forest limit theorems in the source map | **Source connection traced.** Some definitions use totalized limits. The accompanying all-order convergence theorems are essential; the definition `limUnder` alone would not establish the intended coefficient. Regulator removal is sequential. |
| Coefficients describe the actual lattice-derived continuum theory | `YangMills/WilsonProof/Construction.lean`; `MeasuredExpansions.lean`; calibrated common-gate and named correlation estimates | **Source connection traced.** `graphEstimates` and the OPE bridge are used in the same refinement that carries the continuum-limit witness. The published target has passed Comparator. The analytic estimates remain available for proof review. |

The field and coupling choices can depend on the selected continuum hierarchy. They cannot depend on the order currently being tested, and the reference is shared across the refinements. Matching to all orders permits effects smaller than every power of the coupling; this is consistent with different nonperturbative phases.

## The all-orders definition review that remains central

The submission already supplies a useful characterization: its graph sums solve a uniquely specified renormalization-flow problem with specified classical input and pole-subtraction boundary data. Thus the most efficient review is to validate that characterization, rather than enumerate each graph separately.

1. **Classical theory and fields.** Check that `Motif.ploy`, its gauge and BRST/source terms, and the insertion polynomials represent the intended gauge-fixed Yang–Mills theory and gauge-invariant local operators. `Motif.Class_at` identifies the bulk seeds with the interaction part of this expression. The free lines and cubic ghost vertex are already checked in explicit conventions. The renormalized composite-source dictionary remains a broader issue.
2. **Contractions and combinatorics.** Check the linear closure and bilinear joining operations, their graded signs, loop counting, and multiplicities. `bridgeForce_eq`, `closeForce_eq`, `ambient_bob` and `mark_bob` identify the enumerated graph sums with the coefficient flow equations. `Diagram.income_bulk` and `income_mark` then use uniqueness for all orders. That is useful structural evidence, provided the flow equation itself has the intended normalization and field content.
3. **Renormalization conditions.** Check that the permitted local counterterms, dimensional continuation, pure-pole condition, and ultraviolet boundary data implement the claimed scheme. `integrateRen` subtracts the principal part of a summed scale sector with child counterterms already present. The finite ghost-loop result checks a nontrivial consequence, but does not independently establish equivalence to every conventional forest subtraction.
4. **Composite insertions and operator mixing.** Check that the specified insertion system covers the claimed local fields, including derivative and equation-of-motion conventions, and that field and coupling redefinitions are common and sufficiently constrained. For OPEs, the inverse transformation on the output must be retained.
5. **Bridge to physical asymptotics.** Check that the all-order coefficient identities feed into remainder estimates for the same continuum hierarchy, with no new theory or order-dependent choice introduced during assembly. Verify the separate roles of ultraviolet construction, selected large-volume limit, short-distance expansion, dimensional regulator, and graph infrared cutoff.

These are finitely described definitions and general theorems that govern every order. Their review is the essential complement to low-order calculations. The existing source investigation has located the relevant declarations and bridges; it has not yet established an independent all-order identification with a separately formalized conventional perturbative theory.

## A readable Lean check of the quantifiers

[`AllOrdersStatement.lean`](../../checks/matching/AllOrdersStatement.lean) writes out `CorrelationRemainders` and `OPERemainders`, then combines them in `SharedStatement`. Its existential witnesses are placed before the relevant universal quantifiers. It retains the same Wilson lattice data, kernels and continuum-limit witness, and requires the same calibrated measurement for both expansions. It also makes `g_X(r) → 0` explicit. The `coupling_zero` proof follows the submitted `Matching.CorrelationOnly.clockAtZero` argument at the public interface, deriving positivity of the logarithmic coefficient from the running law rather than adding a new assumption.

The theorem `YMReview.NovemberMatching.AllOrders.submitted` derives that statement from the actual `WilsonProof.matchedRun`, assuming only the public gauge-group simplicity hypothesis. Its core projections are deliberately short: they make the target's meaning reviewable and check that the source statement really supplies it. They reuse the public `Reference`, its graph array and conversion; **this is statement alignment, not an independent proof that those graph definitions are standard Yang–Mills perturbation theory**. The condensed statement also leaves the source's additional smeared, phase-agreement and stress clauses in the full target.

The fresh local build passed without warnings on November 13. The final statement and the small-coupling lemma report only `propext`, `Classical.choice` and `Quot.sound`. All 37,673 submission files were checked against the pinned manifest before the build. The local build and axiom record are [all-orders-statement.json](../../evidence/matching/all-orders-statement.json) and [its log](../../evidence/matching/all-orders-statement.log). Reproduce it against the already-built pinned submission with:

```sh
python3 scripts/build_all_orders_statement.py \
  --source vendor/OpenAI-Nov4/submission/lean \
  --work work-cache/all-orders-statement-local
```

The original all-orders Matching target already has successful Comparator receipts under [`evidence/supplied-targets/`](../../evidence/supplied-targets/). This readable consequence is a separate local build and axiom audit, not a new Comparator run. The finite ghost-loop Comparator has its own [records](../../evidence/matching/ghost-finite-comparator/) and a narrower role.
