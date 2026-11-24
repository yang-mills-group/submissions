# Independent checks on the November construction

The November construction has been proved to satisfy the mathematical requirements used in the October assessment, and both group targets passed Comparator. The [two-page summary](existence/november-existence-summary.pdf) describes the result. The [October acceptance specification](https://github.com/yang-mills-group/YM/blob/55ba9fc36293b3f4d52c6b1f813169a0be76ee98/submissions/openai-20261028/checks/AcceptanceSpec.lean) and [combined proof](https://github.com/yang-mills-group/YM/blob/55ba9fc36293b3f4d52c6b1f813169a0be76ee98/submissions/openai-20261028/checks/CombinedAcceptance.lean) supplied the starting points. The separate OPE check was also transferred.

All claims must refer to the same November lattice family, its continuum hierarchy, its phases and its reconstructed fields. Proving existence of another object satisfying the October requirements alongside November's existence theorem would not establish this connection.

| Check | Result needed | Current status |
| --- | --- | --- |
| Construction connection | Expose the native `Final` witness used by the November existence assembly and identify its lattice family, limit hierarchy, phases and reconstructed fields. | Compiled in `NovemberCombined`; `public_realizes` recovers the public existence conditions. |
| Independent OS axioms | Prove the OSreconstruction axioms E0–E4 and E0′ growth for the selected centered stress-trace hierarchy, identifying the kernels, joint test spaces and phase. | Compiled: `CompleteOS` and `NovemberOS.public_os`. |
| Lattice measure and insertions | Reuse the independent Wilson-law comparison, retaining the coupling conversion, microscopic insertions and projection into continuum fields. | Compiled: `lattice_and_scale`; same independent predicate. |
| Order of limits | Preserve full UV convergence at each fixed period and the subsequential IR construction, with one refinement serving the hierarchy. | Compiled in both combined targets. No IR uniqueness claim. |
| Stress tensor and leading trace | Transfer the translation Ward test with its fixed sign and coefficient, identify its stress trace, and prove the same leading two-point coefficient for that field. | Compiled: `translation_ward`, `leading_trace`, `public_trace_eq`. |
| Operator content | Transfer the registered-field coverage, quotient identification, absence of additional null fields, faithfulness and dense word domain. | Compiled: `operator_content`; same independent predicate. |
| Common scale and positive probe | Transfer the existing common calibration and positive continuum-probe conclusions. | Compiled; this does not assert an intrinsic nonzero mass scale or a mass gap. |
| OPE alignment | Relate the November coefficients and remainder estimates to the group's explicit-radius OPE predicate. | Compiled: `OPE.from_source`, attached to the public hierarchy in the new target. |
| Additional retained source results | Identify contact extensions and other October conclusions on the November witness if they are to appear in the new assessment. | Compiled: `Acceptance.source_conclusions` in `RetainedSourceProof`; source conclusions, not a new independent interpretation of every definition. |
| Combined acceptance | Assemble the independent clauses on one November witness and audit its axiom dependencies. | Both combined theorems compile; standard axioms only. |
| Independent-target Comparator | Freeze the combined statement and definitions, then run Comparator on its proof with the checked tool versions. | Both combined targets passed on November 11; source and frozen-input stability verified. |

The OS bridge concerns the selected scalar stress-trace hierarchy with diagonal-flat joint Schwartz tests. Its transfer must preserve that scope; it is not automatically an unrestricted contact-extension theorem or a test of every field in the full collection. The operator-content check likewise does not identify the result with a separately specified canonical Hilbert space.

## Transfer procedure used

The independent October predicate bodies were retained and their proofs adapted to November. Renamed fields and changed source interfaces are recorded in the [port report](november-port.md) and its audit. The additional source conclusions were recovered explicitly.

The individual adapters and their axiom dependencies were checked before the combined-target Comparator run. The final record identifies the exact source and verification inputs. Existing submission and dependency builds were reused; the Comparator overlay built the review modules from source.

November's all-radius, all-phase Maxwell limit is an additional important existence requirement. Its statement and proof path are discussed in the comparison document. It should remain visible in the review alongside the transferred checks. Positive-order perturbative matching is reviewed separately.

## Optional follow-up and matching review

A new November-specific adversarial exercise has not been performed. It is optional supplementary work, not an unfinished condition of the October test transfer. Further targeted existence checks can be added if a concrete discrepancy is identified.

The matching work now includes a proved [all-orders statement restatement](matching/all-orders-statement-review.md) and a completed [finite ghost-loop comparison](matching/ghost-finite-check.md), with its own Comparator pass. The central remaining task is human validation of the all-order reference definitions, renormalization prescription, operator dictionary and their relation to the physical asymptotic statement. The [repository README](../README.md#requirements-for-human-review) sets out the review requirements and how to record conclusions. These matching questions are separate from the completed transfer of the October construction checks.

The earlier experiment applying November conditions to October was stopped before its combined proof compiled and before Comparator started. It is not a result for the present task, which applies the group's requirements to November.
