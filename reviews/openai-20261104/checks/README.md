# Independent November checks

The group's November adapters and combined acceptance theorems compile against the pinned November submission. Read [the port report](../docs/november-port.md) for the meaning of the statements, the changes from October, their limits and the reproduction commands.

| File | Purpose |
| --- | --- |
| [AcceptanceSpec.lean](AcceptanceSpec.lean) | October's independent lattice, OS, Ward, field-content and leading-trace requirements, with the retained source bundle adapted to November. |
| [NovemberAcceptanceSpec.lean](NovemberAcceptanceSpec.lean) | One native construction containing November's public existence conditions and the independent requirements. |
| [NovemberCombined.lean](NovemberCombined.lean) | Proof of the new combined target and the October-shaped target, using November's construction. |
| [CompleteOS.lean](CompleteOS.lean) | Independent E0–E4 and E0′ for the native selected trace. |
| [NovemberOS.lean](NovemberOS.lean) | Identification with the public hierarchy's trace and Schwinger functions. |
| [OPESpec.lean](OPESpec.lean), [OPECheck.lean](OPECheck.lean) | Explicit coefficient and remainder bounds with the radius chosen uniformly before phase and positions. |
| [RetainedSourceProof.lean](RetainedSourceProof.lean), [RetainedContactProof.lean](RetainedContactProof.lean) | Additional reconstruction, contact and calibration conclusions on the November witness. |
| [AxiomAudit.lean](AxiomAudit.lean) | Axiom reports for the main theorems and adapters. |

The OS interface is vendored under [NovemberOSRecon/](NovemberOSRecon/), preserving the source notices. The import prefix differs from October to avoid a module-search collision. The mathematical declarations are unchanged.

The completed Comparator records under `evidence/supplied-targets/` concern OpenAI's supplied targets. The new combined-target run is recorded separately; see [the evidence overview](../evidence/README.md).

The separate [matching checks](matching/) contain the perturbative test specifications, graph-reference audit, free-line and ghost-vertex checks, and a completed independent finite ghost-loop calculation. They are not included in the existence acceptance theorem. The new theorem [`GhostSolution.acceptance`](matching/GhostLoopSolution.lean) proves the full [`SubmittedFinitePartTest`](matching/GhostLoopBenchmark.lean); its separate Comparator run passed. The [proof guide and reproduction commands](../docs/matching/ghost-finite-check.md) explain this graph-level result and the remaining tests of complete physical coefficients.

[`AllOrdersStatement.lean`](matching/AllOrdersStatement.lean) checks the all-orders quantifier structure on one shared lattice-derived construction and measurement. It explicitly exposes arbitrary-order correlation and whole-output OPE remainders and derives that the coupling tends to zero. It reuses the public graph reference and conversion, so it is a statement-alignment check, not an independent all-order identification of the graph rules. The [review checklist](../docs/matching/all-orders-statement-review.md) separates these obligations.
