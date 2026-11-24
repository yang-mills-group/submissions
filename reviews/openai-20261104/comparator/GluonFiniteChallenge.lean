import GluonLoopFinite

/-! Frozen independent finite-part target. The placeholder is confined to
this reference proof. GluonLoopSolution.lean supplies the actual proof;
Comparator permits no definition holes and only standard Lean axioms. -/
set_option autoImplicit false
namespace YMReview.NovemberMatching.GluonSolution
theorem acceptance (G : YM.Gauge) : GluonLoop.SubmittedFinitePartTest G := by
  sorry
end YMReview.NovemberMatching.GluonSolution
