import GhostLoopBenchmark

/-! Frozen independent finite-part target. The placeholder is confined to
this reference proof. GhostLoopSolution.lean supplies the actual proof;
Comparator permits no definition holes and only standard Lean axioms. -/
set_option autoImplicit false
namespace YMReview.NovemberMatching.GhostSolution
theorem acceptance (G : YM.Gauge) : GhostLoop.SubmittedFinitePartTest G := by
  sorry
end YMReview.NovemberMatching.GhostSolution
