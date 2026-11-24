import NovemberOS
import RetainedSourceProof
import OPECheck
import Comparators.Existence.Solution

/-! Extend November's existence assembly while retaining the native witness.
The funded run, fixed-volume returns, refinement, Final and reader are selected
once. OpenAI's continuum requirements and the independent checks are then
proved together. No perturbative Matching solution theorem is used. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace YMReview.November
open YangMills YangMills.Wilson YM YM.Spec YM.OPE.Orbits YM.Nonperturbative
open Filter
open scoped Topology

theorem public_realizes {g : GaugeGroup} {hg : g.IsSimple} {b : ℝ}
    (R : ReviewedConstruction g hg b) : R.publicRun.Realizes R.free :=
  ⟨R.trajectory, R.lattice, R.values, R.fixedVolume,
    fun p hp => (R.refine ⟨p, hp⟩).continuum⟩

/-- One construction satisfies the full November existence target and all
transferred independent checks. The penalty may be any fixed positive number. -/
theorem combined_acceptance (g : GaugeGroup) (hg : g.IsSimple) (b : ℝ) (hb : 0 < b) :
    Nonempty (ReviewedConstruction g hg b) := by
  let nativeSimple := GaugeGroup.coreSimple hg
  let R := Independent.fundedRun nativeSimple hb
  obtain ⟨_, W, penalty, funded, _⟩ := (Independent.constructionRun nativeSimple hb).choose_spec
  have broad := R2IGoals.fromFunded.{0} W nativeSimple funded
  obtain ⟨points, fixed, outer⟩ := LeanPointReturns.nativeReturns R nativeSimple broad.jewel.fullMesh
  let B := maxwellReference g
  let D := IssuedRuns.FinalWilsonData.latticeData R.family R.makes hg B
  have each (request : Extraction.Sequence) : Nonempty (CheckedRefinement hg R.family D points request) := by
    let order : Extraction.Order := ⟨.full, request⟩
    obtain ⟨q, _, S, F, X, L, Q, _, ordered, uv, first, reconstructed, trace, services,
      foundation, trees, _⟩ := broad.refine order
    have core := Independent.Core.of_receipts.{0,0} nativeSimple F L Q reconstructed trace
      services.toServices foundation
    have ope : Headline.SeparatedOPE F Q := by
      refine ⟨core.ope.coefficients, ?_, core.joint⟩
      intro I J _ _ d e a b M η c ε hM hη hc hε degree
      exact core.point a b hM hη hc hε degree
    have tr : Headline.TraceExclusions.{0,0} F :=
      ⟨core.trace.centered, core.trace.identified, core.trace.shortDistance,
       core.trace.positive, core.trace.wick,
       fun n U physical unit translations => core.trace.maxwell n U ⟨physical, unit, translations⟩,
       core.trace.invariant⟩
    have sampled := FixedFields.sampledEstimates F Q X first nativeSimple foundation trace core.services
    obtain ⟨frame, comparison, bounds⟩ := AllRadii.extendFrame F Q X first nativeSimple foundation trace sampled
    have source := Acceptance.source_conclusions hg F L Q X ordered first core trees
    have accepted := Acceptance.accepted_of_source hg F (regular R.family hg R.makes) ordered uv source
    exact ⟨{
      refinement := q
      table := S
      final := F
      reader := Q
      continuum := {
        smeared := wilsonLimit F Q (s := (order.refine q).per) ordered
        pointwise := outer F Q
        reconstruction := publicReconstruction F Q L reconstructed
        fieldSpace := IssuedExistencePhase.FieldTable.tables F Q
        vacuumSectors := ⟨IssuedExistencePhase.VacuumReconstruction.phases F Q L reconstructed⟩
        adjoints := IssuedBridge.FieldQuotient.adjoints R.makes hg B F Q
        phaseCorrelations := IssuedBridge.PhaseCorrelations.law F Q D rfl
        ope := publicOPE F Q ope
        coefficients := publicCoefficientLaws F Q
        fusionTrees := Integration.WilsonSharpPhysicalTreeGeometry.onFiledUniform F Q trees
        ward := ⟨publicWards F Q⟩
        trace := publicTrace F Q hg tr
        ultraviolet := AllRadii.maxwellLimit B (hierarchy F Q) (publicScaling F Q X first)
          frame sampled comparison bounds }
      accepted := accepted
      public_os := public_os F Q
      common_ope := YMReview.OPE.from_source (publicOPE F Q ope) }⟩
  exact ⟨{
    family := R.family
    penalty := penalty
    free := B
    lattice := D
    values := points
    trajectory := IssuedRuns.CutoffTrajectory.realizes R.family R.makes hg B
    fixedVolume := fixed
    refine := fun request => Classical.choice (each request) }⟩

end YMReview.November

namespace YMReview.Acceptance
open YangMills YM YM.Spec

/-- Also recover the October-shaped target with its original arbitrary input
order and positive-penalty quantifiers. This uses November's funded-run theorem. -/
theorem combined_acceptance (g : GaugeGroup) (hg : g.IsSimple) (b : ℝ) (hb : 0 < b) :
    CombinedAcceptance g hg b := by
  let hG := GaugeGroup.coreSimple hg
  let R := Independent.fundedRun hG hb
  obtain ⟨_, W, penalty, funded, _⟩ := (Independent.constructionRun hG hb).choose_spec
  have broad := R2IGoals.fromFunded.{0} W hG funded
  refine ⟨R.family, penalty, fun p => ?_⟩
  obtain ⟨q, _, S, F, X, L, Q, _, ordered, uv, first, reconstructed, trace, services,
    foundation, trees, _⟩ := broad.refine p
  have core := Independent.Core.of_receipts.{0,0} hG F L Q reconstructed trace
    services.toServices foundation
  exact ⟨q, S, F, accepted_of_source hg F (regular R.family hg R.makes) ordered uv
    (source_conclusions hg F L Q X ordered first core trees)⟩

end YMReview.Acceptance
