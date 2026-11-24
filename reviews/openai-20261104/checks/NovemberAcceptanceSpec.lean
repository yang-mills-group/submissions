import AcceptanceSpec
import OPESpec
import YangMills.Existence

/-! Independent requirements attached to the very hierarchy used in November's
existence target. Native data are retained so that the OS, lattice, field and
Ward checks cannot be satisfied by choosing an unrelated second theory. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.November
open YangMills YangMills.Wilson YM YM.Spec YM.OPE.Orbits
open MeasureTheory

/-- The public selected stress-trace kernels paired with the independent
diagonal-flat joint Schwartz tests, in the OSreconstruction coordinates. -/
def publicSchwinger {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C) :
    SchwingerFunctions 3 :=
  fun n f => ∫ x : NPointDomain 3 n,
    T.correlation (some T.selected) (fun _ => ⟨4, T.centeredTrace⟩)
      (YMOSBridge.configEquiv n x) * f.1 x

def PublicOS {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C) : Prop :=
  ∃ axioms : OsterwalderSchraderAxioms 3,
    axioms.S = publicSchwinger T ∧ Nonempty (OSArityLinearGrowthCondition 3 axioms)

/-- One native Final and reader supply every clause for this requested volume
sequence. The public hierarchy is defined from them, not separately selected. -/
structure CheckedRefinement {g : GaugeGroup} (hg : g.IsSimple)
    (C : Family g.core) {B : Maxwell.Reference g}
    (D : WilsonData B (wilsonFamily C)) (values : PeriodPointTable (wilsonFamily C))
    (request : Extraction.Sequence) where
  refinement : Extraction.Order
  table : Table C.book
  final : Final C ((Extraction.Order.mk .full request).refine refinement) table
  reader : Reader final.sector.derivatives final.sector.turns final.room.kernel.spin
  continuum : ContinuumLimit D values (request.choose ∘ refinement.per.choose)
    (hierarchy final reader)
  accepted : Acceptance.Accepted hg final
  public_os : PublicOS (hierarchy final reader)
  common_ope : YMReview.OPE.CommonOPE (hierarchy final reader)

/-- The family, raw lattice fields and fixed-volume point table precede the
requested IR sequence. This retains the entire November existence target and
the group's checks, including the additional source contact/calibration clauses. -/
structure ReviewedConstruction (g : GaugeGroup) (hg : g.IsSimple) (b : ℝ) where
  family : Family g.core
  penalty : family.path.levels.clock.kernel.penalty = b
  free : Maxwell.Reference g
  lattice : WilsonData free (wilsonFamily family)
  values : PeriodPointTable (wilsonFamily family)
  trajectory : WilsonTrajectory free (wilsonFamily family)
  fixedVolume : FixedPointReturns (wilsonFamily family) values
  refine : (request : Extraction.Sequence) → CheckedRefinement hg family lattice values request

def ReviewedConstruction.publicRun {g : GaugeGroup} {hg : g.IsSimple} {b : ℝ}
    (R : ReviewedConstruction g hg b) : Wilson.Construction g where
  family := wilsonFamily R.family
  refine p hp :=
    let V := R.refine ⟨p, hp⟩
    ⟨V.refinement.per.choose, V.refinement.per.monotone, hierarchy V.final V.reader⟩

end YMReview.November
