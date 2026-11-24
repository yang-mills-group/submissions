import CombinedAcceptance
import RetainedContactProof

/-! Recover October's additional source conclusions on the supplied November
Final, reader and scaling frame. The assembly below adapts October's
YM/Nonperturbative/Continuum.lean and Headlines.lean; all analytical lemmas
are imported from the November submission, not from an October build. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.Acceptance
open YM YM.Spec YM.OPE YM.OPE.Orbits YM.Nonperturbative
open YM.Contacts.Solstice YangMills
variable {g : GaugeGroup} {C : Family g.core} {o : Extraction.Order} {S : Table C.book}

private theorem contacts_on (F : Final C o S)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (services : OPE.Services C o S) :
    ∃ M : Contacts.Devices F.sector.derivatives, M.basis = Q.port ∧ MultipleLight F M ∧
      Nonempty (Contacts.Transport.SystemBasis M) ∧ Nonempty (Thresholds M) := by
  let t := F.phase.transport
  let M : Contacts.Devices F.sector.derivatives :=
    ⟨Q.port,Q.spans,F.sector.turns,F.room.kernel,t.injection,t.rights,t.spots,t.motion,
      fun d => Classical.choice (MultipleContact.detector_exists d S)⟩
  exact ⟨M,rfl,provided F M rfl services,Contacts.Transport.real_basis M,
    ⟨(installs M (f := fun _ => 1) (fun _ => zero_lt_one)).choose⟩⟩

private theorem wightman {A : Boundary.Wightman S}
    {W : Boundary.Surface S} {V : S.Rotation} {h : S.RealSpin}
    (H : A.Realizes (W := W) V h) : Headline.WightmanAxioms A W :=
  ⟨H.total.norm, H.total.everywhere, H.total.cyclic, H.total.temperate, H.adj, H.meets,
    A.operators.sees W H.meets A.J H.adj, H.localPairs, H.covariance, A.action.strong,
    H.spectral, H.forward, H.unique⟩

/-- October's small assembly lemma, using the November calibration results. -/
private theorem four_on (F : Final C o S) (X : Climb.Scaling S)
    (hg : g.core.Simple) (first : Pert.FirstExtension F X) : Pert.Position.FourMeters F X := by
  have crest := Pert.Position.credible F X first
  obtain ⟨n, Q, square, clean⟩ := Pert.Position.square_four C hg
  obtain ⟨φ, board⟩ := crest.position _ _ Q clean square
  exact ⟨crest, n, Q, φ, square, clean, board,
    Pert.Position.residency F X first hg clean board⟩

theorem source_conclusions (hg : g.IsSimple) (F : Final C o S)
    (L : EveryPhase.Almanac F)
    (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
    (X : Climb.Scaling S)
    (ordered : (Extraction.Order.mk .full o.per).Ordered C S)
    (first : Pert.FirstExtension F X)
    (core : Independent.Core.{0,0} (GaugeGroup.coreSimple hg) F L Q)
    (nested : OPE.Nesting.Uniform F Q) : SourceConclusions hg F := by
  obtain ⟨M, same, contacts, basis, thresholds⟩ := contacts_on F Q core.services
  have ope : Headline.SeparatedOPE F Q := by
    refine ⟨core.ope.coefficients, ?_, core.joint⟩
    intro I J _ _ d e a b M η c ε hM hη hc hε D
    exact core.point a b hM hη hc hε D
  have tr : Headline.TraceExclusions.{0,0} F :=
    ⟨core.trace.centered, core.trace.identified, core.trace.shortDistance,
     core.trace.positive, core.trace.wick,
     fun n U physical unit translations => core.trace.maxwell n U ⟨physical,unit,translations⟩,
     core.trace.invariant⟩
  exact ⟨L, Q, M, X,
    ⟨wilsonLimit F Q ordered, publicReconstruction F Q L core.reconstruction,
      publicOPE F Q ope, publicTrace F Q hg tr⟩,
    RetainedSource.contactDistribution F M contacts, core,
    ⟨F.realization.allWorld, F.realization.chosen, wightman F.realization.qt,
      fun i => wightman (core.reconstruction.isTheory i), core.reconstruction.at_boundary⟩,
    (fun i => view_axioms _ (core.reconstruction.isTheory i)), ope,
    ⟨nested.direct, nested.tested, nested.joint, nested.jointLaw⟩, tr,
    same, contacts, basis, thresholds, first,
    four_on F X (GaugeGroup.coreSimple hg) first⟩

end YMReview.Acceptance
