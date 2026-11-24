import YangMills.WilsonProof.Construction
import YangMills.PerturbativeMatching

/-!
# All-orders statement alignment

This file restates the correlation and field-valued OPE estimates with their
quantifiers visible, and proves that one submitted Wilson construction satisfies
both with the same reference, lattice limits, measurement and calibration.

This is a check of the all-orders statement and its shared witnesses. It reuses
the public Reference (including the graph evaluator and scheme conversion).
It does not independently validate the all-order graph rules or subtraction
scheme. That mathematical identification remains a definition-review task.
Constants and small-radius thresholds may depend on the truncation order.
All positions are separated; contact extensions and summability are not claimed.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Filter YangMills YangMills.Matching YangMills.PerturbativeMatching
open scoped Topology BigOperators ContDiff Classical

namespace YMReview.NovemberMatching.AllOrders

variable {g : GaugeGroup} {C : WilsonFamily g} {T : Hierarchy C}

/-- The actual continuum correlations, with the physical fields and positions
both rescaled by the same measurement at radius r. -/
def actualCorrelation (M : PerturbativeMatching.Measurement (maxwellReference g) T) {n : ℕ}
    (d : Fin n → ℕ) (v : (i : Fin n) → (maxwellReference g).sector (d i))
    (phase : Option T.Character) (center : Spacetime) (r : ℝ) (x : Points n) : ℂ :=
  T.correlation phase (fun i => ⟨d i, M.frame r (d i) (v i)⟩)
    (WithLp.toLp 2 fun i => center + r • x i)

/-- Coefficients through order N of the single fixed graph reference after the
single prescribed coupling and field conversion. -/
def correlationPrediction (R : Reference g) {n : ℕ} (N : ℕ) (u : ℝ)
    (d : Fin n → ℕ) (v : (i : Fin n) → (maxwellReference g).sector (d i))
    (x : Points n) : ℂ :=
  ∑ k : Fin (N + 1), (u : ℂ)^k.val *
    R.scheme.conversion.correlation R.coefficients k.val (fun i => ⟨d i, v i⟩) x

/-- One R and M are fixed BEFORE every arity, perturbative order, derivative
order, cutoff, compact, phase and field tuple. The eventual radius is chosen
before phases, centers, fields and points, and works for every derivative ≤ j. -/
def CorrelationRemainders (R : Reference g) (M : PerturbativeMatching.Measurement (maxwellReference g) T) : Prop :=
  ∀ (n N j : ℕ) (d : Fin n → ℕ) (K : Set (Points n)),
    IsCompact K → K ⊆ WilsonFamily.separated n →
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∀ (phase : Option T.Character)
        (v : (i : Fin n) → (maxwellReference g).sector (d i))
        (center : Spacetime) (x : Points n), x ∈ K →
        ContDiffAt ℝ j (actualCorrelation M d v phase center r) x ∧
        ContDiffAt ℝ j (correlationPrediction R N (M.coupling r) d v) x ∧
        ∀ l ≤ j, ‖iteratedFDeriv ℝ l (fun y =>
          actualCorrelation M d v phase center r y - correlationPrediction R N (M.coupling r) d v y) x‖ ≤
          A * (∏ i, coefficientNorm (v i)) * |M.coupling r|^(N + 1)

/-- The entire physical OPE output through h, pulled back to the same field
frame as the input insertions. This sums every channel, not just the unit. -/
def actualOutput (M : PerturbativeMatching.Measurement (maxwellReference g) T) {n : ℕ}
    (h : ℕ) (d : Fin n → ℕ) (v : (i : Fin n) → (maxwellReference g).sector (d i))
    (center : Spacetime) (r : ℝ) (x : Points n) : (maxwellReference g).sector h :=
  (M.frame r h).symm
    (∑ e : Fin (h + 1), ∑ channel : T.Channel e.val,
      T.coefficient (fun i => ⟨d i, M.frame r (d i) (v i)⟩) e.val channel
        (fun i => center + r • x i) center •
        M.includeField (Nat.le_of_lt_succ e.isLt) (T.channelField e.val channel))

def outputPrediction (R : Reference g) {n : ℕ} (h N : ℕ) (u : ℝ)
    (d : Fin n → ℕ) (v : (i : Fin n) → (maxwellReference g).sector (d i))
    (x : Points n) : (maxwellReference g).sector h :=
  ∑ k : Fin (N + 1), (u : ℂ)^k.val •
    R.scheme.conversion.ope R.coefficients h k.val (fun i => ⟨d i, v i⟩) x

/-- Arbitrary finite output cutoff h and perturbative order N are separate
quantifiers. This bound is in the coefficient norm of the entire output field. -/
def OPERemainders (R : Reference g) (M : PerturbativeMatching.Measurement (maxwellReference g) T) : Prop :=
  ∀ (n h N : ℕ) (d : Fin n → ℕ) (center : Spacetime) (K : Set (Points n)),
    IsCompact K → K ⊆ WilsonFamily.separated n →
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
      ∀ (v : (i : Fin n) → (maxwellReference g).sector (d i))
        (x : Points n), x ∈ K →
        coefficientNorm (actualOutput M h d v center r x -
          outputPrediction R h N (M.coupling r) d v x) ≤
          A * (∏ i, coefficientNorm (v i)) * |M.coupling r|^(N + 1)

theorem correlation_remainders {R : Reference g} {M : PerturbativeMatching.Measurement (maxwellReference g) T}
    (H : CorrelationExpansion R M) : CorrelationRemainders R M := by
  exact H.shapeDerivatives

theorem ope_remainders {R : Reference g} {M : PerturbativeMatching.Measurement (maxwellReference g) T}
    (H : OPEExpansion R M) : OPERemainders R M := by
  exact H.uniformOnCompact

/-- The running-law hypothesis really supplies a small expansion parameter.
This public-interface proof follows the argument of the submitted
`YangMills.Matching.CorrelationOnly.clockAtZero`: positivity and the normalized
one-loop limit force a positive logarithmic coefficient, then the clock tends to zero. -/
theorem coupling_zero (M : PerturbativeMatching.Measurement (maxwellReference g) T) :
    Tendsto M.coupling (𝓝[>] 0) (𝓝 0) := by
  let a : ℝ := 2 * oneLoopBeta (maxwellReference g)
  let root := fun r : ℝ => Real.sqrt (a * Real.log r⁻¹)
  have logs : Tendsto (fun r : ℝ => Real.log r⁻¹) (𝓝[>] 0) atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have normalized : Tendsto (fun r => M.coupling r * root r) (𝓝[>] 0) (𝓝 1) := M.oneLoop
  have hnorm := normalized.eventually_const_lt (by norm_num : (0:ℝ) < 1)
  have hlog := logs.eventually (eventually_gt_atTop (0:ℝ))
  obtain ⟨r, hc, hprod, hl⟩ := (M.coupling_pos.and (hnorm.and hlog)).exists
  have hroot : 0 < root r := by
    rcases mul_pos_iff.mp hprod with h | h
    · exact h.2
    · exact False.elim (lt_asymm hc h.1)
  have ha : 0 < a := (mul_pos_iff_of_pos_right hl).mp (Real.sqrt_pos.mp hroot)
  have big : Tendsto root (𝓝[>] 0) atTop :=
    Real.tendsto_sqrt_atTop.comp (Filter.Tendsto.const_mul_atTop ha logs)
  have inv : Tendsto (fun r => (root r)⁻¹) (𝓝[>] 0) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp big
  have identify : (fun r => (M.coupling r * root r) * (root r)⁻¹) =ᶠ[𝓝[>] 0] M.coupling := by
    filter_upwards [big.eventually (eventually_gt_atTop (0:ℝ))] with r hr
    simp [hr.ne']
  simpa using (normalized.mul inv).congr' identify

/-- One run and reference, before all requested volume sequences. On each
selected refinement, the same calibrated measurement satisfies both all-orders
estimates and refers to the continuum limit of the retained Wilson lattice.
There is no choice of a new hierarchy or frame for each perturbative order. -/
def SharedStatement (g : GaugeGroup) : Prop :=
  ∃ (run : Wilson.Construction g) (R : Reference g)
    (lattice : Wilson.WilsonData (maxwellReference g) run.family)
    (kernels : Wilson.PeriodPointTable run.family),
    AdmissibleLattice lattice ∧ SmoothMeshLimit run.family kernels ∧
    Wilson.FixedPointReturns run.family kernels ∧
    ∀ (periods : ℕ → ℕ) (strict : StrictMono periods),
      let limit := run.refine periods strict
      ∃ (M : PerturbativeMatching.Measurement (maxwellReference g) limit.hierarchy)
        (J : MSbar.PositionFrames limit.hierarchy (maxwellReference g)),
        Wilson.ContinuumLimit lattice kernels (periods ∘ limit.indices) limit.hierarchy ∧
        FrameCalibration R.scheme M J ∧ HasChannelBasis M ∧
        Tendsto M.coupling (𝓝[>] 0) (𝓝 0) ∧
        CorrelationRemainders R M ∧ OPERemainders R M

theorem of_matchedRun {run : Wilson.Construction g} (H : MatchedRun run) : SharedStatement g := by
  refine ⟨run, H.reference, H.lattice, H.kernels, H.admissible, H.meshLimit,
    H.fixedPeriodLimits, ?_⟩
  intro periods strict
  let F := H.refinement periods strict
  exact ⟨F.measurement, F.positionFrame, F.continuum, F.calibration, F.channelBasis,
    coupling_zero F.measurement,
    correlation_remainders F.correlations, ope_remainders F.operatorProducts⟩

/-- Unconditional statement alignment for the actual submitted construction,
assuming only the stated gauge-group simplicity hypothesis. -/
theorem submitted (g : GaugeGroup) (simple : g.IsSimple) : SharedStatement g := by
  obtain ⟨H⟩ := YangMills.WilsonProof.matchedRun g simple
  exact of_matchedRun H

end YMReview.NovemberMatching.AllOrders

#print axioms YMReview.NovemberMatching.AllOrders.submitted
#print axioms YMReview.NovemberMatching.AllOrders.coupling_zero
#check YMReview.NovemberMatching.AllOrders.submitted
