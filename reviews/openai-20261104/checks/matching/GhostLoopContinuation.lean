import GhostLoopRadial
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic
/-!
# Actual radial continuation of the submitted ghost loop

Evaluates the radial integral on the real regulator axis, starting with the
submitted `closeG`, its radial chopping derivative, and the actual graph.
The full finite-part test additionally needs the regulator jet and the
infrared Mellin limit; neither is asserted by `actual_force_real`.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open YM YM.MS YM.MS.Arts YM.MS.ScaleForest
open Plane Koszul Heat Flux Landau Book Convolve Motif Halo
open Function Filter Set Finset MeasureTheory Metric Real
open Tone Momentum Frame Wire Color Detect Native Native.Wilsonian City Logarithm Signal
open Landau.Detect.Mark Wind High Knobs Arc Rock Path Oceans Plum Alps Garment Pearl Train
open YM.WilsonMS.BetaValue YM.WilsonMS.BetaValue.HeatPapers SquareShift
open scoped BigOperators Topology ContDiff
namespace YMReview.NovemberMatching.GhostContinuation
open GhostRadial

lemma compact_derivative (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (R : ℝ) :
    HasDerivAt (fun R => ∫ t : ℝ in (0:ℝ)..1, f (t,R))
      (∫ t : ℝ in (0:ℝ)..1, deriv (fun R=>f (t,R)) R) R := by
  have h := Heat.Lot mint cour1 hf
  have hc : ContDiff ℝ ∞ (fun R => ∫ t : ℝ in (0:ℝ)..1, f (t,R)) := by
    simpa only [intervalIntegral.integral_of_le zero_le_one] using! h.contDiff
  apply (hc.differentiable (by simp) R).hasDerivAt.congr_deriv
  simp only [← iteratedDeriv_one,iteratedDeriv,intervalIntegral.integral_of_le zero_le_one]
  rw [show iteratedFDeriv ℝ 1 (fun R => ∫ t : ℝ in Set.Ioc 0 1, f (t,R)) R = _ from
    congrFun (h.identity 1) R,ContinuousMultilinearMap.integral_apply (h.integ 1 R)]

/-- Differentiated radial Gaussian polynomial, divided by the radial variable. -/
def radialDerivative (nu A B C R : ℝ) :=
  Real.exp (-(nu*R^2)) * (-2*nu*A+(2-2*nu*R^2)*B+(4*R^2-2*nu*R^4)*C)

lemma density_derivative (nu A B C R : ℝ) :
    HasDerivAt (fun R : ℝ => Real.exp (-(nu*R^2))*(A+R^2*B+R^4*C))
      (R*radialDerivative nu A B C R) R := by
  have he := (((hasDerivAt_pow 2 R).const_mul nu).neg).exp
  have hp := (((hasDerivAt_pow 2 R).mul_const B).const_add A).add
    ((hasDerivAt_pow 4 R).mul_const C)
  apply (he.mul hp).congr_deriv
  simp only [radialDerivative]
  norm_num
  ring

def prefactor (Q x t : ℝ) := t^3*Real.exp (slope t*x^2*Q)*volume4 t

def radialMoment (Q p r u x t R : ℝ) :=
  radialDerivative (ν t)
    (pairValue Q p r u (gaussS (ν t)) (slope t*x) ((slope t+1)*x))
    (GhostLoopFinite.radialSquare Q (p*r) u (gaussS (ν t)) (slope t*x) ((slope t+1)*x))
    (GhostLoopFinite.radialFourth (p*r) u (gaussS (ν t)) (slope t*x) ((slope t+1)*x)) R

lemma weighted_heat_derivative (Q p r u x t R : ℝ) :
    HasDerivAt (fun R : ℝ => Real.exp (-(ν t*R^2))*extendedHeatValue R Q p r u x t)
      (R*(prefactor Q x t*radialMoment Q p r u x t R)) R := by
  have h := (density_derivative (ν t)
    (pairValue Q p r u (gaussS (ν t)) (slope t*x) ((slope t+1)*x))
    (GhostLoopFinite.radialSquare Q (p*r) u (gaussS (ν t)) (slope t*x) ((slope t+1)*x))
    (GhostLoopFinite.radialFourth (p*r) u (gaussS (ν t)) (slope t*x) ((slope t+1)*x)) R).const_mul
      (prefactor Q x t)
  convert! h using 1
  · funext R
    unfold extendedHeatValue prefactor
    ring
  · unfold radialMoment
    ring

lemma weighted_heat_smooth (Q p r u x : ℝ) :
    ContDiff ℝ ∞ (fun v : ℝ × ℝ => Real.exp (-(ν v.1*v.2^2))*extendedHeatValue v.2 Q p r u x v.1) := by
  unfold extendedHeatValue pairValue squareValue firstValue GhostLoopFinite.radialSquare
    GhostLoopFinite.radialFourth gaussS SquareShift.slope volume4 ν
  fun_prop (disch:= intros; positivity)

lemma integrated_radial_derivative (Q p r u x R : ℝ) :
    HasDerivAt (fun R : ℝ => ∫ t : ℝ in (0:ℝ)..1,
      Real.exp (-(ν t*R^2))*extendedHeatValue R Q p r u x t)
      (R*(∫ t : ℝ in (0:ℝ)..1, prefactor Q x t*radialMoment Q p r u x t R)) R := by
  have h := compact_derivative _ (weighted_heat_smooth Q p r u x) R
  simp_rw [(weighted_heat_derivative Q p r u x _ _).deriv,
    intervalIntegral.integral_const_mul] at h
  exact h


/-- The radial chopping derivative of the submitted loop is the explicit
Gaussian polynomial. The smooth extension at zero is not used to divide by R. -/
theorem actual_chop (G : Gauge) (p : SectorP 0) (i : L 0) (a b : G.ColorIndex)
    (R : ℝ) (hR : 0<R) :
    chop (loopCarpet (cursor true).half (TwoPoint.stemPair G true) 0
      (TwoPoint.word i i a b p)) (R,1) =
      (-8*(∑ d : G.ColorIndex,angle d a b)/(room:ℂ)) *
        ((∫ t : ℝ in (0:ℝ)..1, prefactor p.sq 1 t*radialMoment p.sq (p i) (p i) 1 1 t R) : ℝ) := by
  let F := loopCarpet (cursor true).half (TwoPoint.stemPair G true) 0 (TwoPoint.word i i a b p)
  let c : ℂ := -8*(∑ d : G.ColorIndex,angle d a b)/(room:ℂ)
  have hgood := ((loop_converges ((cursor true).ok.forms true) (TwoPoint.stem_form G true)
    (Town_nat 0) (TwoPoint.word i i a b p)).2.1 0)
  have hs : ContDiff ℝ ∞ F := by simpa [F,pruning] using! hgood.1.smooth ()
  have hr : Reflect F := by simpa [F,pruning] using! hgood.2.1
  have hd := integrated_radial_derivative p.sq (p i) (p i) 1 1 R
  have hc := ((Complex.ofRealCLM.hasFDerivAt).comp_hasDerivAt R hd).const_mul c
  have hc' : HasDerivAt (fun R : ℝ => F (R,1))
      (c * ((R*(∫ t : ℝ in (0:ℝ)..1,
        prefactor p.sq 1 t*radialMoment p.sq (p i) (p i) 1 1 t R)) : ℝ)) R := by
    convert! hc using 1
    funext R
    exact actual_carpet_evaluated G p i a b R 1 0
  apply mul_left_cancel₀ (show (R:ℂ)≠0 by exact_mod_cast hR.ne')
  calc
    (R:ℂ)*chop F (R,1) = Arc.d F (R,1) := by
      simpa only [Complex.real_smul] using restore hr hs R 1
    _ = c * ((R*(∫ t : ℝ in (0:ℝ)..1,
        prefactor p.sq 1 t*radialMoment p.sq (p i) (p i) 1 1 t R)) : ℝ) :=
      (Arc.dr hs 1 R).unique hc'
    _ = _ := by push_cast; ring


/-- A uniform Gaussian majorant for the remaining radial/heat Fubini step. -/
lemma radial_weight_integrable (s : ℝ) (hs : -1<s) (c : ℝ → ℝ) (hc : Continuous c) :
    Integrable (fun v : ℝ × ℝ => v.1^s*Real.exp (-(ν v.2*v.1^2))*c v.2) (μhalf.prod mint) := by
  obtain ⟨K,hK⟩ := (isCompact_Icc.image hc.norm).bddAbove
  have hg : Integrable (fun R : ℝ => R^s*Real.exp (-R^2)) μhalf := by
    simpa only [neg_one_mul] using! (integrableOn_rpow_mul_exp_neg_mul_sq (b:=1) (by norm_num) hs)
  have hd : Integrable (fun v : ℝ × ℝ => ‖v.1^s*Real.exp (-v.1^2)‖*K) (μhalf.prod mint) :=
    hg.norm.mul_prod (integrable_const K)
  refine hd.mono' (by fun_prop) ?_
  have ht : ∀ᵐ v ∂μhalf.prod mint, v.2 ∈ Icc (0:ℝ) 1 := by
    apply (Measure.quasiMeasurePreserving_snd (μ:=μhalf) (ν:=mint)).tendsto_ae.eventually
    exact (ae_restrict_mem measurableSet_Ioc).mono (fun _ hx=>Ioc_subset_Icc_self hx)
  filter_upwards [ht] with v hv
  have hcv : ‖c v.2‖ ≤ K := hK (mem_image_of_mem _ hv)
  have he : ‖Real.exp (-(ν v.2*v.1^2))‖ ≤ ‖Real.exp (-v.1^2)‖ := by
    simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    unfold ν
    nlinarith [sq_nonneg v.1,sq_nonneg v.2,mul_nonneg (sq_nonneg v.1) (sq_nonneg v.2)]
  simp only [norm_mul]
  exact mul_le_mul (mul_le_mul_of_nonneg_left he (norm_nonneg _)) hcv (norm_nonneg _) (by positivity)

lemma radial_weight_integral (s : ℝ) (hs : -1<s) (c : ℝ → ℝ) (hc : Continuous c) :
    (∫ R : ℝ, (∫ t : ℝ in (0:ℝ)..1,
      R^s*Real.exp (-(ν t*R^2))*c t) ∂μhalf) =
    ∫ t : ℝ in (0:ℝ)..1, c t * ((ν t)^(-(s+1)/2)/2*Real.Gamma ((s+1)/2)) := by
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  rw [integral_integral_swap (radial_weight_integrable s hs c hc)]
  apply integral_congr_ae
  filter_upwards with t
  rw [MeasureTheory.integral_mul_const]
  have he := integral_rpow_mul_exp_neg_mul_rpow (p:=2) (q:=s) (b:=ν t) (by norm_num) hs (ν_pos t)
  simp only [Real.rpow_two,neg_mul] at he
  rw [he]
  ring


lemma radial_power_shift (z : ℝ) (k : ℕ) (R : ℝ) (hR : 0<R) :
    R^(2*z+1)*R^(2*k) = R^(2*(z+k)+1) := by
  rw [← Real.rpow_natCast R (2*k),← Real.rpow_add hR]
  congr 1
  push_cast
  ring

/-- Real-regulator radial integral of the complete differentiated numerator. -/
theorem radial_moment_integral (z nu A B C : ℝ) (hz : -1<z) (hn : 0<nu) :
    -(∫ R : ℝ, R^(2*z+1)*radialDerivative nu A B C R ∂μhalf)/Real.Gamma (z+1) =
      nu^(-z)*A + z*nu^(-z-1)*B + z*(z+1)*nu^(-z-2)*C := by
  let g (k : ℕ) (R : ℝ) := R^(2*(z+k)+1)*Real.exp (-(nu*R^2))
  have hg (k : ℕ) : Integrable (g k) μhalf := by
    simpa only [g,neg_mul] using! integrableOn_rpow_mul_exp_neg_mul_sq hn (show -1<2*(z+k)+1 by have hk : (0:ℝ)≤k := Nat.cast_nonneg k; linarith)
  have he : (fun R : ℝ => R^(2*z+1)*radialDerivative nu A B C R) =ᵐ[μhalf]
      (fun R => (-2*nu*A+2*B)*g 0 R+(-2*nu*B+4*C)*g 1 R+(-2*nu*C)*g 2 R) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with R hR
    have h2 := radial_power_shift z 1 R hR
    have h4 := radial_power_shift z 2 R hR
    norm_num only [Nat.cast_one,Nat.cast_ofNat,Nat.reduceMul] at h2 h4
    unfold radialDerivative g
    norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,add_zero]
    linear_combination Real.exp (-(nu*R^2)) * (-2*nu*B+4*C)*h2 +
      Real.exp (-(nu*R^2)) * (-2*nu*C)*h4
  have h0 : Integrable (fun R => (-2*nu*A+2*B)*g 0 R) μhalf := (hg 0).const_mul _
  have h1 : Integrable (fun R => (-2*nu*B+4*C)*g 1 R) μhalf := (hg 1).const_mul _
  have h2 : Integrable (fun R => (-2*nu*C)*g 2 R) μhalf := (hg 2).const_mul _
  have h01 : Integrable (fun R => (-2*nu*A+2*B)*g 0 R+(-2*nu*B+4*C)*g 1 R) μhalf := h0.add h1
  rw [integral_congr_ae he,MeasureTheory.integral_add h01 h2,MeasureTheory.integral_add h0 h1]
  simp_rw [MeasureTheory.integral_const_mul]
  have hz0 := GhostLoopFinite.normalized_radial_zero z nu hz hn
  have hz2 := GhostLoopFinite.normalized_radial_two z nu hz hn
  have hz4 := GhostLoopFinite.normalized_radial_four z nu hz hn
  simp only [Real.rpow_two,neg_mul] at hz0 hz2 hz4
  simp only [g,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,add_zero,neg_mul]
  linear_combination A*hz0+B*hz2+C*hz4


lemma radial_family_integrable (z : ℝ) (hz : -1<z) (a b c : ℝ → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    Integrable (fun v : ℝ × ℝ => v.1^(2*z+1)*radialDerivative (ν v.2) (a v.2) (b v.2) (c v.2) v.1)
      (μhalf.prod mint) := by
  let g (k : ℕ) (v : ℝ × ℝ) := v.1^(2*(z+k)+1)*Real.exp (-(ν v.2*v.1^2))
  have h0 : Integrable (fun v : ℝ × ℝ => g 0 v*(-2*ν v.2*a v.2+2*b v.2)) (μhalf.prod mint) := by
    exact radial_weight_integrable _ (by linarith) (fun t=> -2*ν t*a t+2*b t) (by unfold ν; fun_prop)
  have h1 : Integrable (fun v : ℝ × ℝ => g 1 v*(-2*ν v.2*b v.2+4*c v.2)) (μhalf.prod mint) := by
    exact radial_weight_integrable _ (by norm_num; linarith) (fun t=> -2*ν t*b t+4*c t) (by unfold ν; fun_prop)
  have h2 : Integrable (fun v : ℝ × ℝ => g 2 v*(-2*ν v.2*c v.2)) (μhalf.prod mint) := by
    exact radial_weight_integrable _ (by norm_num; linarith) (fun t=> -2*ν t*c t) (by unfold ν; fun_prop)
  apply ((h0.add h1).add h2).congr
  have hr : ∀ᵐ v ∂μhalf.prod mint, 0<v.1 :=
    (Measure.quasiMeasurePreserving_fst (μ:=μhalf) (ν:=mint)).tendsto_ae.eventually
      (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [hr] with v hv
  have h2 := radial_power_shift z 1 v.1 hv
  have h4 := radial_power_shift z 2 v.1 hv
  norm_num only [Nat.cast_one,Nat.cast_ofNat,Nat.reduceMul] at h2 h4
  unfold g radialDerivative
  simp only [Pi.add_apply]
  norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,add_zero]
  linear_combination -Real.exp (-(ν v.2*v.1^2))*(-2*ν v.2*b v.2+4*c v.2)*h2 -
    Real.exp (-(ν v.2*v.1^2))*(-2*ν v.2*c v.2)*h4

/-- Actual exchange and evaluation of the radial/compact integrals. -/
theorem radial_family_integral (z : ℝ) (hz : -1<z) (a b c : ℝ → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    -(∫ R : ℝ, (∫ t : ℝ in (0:ℝ)..1,
      R^(2*z+1)*radialDerivative (ν t) (a t) (b t) (c t) R) ∂μhalf)/Real.Gamma (z+1) =
    ∫ t : ℝ in (0:ℝ)..1,
      (ν t)^(-z)*a t+z*(ν t)^(-z-1)*b t+z*(z+1)*(ν t)^(-z-2)*c t := by
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  rw [integral_integral_swap (radial_family_integrable z hz a b c ha hb hc),
    ← MeasureTheory.integral_neg,← MeasureTheory.integral_div]
  apply integral_congr_ae
  filter_upwards with t
  exact radial_moment_integral z (ν t) (a t) (b t) (c t) hz (ν_pos t)


def coeffA (Q p r u x t : ℝ) := prefactor Q x t *
  pairValue Q p r u (gaussS (ν t)) (SquareShift.slope t*x) ((SquareShift.slope t+1)*x)
def coeffB (Q p r u x t : ℝ) := prefactor Q x t *
  GhostLoopFinite.radialSquare Q (p*r) u (gaussS (ν t)) (SquareShift.slope t*x) ((SquareShift.slope t+1)*x)
def coeffC (Q p r u x t : ℝ) := prefactor Q x t *
  GhostLoopFinite.radialFourth (p*r) u (gaussS (ν t)) (SquareShift.slope t*x) ((SquareShift.slope t+1)*x)

lemma moment_prefactor (Q p r u x t R : ℝ) :
    prefactor Q x t*radialMoment Q p r u x t R =
      radialDerivative (ν t) (coeffA Q p r u x t) (coeffB Q p r u x t) (coeffC Q p r u x t) R := by
  unfold radialMoment coeffA coeffB coeffC radialDerivative
  ring

lemma coeffs_continuous (Q p r u x : ℝ) :
    Continuous (coeffA Q p r u x) ∧ Continuous (coeffB Q p r u x) ∧ Continuous (coeffC Q p r u x) := by
  unfold coeffA coeffB coeffC prefactor pairValue squareValue firstValue
    GhostLoopFinite.radialSquare GhostLoopFinite.radialFourth volume4 gaussS SquareShift.slope ν
  exact ⟨by fun_prop (disch:=intro; positivity),by fun_prop (disch:=intro; positivity),by fun_prop (disch:=intro; positivity)⟩

def continuedValue (z Q p r u x : ℝ) := ∫ t : ℝ in (0:ℝ)..1,
  (ν t)^(-z)*coeffA Q p r u x t + z*(ν t)^(-z-1)*coeffB Q p r u x t +
    z*(z+1)*(ν t)^(-z-2)*coeffC Q p r u x t

lemma actual_radial_integral (z Q p r u x : ℝ) (hz : -1<z) :
    -(∫ R : ℝ, R^(2*z+1)*(∫ t : ℝ in (0:ℝ)..1,
      prefactor Q x t*radialMoment Q p r u x t R) ∂μhalf)/Real.Gamma (z+1) =
      continuedValue z Q p r u x := by
  simp_rw [← intervalIntegral.integral_const_mul,moment_prefactor]
  obtain ⟨ha,hb,hc⟩ := coeffs_continuous Q p r u x
  exact radial_family_integral z hz _ _ _ ha hb hc

/-- Explicit evaluation of the submitted continued force along the real
regulator axis. This is a source-level equality, before any Taylor reading
or infrared limit. -/
theorem actual_force_real (G : Gauge) (p : SectorP 0) (i : L 0) (a b : G.ColorIndex)
    (z : ℝ) (hz : -1<z) :
    TwoPoint.kinetic (TwoPoint.ratePair G true true (z:ℂ)) a b p i i =
      -8*(∑ d : G.ColorIndex,angle d a b) *
      Complex.exp ((z:ℂ)*((Real.log Real.pi-2*Real.log (2*Real.pi):ℝ):ℂ)) *
      (continuedValue z p.sq (p i) (p i) 1 1 : ℝ) := by
  let c : ℂ := -8*(∑ d : G.ColorIndex,angle d a b)/(room:ℂ)
  let J : ℝ := ∫ R : ℝ, R^(2*z+1)*(∫ t : ℝ in (0:ℝ)..1,
      prefactor p.sq 1 t*radialMoment p.sq (p i) (p i) 1 1 t R) ∂μhalf
  have hJ : -J/Real.Gamma (z+1) = continuedValue z p.sq (p i) (p i) 1 1 :=
    actual_radial_integral z p.sq (p i) (p i) 1 1 hz
  unfold TwoPoint.kinetic TwoPoint.ratePair
  rw [GhostLoopFinite.ghost_closeG_physical]
  have hi : (fun R : ℝ => (R:ℂ)^(2*(z:ℂ)+1)*chop (loopCarpet (cursor true).half
      (TwoPoint.stemPair G true) 0 (TwoPoint.word i i a b p)) (R,1)) =ᵐ[μhalf]
      (fun R => c * ((R^(2*z+1)*(∫ t : ℝ in (0:ℝ)..1,
        prefactor p.sq 1 t*radialMoment p.sq (p i) (p i) 1 1 t R)) : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with R hR
    rw [actual_chop G p i a b R hR]
    have hp : (R:ℂ)^(2*(z:ℂ)+1) = ((R^(2*z+1):ℝ):ℂ) := by
      rw [show 2*(z:ℂ)+1=((2*z+1:ℝ):ℂ) by push_cast; rfl,← Complex.ofReal_cpow hR.le]
    rw [hp]
    change _ = c * ((R^(2*z+1)*(∫ t : ℝ in (0:ℝ)..1,
        prefactor p.sq 1 t*radialMoment p.sq (p i) (p i) 1 1 t R)) : ℝ)
    push_cast
    ring
  rw [integral_congr_ae hi,MeasureTheory.integral_const_mul,integral_complex_ofReal]
  change -feeD (z:ℂ)*(c*(J:ℂ)) = _
  rw [← hJ]
  unfold feeD c
  rw [show (z:ℂ)+1=((z+1:ℝ):ℂ) by push_cast; rfl,Complex.Gamma_ofReal]
  have hn : (room:ℂ) ≠ 0 := by exact_mod_cast room_pos.ne'
  push_cast
  field_simp


/-- Rewrite the split moments as the dimension-D Gaussian moment. -/
lemma continued_moment (z Q p r u x t : ℝ) :
    (ν t)^(-z)*coeffA Q p r u x t + z*(ν t)^(-z-1)*coeffB Q p r u x t +
      z*(z+1)*(ν t)^(-z-2)*coeffC Q p r u x t =
    prefactor Q x t*(ν t)^(-z)*
      GhostLoopFinite.momentD (4+2*z) Q (p*r) u (gaussS (ν t)) (SquareShift.slope t*x) ((SquareShift.slope t+1)*x) := by
  rw [GhostLoopFinite.split_radial_polynomial,GhostLoopFinite.moment_four]
  have h1 : (ν t)^(-z-1)=(ν t)^(-z)/(ν t) := by
    rw [Real.rpow_sub (ν_pos t),Real.rpow_one]
  have h2 : (ν t)^(-z-2)=(ν t)^(-z)/(ν t)^2 := by
    rw [Real.rpow_sub (ν_pos t),Real.rpow_two]
  rw [h1,h2]
  unfold coeffA coeffB coeffC gaussS
  generalize prefactor Q x t = P
  generalize pairValue Q p r u (2*ν t)⁻¹ (SquareShift.slope t*x) ((SquareShift.slope t+1)*x) = A
  generalize GhostLoopFinite.radialSquare Q (p*r) u (2*ν t)⁻¹ (SquareShift.slope t*x) ((SquareShift.slope t+1)*x) = B
  generalize GhostLoopFinite.radialFourth (p*r) u (2*ν t)⁻¹ (SquareShift.slope t*x) ((SquareShift.slope t+1)*x) = C
  have hn := (ν_pos t).ne'
  field_simp
  ring

lemma continued_scale (z Q p r u x : ℝ) :
    continuedValue z (x^2*Q) (x*p) (x*r) u 1 = continuedValue z Q p r u x := by
  unfold continuedValue
  simp_rw [continued_moment]
  apply intervalIntegral.integral_congr
  intro t _
  unfold prefactor GhostLoopFinite.momentD
  simp only [one_pow,mul_one]
  rw [show SquareShift.slope t*(x^2*Q)=SquareShift.slope t*x^2*Q by ring]
  ring

lemma actual_force_scaled (G : Gauge) (p : SectorP 0) (i : L 0) (a b : G.ColorIndex)
    (z : ℝ) (hz : -1<z) (x : ℝ) :
    TwoPoint.kinetic (TwoPoint.ratePair G true true (z:ℂ)) a b (x • p) i i =
      -8*(∑ d : G.ColorIndex,angle d a b) *
      Complex.exp ((z:ℂ)*((Real.log Real.pi-2*Real.log (2*Real.pi):ℝ):ℂ)) *
      (continuedValue z p.sq (p i) (p i) 1 x : ℝ) := by
  rw [actual_force_real G (x • p) i a b z hz,Momentum.scaling]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [continued_scale]
end YMReview.NovemberMatching.GhostContinuation
