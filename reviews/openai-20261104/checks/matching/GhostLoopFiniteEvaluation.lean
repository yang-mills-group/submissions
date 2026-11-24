import YM.MS.ScaleForest.Bubbles
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Tactic

/-!
# Exact finite ghost-loop parameter integrals

This file checks the parameter integrals from the explicit Gaussian/Mellin
calculation in the matching notes. It does not silently assume that this
dimensionally continued Gaussian expression equals `TwoPoint.ratePair`.
The latter bridge is proved below at regulator zero; its regulator derivative
requires a further proof through `closeG` and the split radial integral.
-/

noncomputable section
set_option autoImplicit false
open Filter MeasureTheory
open scoped Topology

namespace YMReview.NovemberMatching.GhostLoopFinite

/-- Gaussian moment for dimension D, covariance s, shifts a*p and b*p.
u is the Kronecker delta and v is the product of the external components. -/
def momentD (D Q v u s a b : ℝ) : ℝ :=
  let square := D*(D+2)*s^2 + D*(a^2+b^2)*s*Q + 4*a*b*s*Q + (a*b)^2*Q^2
  let first := 2*(D+2)*(a+b)*s^2 + 2*a*b*(a+b)*s*Q
  s*u*square + s^2*((4*(D+2)*s+2*(a^2+b^2)*Q)*u+8*a*b*v) +
    v*((a+b)*first+a*b*square)

/-- The Gaussian polynomial used in the calculation agrees exactly with the
submitted ordinary four-dimensional Gaussian evaluation. -/
theorem moment_four (Q p r u s a b : ℝ) :
    momentD 4 Q (p*r) u s a b =
      YM.MS.ScaleForest.SquareShift.pairValue Q p r u s a b := by
  unfold momentD YM.MS.ScaleForest.SquareShift.pairValue
    YM.MS.ScaleForest.SquareShift.squareValue YM.MS.ScaleForest.SquareShift.firstValue
  ring

/-- Coefficient of the square of the auxiliary radial coordinate after the
ordinary four-dimensional Gaussian integral. -/
def radialSquare (Q v u s a b : ℝ) :=
  u*(12*s^2+(a^2+b^2)*Q*s) +
    v*(2*(a+b)^2*s+a*b*(8*s+(a^2+b^2)*Q))

/-- Coefficient of the fourth power of the auxiliary radial coordinate. -/
def radialFourth (v u s a b : ℝ) := s*u+a*b*v

/-- The continued moment is recovered from the three split-radial Gaussian
moments, not by guessing a polynomial from its values at integer dimension.
The scalar radial integral identities are checked below. -/
theorem split_radial_polynomial (z Q v u s a b : ℝ) :
    momentD (4+2*z) Q v u s a b = momentD 4 Q v u s a b +
      (2*z*s)*radialSquare Q v u s a b +
      (4*z*(z+1)*s^2)*radialFourth v u s a b := by
  unfold momentD radialSquare radialFourth
  ring

/-- Elementary radial Gaussian integral, with the regulator in its exponent.
The power is real here; agreement along the real axis determines the jet of
the holomorphic continuation once the source-integral bridge is established. -/
theorem gaussian_radial (z nu : ℝ) (hz : -1 < z) (hn : 0 < nu) :
    (∫ r : ℝ in Set.Ioi 0, r^(2*z+1)*Real.exp (-nu*r^(2:ℝ))) =
      nu^(-z-1)/2 * Real.Gamma (z+1) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p:=2) (q:=2*z+1) (b:=nu)
    (by norm_num) (by linarith) hn
  rw [show -(2*z+1+1)/2 = -z-1 by ring, show (2*z+1+1)/2 = z+1 by ring] at h
  convert! h using 1
  ring

/-- The normalized differentiated Gaussian moment of radial degree zero. -/
theorem normalized_radial_zero (z nu : ℝ) (hz : -1 < z) (hn : 0 < nu) :
    (2*nu*(∫ r : ℝ in Set.Ioi 0, r^(2*z+1)*Real.exp (-nu*r^(2:ℝ)))) /
        Real.Gamma (z+1) = nu^(-z) := by
  rw [gaussian_radial z nu hz hn]
  have hg : Real.Gamma (z+1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hp : nu * nu^(-z-1) = nu^(-z) := by
    nth_rw 1 [← Real.rpow_one nu]
    rw [← Real.rpow_add hn]; congr 1; ring
  field_simp
  nlinarith [hp]

/-- The next differentiated radial moment. It is written as the difference
of the two convergent Gaussian integrals obtained by differentiating r² exp.
This check does not itself commute the source's q, t and radial integrals. -/
theorem normalized_radial_two (z nu : ℝ) (hz : -1 < z) (hn : 0 < nu) :
    (2*nu*(∫ r : ℝ in Set.Ioi 0, r^(2*(z+1)+1)*Real.exp (-nu*r^(2:ℝ))) -
      2*(∫ r : ℝ in Set.Ioi 0, r^(2*z+1)*Real.exp (-nu*r^(2:ℝ)))) /
        Real.Gamma (z+1) = z*nu^(-z-1) := by
  rw [gaussian_radial (z+1) nu (by linarith) hn, gaussian_radial z nu hz hn,
    Real.Gamma_add_one (show z+1 ≠ 0 by linarith)]
  have hg : Real.Gamma (z+1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hp : nu*nu^(-(z+1)-1) = nu^(-z-1) := by
    nth_rw 1 [← Real.rpow_one nu]
    rw [← Real.rpow_add hn]; congr 1; ring
  field_simp
  linear_combination (z+1)*hp

/-- Radial degree four, with the same normalization as `closeG`. -/
theorem normalized_radial_four (z nu : ℝ) (hz : -1 < z) (hn : 0 < nu) :
    (2*nu*(∫ r : ℝ in Set.Ioi 0, r^(2*(z+2)+1)*Real.exp (-nu*r^(2:ℝ))) -
      4*(∫ r : ℝ in Set.Ioi 0, r^(2*(z+1)+1)*Real.exp (-nu*r^(2:ℝ)))) /
        Real.Gamma (z+1) = z*(z+1)*nu^(-z-2) := by
  rw [gaussian_radial (z+2) nu (by linarith) hn,
    gaussian_radial (z+1) nu (by linarith) hn,
    Real.Gamma_add_one (show z+2 ≠ 0 by linarith),
    show z+2=(z+1)+1 by ring,
    Real.Gamma_add_one (show z+1 ≠ 0 by linarith)]
  have hg : Real.Gamma (z+1) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hp : nu*nu^(-((z+1)+1)-1) = nu^(-z-2) := by
    nth_rw 1 [← Real.rpow_one nu]
    rw [← Real.rpow_add hn]; congr 1; ring
  have he : -(z+1)-1 = -z-2 := by ring
  rw [he]
  field_simp
  linear_combination 2*(z+1)*(z+2)*hp

open YM YM.MS YM.MS.Arts YM.MS.ScaleForest YM.MS.ScaleForest.TwoPoint
  YM.MS.ScaleForest.SquareShift in
/-- Exact ordinary force of the actual graph, for arbitrary physical momentum
and each diagonal tensor component. This is not a dimensional-jet identity. -/
theorem submitted_force_four (G : Gauge) (hG : G.Simple)
    (a b : G.ColorIndex) (p : SectorP 0) (mu : L 0) :
    kinetic (ratePair G true true 0) a b p mu mu =
      (if a=b then (G.casimir:ℂ) else 0) *
        (-8 * (∫ t : ℝ in (0:ℝ)..1,
          heatValue p.sq (p mu) (p mu) 1 1 t : ℝ)) := by
  have he : kinetic (ratePair G true true 0) a b p mu mu =
      traceAd a b * (-8*(momentTensor p mu mu:ℂ)) := by
    rw [log_rate]
    unfold bothTensor ghostTensor
    simp only [ne_eq, not_true_eq_false, if_false, if_true, ← mul_add]
    simp_rw [intervalIntegral.integral_const_mul]
    rw [MeasureTheory.integral_const_mul,
      show (∫ q, (∫ r in (0:ℝ)..1, twin p mu mu r q + twin p mu mu r (-q))
        ∂YM.WilsonMS.BetaValue.mplane) = _ from (from_integral p mu mu).1]
    unfold traceAd
    ring
  rw [he, traceAd, sums_angles hG]
  have hm := payment_line p mu mu 1
  simp only [one_smul, kk_self] at hm
  rw [hm]

open YM YM.MS YM.MS.Arts YM.MS.ScaleForest in
/-- The selected ghost line has no vector-vector entry, in every test sector. -/
theorem ghost_vector_line_zero (G : Gauge) (m : ℕ) (s t : Bool)
    (i j : L m) (a b : G.ColorIndex) (q : SectorP m) :
    (cursor true).half m (vleg s i a) (vleg t j b) q = 0 := by
  change pickLine true (Garment.Wick.A0 G 0) m _ _ q = 0
  rw [radial_atOne]
  cases s <;> cases t <;>
    simp [pickLine, radial, City.LegsK, Landau.choir, vleg, Landau.parity, Landau.p, City.L0]

open YM YM.MS YM.MS.Arts YM.MS.ScaleForest in
/-- No extra polarization-trace term is present in this ghost closure.
The dimensional dependence still enters through the radial integration. -/
theorem ghost_yeast_zero (G : Gauge) (m : ℕ) (F : Mob G)
    (q : SectorP m) (w : List (Shore G m)) :
    yeast (cursor true).half F q w = 0 := by
  unfold yeast token fleck
  simp only [ghost_vector_line_zero, zero_mul, Finset.sum_const_zero]

open YM YM.MS YM.MS.Arts YM.MS.ScaleForest in
theorem ghost_innerTrace_no_explicit_z (G : Gauge) (m : ℕ) (F : Mob G)
    (q : SectorP m) (w : List (Shore G m)) (z : ℂ) :
    innerTrace (cursor true).half F z q w =
      ∑ i, ∑ j, (cursor true).half m i j q * F m ((i,q)::(j,-q)::w) := by
  rw [innerTrace, ghost_yeast_zero]
  simp

open YM YM.MS YM.MS.Arts YM.MS.ScaleForest in
/-- The actual split-radial integrand has no hidden regulator dependence
before its radial weight is applied. This holds for any fixed inserted Mob. -/
theorem ghost_loopCarpet_regulator (G : Gauge) (m : ℕ) (F : Mob G)
    (w : List (Shore G m)) (z : ℂ) :
    loopCarpet (cursor true).half F z w = loopCarpet (cursor true).half F 0 w := by
  funext p
  unfold loopCarpet
  simp_rw [ghost_innerTrace_no_explicit_z]

open YM YM.MS YM.MS.Arts YM.MS.ScaleForest YM.MS.Train YM.MS.Arc in
/-- Exact source-level form of the continuation in the physical sector.
Evaluating the remaining fixed radial function is still required. -/
theorem ghost_closeG_physical (G : Gauge) (F : Mob G)
    (w : List (Shore G 0)) (z : ℂ) :
    closeG (cursor true).half z 0 F 0 w =
      -feeD z * (∫ r : ℝ, (r:ℂ)^(2*z+1) *
        chop (loopCarpet (cursor true).half F 0 w) (r,1) ∂μhalf) := by
  rw [closeG, ghost_loopCarpet_regulator]
  simp [gage, pruning, tenorK, Pearl.weight, Alps.amount, smul_eq_mul]

/-- Non-logarithmic polynomial in the delta*p² channel. -/
def Pdelta (x : ℝ) := x*(1-x)*(1+2*x*(1-x))
/-- Non-logarithmic polynomial in the p_mu*p_nu channel. -/
def Ppair (x : ℝ) := 2*x*(1-x)*(4-18*x*(1-x))
/-- Logarithmic polynomial in the first channel; twice this in the second. -/
def Wlog (x : ℝ) := x*(1-x)*(3-20*x*(1-x))

theorem pow_log_continuous (n : ℕ) :
    Continuous (fun x : ℝ => x^(n+1)*Real.log x) := by
  have h := (continuous_id.pow n).mul Real.continuous_mul_log
  simpa only [pow_succ, mul_assoc] using! h

/-- The endpoint-safe logarithmic moment at any positive upper bound. -/
theorem integral_pow_log_to (n : ℕ) (b : ℝ) (hb : 0 < b) :
    (∫ x : ℝ in (0:ℝ)..b, x^(n+1)*Real.log x) =
      b^(n+2)*(Real.log b/(n+2:ℕ)-1/((n+2:ℕ):ℝ)^2) := by
  let F (x : ℝ) := x^(n+1)*(x*Real.log x)/(n+2:ℕ) - x^(n+2)/((n+2:ℕ):ℝ)^2
  have hn : ((n+2:ℕ):ℝ) ≠ 0 := by positivity
  have hF : Continuous F := by
    exact (((continuous_id.pow _).mul Real.continuous_mul_log).div_const _).sub
      ((continuous_id.pow _).div_const _)
  have hd (x : ℝ) (hx : x ∈ Set.Ioo (0:ℝ) b) : HasDerivAt F (x^(n+1)*Real.log x) x := by
    have h := (((hasDerivAt_pow (n+1) x).mul (Real.hasDerivAt_mul_log hx.1.ne')).div_const
      ((n+2:ℕ):ℝ)).sub ((hasDerivAt_pow (n+2) x).div_const (((n+2:ℕ):ℝ)^2))
    apply h.congr_deriv
    simp only [Nat.add_sub_cancel, show n+2-1=n+1 by omega, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat]
    rw [show x^(n+1)=x^n*x by rw [pow_succ]]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb.le hF.continuousOn hd
    ((pow_log_continuous n).intervalIntegrable 0 b)]
  simp only [F, zero_pow (by omega : n+1 ≠ 0), zero_pow (by omega : n+2 ≠ 0),
    zero_mul, zero_div, sub_zero, sub_self]
  rw [show b^(n+2)=b^(n+1)*b by rw [show n+2=(n+1)+1 by omega, pow_succ]]
  ring

/-- Endpoint-safe integration: the primitive uses x log x, which extends
continuously across zero. No differentiation of log at zero is assumed. -/
theorem integral_pow_log (n : ℕ) :
    (∫ x : ℝ in (0:ℝ)..1, x^(n+1)*Real.log x) = -1/((n+2:ℕ):ℝ)^2 := by
  let F (x : ℝ) := x^(n+1)*(x*Real.log x)/(n+2:ℕ) - x^(n+2)/((n+2:ℕ):ℝ)^2
  have hn : ((n+2:ℕ):ℝ) ≠ 0 := by positivity
  have hF : Continuous F := by
    exact (((continuous_id.pow _).mul Real.continuous_mul_log).div_const _).sub
      ((continuous_id.pow _).div_const _)
  have hd (x : ℝ) (hx : x ∈ Set.Ioo (0:ℝ) 1) : HasDerivAt F (x^(n+1)*Real.log x) x := by
    have h := (((hasDerivAt_pow (n+1) x).mul (Real.hasDerivAt_mul_log hx.1.ne')).div_const
      ((n+2:ℕ):ℝ)).sub ((hasDerivAt_pow (n+2) x).div_const (((n+2:ℕ):ℝ)^2))
    apply h.congr_deriv
    simp only [Nat.add_sub_cancel, show n+2-1=n+1 by omega, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat]
    rw [show x^(n+1)=x^n*x by rw [pow_succ]]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hF.continuousOn hd
    ((pow_log_continuous n).intervalIntegrable 0 1)]
  simp [F, div_eq_mul_inv]

theorem integral_Pdelta : (∫ x : ℝ in (0:ℝ)..1, Pdelta x) = 7/30 := by
  have he : Pdelta = fun x : ℝ => x + x^2 - 4*x^3 + 2*x^4 := by funext x; unfold Pdelta; ring
  rw [he]
  have h1 : IntervalIntegrable (fun x : ℝ => x) volume 0 1 := continuous_id.intervalIntegrable _ _
  have hp (n : ℕ) : IntervalIntegrable (fun x : ℝ => x^n) volume 0 1 :=
    (continuous_id.pow n).intervalIntegrable _ _
  rw [intervalIntegral.integral_add ((h1.add (hp 2)).sub ((hp 3).const_mul 4)) ((hp 4).const_mul 2),
    intervalIntegral.integral_sub (h1.add (hp 2)) ((hp 3).const_mul 4),
    intervalIntegral.integral_add h1 (hp 2)]
  simp only [intervalIntegral.integral_const_mul]
  norm_num [integral_id, integral_pow]

theorem integral_Ppair : (∫ x : ℝ in (0:ℝ)..1, Ppair x) = 2/15 := by
  have he : Ppair = fun x : ℝ => 8*x - 44*x^2 + 72*x^3 - 36*x^4 := by funext x; unfold Ppair; ring
  rw [he]
  have h1 : IntervalIntegrable (fun x : ℝ => x) volume 0 1 := continuous_id.intervalIntegrable _ _
  have hp (n : ℕ) : IntervalIntegrable (fun x : ℝ => x^n) volume 0 1 :=
    (continuous_id.pow n).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (((h1.const_mul 8).sub ((hp 2).const_mul 44)).add
    ((hp 3).const_mul 72)) ((hp 4).const_mul 36),
    intervalIntegral.integral_add ((h1.const_mul 8).sub ((hp 2).const_mul 44)) ((hp 3).const_mul 72),
    intervalIntegral.integral_sub (h1.const_mul 8) ((hp 2).const_mul 44)]
  simp only [intervalIntegral.integral_const_mul]
  have hx : (∫ x : ℝ in (0:ℝ)..1, 8*x) = 4 := by
    rw [intervalIntegral.integral_const_mul]
    norm_num [integral_id]
  try rw [hx]
  norm_num [integral_id, integral_pow]

theorem integral_Wlog_log :
    (∫ x : ℝ in (0:ℝ)..1, Wlog x*Real.log x) = 19/180 := by
  have he : (fun x : ℝ => Wlog x*Real.log x) = fun x =>
      3*(x*Real.log x)-23*(x^2*Real.log x)+40*(x^3*Real.log x)-20*(x^4*Real.log x) := by
    funext x; unfold Wlog; ring
  rw [he]
  have hp (n : ℕ) : IntervalIntegrable (fun x : ℝ => x^(n+1)*Real.log x) volume 0 1 :=
    (pow_log_continuous n).intervalIntegrable (0:ℝ) 1
  have h0 : IntervalIntegrable (fun x : ℝ => x*Real.log x) volume 0 1 := by simpa using hp 0
  rw [intervalIntegral.integral_sub (((h0.const_mul 3).sub ((hp 1).const_mul 23)).add
      ((hp 2).const_mul 40)) ((hp 3).const_mul 20),
    intervalIntegral.integral_add ((h0.const_mul 3).sub ((hp 1).const_mul 23)) ((hp 2).const_mul 40),
    intervalIntegral.integral_sub (h0.const_mul 3) ((hp 1).const_mul 23)]
  simp only [intervalIntegral.integral_const_mul]
  have h := integral_pow_log 0
  norm_num at h
  rw [h, integral_pow_log 1, integral_pow_log 2, integral_pow_log 3]
  norm_num

/-- Exact finite coefficient after reflection of the half-interval and
combination of the ordinary Mellin part with the first regulator jet. -/
theorem finite_delta_parameter :
    (∫ x : ℝ in (0:ℝ)..1, Pdelta x)/2 +
      (∫ x : ℝ in (0:ℝ)..1, Wlog x*Real.log x) = 2/9 := by
  rw [integral_Pdelta, integral_Wlog_log]
  norm_num

theorem finite_pair_parameter :
    (∫ x : ℝ in (0:ℝ)..1, Ppair x)/2 +
      2*(∫ x : ℝ in (0:ℝ)..1, Wlog x*Real.log x) = 5/18 := by
  rw [integral_Ppair, integral_Wlog_log]
  norm_num

theorem Wlog_reflect (x : ℝ) : Wlog (1-x) = Wlog x := by unfold Wlog; ring

theorem continuous_weighted_log : Continuous (fun x : ℝ => Wlog x*Real.log x) := by
  have h : Continuous (fun x : ℝ => (x*Real.log x)*((1-x)*(3-20*x*(1-x)))) :=
    Real.continuous_mul_log.mul (by fun_prop)
  convert h using 1
  funext x; unfold Wlog; ring

theorem continuous_reflected_log : Continuous (fun x : ℝ => Wlog x*Real.log (1-x)) := by
  have h := continuous_weighted_log.comp (show Continuous (fun x : ℝ => 1-x) by fun_prop)
  simpa only [Function.comp_def, Wlog_reflect] using! h

theorem integral_reflected_log :
    (∫ x : ℝ in (0:ℝ)..1, Wlog x*Real.log (1-x)) = 19/180 := by
  have h := intervalIntegral.integral_comp_sub_left (fun x : ℝ => Wlog x*Real.log x)
    (a:=0) (b:=1) 1
  simp only [Wlog_reflect, sub_self, sub_zero] at h
  rw [h, integral_Wlog_log]

theorem half_integral (f : ℝ → ℝ) (hf : Continuous f) (hs : ∀ x, f (1-x)=f x) :
    (∫ x : ℝ in (0:ℝ)..(1/2:ℝ), f x) = (∫ x : ℝ in (0:ℝ)..1, f x)/2 := by
  have he := intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (μ:=volume) (0:ℝ) (1/2:ℝ)) (hf.intervalIntegrable (μ:=volume) (1/2:ℝ) 1)
  have hr := intervalIntegral.integral_comp_sub_left f (a:=0) (b:=(1/2:ℝ)) 1
  simp only [hs, sub_zero] at hr
  norm_num at hr
  linarith

/-- The half-interval logarithm needed for the actual dimensional jet. -/
theorem integral_Wlog_half_log :
    (∫ x : ℝ in (0:ℝ)..(1/2:ℝ), Wlog x*Real.log x) =
      1/1440+Real.log 2/12 := by
  have he : (fun x : ℝ => Wlog x*Real.log x) = fun x =>
      3*(x*Real.log x)-23*(x^2*Real.log x)+40*(x^3*Real.log x)-20*(x^4*Real.log x) := by
    funext x; unfold Wlog; ring
  rw [he]
  have hp (n : ℕ) : IntervalIntegrable (fun x : ℝ => x^(n+1)*Real.log x) volume 0 (1/2) :=
    (pow_log_continuous n).intervalIntegrable (0:ℝ) (1/2)
  have h0 : IntervalIntegrable (fun x : ℝ => x*Real.log x) volume 0 (1/2) := by simpa using hp 0
  rw [intervalIntegral.integral_sub (((h0.const_mul 3).sub ((hp 1).const_mul 23)).add
      ((hp 2).const_mul 40)) ((hp 3).const_mul 20),
    intervalIntegral.integral_add ((h0.const_mul 3).sub ((hp 1).const_mul 23)) ((hp 2).const_mul 40),
    intervalIntegral.integral_sub (h0.const_mul 3) ((hp 1).const_mul 23)]
  simp only [intervalIntegral.integral_const_mul]
  have h := integral_pow_log_to 0 (1/2) (by norm_num)
  simp only [Nat.reduceAdd, pow_one] at h
  rw [h, integral_pow_log_to 1 _ (by norm_num),
    integral_pow_log_to 2 _ (by norm_num), integral_pow_log_to 3 _ (by norm_num)]
  rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0), Real.log_one]
  norm_num
  ring

theorem integral_Wlog_half_log_reflected :
    (∫ x : ℝ in (0:ℝ)..(1/2:ℝ), Wlog x*Real.log (1-x)) =
      151/1440-Real.log 2/12 := by
  have hc : Continuous (fun x : ℝ => Wlog x*Real.log x) := continuous_weighted_log
  have h := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ:=volume) (0:ℝ) (1/2))
    (hc.intervalIntegrable (μ:=volume) (1/2) 1)
  have hr := intervalIntegral.integral_comp_sub_left (fun x : ℝ => Wlog x*Real.log x)
    (a:=0) (b:=(1/2:ℝ)) 1
  simp only [Wlog_reflect, sub_zero] at hr
  norm_num at hr
  rw [hr]
  rw [integral_Wlog_log, integral_Wlog_half_log] at h
  linarith

def Jdelta (x : ℝ) := x*(1-x)*(1-9*x*(1-x))

theorem integral_Jdelta_half : (∫ x : ℝ in (0:ℝ)..(1/2:ℝ), Jdelta x) = -1/15 := by
  have he : Jdelta = fun x : ℝ => x-10*x^2+18*x^3-9*x^4 := by funext x; unfold Jdelta; ring
  rw [he]
  have h1 : IntervalIntegrable (fun x : ℝ => x) volume 0 (1/2) := continuous_id.intervalIntegrable _ _
  have hp (n : ℕ) : IntervalIntegrable (fun x : ℝ => x^n) volume 0 (1/2) :=
    (continuous_id.pow n).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub ((h1.sub ((hp 2).const_mul 10)).add ((hp 3).const_mul 18))
      ((hp 4).const_mul 9),
    intervalIntegral.integral_add (h1.sub ((hp 2).const_mul 10)) ((hp 3).const_mul 18),
    intervalIntegral.integral_sub h1 ((hp 2).const_mul 10)]
  simp only [intervalIntegral.integral_const_mul]
  norm_num [integral_id, integral_pow]

theorem integral_Wlog_half : (∫ x : ℝ in (0:ℝ)..(1/2:ℝ), Wlog x) = -1/12 := by
  have he : Wlog = fun x : ℝ => 3*x-23*x^2+40*x^3-20*x^4 := by funext x; unfold Wlog; ring
  rw [he]
  have h1 : IntervalIntegrable (fun x : ℝ => x) volume 0 (1/2) := continuous_id.intervalIntegrable _ _
  have hp (n : ℕ) : IntervalIntegrable (fun x : ℝ => x^n) volume 0 (1/2) :=
    (continuous_id.pow n).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub (((h1.const_mul 3).sub ((hp 2).const_mul 23)).add ((hp 3).const_mul 40))
      ((hp 4).const_mul 20),
    intervalIntegral.integral_add ((h1.const_mul 3).sub ((hp 2).const_mul 23)) ((hp 3).const_mul 40),
    intervalIntegral.integral_sub (h1.const_mul 3) ((hp 2).const_mul 23)]
  simp only [intervalIntegral.integral_const_mul]
  have hx : (∫ x : ℝ in (0:ℝ)..(1/2:ℝ), 3*x) = 3/8 := by
    rw [intervalIntegral.integral_const_mul]; norm_num [integral_id]
  rw [hx]
  norm_num [integral_pow]

/-- Exact finite local jet in the explicit split-radial Gaussian formula.
Its equality to `ruby (highTensor 4 ratePair) 1` is a distinct source bridge. -/
theorem regulator_jet_parameter :
    (∫ x : ℝ in (0:ℝ)..(1/2:ℝ), Jdelta x) +
    (∫ x : ℝ in (0:ℝ)..(1/2:ℝ), Wlog x*Real.log (1-x)) -
    Real.log (4*Real.pi)*(∫ x : ℝ in (0:ℝ)..(1/2:ℝ), Wlog x) =
      11/288+Real.log (2*Real.pi)/12 := by
  rw [integral_Jdelta_half, integral_Wlog_half_log_reflected, integral_Wlog_half,
    Real.log_mul (by norm_num : (4:ℝ) ≠ 0) Real.pi_pos.ne',
    Real.log_mul (by norm_num : (2:ℝ) ≠ 0) Real.pi_pos.ne',
    show Real.log (4:ℝ) = 2*Real.log 2 by rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]; norm_num]
  ring

def deltaIntegrand (x : ℝ) := Pdelta x + Wlog x*(Real.log x+Real.log (1-x))
def pairIntegrand (x : ℝ) := Ppair x + 2*Wlog x*(Real.log x+Real.log (1-x))

def coeffA (D x u : ℝ) := u*(D+2)*(D+4)*((1-x)/2)^3
def coeffB (D x u v : ℝ) := ((1-x)/2)^2 *
  (u*((D+2)*(x^2+(1-x)^2)-4*x*(1-x)) +
    v*(2*(D+2)*(1-2*x)^2-(D*(D+2)+8)*x*(1-x)))
def coeffC (D x u v : ℝ) := ((1-x)/2)*
  (u*x^2*(1-x)^2 + v*(-2*x*(1-x)*(1-2*x)^2-
    x*(1-x)*(D*(x^2+(1-x)^2)-4*x*(1-x))))
def coeffD (x v : ℝ) := -v*x^3*(1-x)^3
def jetA (x u : ℝ) := 28*u*((1-x)/2)^3
def jetB (x u v : ℝ) := ((1-x)/2)^2 *
  (2*u*(x^2+(1-x)^2) + v*(4*(1-2*x)^2-20*x*(1-x)))

theorem moment_expansion (D x u v t : ℝ) :
    momentD D 1 v u ((1-x)/2) (-x*t) ((1-x)*t) =
      coeffA D x u + coeffB D x u v*t^2 + coeffC D x u v*t^4 + coeffD x v*t^6 := by
  unfold momentD coeffA coeffB coeffC coeffD
  ring

theorem local_taylor_derivative (x u v : ℝ) :
    HasDerivAt (fun z : ℝ => coeffB (4+2*z) x u v-x*coeffA (4+2*z) x u)
      (jetB x u v-x*jetA x u) 0 := by
  let k := 4*((1-x)/2)^2*(-v*x*(1-x)-x*u*((1-x)/2))
  have he : (fun z : ℝ => coeffB (4+2*z) x u v-x*coeffA (4+2*z) x u) =
      fun z => (coeffB 4 x u v-x*coeffA 4 x u) +
        z*(jetB x u v-x*jetA x u)+z^2*k := by
    funext z; unfold coeffA coeffB jetA jetB k; ring
  rw [he]
  convert! (((hasDerivAt_id' (0:ℝ)).mul_const (jetB x u v-x*jetA x u)).const_add
    (coeffB 4 x u v-x*coeffA 4 x u)).add ((hasDerivAt_pow 2 (0:ℝ)).mul_const k) using 1
  norm_num

/-- Algebraic reduction of the combined finite Mellin value and dimensional
jet. The common log(4*pi) and Euler-constant terms have cancelled at mu_bar=1.
The split-radial integral bridge establishing these as the source's terms is
not assumed or proved by this algebraic identity. -/
theorem finite_integrand_reduction (x u v : ℝ) (hx : x ≠ 0) (hr : 1-x ≠ 0) :
    2*x/(1-x) * (x*coeffA 4 x u + jetB x u v-x*jetA x u-
      coeffC 4 x u v/x-coeffD x v/x^2 +
      (coeffB 4 x u v-x*coeffA 4 x u)*(Real.log x+Real.log (1-x))) =
      u*deltaIntegrand x+v*pairIntegrand x := by
  unfold coeffA coeffB coeffC coeffD jetA jetB deltaIntegrand pairIntegrand Pdelta Ppair Wlog
  field_simp
  ring

theorem finite_delta_half : (∫ x : ℝ in (0:ℝ)..(1/2:ℝ), deltaIntegrand x) = 2/9 := by
  have hp : Continuous Pdelta := by unfold Pdelta; fun_prop
  have hf : Continuous deltaIntegrand := by
    convert! hp.add (continuous_weighted_log.add continuous_reflected_log) using 1
    funext x; simp only [deltaIntegrand, Pi.add_apply]; ring
  have hs (x : ℝ) : deltaIntegrand (1-x)=deltaIntegrand x := by
    have he : Pdelta (1-x)=Pdelta x := by unfold Pdelta; ring
    simp only [deltaIntegrand, he, Wlog_reflect, sub_sub_cancel]; ring
  rw [half_integral deltaIntegrand hf hs]
  simp only [deltaIntegrand, mul_add]
  have hi : IntervalIntegrable (fun x : ℝ => Wlog x*Real.log x+Wlog x*Real.log (1-x)) volume 0 1 :=
    (continuous_weighted_log.intervalIntegrable _ _).add (continuous_reflected_log.intervalIntegrable _ _)
  rw [intervalIntegral.integral_add (hp.intervalIntegrable _ _)
      hi,
    intervalIntegral.integral_add (continuous_weighted_log.intervalIntegrable _ _)
      (continuous_reflected_log.intervalIntegrable _ _),
    integral_Pdelta, integral_Wlog_log, integral_reflected_log]
  norm_num

theorem finite_pair_half : (∫ x : ℝ in (0:ℝ)..(1/2:ℝ), pairIntegrand x) = 5/18 := by
  have hp : Continuous Ppair := by unfold Ppair; fun_prop
  have hf : Continuous pairIntegrand := by
    convert! hp.add ((continuous_weighted_log.const_mul 2).add (continuous_reflected_log.const_mul 2)) using 1
    funext x; simp only [pairIntegrand, Pi.add_apply]; ring
  have hs (x : ℝ) : pairIntegrand (1-x)=pairIntegrand x := by
    have he : Ppair (1-x)=Ppair x := by unfold Ppair; ring
    simp only [pairIntegrand, he, Wlog_reflect, sub_sub_cancel]; ring
  rw [half_integral pairIntegrand hf hs]
  simp only [pairIntegrand, mul_add, mul_assoc]
  have hi : IntervalIntegrable (fun x : ℝ => 2*(Wlog x*Real.log x)+2*(Wlog x*Real.log (1-x))) volume 0 1 :=
    ((continuous_weighted_log.const_mul 2).intervalIntegrable _ _).add
      ((continuous_reflected_log.const_mul 2).intervalIntegrable _ _)
  rw [intervalIntegral.integral_add (hp.intervalIntegrable _ _)
      hi,
    intervalIntegral.integral_add ((continuous_weighted_log.const_mul 2).intervalIntegrable _ _)
      ((continuous_reflected_log.const_mul 2).intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const_mul]
  rw [integral_Ppair, integral_Wlog_log, integral_reflected_log]
  norm_num

open YM YM.MS YM.MS.Arts YM.MS.ScaleForest YM.MS.Pearl in
/-- Explicit remaining source-specific jet comparison. The elementary
split-radial calculation in the notes predicts this value; no theorem proving
this predicate is claimed in this file. It is stronger than evaluation at z=0.
The infrared Mellin limit also still needs a proof to finish the full test. -/
def SubmittedRegulatorJetTest (G : Gauge) : Prop :=
  G.Simple → ∀ (a b : G.ColorIndex) (p : SectorP 0) (i j : L 0),
    ruby (highTensor 4 (TwoPoint.ratePair G true true)) 1 0 (TwoPoint.word i j a b p) =
      (if a=b then (G.casimir:ℂ) else 0) *
        ((if i=j then (p.sq:ℂ) else 0)+2*(p i:ℂ)*(p j:ℂ)) /
        (16*(Real.pi:ℂ)^2) * (11/288+(Real.log (2*Real.pi):ℂ)/12)

end YMReview.NovemberMatching.GhostLoopFinite

#print axioms YMReview.NovemberMatching.GhostLoopFinite.moment_four
#print axioms YMReview.NovemberMatching.GhostLoopFinite.integral_pow_log
#print axioms YMReview.NovemberMatching.GhostLoopFinite.integral_Pdelta
#print axioms YMReview.NovemberMatching.GhostLoopFinite.integral_Ppair
#print axioms YMReview.NovemberMatching.GhostLoopFinite.integral_Wlog_log
#print axioms YMReview.NovemberMatching.GhostLoopFinite.submitted_force_four
#print axioms YMReview.NovemberMatching.GhostLoopFinite.finite_delta_parameter
#print axioms YMReview.NovemberMatching.GhostLoopFinite.finite_pair_parameter
#print axioms YMReview.NovemberMatching.GhostLoopFinite.finite_delta_half
#print axioms YMReview.NovemberMatching.GhostLoopFinite.finite_pair_half
#print axioms YMReview.NovemberMatching.GhostLoopFinite.moment_expansion
#print axioms YMReview.NovemberMatching.GhostLoopFinite.local_taylor_derivative
#print axioms YMReview.NovemberMatching.GhostLoopFinite.finite_integrand_reduction
#print axioms YMReview.NovemberMatching.GhostLoopFinite.ghost_yeast_zero
#print axioms YMReview.NovemberMatching.GhostLoopFinite.ghost_innerTrace_no_explicit_z

#print axioms YMReview.NovemberMatching.GhostLoopFinite.split_radial_polynomial
#print axioms YMReview.NovemberMatching.GhostLoopFinite.gaussian_radial
#print axioms YMReview.NovemberMatching.GhostLoopFinite.normalized_radial_zero
#print axioms YMReview.NovemberMatching.GhostLoopFinite.normalized_radial_two
#print axioms YMReview.NovemberMatching.GhostLoopFinite.normalized_radial_four
#print axioms YMReview.NovemberMatching.GhostLoopFinite.regulator_jet_parameter

#print axioms YMReview.NovemberMatching.GhostLoopFinite.ghost_loopCarpet_regulator
#print axioms YMReview.NovemberMatching.GhostLoopFinite.ghost_closeG_physical
