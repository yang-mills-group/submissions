import YM.MS.ScaleForest.Bubbles
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Independent ghost-loop tensor benchmark

Conventions: D=4-2ε, L=log(mu_bar²/p²), Euclidean p²>0. Strip off g² and
the color factor, and use the sign of the negative bare tensor integral
  - integral k_mu (k+p)_nu / (k² (k+p)²).
Feynman parametrization gives, with this sign convention, the meromorphic tensor
  Q(ε,L)/ε * (δ_mu_nu p²/(2(1-ε)) + p_mu p_nu)/(16π²).
Here Q is the explicit Gamma expression below. This file proves its Laurent
coefficients and compares the pole tensor to the submitted *actual* bubble
counterterm. It also identifies the actual finite reading, checks its scale
dependence and reduces the finite comparison to one reference scale. The
integrated heat line has the expected pointwise IR limit. The dimensional
integral reduction and equality of the submitted finite bubble with the
conventional answer remain open.

The Gamma expression is the recurrence-reduced form of
  exp((L+γ)ε) Γ(1+ε) Γ(2-ε)^2 / Γ(4-2ε).
No submitted graph evaluator or subtraction data defines our reference.

External numerical cross-check: Andreas Rodigast, "One-Loop Divergences of
the Yang-Mills Theory Coupled to Gravitation", revised 20 August 2008,
§4.3.1, eq. (4.30), printed p.27 (PDF p.37):
https://qft.physik.hu-berlin.de/wp-content/uploads/2012/10/DA-andreas.pdf
That formula uses D=4-ε_R, so ε_R=2ε, and Minkowski conventions. Its tensor
coefficients 1/12 and 1/6 and finite constants 8/3 and 5/3 are comparison
values, not a substitute for the convention and graph bridges.
-/

noncomputable section
set_option autoImplicit false
open Filter
open scoped Topology

namespace YMReview.NovemberMatching.GhostLoop

local notation "γ" => (Real.eulerMascheroniConstant : ℂ)

/-- Scalar numerator after cancelling the simple Gamma pole. -/
def numerator (L e : ℂ) : ℂ :=
  Complex.exp ((L + γ) * e) * Complex.Gamma (1 + e) *
    Complex.Gamma (1 - e)^2 / Complex.Gamma (1 - 2*e) *
    ((1-e)/(2*(3-2*e)*(1-2*e)))

/-- Recurrence reduction of the Euler beta-integral expression. The excluded
points are away from the punctured neighborhood used for the Laurent limit. -/
theorem numerator_gamma_ratio (L e : ℂ) (h1 : 1-e ≠ 0)
    (h2 : 1-2*e ≠ 0) (h3 : 2-2*e ≠ 0) (h4 : 3-2*e ≠ 0) :
    numerator L e = Complex.exp ((L+γ)*e) * Complex.Gamma (1+e) *
      Complex.Gamma (2-e)^2 / Complex.Gamma (4-2*e) := by
  have g2 : Complex.Gamma (2-e) = (1-e)*Complex.Gamma (1-e) := by
    rw [show 2-e=(1-e)+1 by ring, Complex.Gamma_add_one _ h1]
  have gd2 : Complex.Gamma (2-2*e) = (1-2*e)*Complex.Gamma (1-2*e) := by
    rw [show 2-2*e=(1-2*e)+1 by ring, Complex.Gamma_add_one _ h2]
  have gd3 : Complex.Gamma (3-2*e) = (2-2*e)*(1-2*e)*Complex.Gamma (1-2*e) := by
    rw [show 3-2*e=(2-2*e)+1 by ring, Complex.Gamma_add_one _ h3, gd2]
    ring
  have gd4 : Complex.Gamma (4-2*e) = (3-2*e)*(2-2*e)*(1-2*e)*Complex.Gamma (1-2*e) := by
    rw [show 4-2*e=(3-2*e)+1 by ring, Complex.Gamma_add_one _ h4, gd3]
    ring
  rw [g2, gd4]
  unfold numerator
  field_simp [h1, h2, h3, h4]

theorem numerator_zero (L : ℂ) : numerator L 0 = 1/6 := by
  norm_num [numerator, Complex.Gamma_one]

theorem numerator_derivative (L : ℂ) :
    HasDerivAt (numerator L) ((L + 5/3)/6) 0 := by
  have hp : HasDerivAt (fun e : ℂ => Complex.Gamma (1+e)) (-γ) 0 := by
    have h : HasDerivAt Complex.Gamma (-γ) (1+(0:ℂ)) := by simpa using Complex.hasDerivAt_Gamma_one
    simpa [Function.comp_def] using! h.comp 0 (h:=fun e:ℂ => 1+e) ((hasDerivAt_id' (0:ℂ)).const_add 1)
  have hm : HasDerivAt (fun e : ℂ => Complex.Gamma (1-e)) γ 0 := by
    have h : HasDerivAt Complex.Gamma (-γ) (1-(0:ℂ)) := by simpa using Complex.hasDerivAt_Gamma_one
    simpa [Function.comp_def] using! h.comp 0 (h:=fun e:ℂ => 1-e) ((hasDerivAt_id' (0:ℂ)).const_sub 1)
  have hd : HasDerivAt (fun e : ℂ => Complex.Gamma (1-2*e)) (2*γ) 0 := by
    have h : HasDerivAt Complex.Gamma (-γ) (1-2*(0:ℂ)) := by simpa using Complex.hasDerivAt_Gamma_one
    convert! h.comp 0 (h:=fun e:ℂ => 1-2*e)
      (((hasDerivAt_id' (0:ℂ)).const_mul 2).const_sub 1) using 1
    norm_num
    ring
  have he := ((hasDerivAt_id' (0:ℂ)).const_mul (L+γ)).cexp
  have hr := (((hasDerivAt_id' (0:ℂ)).const_sub 1).div
    ((((hasDerivAt_id' (0:ℂ)).const_mul 2).const_sub 3).const_mul 2 |>.mul
      (((hasDerivAt_id' (0:ℂ)).const_mul 2).const_sub 1)) (by norm_num))
  have h := ((((he.mul hp).mul (hm.pow 2)).div hd (by simp [Complex.Gamma_one])).mul hr)
  apply h.congr_deriv
  norm_num [Complex.Gamma_one]
  ring

/-- The two tensor slots are u=δ_mu_nu p² and v=p_mu p_nu. -/
def tensorNumerator (L u v e : ℂ) : ℂ :=
  numerator L e * (u/(2*(1-e)) + v) / (16 * (Real.pi : ℂ)^2)

def residue (u v : ℂ) : ℂ :=
  (u/12 + v/6)/(16 * (Real.pi : ℂ)^2)

def finitePart (L u v : ℂ) : ℂ :=
  (u/12 * (L+8/3) + v/6 * (L+5/3))/(16 * (Real.pi : ℂ)^2)

theorem finitePart_shift (L d u v : ℂ) :
    finitePart (L+d) u v = finitePart L u v + d * residue u v := by
  unfold finitePart residue
  ring

theorem tensor_zero (L u v : ℂ) : tensorNumerator L u v 0 = residue u v := by
  rw [tensorNumerator, numerator_zero]
  simp only [sub_zero, mul_one]
  unfold residue
  ring

theorem tensor_derivative (L u v : ℂ) :
    HasDerivAt (tensorNumerator L u v) (finitePart L u v) 0 := by
  have ht := (((hasDerivAt_const (0:ℂ) u).div
    (((hasDerivAt_id' (0:ℂ)).const_sub 1).const_mul 2) (by norm_num)).add_const v)
  have h := ((numerator_derivative L).mul ht).div_const (16*(Real.pi:ℂ)^2)
  apply h.congr_deriv
  norm_num [numerator_zero, finitePart]
  ring

/-- Actual punctured-regulator finite-part limit of the independent formula. -/
theorem finite_limit (L u v : ℂ) :
    Tendsto (fun e : ℂ => tensorNumerator L u v e / e - residue u v / e)
      (𝓝[≠] 0) (𝓝 (finitePart L u v)) := by
  have h := (tensor_derivative L u v).tendsto_slope
  simpa only [slope_fun_def_field, sub_zero, tensor_zero, sub_div] using h

/-- Negative control: freezing the evanescent tensor denominator 1/(1-ε)
would give the same 5/3 constant in both tensor channels. Its finite error is
nonzero in the δ_mu_nu p² channel. -/
theorem premature_tensor_error (L u v : ℂ) :
    finitePart L u v - residue u v * (L+5/3) =
      u/(192*(Real.pi:ℂ)^2) := by
  unfold finitePart residue
  ring

theorem premature_tensor_error_nonzero :
    finitePart 0 1 0 ≠ residue 1 0 * (5/3) := by
  intro h
  have hx := premature_tensor_error 0 1 0
  rw [zero_add, h, sub_self] at hx
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact (one_div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hp))) hx.symm

/-- This elementary parameter integral supplies the residue weight. -/
theorem parameter_weight : (∫ x : ℝ in (0:ℝ)..1, x*(1-x)) = 1/6 := by
  have hf : (fun x : ℝ => x*(1-x)) = fun x => x - x^2 := by funext x; ring
  rw [hf]
  have h1 : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  have h2 : IntervalIntegrable (fun x : ℝ => x^2) MeasureTheory.volume 0 1 :=
    (continuous_id.pow 2).intervalIntegrable 0 1
  rw [intervalIntegral.integral_sub h1 h2]
  norm_num [integral_id, integral_pow]

open YM YM.MS YM.MS.Arts YM.MS.ScaleForest in
/-- Comparison with the pole of the two actual cubic vertices and ghost lines.
The RHS is our independently stated parameter-residue tensor. -/
theorem submitted_pole (G : Gauge) (hG : G.Simple) (m : ℕ)
    (a b : G.ColorIndex) (p : SectorP m) (i j : L m) :
    TwoPoint.kinetic (TwoPoint.poleTensor G true true) a b p i j =
      (if a=b then (G.casimir:ℂ) else 0) *
        residue (if i=j then (p.sq:ℂ) else 0) ((p i:ℂ)*(p j:ℂ)) := by
  rw [TwoPoint.ghost_bill]
  unfold TwoPoint.ghost_residue TwoPoint.traceAd
  rw [sums_angles hG]
  unfold TwoPoint.counterScale SquareShift.logArea residue
  push_cast
  ring

open YM YM.MS YM.MS.Arts YM.MS.ScaleForest YM.MS.Train in
/-- The actual renormalized graph reading equals the source's explicit finite
formula. This is a bridge to the graph, not yet its integral evaluation. -/
theorem submitted_finite_reading (G : Gauge) (y s : ℝ) :
    Outlook.four 4 (TwoPoint.bubble G true true).instructions.renorm (y,s) =
      oneLoopFinite 4 (TwoPoint.ratePair G true true) s y 0 := by
  have h := (twoVertex_laurent (interaction G 1) (interaction G 1)
    (cursor true) (cursor true)).2.2 s y
  exact congrArg (fun F : Mob G => F 0) (YM.MS.Pearl.chosen (n:=0) h).symm

open YM YM.MS YM.MS.Arts YM.MS.ScaleForest in
/-- The mass-scale change is determined by the actual pole, at every retained
infrared length. No interchange of infrared and regulator limits is used. -/
theorem submitted_scale_difference (G : Gauge) (y y' s : ℝ)
    (a b : G.ColorIndex) (p : SectorP 0) (i j : L 0) :
    Outlook.four 4 (TwoPoint.bubble G true true).instructions.renorm (y',s)
        (TwoPoint.word i j a b p) -
      Outlook.four 4 (TwoPoint.bubble G true true).instructions.renorm (y,s)
        (TwoPoint.word i j a b p) =
      (2*(y'-y):ℂ) * TwoPoint.kinetic (TwoPoint.poleTensor G true true) a b p i j := by
  rw [submitted_finite_reading, submitted_finite_reading]
  unfold oneLoopFinite TwoPoint.poleTensor TwoPoint.kinetic
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  push_cast
  ring

open YM YM.MS YM.MS.Arts YM.MS.ScaleForest in
/-- The independently specified logarithmic coefficient agrees with the
submitted graph, even before the infrared-length limit. -/
theorem submitted_scale_coefficient (G : Gauge) (hG : G.Simple) (y y' s : ℝ)
    (a b : G.ColorIndex) (p : SectorP 0) (i j : L 0) :
    Outlook.four 4 (TwoPoint.bubble G true true).instructions.renorm (y',s)
        (TwoPoint.word i j a b p) -
      Outlook.four 4 (TwoPoint.bubble G true true).instructions.renorm (y,s)
        (TwoPoint.word i j a b p) =
      (2*(y'-y):ℂ) * (if a=b then (G.casimir:ℂ) else 0) *
        residue (if i=j then (p.sq:ℂ) else 0) ((p i:ℂ)*(p j:ℂ)) := by
  rw [submitted_scale_difference, submitted_pole G hG]
  ring

open YM YM.MS YM.MS.Arts YM.MS.ScaleForest in
/-- Proposed next comparison, NOT proved here. First remove the dimensional
regulator via the submission's `four`, then take the infrared length to infinity
at nonzero external momentum. The common MSbar energy scale is mu_bar.
This concerns a gauge-dependent graph contribution, not a complete physical
gauge-invariant correlation or a new final matching acceptance theorem. -/
def SubmittedFinitePartTest (G : Gauge) : Prop :=
  G.Simple → ∀ mu_bar : ℝ, 0 < mu_bar → ∀ (a b : G.ColorIndex) (p : SectorP 0)
    (i j : L 0), 0 < p.sq →
    Tendsto (fun s : ℝ => Outlook.four 4 (TwoPoint.bubble G true true).instructions.renorm
      (Real.log mu_bar + (Real.eulerMascheroniConstant - Real.log (4*Real.pi))/2, s)
      (TwoPoint.word i j a b p)) atTop
      (𝓝 ((if a=b then (G.casimir:ℂ) else 0) *
        finitePart (Real.log (mu_bar^2/p.sq) : ℂ)
          (if i=j then (p.sq:ℂ) else 0) ((p i:ℂ)*(p j:ℂ))))

open YM YM.MS YM.MS.Arts YM.MS.ScaleForest in
/-- Remaining reference-scale test (mu_bar=1 in the chosen momentum units).
It still quantifies over all nonzero momenta and both tensor channels. -/
def ReferenceScaleTest (G : Gauge) : Prop :=
  G.Simple → ∀ (a b : G.ColorIndex) (p : SectorP 0) (i j : L 0), 0 < p.sq →
    Tendsto (fun s : ℝ => Outlook.four 4 (TwoPoint.bubble G true true).instructions.renorm
      ((Real.eulerMascheroniConstant - Real.log (4*Real.pi))/2, s)
      (TwoPoint.word i j a b p)) atTop
      (𝓝 ((if a=b then (G.casimir:ℂ) else 0) *
        finitePart (Real.log (1/p.sq) : ℂ)
          (if i=j then (p.sq:ℂ) else 0) ((p i:ℂ)*(p j:ℂ))))

open YM YM.MS YM.MS.Arts YM.MS.ScaleForest in
/-- A proved reduction, not a proof of either test: the one reference-scale
comparison is equivalent to the proposed comparison at every positive scale. -/
theorem finite_test_iff_reference (G : Gauge) :
    SubmittedFinitePartTest G ↔ ReferenceScaleTest G := by
  constructor
  · intro h hG a b p i j hp
    simpa using h hG 1 (by norm_num) a b p i j hp
  intro h hG mu hmu a b p i j hp
  let y0 := (Real.eulerMascheroniConstant - Real.log (4*Real.pi))/2
  let c : ℂ := if a=b then (G.casimir:ℂ) else 0
  let u : ℂ := if i=j then (p.sq:ℂ) else 0
  let v : ℂ := (p i:ℂ)*(p j:ℂ)
  have hl : (Real.log (mu^2/p.sq):ℂ) = (Real.log (1/p.sq):ℂ) + 2*(Real.log mu:ℂ) := by
    rw [Real.log_div (pow_ne_zero 2 hmu.ne') hp.ne', Real.log_pow,
      Real.log_div one_ne_zero hp.ne', Real.log_one]
    push_cast
    ring
  have hc := (h hG a b p i j hp).add_const ((2*(Real.log mu:ℂ))*c*residue u v)
  have hv : c * finitePart (Real.log (1/p.sq):ℂ) u v +
      (2*(Real.log mu:ℂ))*c*residue u v =
      c * finitePart (Real.log (mu^2/p.sq):ℂ) u v := by
    rw [hl, finitePart_shift]
    ring
  change Tendsto _ _ (𝓝 (c * finitePart (Real.log (mu^2/p.sq):ℂ) u v))
  rw [← hv]
  apply hc.congr'
  filter_upwards [] with s
  have he := submitted_scale_coefficient G hG y0 (Real.log mu + y0) s a b p i j
  simp only [Complex.ofReal_add, add_sub_cancel_right] at he
  linear_combination -he

/-- Scalar dressing of the actual integrated heat line, with t=rho² q². -/
def heatDressing (t : ℝ) : ℝ := 1-(1+t)*Real.exp (-t)

theorem heatDressing_bounds (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ heatDressing t ∧ heatDressing t ≤ 1 := by
  have h : (1+t)*Real.exp (-t) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos t)]
    linarith [Real.add_one_le_exp t]
  have hpos : 0 ≤ (1+t)*Real.exp (-t) := mul_nonneg (by linarith) (Real.exp_pos _).le
  constructor <;> unfold heatDressing <;> linarith

theorem heatDressing_limit : Tendsto heatDressing atTop (𝓝 1) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.add
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
  have he : Tendsto (fun t : ℝ => (1+t)*Real.exp (-t)) atTop (𝓝 0) := by
    simpa only [add_mul, one_mul, pow_one, zero_add] using h
  simpa only [heatDressing, sub_zero] using! he.const_sub 1

open YM YM.MS YM.MS.Arts YM.MS.ScaleForest in
/-- Pointwise IR removal for the actual integrated line, at nonzero momentum.
This does NOT justify moving this limit inside a UV-divergent loop integral. -/
theorem submitted_line_limit (G : Gauge) (m : ℕ) (p : SectorP m)
    (i j : Cfield G m) (hp : 0 < p.sq) :
    Tendsto (fun rho : ℝ => (2:ℂ)*halfP G rho m i j p) atTop
      (𝓝 (Landau.choir Swirl.Near.Tail id i j p)) := by
  have hr : Tendsto (fun rho : ℝ => rho^2*p.sq) atTop atTop :=
    (tendsto_pow_atTop (by decide : (2:ℕ) ≠ 0)).atTop_mul_const hp
  have hd := Complex.continuous_ofReal.continuousAt.tendsto.comp (heatDressing_limit.comp hr)
  have hh := hd.mul_const (Landau.choir Swirl.Near.Tail id i j p)
  simp only [Complex.ofReal_one, one_mul] at hh
  apply hh.congr'
  filter_upwards [] with rho
  rw [halfP_components]
  simp [heatDressing]

end YMReview.NovemberMatching.GhostLoop

#print axioms YMReview.NovemberMatching.GhostLoop.numerator_zero
#print axioms YMReview.NovemberMatching.GhostLoop.numerator_gamma_ratio
#print axioms YMReview.NovemberMatching.GhostLoop.numerator_derivative
#print axioms YMReview.NovemberMatching.GhostLoop.tensor_zero
#print axioms YMReview.NovemberMatching.GhostLoop.tensor_derivative
#print axioms YMReview.NovemberMatching.GhostLoop.finite_limit
#print axioms YMReview.NovemberMatching.GhostLoop.parameter_weight
#print axioms YMReview.NovemberMatching.GhostLoop.submitted_pole
#print axioms YMReview.NovemberMatching.GhostLoop.premature_tensor_error
#print axioms YMReview.NovemberMatching.GhostLoop.premature_tensor_error_nonzero
#print axioms YMReview.NovemberMatching.GhostLoop.submitted_finite_reading
#print axioms YMReview.NovemberMatching.GhostLoop.submitted_scale_difference
#print axioms YMReview.NovemberMatching.GhostLoop.submitted_scale_coefficient
#print axioms YMReview.NovemberMatching.GhostLoop.finitePart_shift
#print axioms YMReview.NovemberMatching.GhostLoop.finite_test_iff_reference
#print axioms YMReview.NovemberMatching.GhostLoop.heatDressing_bounds
#print axioms YMReview.NovemberMatching.GhostLoop.heatDressing_limit
#print axioms YMReview.NovemberMatching.GhostLoop.submitted_line_limit
