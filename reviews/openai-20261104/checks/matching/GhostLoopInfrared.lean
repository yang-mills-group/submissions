import GhostLoopJet
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
/-!
# Closed physical ghost-loop force

Evaluates the compact heat-parameter integral as an elementary exponential
and rational expression. No infrared limit or finite subtraction constant
is assumed. The apparent singularities at zero are removable.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open YM YM.MS YM.MS.Arts YM.MS.ScaleForest
open Plane Koszul Heat Flux Landau Book Convolve Motif Halo
open Function Filter Set Finset MeasureTheory Metric Real
open Tone Momentum Frame Wire Color Detect Native Native.Wilsonian City Logarithm Signal
open Landau.Detect.Mark Wind High Knobs Arc Rock Path Oceans Plum Alps Garment Pearl Train Shine Hem Mell
open YM.WilsonMS.BetaValue YM.WilsonMS.BetaValue.HeatPapers SquareShift
open scoped BigOperators Topology ContDiff
namespace YMReview.NovemberMatching.GhostInfrared
open GhostRadial GhostContinuation GhostJet

/-- Primitive of a polynomial times a decaying exponential. -/
def laplacePrimitive (X : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun u => -Real.exp (-X*u)/X
  | n+1 => fun u => -u^(n+1)*Real.exp (-X*u)/X+(n+1)/X*laplacePrimitive X n u

lemma laplacePrimitive_deriv (X : ℝ) (hX : X≠0) (n : ℕ) (u : ℝ) :
    HasDerivAt (laplacePrimitive X n) (u^n*Real.exp (-X*u)) u := by
  induction n with
  | zero =>
    convert! (((hasDerivAt_id' u).const_mul (-X)).exp.neg).div_const X using 1
    simp only [pow_zero,one_mul]
    field_simp
  | succ n ih =>
    convert! ((((hasDerivAt_pow (n+1) u).neg.mul
      (((hasDerivAt_id' u).const_mul (-X)).exp)).div_const X).add
        (ih.const_mul ((n+1)/X))) using 1
    simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,Pi.neg_apply]
    field_simp
    ring

lemma laplaceMoment (X : ℝ) (hX : X≠0) (n : ℕ) :
    (∫ u:ℝ in (0:ℝ)..(1/2:ℝ),u^n*Real.exp (-X*u)) =
      laplacePrimitive X n (1/2)-laplacePrimitive X n 0 := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _=>laplacePrimitive_deriv X hX n u)
    ((show Continuous (fun u:ℝ=>u^n*Real.exp (-X*u)) by fun_prop).intervalIntegrable _ _)

def heatPolynomial (v u X : ℝ) :=
  6*u*(1-u)^2+
  u*(1-u)/4*(6*(u^2+(1-u)^2)-4*u*(1-u)+v*(12*(1-2*u)^2-32*u*(1-u)))*X+
  u/2*(u^2*(1-u)^2+v*(-2*u*(1-u)*(1-2*u)^2-u*(1-u)*(4*(u^2+(1-u)^2)-4*u*(1-u))))*X^2-
  v*u^4*(1-u)^2*X^3

def heatCoeff (v X : ℝ) : Fin 7 → ℝ := ![
  0,
  6+3/2*X+3*X*v,
  -12-11/2*X-23*X*v-3*X^2*v,
  6+8*X+40*X*v+1/2*X^2+13*X^2*v,
  -4*X-20*X*v-X^2-20*X^2*v-X^3*v,
  1/2*X^2+10*X^2*v+2*X^3*v,
  -X^3*v]

lemma heatPolynomial_coeff (v u X : ℝ) :
    heatPolynomial v u X = ∑ n:Fin 7, heatCoeff v X n*u^(n:ℕ) := by
  simp [heatCoeff,Fin.sum_univ_succ,heatPolynomial]
  ring

/-- The elementary, exact physical force after the compact heat-parameter
integration. The apparent singularities at X=0 are removable. -/
def forceValue (v X : ℝ) := Real.exp (-X/2)*
  ((2-8*v)/X^2+(-1/2-v)/X+(-5/32+v/2)+(-1/64+v/8)*X+v/64*X^2)+
  (-2+8*v)/X^2+(3/2-3*v)/X

lemma heatPolynomial_integral (v X : ℝ) (hX : X≠0) :
    (∫ u:ℝ in (0:ℝ)..(1/2:ℝ),Real.exp (-X*u)*heatPolynomial v u X) =
      forceValue v X := by
  simp_rw [heatPolynomial_coeff,Finset.mul_sum,
    show ∀ n:Fin 7,∀ u:ℝ,Real.exp (-X*u)*(heatCoeff v X n*u^(n:ℕ)) =
      heatCoeff v X n*(u^(n:ℕ)*Real.exp (-X*u)) from by intros; ring]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul,laplaceMoment X hX]
    simp only [heatCoeff,Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,
      Matrix.cons_val_zero,Matrix.cons_val_succ]
    norm_num [laplacePrimitive,forceValue]
    rw [show -(X*(1/2))= -X/2 by ring]
    field_simp
    ring
  · intro n _
    exact (show Continuous (fun u:ℝ=>heatCoeff v X n*(u^(n:ℕ)*Real.exp (-X*u))) by fun_prop).intervalIntegrable _ _

lemma density_parameter (v t x : ℝ) : density 0 v t x =
    logArea/2*(Real.exp (-(x^2)*ratio t)*heatPolynomial v (ratio t) (x^2))*(2*t/(ν t)^2) := by
  unfold density GhostJet.weight
  simp only [neg_zero,Real.rpow_zero,mul_one,mul_zero,add_zero]
  rw [show -ratio t*x^2= -(x^2)*ratio t by ring]
  unfold heatPolynomial GhostLoopFinite.coeffA GhostLoopFinite.coeffB GhostLoopFinite.coeffC GhostLoopFinite.coeffD
    volume4 ratio logArea ν
  generalize Real.exp (-(x^2)*(t^2/(1+t^2))) = e
  field_simp
  ring

lemma continued_forceValue (v x : ℝ) (hx : x≠0) :
    (∫ t:ℝ in (0:ℝ)..1,density 0 v t x) = logArea/2*forceValue v (x^2) := by
  simp_rw [density_parameter,mul_assoc (logArea/2),intervalIntegral.integral_const_mul]
  rw [parameter_substitution (fun u:ℝ=>Real.exp (-(x^2)*u)*heatPolynomial v u (x^2)) (by unfold heatPolynomial; fun_prop),
    heatPolynomial_integral v (x^2) (pow_ne_zero _ hx)]

/-- Closed evaluation of the actual physical force, with no statement about
its finite infrared limit assumed. -/
theorem submitted_force_unit (G : Gauge) (p : SectorP 0) (hp : p.sq=1)
    (i : L 0) (a b : G.ColorIndex) (x : ℝ) (hx : x≠0) :
    TwoPoint.ratePair G true true 0 0 (TwoPoint.word i i a b (x • p)) =
      -4*(∑ d:G.ColorIndex,angle d a b)*(logArea:ℂ)*(forceValue (p i*p i) (x^2):ℂ) := by
  have ht := actual_force_scaled G p i a b (0:ℝ) (by norm_num) x
  simp only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one,hp,continued_density,
    continued_forceValue _ x hx] at ht
  change TwoPoint.kinetic _ a b (x • p) i i = _
  rw [ht]
  push_cast
  ring
end YMReview.NovemberMatching.GhostInfrared
