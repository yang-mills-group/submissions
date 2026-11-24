import GluonLoopJet
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open YM YM.MS YM.MS.Arts YM.MS.ScaleForest
open Plane Koszul Heat Flux Landau Book Convolve Motif Halo
open Function Filter Set Finset MeasureTheory Real
open Tone Momentum Frame Wire Color Detect Native Native.Wilsonian City Logarithm Signal
open Landau.Detect.Mark Wind High Knobs Arc Rock Path Oceans Plum Alps Garment Pearl Train Shine Hem Mell
open YM.WilsonMS.BetaValue YM.WilsonMS.BetaValue.HeatPapers SquareShift
open scoped Topology ContDiff
namespace YMReview.NovemberMatching.GluonInfrared
open GluonCarpet GluonJet
local notation "e" => TwoPoint.primary 0

def probeValue (long:Bool) : ℝ := if long then 1 else 0

lemma density_parameter (long:Bool) (t x:ℝ) :
    density long 0 t x=logArea/4*(Real.exp (-(x^2)*GhostJet.ratio t)*
      GluonHeat.heatPolynomial (probeValue long) (GhostJet.ratio t) (x^2))*(2*t/(ν t)^2) := by
  unfold density GhostJet.weight
  simp only [neg_zero,Real.rpow_zero,mul_one]
  have he : -GhostJet.ratio t*x^2= -(x^2)*GhostJet.ratio t := by ring
  rw [he]
  unfold c0 c1 c2 c3 probeValue GluonHeat.heatPolynomial GluonHeat.heatT GluonHeat.heatL
    GhostJet.ratio volume4 logArea ν
  cases long <;> simp only [Bool.false_eq_true,if_false,if_true]
  all_goals
    generalize Real.exp (-(x^2)*(t^2/(1+t^2)))=E
    field_simp
    ring

lemma continued_integral (long:Bool) (x:ℝ) :
    GluonContinuation.continuedValue long 0 x=logArea/4*
      (∫ u:ℝ in (0:ℝ)..(1/2:ℝ),Real.exp (-(x^2)*u)*GluonHeat.heatPolynomial (probeValue long) u (x^2)) := by
  rw [continued_density]
  simp_rw [density_parameter,mul_assoc (logArea/4),intervalIntegral.integral_const_mul]
  rw [GhostJet.parameter_substitution (fun u:ℝ=>Real.exp (-(x^2)*u)*GluonHeat.heatPolynomial (probeValue long) u (x^2)) (by unfold GluonHeat.heatPolynomial GluonHeat.heatT GluonHeat.heatL;fun_prop)]

theorem submitted_force_unit (G:Gauge) (long:Bool) (a b:G.ColorIndex) (x:ℝ) (hx:x≠0) :
    TwoPoint.ratePair G false false 0 0 (TwoPoint.word (axis long) (axis long) a b (x • e))=
      (∑ d:G.ColorIndex,angle d a b)*(logArea:ℂ)*(GluonLoop.forceValue (probeValue long) (x^2):ℂ) := by
  have h:=GluonContinuation.actual_force_real G long a b 0 x (by norm_num)
  simp only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one,continued_integral,
    GluonHeat.heatPolynomial_integral _ _ (pow_ne_zero _ hx)] at h
  rw [h]
  push_cast
  ring

lemma continued_zero (long:Bool) :
    GluonContinuation.continuedValue long 0 0=logArea*33/16 := by
  rw [continued_integral]
  have he : (fun u:ℝ=>Real.exp (-(0^2)*u)*GluonHeat.heatPolynomial (probeValue long) u (0^2))=
      fun u=>144*u-288*u^2+144*u^3 := by
    funext u
    unfold GluonHeat.heatPolynomial GluonHeat.heatT GluonHeat.heatL
    norm_num
    ring
  rw [he,intervalIntegral.integral_add,intervalIntegral.integral_sub]
  · simp only [intervalIntegral.integral_const_mul]
    norm_num [integral_id,integral_pow]
    rw [intervalIntegral.integral_const_mul]
    norm_num [integral_id]
    ring
  all_goals exact (by fun_prop : Continuous _).intervalIntegrable _ _

lemma density_first (long:Bool) (t:ℝ) : HasDerivAt (fun x:ℝ=>density long 0 t x) 0 0 := by
  let g (y:ℝ):=GhostJet.weight 0 t*Real.exp (-GhostJet.ratio t*y)*
    (c0 0 (GhostJet.ratio t)+c1 long 0 (GhostJet.ratio t)*y+
      c2 long 0 (GhostJet.ratio t)*y^2+c3 long 0 (GhostJet.ratio t)*y^3)
  have hg : DifferentiableAt ℝ g ((0:ℝ)^2) := by unfold g;fun_prop
  have h:=hg.hasDerivAt.comp (h:=fun x:ℝ=>x^2) (0:ℝ) (hasDerivAt_pow 2 (0:ℝ))
  convert! h using 1
  · funext x
    unfold density g
    simp only [Function.comp_def,mul_zero,add_zero]
    ring
  norm_num

lemma continued_first (long:Bool) : HasDerivAt (fun x:ℝ=>GluonContinuation.continuedValue long 0 x) 0 0 := by
  simp_rw [continued_density]
  have h:=GhostContinuation.compact_derivative _ (density_smooth long 0) 0
  simp only [(density_first long _).deriv,intervalIntegral.integral_zero] at h
  exact h

end YMReview.NovemberMatching.GluonInfrared
#print axioms YMReview.NovemberMatching.GluonInfrared.submitted_force_unit
