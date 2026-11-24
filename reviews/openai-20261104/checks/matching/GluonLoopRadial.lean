import GluonLoopCarpet
import GluonLoopGaussian
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open YM YM.MS YM.MS.Arts YM.MS.ScaleForest
open Plane Koszul Heat Flux Landau Book Convolve Motif Halo
open Function Filter Set Finset MeasureTheory Real
open Tone Momentum Frame Wire Color Detect Native Native.Wilsonian City Logarithm Signal
open Landau.Detect.Mark Wind High Knobs Arc Rock Path Oceans Plum Alps Garment Pearl Train
open YM.WilsonMS.BetaValue YM.WilsonMS.BetaValue.HeatPapers SquareShift
open _root_.YM.PertExtension RG FormalOPE FormalOPE.RG10 FormalOPE.RG10.MultiGauge Papers
namespace YMReview.NovemberMatching.GluonRadial
open GluonCarpet GluonGaussian GluonContraction
local notation "e" => TwoPoint.primary 0

lemma at_numerator (long:Bool) (H R u x:ℝ) (q:SectorP 0) :
    numerator long H R x (q+(-u*x) • e)=meterR q (numeratorPoly long H R u x) := by
  cases long <;>
    simp [numerator,numeratorPoly,crossPoly,GluonGaussian.core,sqE,GluonGaussian.speed,perp,
      GluonContraction.A,B,K,atP,atR,at_pane,at_sq,Momentum.sq,
      Fin.sum_univ_succ,TwoPoint.primary,spray,Pi.single_apply,TwoPoint.zeroDirection,rises] <;> ring

lemma numerator_sheet (long:Bool) (H R x:ℝ) : Sheet (numerator long H R x) := by
  have ha : Sheet (fun q:SectorP 0=>A q R) := Sheet.heat_sq.add (Sheet.num _)
  have hb : Sheet (fun q:SectorP 0=>B q R x) :=
    ((Sheet.heat_sq.add (Sheet.num _)).add ((Sheet.num _).mul (Sheet.read 0))).add (Sheet.num _)
  have hk : Sheet (fun q:SectorP 0=>K q R) := ha.sub ((Sheet.read 0).pow 2)
  cases long
  · exact (Sheet.num _).mul (((Sheet.num _).mul ((ha.add hb).sub ((Sheet.read 1).pow 2))).mul hk |>.add
      ((((Sheet.num _).mul ha).mul hb).mul ((Sheet.read 1).pow 2)))
  · exact ((((Sheet.num _).mul (Sheet.read 0)).add (Sheet.num _)).pow 2).mul
      ((((Sheet.num _).mul ha).mul hb).sub ((Sheet.num _).mul hk))

def heatValue (long:Bool) (H R x t:ℝ) :=
  GhostContinuation.prefactor 1 x t*(GluonGaussian.moment long 4 H (GhostJet.ratio t) (x^2) (gaussS (ν t))+
    R^2*GluonGaussian.radial long H (GhostJet.ratio t) (x^2) (gaussS (ν t))+
    R^4*GluonGaussian.fourth long H (GhostJet.ratio t) (x^2) (gaussS (ν t)))

lemma numerator_tune (long:Bool) (H R x t:ℝ) :
    tune (x • e) (numerator long H R x) t=heatValue long H R x t := by
  unfold tune heatValue GhostContinuation.prefactor volume4
  let X:=numeratorPoly long H R (GhostJet.ratio t) x
  have hp (q:SectorP 0) : numerator long H R x (q+(slope t*x) • e)=X.val q :=
    at_numerator long H R (GhostJet.ratio t) x q
  rw [←integral_add_right_eq_self _ ((slope t*x) • e),
    ←numerator_value (ν_pos t) long H R (GhostJet.ratio t) x, mul_assoc (t^3*_)]
  rw [←net_order (ν_pos t)]
  have hm (q:SectorP 0) : Pill t (x • e) (q+(slope t*x) • e)=
      t^3*Real.exp (slope t*x^2*1)*Real.exp (-(ν t*q.sq)) := by
    have he:=SquareShift.moveDensity e q x t
    rw [TwoPoint.primary_sq] at he
    exact he
  simp_rw [hm,hp,mul_assoc,MeasureTheory.integral_const_mul,←neg_mul]
  exact congr_arg₂ _ rfl (congr_arg₂ _ rfl
    (integral_congr_ae (Eventually.of_forall fun q:SectorP 0=>mul_comm ..)))

lemma kernel_as (long:Bool) (z t R x:ℝ) (q:SectorP 0) :
    GluonCarpet.radialKernel long z t R x q=Real.exp (-(ν t*R^2))*
      (Pill t (x • e) q*numerator long (4+2*z) R x q) := by
  unfold GluonCarpet.radialKernel
  ring

lemma weighted_bond (long:Bool) (z R x:ℝ) :
    Integrable (fun v:SectorP 0 × ℝ=>GluonCarpet.radialKernel long z v.2 R x v.1) (mplane.prod mint) := by
  have hb:=(bond (x • e) (numerator long (4+2*z) R x) (numerator_sheet long (4+2*z) R x)).norm
  refine hb.mono' ?_ ?_
  · have hc : Continuous (fun v:SectorP 0 × ℝ=>GluonCarpet.radialKernel long z v.2 R x v.1) := by
      unfold GluonCarpet.radialKernel Pill City.brush numerator GluonContraction.A B K ν Momentum.sq
      cases long <;> simp only [Bool.false_eq_true,if_false,if_true] <;> fun_prop
    exact hc.aestronglyMeasurable
  filter_upwards with v
  rw [kernel_as,norm_mul]
  have he : ‖Real.exp (-(ν v.2*v.1.sq*0+ν v.2*R^2))‖≤1 := by
    simp only [mul_zero,zero_add,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (ν_pos v.2).le (sq_nonneg R)))
  simp only [mul_zero,zero_add] at he
  simpa only [Real.norm_eq_abs,abs_norm,one_mul] using mul_le_mul_of_nonneg_right he
    (norm_nonneg (Pill v.2 (x • e) v.1*numerator long (4+2*z) R x v.1))

lemma radial_payment (long:Bool) (z R x:ℝ) :
    (∫ q : SectorP 0, (∫ t : ℝ in (0:ℝ)..1,
      (GluonCarpet.radialKernel long z t R x q : ℂ) + (GluonCarpet.radialKernel long z t R x (-q) : ℂ)) ∂mplane) =
      2 * ((∫ t : ℝ in (0:ℝ)..1,
        Real.exp (-(ν t*R^2))*heatValue long (4+2*z) R x t) : ℝ) := by
  let Z (q : SectorP 0) : ℝ := ∫ t : ℝ, GluonCarpet.radialKernel long z t R x q ∂mint
  have hz : Integrable Z mplane := (weighted_bond long z R x).integral_prod_left
  have ht (q : SectorP 0) : Integrable (fun t : ℝ => GluonCarpet.radialKernel long z t R x q) mint := by
    have hc : Continuous (fun t : ℝ => GluonCarpet.radialKernel long z t R x q) := by
      unfold GluonCarpet.radialKernel Pill City.brush ν
      fun_prop
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (hc.intervalIntegrable 0 1)
  have hpoint (q : SectorP 0) : (∫ t : ℝ in (0:ℝ)..1,
      (GluonCarpet.radialKernel long z t R x q : ℂ) + (GluonCarpet.radialKernel long z t R x (-q) : ℂ)) =
      (Z q : ℂ)+(Z (-q) : ℂ) := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    change (∫ t : ℝ, (GluonCarpet.radialKernel long z t R x q : ℂ)+(GluonCarpet.radialKernel long z t R x (-q) : ℂ) ∂mint) = _
    have ha : Integrable (fun t => (GluonCarpet.radialKernel long z t R x q : ℂ)) mint := Complex.ofRealCLM.integrable_comp (ht q)
    have hb : Integrable (fun t => (GluonCarpet.radialKernel long z t R x (-q) : ℂ)) mint := Complex.ofRealCLM.integrable_comp (ht (-q))
    rw [MeasureTheory.integral_add ha hb,
      integral_complex_ofReal,integral_complex_ofReal]
  simp_rw [hpoint]
  have ha : Integrable (fun q => (Z q : ℂ)) mplane := Complex.ofRealCLM.integrable_comp hz
  have hb : Integrable (fun q => (Z (-q) : ℂ)) mplane := Complex.ofRealCLM.integrable_comp hz.comp_neg
  rw [MeasureTheory.integral_add ha hb,integral_complex_ofReal,integral_complex_ofReal,
    integral_neg_eq_self]
  rw [show (∫ q : SectorP 0, Z q ∂mplane) =
    ∫ t : ℝ, (∫ q : SectorP 0, GluonCarpet.radialKernel long z t R x q ∂mplane) ∂mint from
      integral_integral_swap (weighted_bond long z R x)]
  simp_rw [kernel_as,MeasureTheory.integral_const_mul]
  have he (t : ℝ) : (∫ a : SectorP 0, Pill t (x • e) a * numerator long (4+2*z) R x a ∂mplane) =
      heatValue long (4+2*z) R x t := by
    simpa only [tune] using! numerator_tune long (4+2*z) R x t
  simp_rw [he,intervalIntegral.integral_of_le zero_le_one]
  ring


/-- Compact-parameter formula for the actual loop carpet, including the
Lebesgue/(2π)^4 conversion and both loop orientations. -/
theorem actual_carpet_evaluated (G:Gauge) (long:Bool) (a b:G.ColorIndex)
    (R x z:ℝ) :
    loopCarpet (cursor false).half (TwoPoint.stemPair G false) (z:ℂ)
      (TwoPoint.word (axis long) (axis long) a b e) (R,x) =
    (4 * (∑ d : G.ColorIndex, angle d a b) / (room : ℂ)) *
      ((∫ t : ℝ in (0:ℝ)..1,
        Real.exp (-(ν t*R^2))*heatValue long (4+2*z) R x t) : ℝ) := by
  rw [GluonCarpet.actual_carpet]
  have hp := radial_payment long z R x
  rw [show mplane = ENNReal.ofReal room • (Px 0) from rfl,
    integral_smul_measure,ENNReal.toReal_ofReal room_pos.le,Complex.real_smul] at hp
  have hn : (room : ℂ) ≠ 0 := by exact_mod_cast room_pos.ne'
  simp_rw [← mul_add,intervalIntegral.integral_const_mul,MeasureTheory.integral_const_mul]
  apply (mul_left_cancel₀ hn)
  calc
    (room:ℂ) * ((∑ d : G.ColorIndex, angle d a b) * (2 *
      (∫ q : SectorP 0, (∫ t : ℝ in (0:ℝ)..1,
        (GluonCarpet.radialKernel long z t R x q : ℂ)+(GluonCarpet.radialKernel long z t R x (-q) : ℂ)) ∂Px 0))) =
      (2*(∑ d : G.ColorIndex,angle d a b)) *
        ((room:ℂ)*(∫ q : SectorP 0, (∫ t : ℝ in (0:ℝ)..1,
        (GluonCarpet.radialKernel long z t R x q : ℂ)+(GluonCarpet.radialKernel long z t R x (-q) : ℂ)) ∂Px 0)) := by ring
    _ = _ := by
      rw [hp]
      generalize (∫ t : ℝ in (0:ℝ)..1,
        Real.exp (-(ν t*R^2))*heatValue long (4+2*z) R x t) = J
      field_simp
      ring


end YMReview.NovemberMatching.GluonRadial
#print axioms YMReview.NovemberMatching.GluonRadial.actual_carpet_evaluated
