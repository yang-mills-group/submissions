import GluonLoopInfrared
/-!
# Source scale equation and ultraviolet boundary condition

Relates the actual source ordinary/plow subtraction to its scale derivative
and ultraviolet boundary. The top Taylor term cancels against the explicit
logarithmic subtraction in oneLoopFinite.
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
namespace YMReview.NovemberMatching.GluonFlow
open GhostFlow GluonCarpet GluonInfrared
local notation "e" => TwoPoint.primary 0

lemma source_tad_two (G:Gauge) (long:Bool) (a b:G.ColorIndex) :
    Tad (TwoPoint.ratePair G false false 0) 2 0 (TwoPoint.word (axis long) (axis long) a b e) =
      33/4*(∑ d:G.ColorIndex,angle d a b)*(logArea:ℂ) := by
  rw [tad_word (n:=0)]
  simp only [reading,iteratedDeriv_zero,Nat.factorial_zero,Nat.cast_one,inv_one,one_smul]
  have h := GluonContinuation.actual_force_real G long a b 0 0 (by norm_num)
  simp only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one,GluonInfrared.continued_zero] at h
  change TwoPoint.ratePair G false false 0 0 (TwoPoint.word (axis long) (axis long) a b (0 • e)) = _
  rw [h]
  push_cast
  ring

lemma source_tad_three (G:Gauge) (long:Bool) (a b:G.ColorIndex) :
    Tad (TwoPoint.ratePair G false false 0) 3 0 (TwoPoint.word (axis long) (axis long) a b e) = 0 := by
  rw [tad_word (n:=1)]
  have hh : HasDerivAt (fun x:ℝ=>TwoPoint.ratePair G false false 0 0 (TwoPoint.word (axis long) (axis long) a b (x • e))) 0 0 := by
    have h := ((Complex.ofRealCLM.hasFDerivAt).comp_hasDerivAt 0 (GluonInfrared.continued_first long)).const_mul
      (4*∑ d:G.ColorIndex,angle d a b)
    convert! h using 1
    · funext x
      have ht := GluonContinuation.actual_force_real G long a b 0 x (by norm_num)
      simpa only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one] using! ht
    simp
  simp only [reading,iteratedDeriv_one,Nat.factorial_one,Nat.cast_one,inv_one,one_smul,hh.deriv]

lemma lowerTaylor_unit (G:Gauge) (long:Bool) (a b:G.ColorIndex) (s:ℝ) :
    plow (-4) s (lowerTaylor 4 4 (TwoPoint.ratePair G false false) 0) 0 (TwoPoint.word (axis long) (axis long) a b e) =
      (-33/8)*(∑ d:G.ColorIndex,angle d a b)*(logArea:ℂ)*(Real.exp (-2*s):ℂ) := by
  let W := TwoPoint.ratePair G false false 0
  have h0 : Tad W 0 0 (TwoPoint.word (axis long) (axis long) a b e)=0 := t_exc (by change (0:ℤ)<2; norm_num)
  have h1 : Tad W 1 0 (TwoPoint.word (axis long) (axis long) a b e)=0 := t_exc (by change (1:ℤ)<2; norm_num)
  have h2 := source_tad_two G long a b
  have h3 := source_tad_three G long a b
  unfold lowerTaylor cPos
  simp only [vamp,toll,mul_zero,zero_mul,add_zero,Nat.cast_ofNat]
  rw [←Alps.cert,map_sum]
  simp only [map_smul,Alps.cert,move_tad (GluonLoop.source_price G),Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  simp only [Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,zero_add]
  simp only [←show W=TwoPoint.ratePair G false false 0 from rfl,h0,h1,mul_zero,zero_add]
  rw [h2,h3]
  norm_num
  have he : amount (-2) s=(Real.exp (-2*s):ℂ) := by
    rw [amount,Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [he]
  push_cast
  ring

lemma ordinary_boundary (G:Gauge) (long:Bool) (a b:G.ColorIndex) :
    Tendsto (fun s:ℝ=>
      plow (-4) s (ordinary 4 (TwoPoint.ratePair G false false) 0) 0 (TwoPoint.word (axis long) (axis long) a b e) -
      (-33/8)*(∑ d:G.ColorIndex,angle d a b)*(logArea:ℂ)*(Real.exp (-2*s):ℂ)) atBot (𝓝 0) := by
  have h := frame_lim (W:=TwoPoint.ratePair G false false 0) (x:=(-4:ℂ)) (n:=5) 0 (TwoPoint.word (axis long) (axis long) a b e)
  convert! h using 1
  funext s
  unfold ordinary
  simp only [vamp,toll,mul_zero,zero_mul,add_zero,Nat.cast_ofNat]
  rw [←Alps.cert,map_add,Alps.cert,Alps.cert]
  simp only [Pi.add_apply]
  rw [lowerTaylor_unit G long a b s]
  ring


end YMReview.NovemberMatching.GluonFlow
#print axioms YMReview.NovemberMatching.GluonFlow.ordinary_boundary
