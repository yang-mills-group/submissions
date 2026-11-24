import GluonLoopFlow
import GluonLoopJetParameter
import GluonLoopTensor
/-!
# Exact finite amplitude at unit external momentum

The actual source amplitude and the explicit primitive have the same scale
derivative and ultraviolet boundary. This fixes the additive constant,
proves equality at every retained cutoff, and permits the infrared limit.
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
namespace YMReview.NovemberMatching.GluonUnit
open GluonCarpet GluonInfrared GluonLoop GhostFlow
local notation "e" => TwoPoint.primary 0
lemma primitive_time_derivative (v s:ℝ) :
    HasDerivAt (fun s:ℝ=>primitive v (Real.exp (2*s)))
      (Real.exp (-2*s)*forceValue v (Real.exp (2*s))) s := by
  have h := (primitive_deriv v (Real.exp (2*s)) (Real.exp_ne_zero _)).comp s
    (((hasDerivAt_id' s).const_mul 2).exp)
  convert! h using 1
  rw [show -2*s= -(2*s) by ring,Real.exp_neg]
  field_simp

lemma exp_square (s:ℝ) : (Real.exp s)^2=Real.exp (2*s) := by
  rw [←Real.exp_nat_mul]
  norm_num

/-- The finite source amplitude, evaluated exactly at retained infrared
cutoff, with the UV subtraction fixing the additive constant. -/
theorem finite_unit_exact (G:Gauge) (long:Bool) (a b:G.ColorIndex) (s y:ℝ) :
    oneLoopFinite 4 (TwoPoint.ratePair G false false) s y 0 (TwoPoint.word (axis long) (axis long) a b e) =
      (∑ d:G.ColorIndex,angle d a b)*(logArea:ℂ)*(primitive (probeValue long) (Real.exp (2*s)):ℂ)+
      -(∑ d:G.ColorIndex,angle d a b)*(logArea:ℂ)*(finiteConstant (probeValue long):ℂ)+
      ruby (highTensor 4 (TwoPoint.ratePair G false false)) 1 0 (TwoPoint.word (axis long) (axis long) a b e)-
      2*(y:ℂ)*highTensor 4 (TwoPoint.ratePair G false false) 0 0 (TwoPoint.word (axis long) (axis long) a b e) := by
  let v := probeValue long
  let C := (∑ d:G.ColorIndex,angle d a b)*(logArea:ℂ)
  let H := highTensor 4 (TwoPoint.ratePair G false false) 0 0 (TwoPoint.word (axis long) (axis long) a b e)
  let J := ruby (highTensor 4 (TwoPoint.ratePair G false false)) 1 0 (TwoPoint.word (axis long) (axis long) a b e)
  let F (s:ℝ) := oneLoopFinite 4 (TwoPoint.ratePair G false false) s y 0 (TwoPoint.word (axis long) (axis long) a b e)
  let Q (s:ℝ) := C*(primitive v (Real.exp (2*s)):ℂ)+ -C*(finiteConstant v:ℂ)+J-2*(y:ℂ)*H
  have hH : H= C*(k v:ℂ) := by simpa only [H,C,v,mul_assoc] using GluonJetParameter.source_high_unit G long a b
  have hF (s:ℝ) : HasDerivAt F
      (C*(↑(Real.exp (-2*s)*forceValue v (Real.exp (2*s))):ℂ)) s := by
    have h := finite_derivative (TwoPoint.ratePair G false false) (GluonLoop.source_price G) s y 0 (TwoPoint.word (axis long) (axis long) a b e)
    rw [plow_word,GluonInfrared.submitted_force_unit G long a b _ (Real.exp_ne_zero _),exp_square] at h
    convert! h using 1
    unfold C v
    push_cast
    ring
  have hQ (s:ℝ) : HasDerivAt Q
      (C*(↑(Real.exp (-2*s)*forceValue v (Real.exp (2*s))):ℂ)) s := by
    exact (((((Complex.ofRealCLM.hasFDerivAt).comp_hasDerivAt s (primitive_time_derivative v s)).const_mul (C)).add_const
      (-C*(finiteConstant v:ℂ))).add_const J).sub_const (2*(y:ℂ)*H)
  have hd (s:ℝ) : HasDerivAt (fun s:ℝ=>F s-Q s) 0 s := by
    simpa only [sub_self] using! (hF s).sub (hQ s)
  have hc : ∀ t s:ℝ,F t-Q t=F s-Q s :=
    is_const_of_deriv_eq_zero (fun s=>(hd s).differentiableAt) (fun s=>(hd s).deriv)
  have hu := GluonFlow.ordinary_boundary G long a b
  have hx : Tendsto (fun s:ℝ=>Real.exp (2*s)) atBot (𝓝[>] (0:ℝ)) :=
    Real.tendsto_exp_atBot_nhdsGT.comp ((tendsto_const_mul_atBot_of_pos (by norm_num : (0:ℝ)<2)).mpr tendsto_id)
  have hv := ((primitive_small v).comp hx).sub_const (finiteConstant v)
  simp only [sub_self] at hv
  have hz := hu.add ((Complex.continuous_ofReal.tendsto (0:ℝ)).comp hv |>.const_mul (-C))
  simp only [Complex.ofReal_zero,mul_zero,add_zero] at hz
  have hlim : Tendsto (fun s:ℝ=>F s-Q s) atBot (𝓝 0) := by
    apply hz.congr'
    apply Eventually.of_forall
    intro s
    simp only [Function.comp_def,Real.log_exp]
    unfold F Q oneLoopFinite
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    simp only [←show H=highTensor 4 (TwoPoint.ratePair G false false) 0 0 (TwoPoint.word (axis long) (axis long) a b e) from rfl,
      ←show J=ruby (highTensor 4 (TwoPoint.ratePair G false false)) 1 0 (TwoPoint.word (axis long) (axis long) a b e) from rfl,hH]
    rw [show -2*s= -(2*s) by ring,Real.exp_neg]
    unfold C
    push_cast
    field_simp
    ring
  have hs : Tendsto (fun _t:ℝ=>F s-Q s) atBot (𝓝 0) := hlim.congr (fun t=>hc t s)
  have he : F s-Q s=0 := tendsto_nhds_unique tendsto_const_nhds hs
  have h := sub_eq_zero.mp he
  simpa only [F,Q,C,v,H,J,mul_assoc,neg_mul] using h


theorem finite_unit_limit (G:Gauge) (hG:G.Simple) (long:Bool) (a b:G.ColorIndex) (y:ℝ) :
    Tendsto (fun s:ℝ=>oneLoopFinite 4 (TwoPoint.ratePair G false false) s y 0
      (TwoPoint.word (axis long) (axis long) a b e)) atTop
      (𝓝 ((if a=b then (G.casimir:ℂ) else 0)*
        GluonLoop.finitePart ((2*y-Real.eulerMascheroniConstant+Real.log (4*Real.pi):ℝ):ℂ)
          1 (probeValue long:ℝ))) := by
  have hx : Tendsto (fun s:ℝ=>Real.exp (2*s)) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_const_mul_atTop_of_pos (by norm_num : (0:ℝ)<2)).mpr tendsto_id)
  have h:=(Complex.continuous_ofReal.tendsto (0:ℝ)).comp ((GluonLoop.primitive_large (probeValue long)).comp hx)
  have ht:=((((h.const_mul ((∑ d:G.ColorIndex,angle d a b)*(logArea:ℂ))).add_const
    (-(∑ d:G.ColorIndex,angle d a b)*(logArea:ℂ)*(finiteConstant (probeValue long):ℂ))).add_const
    (ruby (highTensor 4 (TwoPoint.ratePair G false false)) 1 0 (TwoPoint.word (axis long) (axis long) a b e))).sub_const
    (2*(y:ℂ)*highTensor 4 (TwoPoint.ratePair G false false) 0 0 (TwoPoint.word (axis long) (axis long) a b e)))
  simp only [Complex.ofReal_zero,mul_zero,zero_add] at ht
  convert! ht using 1
  · funext s
    exact finite_unit_exact G long a b s y
  · congr 1
    rw [GluonJetParameter.submitted_jet_unit,GluonJetParameter.source_high_unit,sums_angles hG]
    have hc:=congrArg Complex.ofReal (GluonLoop.finite_constants (probeValue long) y)
    push_cast at hc
    unfold GluonLoop.finitePart logArea
    push_cast
    linear_combination -((if a=b then (G.casimir:ℂ) else 0)/(16*(Real.pi:ℂ)^2))*hc

end YMReview.NovemberMatching.GluonUnit
#print axioms YMReview.NovemberMatching.GluonUnit.finite_unit_exact
#print axioms YMReview.NovemberMatching.GluonUnit.finite_unit_limit
