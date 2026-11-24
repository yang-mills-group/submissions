import GhostLoopFlow
import GhostLoopPrimitive
import GhostLoopBenchmark
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
namespace YMReview.NovemberMatching.GhostUnit
open GhostRadial GhostContinuation GhostJet GhostInfrared GhostFlow GhostPrimitive

lemma source_high_unit (G:Gauge) (p:SectorP 0) (hp:p.sq=1) (i:L 0) (a b:G.ColorIndex) :
    highTensor 4 (TwoPoint.ratePair G true true) 0 0 (TwoPoint.word i i a b p) =
      -4*(∑ d:G.ColorIndex,angle d a b)*(logArea:ℂ)*(k (p i*p i):ℂ) := by
  have he : highTensor 4 (TwoPoint.ratePair G true true) 0 0 (TwoPoint.word i i a b p) =
      -TwoPoint.kinetic (TwoPoint.poleTensor G true true) a b p i i := by simp [TwoPoint.poleTensor,TwoPoint.kinetic]
  rw [he,TwoPoint.ghost_bill]
  simp only [TwoPoint.ghost_residue,TwoPoint.traceAd,TwoPoint.counterScale,hp,ite_true]
  unfold k
  push_cast
  ring

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
theorem finite_unit_exact (G:Gauge) (p:SectorP 0) (hp:p.sq=1)
    (i:L 0) (a b:G.ColorIndex) (s y:ℝ) :
    oneLoopFinite 4 (TwoPoint.ratePair G true true) s y 0 (TwoPoint.word i i a b p) =
      -4*(∑ d:G.ColorIndex,angle d a b)*(logArea:ℂ)*(primitive (p i*p i) (Real.exp (2*s)):ℂ)+
      4*(∑ d:G.ColorIndex,angle d a b)*(logArea:ℂ)*(finiteConstant (p i*p i):ℂ)+
      ruby (highTensor 4 (TwoPoint.ratePair G true true)) 1 0 (TwoPoint.word i i a b p)-
      2*(y:ℂ)*highTensor 4 (TwoPoint.ratePair G true true) 0 0 (TwoPoint.word i i a b p) := by
  let v := p i*p i
  let C := (∑ d:G.ColorIndex,angle d a b)*(logArea:ℂ)
  let H := highTensor 4 (TwoPoint.ratePair G true true) 0 0 (TwoPoint.word i i a b p)
  let J := ruby (highTensor 4 (TwoPoint.ratePair G true true)) 1 0 (TwoPoint.word i i a b p)
  let F (s:ℝ) := oneLoopFinite 4 (TwoPoint.ratePair G true true) s y 0 (TwoPoint.word i i a b p)
  let Q (s:ℝ) := -4*C*(primitive v (Real.exp (2*s)):ℂ)+4*C*(finiteConstant v:ℂ)+J-2*(y:ℂ)*H
  have hH : H= -4*C*(k v:ℂ) := by simpa only [H,C,v,mul_assoc] using source_high_unit G p hp i a b
  have hF (s:ℝ) : HasDerivAt F
      (-4*C*(↑(Real.exp (-2*s)*forceValue v (Real.exp (2*s))):ℂ)) s := by
    have h := finite_derivative (TwoPoint.ratePair G true true) (source_price G) s y 0 (TwoPoint.word i i a b p)
    rw [plow_word,submitted_force_unit G p hp i a b _ (Real.exp_ne_zero _),exp_square] at h
    convert! h using 1
    unfold C v
    push_cast
    ring
  have hQ (s:ℝ) : HasDerivAt Q
      (-4*C*(↑(Real.exp (-2*s)*forceValue v (Real.exp (2*s))):ℂ)) s := by
    exact (((((Complex.ofRealCLM.hasFDerivAt).comp_hasDerivAt s (primitive_time_derivative v s)).const_mul (-4*C)).add_const
      (4*C*(finiteConstant v:ℂ))).add_const J).sub_const (2*(y:ℂ)*H)
  have hd (s:ℝ) : HasDerivAt (fun s:ℝ=>F s-Q s) 0 s := by
    simpa only [sub_self] using! (hF s).sub (hQ s)
  have hc : ∀ t s:ℝ,F t-Q t=F s-Q s :=
    is_const_of_deriv_eq_zero (fun s=>(hd s).differentiableAt) (fun s=>(hd s).deriv)
  have hu := ordinary_boundary G p hp i a b
  have hx : Tendsto (fun s:ℝ=>Real.exp (2*s)) atBot (𝓝[>] (0:ℝ)) :=
    Real.tendsto_exp_atBot_nhdsGT.comp ((tendsto_const_mul_atBot_of_pos (by norm_num : (0:ℝ)<2)).mpr tendsto_id)
  have hv := ((primitive_small v).comp hx).sub_const (finiteConstant v)
  simp only [sub_self] at hv
  have hz := hu.add ((Complex.continuous_ofReal.tendsto (0:ℝ)).comp hv |>.const_mul (4*C))
  simp only [Complex.ofReal_zero,mul_zero,add_zero] at hz
  have hlim : Tendsto (fun s:ℝ=>F s-Q s) atBot (𝓝 0) := by
    apply hz.congr'
    apply Eventually.of_forall
    intro s
    simp only [Function.comp_def,Real.log_exp]
    unfold F Q oneLoopFinite
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    simp only [←show H=highTensor 4 (TwoPoint.ratePair G true true) 0 0 (TwoPoint.word i i a b p) from rfl,
      ←show J=ruby (highTensor 4 (TwoPoint.ratePair G true true)) 1 0 (TwoPoint.word i i a b p) from rfl,hH]
    rw [show -2*s= -(2*s) by ring,Real.exp_neg]
    unfold C
    push_cast
    field_simp
    ring
  have hs : Tendsto (fun _t:ℝ=>F s-Q s) atBot (𝓝 0) := hlim.congr (fun t=>hc t s)
  have he : F s-Q s=0 := tendsto_nhds_unique tendsto_const_nhds hs
  have h := sub_eq_zero.mp he
  simpa only [F,Q,C,v,H,J,mul_assoc] using h

/-- The retained infrared cutoff can be removed and gives the conventional
finite ghost-loop value, for every unit momentum and diagonal slot. -/
theorem finite_unit_limit (G:Gauge) (hG:G.Simple) (p:SectorP 0) (hp:p.sq=1)
    (i:L 0) (a b:G.ColorIndex) (y:ℝ) :
    Tendsto (fun s:ℝ=>oneLoopFinite 4 (TwoPoint.ratePair G true true) s y 0 (TwoPoint.word i i a b p))
      atTop (𝓝 ((if a=b then (G.casimir:ℂ) else 0)*
        GhostLoop.finitePart ((2*y-Real.eulerMascheroniConstant+Real.log (4*Real.pi):ℝ):ℂ)
          1 ((p i:ℂ)*(p i:ℂ)))) := by
  have hx : Tendsto (fun s:ℝ=>Real.exp (2*s)) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_const_mul_atTop_of_pos (by norm_num : (0:ℝ)<2)).mpr tendsto_id)
  have h := (Complex.continuous_ofReal.tendsto (0:ℝ)).comp ((primitive_large (p i*p i)).comp hx)
  have ht := ((((h.const_mul (-4*(∑ d:G.ColorIndex,angle d a b)*(logArea:ℂ))).add_const
    (4*(∑ d:G.ColorIndex,angle d a b)*(logArea:ℂ)*(finiteConstant (p i*p i):ℂ))).add_const
      (ruby (highTensor 4 (TwoPoint.ratePair G true true)) 1 0 (TwoPoint.word i i a b p))).sub_const
        (2*(y:ℂ)*highTensor 4 (TwoPoint.ratePair G true true) 0 0 (TwoPoint.word i i a b p)))
  simp only [Complex.ofReal_zero,mul_zero,zero_add] at ht
  convert! ht using 1
  · funext s
    exact finite_unit_exact G p hp i a b s y
  · congr 1
    rw [submitted_jet_unit G hG p hp i a b,source_high_unit G p hp i a b,sums_angles hG]
    have hl : Real.log 2+Real.log (2*Real.pi)=Real.log (4*Real.pi) := by
      rw [←Real.log_mul (by norm_num : (2:ℝ)≠0) (by positivity)]
      congr 1
      ring
    unfold finiteConstant k GhostLoop.finitePart logArea
    push_cast
    have hlc := congrArg Complex.ofReal hl
    push_cast at hlc
    rw [←hlc]
    ring
end YMReview.NovemberMatching.GhostUnit

