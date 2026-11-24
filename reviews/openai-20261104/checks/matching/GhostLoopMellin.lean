import GhostLoopInfrared
import Mathlib.NumberTheory.Harmonic.GammaDeriv
/-!
# Exponential integral and its normalization

Derives the logarithmic Gaussian integral from the Gamma derivative, then
proves the small-argument and large-argument limits needed to fix the
finite part. These are ordinary real analysis lemmas.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open YM YM.MS YM.MS.Arts YM.MS.ScaleForest
open Function Filter Set Finset MeasureTheory Metric Real Asymptotics
open scoped BigOperators Topology ContDiff
namespace YMReview.NovemberMatching.GhostMellin
open GhostInfrared

def logExp (t : ℝ) := Real.log t*Real.exp (-t)

lemma logExp_integrable : IntegrableOn logExp (Set.Ioi (0:ℝ)) := by
  have H := (mellin_hasDerivAt_of_isBigO_rpow (E:=ℂ) (s:=1) (a:=2) (b:=0)
    (f:=fun t:ℝ=>(Real.exp (-t):ℂ))
    ((show Continuous (fun t:ℝ=>(Real.exp (-t):ℂ)) by fun_prop).continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (by
      rw [← isBigO_norm_left]
      simp_rw [Complex.norm_real, isBigO_norm_left]
      simpa only [neg_one_mul] using (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one (-2:ℝ)).isBigO)
    (by norm_num)
    (by
      simp_rw [neg_zero,Real.rpow_zero]
      apply isBigO_const_of_tendsto (y:=(1:ℂ)) (c:=(1:ℝ)) _ one_ne_zero
      convert! ((show Continuous (fun t:ℝ=>(Real.exp (-t):ℂ)) by fun_prop).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds using 1
      simp)
    (by norm_num)).1
  unfold MellinConvergent at H
  simp only [sub_self,Complex.cpow_zero,one_smul,Complex.real_smul] at H
  have HR := H.re
  change Integrable (fun x:ℝ=>((Real.log x:ℂ)*(Real.exp (-x):ℂ)).re) _ at HR
  change Integrable (fun x:ℝ=>Real.log x*Real.exp (-x)) (volume.restrict (Set.Ioi 0))
  simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero] using HR

lemma logExp_integral : (∫ t:ℝ in Set.Ioi 0,logExp t) = -Real.eulerMascheroniConstant := by
  have h := Complex.hasDerivAt_GammaIntegral (s:=1) (by norm_num)
  have hg : HasDerivAt Complex.GammaIntegral (-(Real.eulerMascheroniConstant:ℂ)) 1 :=
    Complex.hasDerivAt_Gamma_one.congr_of_eventuallyEq (by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show (0:ℝ)<(1:ℂ).re by norm_num)] with z hz
      exact (Complex.Gamma_eq_integral hz).symm)
  have he := h.unique hg
  simp only [sub_self,Complex.cpow_zero,one_mul,←Complex.ofReal_mul] at he
  rw [integral_complex_ofReal] at he
  exact_mod_cast he

lemma logExp_interval (a b : ℝ) : IntervalIntegrable logExp volume a b := by
  exact intervalIntegral.intervalIntegrable_log'.mul_continuousOn
    (show ContinuousOn (fun t:ℝ=>Real.exp (-t)) (uIcc a b) by fun_prop)

/-- Exponential integral E₁, defined by an ordinary integrable logarithmic
kernel. This representation also controls the constant in its UV expansion. -/
def expTail (x : ℝ) := -Real.eulerMascheroniConstant - (∫ t:ℝ in (0:ℝ)..x,logExp t) -
  Real.exp (-x)*Real.log x

lemma expTail_integral (x : ℝ) (hx : 0≤x) : expTail x =
    (∫ t:ℝ in Set.Ioi x,logExp t)-Real.exp (-x)*Real.log x := by
  rw [expTail,←logExp_integral,←intervalIntegral.integral_Ioi_sub_Ioi logExp_integrable hx]
  ring

lemma expTail_deriv (x : ℝ) (hx : x≠0) :
    HasDerivAt expTail (-Real.exp (-x)/x) x := by
  have hc : ContinuousAt logExp x := by unfold logExp; fun_prop
  have hi := intervalIntegral.integral_hasDerivAt_right (logExp_interval 0 x)
    (show AEStronglyMeasurable logExp volume from (by unfold logExp; fun_prop)).stronglyMeasurableAtFilter hc
  have he := (((hasDerivAt_id' x).neg).exp).mul (Real.hasDerivAt_log hx)
  convert! (hi.const_sub (-Real.eulerMascheroniConstant)).sub he using 1
  simp only [logExp,Pi.neg_apply]
  field_simp
  ring

lemma expTail_small : Tendsto (fun x:ℝ=>expTail x+Real.log x) (𝓝[>] 0)
    (𝓝 (-Real.eulerMascheroniConstant)) := by
  have hi : Tendsto (fun x:ℝ=>∫ t:ℝ in (0:ℝ)..x,logExp t) (𝓝 (0:ℝ)) (𝓝 0) := by
    have h := intervalIntegral.continuous_primitive (fun a b=>logExp_interval a b) 0
    simpa using h.tendsto (0:ℝ)
  have he : Tendsto (fun x:ℝ=>(1-Real.exp (-x))/x) (𝓝[≠] 0) (𝓝 1) := by
    have h := ((hasDerivAt_id' (0:ℝ)).neg.exp.const_sub 1).tendsto_slope
    norm_num only [Pi.neg_apply,neg_zero,Real.exp_zero,one_mul,neg_neg] at h
    convert! h using 1
    funext x
    simp only [_root_.slope,vsub_eq_sub,neg_zero,Real.exp_zero,sub_self,sub_zero,smul_eq_mul]
    ring
  have hx : Tendsto (fun x:ℝ=>x*Real.log x) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Real.continuous_mul_log.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have ht := (he.mono_left (nhdsWithin_mono _ (fun x hx=>(ne_of_gt hx)))).mul hx
  have hh := (((tendsto_const_nhds (x:= -Real.eulerMascheroniConstant)).sub (hi.mono_left nhdsWithin_le_nhds)).add ht)
  simp only [sub_zero,mul_zero,add_zero] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  unfold expTail
  have hx0 : x≠0 := ne_of_gt hx
  field_simp [hx0]
  ring

lemma exp_log_large : Tendsto (fun x:ℝ=>Real.exp (-x)*Real.log x) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hl := isLittleO_log_rpow_atTop (show (0:ℝ)<1 by norm_num)
  have hv := hl.tendsto_div_nhds_zero
  simp only [Real.rpow_one,pow_one] at hv h
  have hh := h.mul hv
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
  field_simp

lemma expTail_large : Tendsto expTail atTop (𝓝 0) := by
  have h := (tendsto_integral_Ioi_zero (f:=logExp) (μ:=volume) tendsto_id).sub exp_log_large
  simp only [sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
  exact (expTail_integral x hx).symm
end YMReview.NovemberMatching.GhostMellin
