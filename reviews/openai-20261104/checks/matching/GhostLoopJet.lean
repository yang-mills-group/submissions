import GhostLoopContinuation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic
/-!
# Actual regulator derivative of the submitted ghost loop

Derives the first continued Taylor coefficient from the source integral,
then uses source covariance and homogeneity to cover every tensor component.
The independent SubmittedRegulatorJetTest is discharged here.
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
namespace YMReview.NovemberMatching.GhostJet
open GhostRadial GhostContinuation Shine Hem Mell

lemma compact_iterated (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (fun x => ∫ t : ℝ in (0:ℝ)..1, f (t,x)) x =
      ∫ t : ℝ in (0:ℝ)..1, iteratedDeriv j (fun x=>f (t,x)) x := by
  have h := Heat.Lot mint cour1 hf
  simp only [iteratedDeriv,intervalIntegral.integral_of_le zero_le_one]
  rw [show iteratedFDeriv ℝ j (fun x => ∫ t : ℝ in Set.Ioc 0 1, f (t,x)) x = _ from
    congrFun (h.identity j) x,ContinuousMultilinearMap.integral_apply (h.integ j x)]

def ratio (t : ℝ) := t^2/ν t
lemma ratio_lt_one (t : ℝ) : ratio t<1 := by
  rw [ratio,div_lt_one (ν_pos t)]
  unfold ν
  linarith
lemma ratio_complement (t : ℝ) : 1-ratio t = (ν t)⁻¹ := by
  unfold ratio ν
  field_simp
  ring
lemma ratio_gauss (t : ℝ) : gaussS (ν t) = (1-ratio t)/2 := by
  rw [ratio_complement]
  unfold gaussS
  field_simp
lemma ratio_slope (t : ℝ) : SquareShift.slope t = -ratio t := rfl

lemma ratio_derivative (t : ℝ) : HasDerivAt ratio (2*t/(ν t)^2) t := by
  have hν : HasDerivAt ν (2*t) t := by
    convert! (hasDerivAt_pow 2 t).const_add 1 using 1
    norm_num
  convert! (hasDerivAt_pow 2 t).div hν (ν_pos t).ne' using 1
  unfold ν
  field_simp
  ring

lemma ratio_interval (t : ℝ) (ht : t∈Icc (0:ℝ) 1) : ratio t∈Icc (0:ℝ) (1/2:ℝ) := by
  constructor
  · exact div_nonneg (sq_nonneg t) (ν_pos t).le
  rw [ratio,div_le_iff₀ (ν_pos t)]
  unfold ν
  nlinarith [ht.1,ht.2]

lemma parameter_substitution (f : ℝ → ℝ) (hf : ContinuousOn f (Icc (0:ℝ) (1/2:ℝ))) :
    (∫ t : ℝ in (0:ℝ)..1, f (ratio t)*(2*t/(ν t)^2)) = ∫ u : ℝ in (0:ℝ)..(1/2:ℝ), f u := by
  have h := intervalIntegral.integral_comp_mul_deriv' (a:=(0:ℝ)) (b:=1)
    (fun t _ => ratio_derivative t) (show ContinuousOn (fun t:ℝ=>2*t/(ν t)^2) (uIcc 0 1) from
      (by apply Continuous.continuousOn; unfold ν; fun_prop (disch:=intro; positivity)))
    (g:=f) (hf.mono (by rintro _ ⟨t,ht,rfl⟩; exact ratio_interval t (by simpa using ht)))
  simpa [Function.comp_def,ratio,ν,show (1:ℝ)+1=2 by norm_num] using h

def weight (z t : ℝ) := t^3*volume4 t*(ν t)^(-z)
def localValue (z v t : ℝ) := weight z t *
  (GhostLoopFinite.coeffB (4+2*z) (ratio t) 1 v-ratio t*GhostLoopFinite.coeffA (4+2*z) (ratio t) 1)
def density (z v t x : ℝ) := weight z t * Real.exp (-ratio t*x^2) *
  (GhostLoopFinite.coeffA (4+2*z) (ratio t) 1+
    GhostLoopFinite.coeffB (4+2*z) (ratio t) 1 v*x^2+
    GhostLoopFinite.coeffC (4+2*z) (ratio t) 1 v*x^4+GhostLoopFinite.coeffD (ratio t) v*x^6)

lemma continued_density (z p r x : ℝ) :
    continuedValue z 1 p r 1 x = ∫ t : ℝ in (0:ℝ)..1, density z (p*r) t x := by
  unfold continuedValue
  simp_rw [continued_moment]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [ratio_gauss,ratio_slope,show -ratio t+1=1-ratio t by ring,
    GhostLoopFinite.moment_expansion]
  unfold density prefactor weight
  rw [ratio_slope]
  simp only [mul_one]
  ring

lemma density_smooth (z v : ℝ) : ContDiff ℝ ∞ (fun tx : ℝ × ℝ => density z v tx.1 tx.2) := by
  unfold density weight GhostLoopFinite.coeffA GhostLoopFinite.coeffB GhostLoopFinite.coeffC GhostLoopFinite.coeffD
    ratio volume4 ν
  fun_prop (disch:= intros; positivity)

lemma density_second (z v t : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => density z v t x) 0 = 2*localValue z v t := by
  unfold density
  rw [show (fun x:ℝ=>weight z t*Real.exp (-ratio t*x^2)*
      (GhostLoopFinite.coeffA (4+2*z) (ratio t) 1+
       GhostLoopFinite.coeffB (4+2*z) (ratio t) 1 v*x^2+
       GhostLoopFinite.coeffC (4+2*z) (ratio t) 1 v*x^4+GhostLoopFinite.coeffD (ratio t) v*x^6)) =
      fun x => weight z t*(Real.exp (-ratio t*x^2)*
      (GhostLoopFinite.coeffA (4+2*z) (ratio t) 1+
       GhostLoopFinite.coeffB (4+2*z) (ratio t) 1 v*x^2+
       GhostLoopFinite.coeffC (4+2*z) (ratio t) 1 v*x^4+GhostLoopFinite.coeffD (ratio t) v*x^6)) from by funext x; ring,
    iteratedDeriv_const_mul,sample_sextic]
  · unfold localValue
    ring
  · fun_prop

lemma continued_second (z p r : ℝ) :
    iteratedDeriv 2 (fun x : ℝ => continuedValue z 1 p r 1 x) 0 =
      2*(∫ t : ℝ in (0:ℝ)..1, localValue z (p*r) t) := by
  simp_rw [continued_density]
  rw [compact_iterated _ (density_smooth z (p*r))]
  simp_rw [density_second,intervalIntegral.integral_const_mul]

/-- The actual continued top Taylor term at any unit physical momentum. -/
theorem actual_high_real (G : Gauge) (p : SectorP 0) (hp : p.sq=1) (i : L 0)
    (a b : G.ColorIndex) (z : ℝ) (hz : -1<z) :
    highTensor 4 (TwoPoint.ratePair G true true) (z:ℂ) 0 (TwoPoint.word i i a b p) =
      4*(∑ d : G.ColorIndex,angle d a b)*
        Complex.exp ((z:ℂ)*((Real.log Real.pi-2*Real.log (2*Real.pi):ℝ):ℂ)) *
        ((∫ t : ℝ in (0:ℝ)..1, localValue z ((p i)*(p i)) t) : ℝ) := by
  unfold highTensor
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [TwoPoint.torch_equiv]
  simp_rw [show ∀ x:ℝ,TwoPoint.ratePair G true true (z:ℂ) 0 (TwoPoint.word i i a b (x • p)) = _ from
    fun x=>actual_force_scaled G p i a b z hz x,hp,read_const]
  have hs : ContDiff ℝ ∞ (fun x:ℝ=>continuedValue z 1 (p i) (p i) 1 x) := by
    simp_rw [continued_density,intervalIntegral.integral_of_le zero_le_one]
    exact (Heat.Lot mint cour1 (density_smooth z (p i*p i))).contDiff
  rw [TwoPoint.cast_price _ hs,continued_second]
  norm_num
  ring


/-- Extract the actual source Taylor coefficient from a derivative on the
real regulator axis. The punctured holomorphic germ fixes this derivative. -/
lemma ruby_real_derivative {G : Gauge} {f : ℂ → Mob G} (hl : Shine.Lift f (f 0))
    {m : ℕ} (w : List (Shore G m)) (D : ℂ)
    (hd : HasDerivAt (fun z : ℝ => f (z:ℂ) m w) D 0) : ruby f 1 m w = D := by
  obtain ⟨H,hH,hS⟩ := (Rub (show Shine.Live f from ⟨_,hl⟩) 1)
  rw [Shine.Lift.unique hH hl] at hS
  have hs := (Shine.Lift.wind hS) m w
  have he : Tendsto (fun z : ℝ => (z:ℂ)) (𝓝[≠] (0:ℝ)) Shine.dotty := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using hz
  have hh := hs.comp he
  apply tendsto_nhds_unique hh
  convert! hd.tendsto_slope using 1
  funext z
  simp [Shine.slip,_root_.slope,Complex.real_smul]

def jetLocal (v t : ℝ) := t^3*volume4 t *
  (GhostLoopFinite.jetB (ratio t) 1 v-ratio t*GhostLoopFinite.jetA (ratio t) 1 -
    Real.log (ν t)*(GhostLoopFinite.coeffB 4 (ratio t) 1 v-ratio t*GhostLoopFinite.coeffA 4 (ratio t) 1))

lemma localValue_smooth (v : ℝ) : ContDiff ℝ ∞ (fun tz : ℝ × ℝ => localValue tz.2 v tz.1) := by
  unfold localValue weight GhostLoopFinite.coeffA GhostLoopFinite.coeffB ratio volume4 ν
  fun_prop (disch:=intros; positivity)

lemma localValue_derivative (v t : ℝ) :
    HasDerivAt (fun z : ℝ => localValue z v t) (jetLocal v t) 0 := by
  have he : (fun z : ℝ => weight z t) =
    fun z : ℝ => t^3*volume4 t*Real.exp (-z*Real.log (ν t)) := by
    funext z
    rw [weight,Real.rpow_def_of_pos (ν_pos t)]
    congr 2
    ring
  have hw : HasDerivAt (fun z : ℝ => weight z t) (-Real.log (ν t)*(t^3*volume4 t)) 0 := by
    rw [he]
    convert! ((((hasDerivAt_id' (0:ℝ)).neg).mul_const (Real.log (ν t))).exp).const_mul (t^3*volume4 t) using 1
    simp
    ring
  have h := hw.mul (GhostLoopFinite.local_taylor_derivative (ratio t) 1 v)
  apply h.congr_deriv
  simp only [weight,neg_zero,Real.rpow_zero,mul_one,jetLocal]
  ring

lemma integrated_jet (v : ℝ) :
    HasDerivAt (fun z : ℝ => ∫ t : ℝ in (0:ℝ)..1, localValue z v t)
      (∫ t : ℝ in (0:ℝ)..1, jetLocal v t) 0 := by
  have h := compact_derivative _ (localValue_smooth v) 0
  simp_rw [(localValue_derivative v _).deriv] at h
  exact h

def conventionConstant : ℝ := Real.log Real.pi-2*Real.log (2*Real.pi)
def jetWithScale (v t : ℝ) := jetLocal v t + conventionConstant*localValue 0 v t

lemma local_continuous (z v : ℝ) : Continuous (localValue z v) := by
  exact (localValue_smooth v).continuous.comp (show Continuous (fun t:ℝ=>(t,z)) by fun_prop)
lemma jet_continuous (v : ℝ) : Continuous (jetLocal v) := by
  unfold jetLocal ratio volume4 ν GhostLoopFinite.jetB GhostLoopFinite.jetA GhostLoopFinite.coeffB GhostLoopFinite.coeffA
  fun_prop (disch:=intros; positivity)

/-- The derivative of the actual top Taylor term, before the last elementary
heat-parameter integration. -/
theorem actual_high_derivative (G : Gauge) (p : SectorP 0) (hp : p.sq=1) (i : L 0)
    (a b : G.ColorIndex) :
    HasDerivAt (fun z : ℝ => highTensor 4 (TwoPoint.ratePair G true true) (z:ℂ) 0 (TwoPoint.word i i a b p))
      (4*(∑ d : G.ColorIndex,angle d a b)*
        ((∫ t : ℝ in (0:ℝ)..1, jetWithScale (p i*p i) t) : ℝ)) 0 := by
  let v := p i*p i
  have hx := (((hasDerivAt_id' (0:ℝ)).mul_const conventionConstant).exp).mul (integrated_jet v)
  have hc := ((Complex.ofRealCLM.hasFDerivAt).comp_hasDerivAt 0 hx).const_mul
    (4*(∑ d : G.ColorIndex,angle d a b))
  have hj : (∫ t : ℝ in (0:ℝ)..1, jetWithScale v t) =
      (∫ t : ℝ in (0:ℝ)..1, jetLocal v t) + conventionConstant*(∫ t : ℝ in (0:ℝ)..1, localValue 0 v t) := by
    unfold jetWithScale
    rw [intervalIntegral.integral_add ((jet_continuous v).intervalIntegrable _ _)
      (((local_continuous 0 v).const_mul _).intervalIntegrable _ _),intervalIntegral.integral_const_mul]
  apply (hc.congr_deriv (by
    simp only [zero_mul,Real.exp_zero,one_mul]
    change (4*(∑ d : G.ColorIndex,angle d a b))*
      (((conventionConstant*(∫ t : ℝ in (0:ℝ)..1,localValue 0 v t))+
        (∫ t : ℝ in (0:ℝ)..1,jetLocal v t)):ℝ) = _
    rw [hj]
    push_cast
    ring)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds (show (0:ℝ)∈Set.Ioi (-1:ℝ) by norm_num)] with z hz
  rw [actual_high_real G p hp i a b z hz]
  dsimp only [Function.comp_apply,Pi.mul_apply,Complex.ofRealCLM_apply]
  push_cast
  unfold conventionConstant v
  push_cast
  ring


lemma convention_log : conventionConstant = -Real.log (4*Real.pi) := by
  unfold conventionConstant
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) Real.pi_pos.ne',
    Real.log_mul (by norm_num : (4:ℝ)≠0) Real.pi_pos.ne',
    show Real.log (4:ℝ)=2*Real.log 2 from by rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num]
  ring

def jetParameter (u : ℝ) := GhostLoopFinite.Jdelta u+
  GhostLoopFinite.Wlog u*Real.log (1-u)-Real.log (4*Real.pi)*GhostLoopFinite.Wlog u

lemma jetParameter_continuous : Continuous jetParameter := by
  unfold jetParameter
  exact ((show Continuous GhostLoopFinite.Jdelta from by unfold GhostLoopFinite.Jdelta; fun_prop).add
    GhostLoopFinite.continuous_reflected_log).sub
      ((show Continuous GhostLoopFinite.Wlog from by unfold GhostLoopFinite.Wlog; fun_prop).const_mul _)

lemma jetParameter_integral : (∫ u : ℝ in (0:ℝ)..(1/2:ℝ),jetParameter u) =
    11/288+Real.log (2*Real.pi)/12 := by
  have hj : Continuous GhostLoopFinite.Jdelta := by unfold GhostLoopFinite.Jdelta; fun_prop
  have hw : Continuous GhostLoopFinite.Wlog := by unfold GhostLoopFinite.Wlog; fun_prop
  unfold jetParameter
  have ha : IntervalIntegrable (fun u => GhostLoopFinite.Jdelta u+GhostLoopFinite.Wlog u*Real.log (1-u)) volume 0 (1/2) :=
    (hj.add GhostLoopFinite.continuous_reflected_log).intervalIntegrable _ _
  have hb : IntervalIntegrable (fun u => Real.log (4*Real.pi)*GhostLoopFinite.Wlog u) volume 0 (1/2) :=
    (hw.const_mul _).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub ha hb,intervalIntegral.integral_add (hj.intervalIntegrable _ _)
    (GhostLoopFinite.continuous_reflected_log.intervalIntegrable _ _),intervalIntegral.integral_const_mul]
  exact GhostLoopFinite.regulator_jet_parameter

lemma jet_parameter_change (v t : ℝ) :
    jetWithScale v t = logArea/4*(1+2*v)*jetParameter (ratio t)*(2*t/(ν t)^2) := by
  have hl : Real.log (1-ratio t) = -Real.log (ν t) := by rw [ratio_complement,Real.log_inv]
  unfold jetWithScale jetParameter jetLocal localValue weight
  simp only [neg_zero,Real.rpow_zero,mul_one,mul_zero,add_zero]
  rw [hl,convention_log]
  unfold GhostLoopFinite.Jdelta GhostLoopFinite.Wlog GhostLoopFinite.jetB GhostLoopFinite.jetA
    GhostLoopFinite.coeffB GhostLoopFinite.coeffA volume4 logArea ratio ν
  generalize Real.log (1+t^2) = l
  generalize Real.log (4*Real.pi) = k
  field_simp
  ring

lemma integrated_jet_value (v : ℝ) :
    (∫ t : ℝ in (0:ℝ)..1,jetWithScale v t) =
      logArea/4*(1+2*v)*(11/288+Real.log (2*Real.pi)/12) := by
  simp_rw [jet_parameter_change,mul_assoc (logArea/4*(1+2*v)),intervalIntegral.integral_const_mul]
  rw [parameter_substitution jetParameter jetParameter_continuous.continuousOn,jetParameter_integral]

/-- Exact source coefficient, for every unit momentum and diagonal tensor slot. -/
theorem submitted_jet_unit (G : Gauge) (hG : G.Simple) (p : SectorP 0) (hp : p.sq=1) (i : L 0)
    (a b : G.ColorIndex) :
    ruby (highTensor 4 (TwoPoint.ratePair G true true)) 1 0 (TwoPoint.word i i a b p) =
      (if a=b then (G.casimir:ℂ) else 0) *
        (1+2*(p i:ℂ)*(p i:ℂ))/(16*(Real.pi:ℂ)^2) *
          (11/288+(Real.log (2*Real.pi):ℂ)/12) := by
  have hl := (close_form (G:=G) (cursor true)
    (firstResult (interaction G 1) (interaction G 1) (cursor true))).2
  have he := ruby_real_derivative (high_lift hl 4) (TwoPoint.word i i a b p) _
    (actual_high_derivative G p hp i a b)
  change ruby (highTensor 4 (TwoPoint.ratePair G true true)) 1 0 (TwoPoint.word i i a b p) = _ at he
  rw [he,integrated_jet_value,sums_angles hG]
  unfold logArea
  push_cast
  ring

/-- Symmetry and homogeneity pass to each actual regulator coefficient. -/
lemma pick_home {G : Gauge} {f : Coat G} {F : Mob G} {j h : ℕ}
    (hp : Pick j f F) (he : ∀ᶠ z in dotty, Home (f z) h) : Home F h := by
  intro s
  apply (hp.mount (-(h:ℂ)) s).unique
  exact hp.congr (he.mono fun z hz => (hz s).symm)

lemma pick_sturdy {G : Gauge} {f : Coat G} {F : Mob G} {j : ℕ} {b : Bool}
    (hp : Pick j f F) (he : ∀ᶠ z in dotty, Sturdy b (f z)) : Sturdy b F := by
  induction j generalizing f with
  | zero => exact Lift.acre hp Wind.time he
  | succ j ih =>
    obtain ⟨H,hH,hp⟩ := hp
    have hS : Sturdy b H := Lift.acre hH Wind.time he
    apply ih hp
    filter_upwards [he] with z hz
    exact (sturdy b G).smul_mem _ ((sturdy b G).sub_mem hz hS)

lemma high_jet_properties (G : Gauge) :
    Sturdy true (ruby (highTensor 4 (TwoPoint.ratePair G true true)) 1) ∧
    Home (ruby (highTensor 4 (TwoPoint.ratePair G true true)) 1) 4 ∧
    kPrice (ruby (highTensor 4 (TwoPoint.ratePair G true true)) 1) := by
  have hl := (close_form (G:=G) (cursor true)
    (firstResult (interaction G 1) (interaction G 1) (cursor true))).2
  have hh := high_lift hl 4
  have hp := Rub (show Live (highTensor 4 (TwoPoint.ratePair G true true)) from ⟨_,hh⟩) 1
  have hf : ∀ᶠ z in dotty, Form0 true (TwoPoint.ratePair G true true z) := by
    filter_upwards [high0] with z hz
    unfold TwoPoint.ratePair
    rw [closeG_eq]
    exact (torn hz (TwoPoint.stem_form G true) ((cursor true).ok.forms true)).smul _
  refine ⟨pick_sturdy hp ?_,pick_home hp ?_,hp.price⟩
  · filter_upwards [hf] with z hz
    exact Sturdy_scale (need_true.jet hz.token hz.price 4) _
  · filter_upwards [hf] with z hz
    exact (Home.tad hz.price).smul _

/-- The actual regulator jet agrees with the independent formula, on every
momentum and tensor component, including all auxiliary sectors. -/
theorem submitted_jet (G : Gauge) (hG : G.Simple) (m : ℕ) (p : SectorP m)
    (i j : L m) (a b : G.ColorIndex) :
    ruby (highTensor 4 (TwoPoint.ratePair G true true)) 1 m (TwoPoint.word i j a b p) =
      (if a=b then (G.casimir:ℂ) else 0) *
        ((if i=j then (p.sq:ℂ) else 0)+2*(p i:ℂ)*(p j:ℂ))/(16*(Real.pi:ℂ)^2) *
          (11/288+(Real.log (2*Real.pi):ℂ)/12) := by
  obtain ⟨hs,hh,hp⟩ := high_jet_properties G
  rw [show ruby (highTensor 4 (TwoPoint.ratePair G true true)) 1 m (TwoPoint.word i j a b p) = _ from
    TwoPoint.summation_rule a b hs hh hp p i j]
  unfold TwoPoint.along TwoPoint.across TwoPoint.kinetic
  rw [submitted_jet_unit G hG _ TwoPoint.primary_sq,
    submitted_jet_unit G hG _ TwoPoint.primary_sq]
  simp only [show TwoPoint.zeroDirection 0=(0:Axis) from rfl,
    show TwoPoint.trans 0=(1:Axis) from rfl,TwoPoint.dotProbe,
    show kk (0:Axis) 0=1 from rfl,show kk (1:Axis) 0=0 from rfl,
    Complex.ofReal_one,Complex.ofReal_zero]
  unfold TwoPoint.tensor2
  split_ifs <;> ring

/-- Unconditional discharge of the independent regulator-jet target. -/
theorem submitted_regulator_jet_test (G : Gauge) : GhostLoopFinite.SubmittedRegulatorJetTest G := by
  intro hG a b p i j
  exact submitted_jet G hG 0 p i j a b
end YMReview.NovemberMatching.GhostJet

