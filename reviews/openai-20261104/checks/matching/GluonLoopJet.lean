import GluonLoopContinuation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
open YM YM.MS YM.MS.Arts YM.MS.ScaleForest
open Plane Koszul Heat Flux Landau Book Convolve Motif Halo
open Function Filter Set Finset MeasureTheory Real
open Tone Momentum Frame Wire Color Detect Native Native.Wilsonian City Logarithm Signal
open Landau.Detect.Mark Wind High Knobs Arc Rock Path Oceans Plum Alps Garment Pearl Train Shine Hem Mell
open YM.WilsonMS.BetaValue YM.WilsonMS.BetaValue.HeatPapers SquareShift
open scoped Topology ContDiff
namespace YMReview.NovemberMatching.GluonJet
open GluonCarpet GluonContinuation
local notation "e" => TwoPoint.primary 0

def c0 (z u:ℝ) := 4*(3+2*z)*(6+2*z)*(8+2*z)*((1-u)/2)^3
def c1 (long:Bool) (z u:ℝ) :=
  if long then ((1-u)/2)^2*((3+2*z)*(4*(6+2*z)*(u^2+(1-u)^2)-48*u*(1-u)+
    (1-2*u)^2*(6+2*z)*(12+2*z))-4*(3+2*z))
  else 4*((1-u)/2)^2*(2*(4+2*z)^2+(4+2*z)-5+
    (3+2*z)*((6+2*z)*(u^2+(1-u)^2)-4*u*(1-u)))
def c2 (long:Bool) (z u:ℝ) :=
  if long then ((1-u)/2)*((3+2*z)*(4*u^2*(1-u)^2-8*u*(1-u)*(1-2*u)^2+
    (1-2*u)^2*((4+2*z)*(u^2+(1-u)^2)-4*u*(1-u)))-(1-2*u)^2*(3+2*z))
  else 4*((1-u)/2)*((u^2+(1-u)^2)*(3+2*z)+(3+2*z)*u^2*(1-u)^2)
def c3 (long:Bool) (z u:ℝ) := if long then (3+2*z)*(1-2*u)^2*u^2*(1-u)^2 else 0

lemma moment_expansion (long:Bool) (z u x:ℝ) :
    GluonGaussian.moment long (4+2*z) (4+2*z) u (x^2) ((1-u)/2)=
      c0 z u+c1 long z u*x^2+c2 long z u*x^4+c3 long z u*x^6 := by
  cases long <;> simp only [GluonGaussian.moment,c0,c1,c2,c3,Bool.false_eq_true,if_false,if_true,
    GluonHeat.momentT,GluonHeat.momentL] <;> ring

def localValue (long:Bool) (z t:ℝ) := GhostJet.weight z t*(c1 long z (GhostJet.ratio t)-GhostJet.ratio t*c0 z (GhostJet.ratio t))
def density (long:Bool) (z t x:ℝ) := GhostJet.weight z t*Real.exp (-GhostJet.ratio t*x^2)*
  (c0 z (GhostJet.ratio t)+c1 long z (GhostJet.ratio t)*x^2+
    c2 long z (GhostJet.ratio t)*x^4+c3 long z (GhostJet.ratio t)*x^6)

lemma continued_density (long:Bool) (z x:ℝ) :
    GluonContinuation.continuedValue long z x=∫ t:ℝ in (0:ℝ)..1,density long z t x := by
  unfold GluonContinuation.continuedValue
  simp_rw [GluonContinuation.continued_moment]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [GhostJet.ratio_gauss,moment_expansion]
  unfold density GhostContinuation.prefactor GhostJet.weight
  rw [GhostJet.ratio_slope]
  simp only [mul_one]
  ring

lemma density_smooth (long:Bool) (z:ℝ) :
    ContDiff ℝ ∞ (fun tx:ℝ × ℝ=>density long z tx.1 tx.2) := by
  unfold density GhostJet.weight c0 c1 c2 c3 GhostJet.ratio volume4 ν
  cases long <;> simp only [Bool.false_eq_true,if_false,if_true] <;>
    fun_prop (disch:=intros;positivity)

lemma density_second (long:Bool) (z t:ℝ) :
    iteratedDeriv 2 (fun x:ℝ=>density long z t x) 0=2*localValue long z t := by
  unfold density
  rw [show (fun x:ℝ=>GhostJet.weight z t*Real.exp (-GhostJet.ratio t*x^2)*
      (c0 z (GhostJet.ratio t)+c1 long z (GhostJet.ratio t)*x^2+
        c2 long z (GhostJet.ratio t)*x^4+c3 long z (GhostJet.ratio t)*x^6)) =
      fun x=>GhostJet.weight z t*(Real.exp (-GhostJet.ratio t*x^2)*
      (c0 z (GhostJet.ratio t)+c1 long z (GhostJet.ratio t)*x^2+
        c2 long z (GhostJet.ratio t)*x^4+c3 long z (GhostJet.ratio t)*x^6)) from by funext x;ring,
    iteratedDeriv_const_mul,sample_sextic]
  · unfold localValue;ring
  · fun_prop

lemma continued_second (long:Bool) (z:ℝ) :
    iteratedDeriv 2 (fun x:ℝ=>GluonContinuation.continuedValue long z x) 0=
      2*(∫ t:ℝ in (0:ℝ)..1,localValue long z t) := by
  simp_rw [continued_density]
  rw [GhostJet.compact_iterated _ (density_smooth long z)]
  simp_rw [density_second,intervalIntegral.integral_const_mul]

theorem actual_high_real (G:Gauge) (long:Bool) (a b:G.ColorIndex) (z:ℝ) (hz:-(1/2:ℝ)<z) :
    highTensor 4 (TwoPoint.ratePair G false false) (z:ℂ) 0 (TwoPoint.word (axis long) (axis long) a b e)=
      -2*(∑ d:G.ColorIndex,angle d a b)*
      Complex.exp ((z:ℂ)*((Real.log Real.pi-2*Real.log (2*Real.pi):ℝ):ℂ))*
        ((∫ t:ℝ in (0:ℝ)..1,localValue long z t):ℝ) := by
  unfold highTensor
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [TwoPoint.torch_equiv]
  simp_rw [GluonContinuation.actual_force_real G long a b z _ hz,read_const]
  have hs : ContDiff ℝ ∞ (fun x:ℝ=>GluonContinuation.continuedValue long z x) := by
    simp_rw [continued_density,intervalIntegral.integral_of_le zero_le_one]
    exact (Heat.Lot mint cour1 (density_smooth long z)).contDiff
  rw [TwoPoint.cast_price _ hs,continued_second]
  norm_num
  ring

def localJet (long:Bool) (u:ℝ) :=
  (if long then ((1-u)/2)^2*(72*(u^2+(1-u)^2)-96*u*(1-u)+252*(1-2*u)^2-8)
  else 4*((1-u)/2)^2*(34+18*(u^2+(1-u)^2)-8*u*(1-u)))-u*720*((1-u)/2)^3

def localQuad (long:Bool) (u:ℝ) :=
  (if long then ((1-u)/2)^2*(16*(u^2+(1-u)^2)+84*(1-2*u)^2)
  else 4*((1-u)/2)^2*(8+4*(u^2+(1-u)^2)))-u*272*((1-u)/2)^3

def localCube (long:Bool) (u:ℝ) :=
  (if long then 8*((1-u)/2)^2*(1-2*u)^2 else 0)-u*32*((1-u)/2)^3

lemma local_expansion (long:Bool) (z u:ℝ) :
    c1 long z u-u*c0 z u=c1 long 0 u-u*c0 0 u+z*localJet long u+
      z^2*localQuad long u+z^3*localCube long u := by
  cases long <;> simp only [c0,c1,localJet,localQuad,localCube,Bool.false_eq_true,if_false,if_true] <;> ring

lemma local_taylor_derivative (long:Bool) (u:ℝ) :
    HasDerivAt (fun z:ℝ=>c1 long z u-u*c0 z u) (localJet long u) 0 := by
  rw [show (fun z:ℝ=>c1 long z u-u*c0 z u)=
      fun z=>c1 long 0 u-u*c0 0 u+z*localJet long u+z^2*localQuad long u+z^3*localCube long u from
        funext fun z=>local_expansion long z u]
  convert! ((((hasDerivAt_id' (0:ℝ)).mul_const (localJet long u)).const_add
    (c1 long 0 u-u*c0 0 u)).add ((hasDerivAt_pow 2 (0:ℝ)).mul_const (localQuad long u))).add
    ((hasDerivAt_pow 3 (0:ℝ)).mul_const (localCube long u)) using 1
  norm_num

def jetLocal (long:Bool) (t:ℝ) := t^3*volume4 t*
  (localJet long (GhostJet.ratio t)-Real.log (ν t)*(c1 long 0 (GhostJet.ratio t)-GhostJet.ratio t*c0 0 (GhostJet.ratio t)))
def jetWithScale (long:Bool) (t:ℝ) := jetLocal long t+GhostJet.conventionConstant*localValue long 0 t

lemma localValue_smooth (long:Bool) :
    ContDiff ℝ ∞ (fun tz:ℝ × ℝ=>localValue long tz.2 tz.1) := by
  unfold localValue GhostJet.weight c0 c1 GhostJet.ratio volume4 ν
  cases long <;> simp only [Bool.false_eq_true,if_false,if_true] <;>
    fun_prop (disch:=intros;positivity)

lemma localValue_derivative (long:Bool) (t:ℝ) :
    HasDerivAt (fun z:ℝ=>localValue long z t) (jetLocal long t) 0 := by
  have he : (fun z:ℝ=>GhostJet.weight z t)=fun z=>t^3*volume4 t*Real.exp (-z*Real.log (ν t)) := by
    funext z
    rw [GhostJet.weight,Real.rpow_def_of_pos (ν_pos t)]
    congr 2
    ring
  have hw : HasDerivAt (fun z:ℝ=>GhostJet.weight z t) (-Real.log (ν t)*(t^3*volume4 t)) 0 := by
    rw [he]
    convert! ((((hasDerivAt_id' (0:ℝ)).neg).mul_const (Real.log (ν t))).exp).const_mul (t^3*volume4 t) using 1
    simp
    ring
  have h:=hw.mul (local_taylor_derivative long (GhostJet.ratio t))
  apply h.congr_deriv
  simp only [GhostJet.weight,neg_zero,Real.rpow_zero,mul_one,jetLocal]
  ring

lemma integrated_jet (long:Bool) :
    HasDerivAt (fun z:ℝ=>∫ t:ℝ in (0:ℝ)..1,localValue long z t)
      (∫ t:ℝ in (0:ℝ)..1,jetLocal long t) 0 := by
  have h:=GhostContinuation.compact_derivative _ (localValue_smooth long) 0
  simp_rw [(localValue_derivative long _).deriv] at h
  exact h

lemma local_continuous (long:Bool) (z:ℝ) : Continuous (localValue long z) :=
  (localValue_smooth long).continuous.comp (show Continuous (fun t:ℝ=>(t,z)) by fun_prop)
lemma jet_continuous (long:Bool) : Continuous (jetLocal long) := by
  unfold jetLocal localJet c0 c1 GhostJet.ratio volume4 ν
  cases long <;> simp only [Bool.false_eq_true,if_false,if_true] <;>
    fun_prop (disch:=intros;positivity)

theorem actual_high_derivative (G:Gauge) (long:Bool) (a b:G.ColorIndex) :
    HasDerivAt (fun z:ℝ=>highTensor 4 (TwoPoint.ratePair G false false) (z:ℂ) 0
      (TwoPoint.word (axis long) (axis long) a b e))
      (-2*(∑ d:G.ColorIndex,angle d a b)*((∫ t:ℝ in (0:ℝ)..1,jetWithScale long t):ℝ)) 0 := by
  have hx:=(((hasDerivAt_id' (0:ℝ)).mul_const GhostJet.conventionConstant).exp).mul (integrated_jet long)
  have hc:=((Complex.ofRealCLM.hasFDerivAt).comp_hasDerivAt 0 hx).const_mul
    (-2*(∑ d:G.ColorIndex,angle d a b))
  have hj : (∫ t:ℝ in (0:ℝ)..1,jetWithScale long t)=
      (∫ t:ℝ in (0:ℝ)..1,jetLocal long t)+GhostJet.conventionConstant*(∫ t:ℝ in (0:ℝ)..1,localValue long 0 t) := by
    unfold jetWithScale
    rw [intervalIntegral.integral_add ((jet_continuous long).intervalIntegrable _ _)
      (((local_continuous long 0).const_mul _).intervalIntegrable _ _),intervalIntegral.integral_const_mul]
  apply (hc.congr_deriv (by
    simp only [zero_mul,Real.exp_zero,one_mul]
    change (-2*(∑ d:G.ColorIndex,angle d a b))*
      (((GhostJet.conventionConstant*(∫ t:ℝ in (0:ℝ)..1,localValue long 0 t))+
        (∫ t:ℝ in (0:ℝ)..1,jetLocal long t)):ℝ)=_
    rw [hj]
    push_cast
    ring)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds (show (0:ℝ)∈Set.Ioi (-(1/2:ℝ)) by norm_num)] with z hz
  rw [actual_high_real G long a b z hz]
  dsimp only [Function.comp_apply,Pi.mul_apply,Complex.ofRealCLM_apply]
  push_cast
  unfold GhostJet.conventionConstant
  push_cast
  ring

end YMReview.NovemberMatching.GluonJet
#print axioms YMReview.NovemberMatching.GluonJet.actual_high_derivative
