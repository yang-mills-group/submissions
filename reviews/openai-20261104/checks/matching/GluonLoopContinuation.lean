import GluonLoopRadial
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
open scoped Topology ContDiff
namespace YMReview.NovemberMatching.GluonContinuation
open GluonCarpet GluonRadial GhostContinuation
local notation "e" => TwoPoint.primary 0

def coeffA (long:Bool) (z x t:ℝ) := prefactor 1 x t*
  GluonGaussian.moment long 4 (4+2*z) (GhostJet.ratio t) (x^2) (gaussS (ν t))
def coeffB (long:Bool) (z x t:ℝ) := prefactor 1 x t*
  GluonGaussian.radial long (4+2*z) (GhostJet.ratio t) (x^2) (gaussS (ν t))
def coeffC (long:Bool) (z x t:ℝ) := prefactor 1 x t*
  GluonGaussian.fourth long (4+2*z) (GhostJet.ratio t) (x^2) (gaussS (ν t))
def radialValue (long:Bool) (z x t R:ℝ) :=
  radialDerivative (ν t) (coeffA long z x t) (coeffB long z x t) (coeffC long z x t) R

def continuedValue (long:Bool) (z x:ℝ) := ∫ t:ℝ in (0:ℝ)..1,
  (ν t)^(-z)*coeffA long z x t+z*(ν t)^(-z-1)*coeffB long z x t+
    z*(z+1)*(ν t)^(-z-2)*coeffC long z x t

lemma weighted_heat_derivative (long:Bool) (z x t R:ℝ) :
    HasDerivAt (fun R:ℝ=>Real.exp (-(ν t*R^2))*heatValue long (4+2*z) R x t)
      (R*radialValue long z x t R) R := by
  convert! density_derivative (ν t) (coeffA long z x t) (coeffB long z x t) (coeffC long z x t) R using 1
  funext R
  unfold GluonRadial.heatValue coeffA coeffB coeffC
  ring

lemma weighted_heat_smooth (long:Bool) (z x:ℝ) :
    ContDiff ℝ ∞ (fun v:ℝ × ℝ=>Real.exp (-(ν v.1*v.2^2))*heatValue long (4+2*z) v.2 x v.1) := by
  unfold GluonRadial.heatValue prefactor GluonGaussian.moment GluonGaussian.radial GluonGaussian.fourth
  cases long <;> simp only [Bool.false_eq_true,if_false,if_true]
  all_goals
    dsimp only [GluonHeat.momentT,GluonHeat.radialT,GluonHeat.fourthT,GluonHeat.momentL,GluonHeat.radialL,GluonHeat.fourthL,
      GhostJet.ratio,gaussS,SquareShift.slope,volume4,ν]
    fun_prop (disch:=intros;positivity)

lemma integrated_radial_derivative (long:Bool) (z x R:ℝ) :
    HasDerivAt (fun R:ℝ=>∫ t:ℝ in (0:ℝ)..1,Real.exp (-(ν t*R^2))*heatValue long (4+2*z) R x t)
      (R*(∫ t:ℝ in (0:ℝ)..1,radialValue long z x t R)) R := by
  have h:=compact_derivative _ (weighted_heat_smooth long z x) R
  simp_rw [(weighted_heat_derivative long z x _ _).deriv,intervalIntegral.integral_const_mul] at h
  exact h

lemma carpet_scaled (G:Gauge) (long:Bool) (a b:G.ColorIndex) (R x y z:ℝ) :
    loopCarpet (cursor false).half (TwoPoint.stemPair G false) (z:ℂ)
      (TwoPoint.word (axis long) (axis long) a b (x • e)) (R,y) =
    (4*(∑ d:G.ColorIndex,angle d a b)/(room:ℂ))*
      ((∫ t:ℝ in (0:ℝ)..1,Real.exp (-(ν t*R^2))*heatValue long (4+2*z) R (y*x) t):ℝ) := by
  rw [←GluonRadial.actual_carpet_evaluated G long a b R (y*x) z]
  unfold loopCarpet
  simp_rw [GhostRadial.ray_word,smul_smul]

lemma actual_chop (G:Gauge) (long:Bool) (a b:G.ColorIndex) (z x R:ℝ) (hz:-(1/2:ℝ)<z) (hR:0<R) :
    chop (loopCarpet (cursor false).half (TwoPoint.stemPair G false) (z:ℂ)
      (TwoPoint.word (axis long) (axis long) a b (x • e))) (R,1) =
      (4*(∑ d:G.ColorIndex,angle d a b)/(room:ℂ))*
        ((∫ t:ℝ in (0:ℝ)..1,radialValue long z x t R):ℝ) := by
  let F:=loopCarpet (cursor false).half (TwoPoint.stemPair G false) (z:ℂ)
    (TwoPoint.word (axis long) (axis long) a b (x • e))
  let c:ℂ:=4*(∑ d:G.ColorIndex,angle d a b)/(room:ℂ)
  have hzT : (z:ℂ)∈Town := by change 0<2*z+1; linarith
  have hgood:=((loop_converges ((cursor false).ok.forms true) (TwoPoint.stem_form G false)
    hzT (TwoPoint.word (axis long) (axis long) a b (x • e))).2.1 0)
  have hs : ContDiff ℝ ∞ F := by simpa [F,pruning] using! hgood.1.smooth ()
  have hr : Reflect F := by simpa [F,pruning] using! hgood.2.1
  have hd:=integrated_radial_derivative long z x R
  have hc:=((Complex.ofRealCLM.hasFDerivAt).comp_hasDerivAt R hd).const_mul c
  have hc' : HasDerivAt (fun R:ℝ=>F (R,1))
      (c*((R*(∫ t:ℝ in (0:ℝ)..1,radialValue long z x t R)):ℝ)) R := by
    convert! hc using 1
    funext R
    simpa only [one_mul,F,c,Function.comp_def,Complex.ofRealCLM_apply] using carpet_scaled G long a b R x 1 z
  apply mul_left_cancel₀ (show (R:ℂ)≠0 by exact_mod_cast hR.ne')
  calc
    (R:ℂ)*chop F (R,1)=Arc.d F (R,1) := by
      simpa only [Complex.real_smul] using restore hr hs R 1
    _=c*((R*(∫ t:ℝ in (0:ℝ)..1,radialValue long z x t R)):ℝ) :=
      (Arc.dr hs 1 R).unique hc'
    _=_ := by push_cast; ring

lemma coeffs_continuous (long:Bool) (z x:ℝ) :
    Continuous (coeffA long z x) ∧ Continuous (coeffB long z x) ∧ Continuous (coeffC long z x) := by
  unfold coeffA coeffB coeffC prefactor GluonGaussian.moment GluonGaussian.radial GluonGaussian.fourth
  cases long <;> simp only [Bool.false_eq_true,if_false,if_true]
  all_goals
    dsimp only [GluonHeat.momentT,GluonHeat.radialT,GluonHeat.fourthT,GluonHeat.momentL,GluonHeat.radialL,GluonHeat.fourthL,
      GhostJet.ratio,gaussS,SquareShift.slope,volume4,ν]
    exact ⟨by fun_prop (disch:=intros;positivity),by fun_prop (disch:=intros;positivity),by fun_prop (disch:=intros;positivity)⟩

lemma actual_radial_integral (long:Bool) (z x:ℝ) (hz:-1<z) :
    -(∫ R:ℝ,R^(2*z+1)*(∫ t:ℝ in (0:ℝ)..1,radialValue long z x t R) ∂μhalf)/Real.Gamma (z+1)=
      continuedValue long z x := by
  simp_rw [←intervalIntegral.integral_const_mul]
  obtain ⟨ha,hb,hc⟩:=coeffs_continuous long z x
  exact radial_family_integral z hz _ _ _ ha hb hc

lemma close_physical (G:Gauge) (F:Mob G) (w:List (Shore G 0)) (z:ℂ) :
    closeG (cursor false).half z 0 F 0 w= -feeD z*
      (∫ R:ℝ,(R:ℂ)^(2*z+1)*chop (loopCarpet (cursor false).half F z w) (R,1) ∂μhalf) := by
  rw [closeG]
  simp [gage,pruning,tenorK,Pearl.weight,Alps.amount,smul_eq_mul]

theorem actual_force_real (G:Gauge) (long:Bool) (a b:G.ColorIndex) (z x:ℝ) (hz:-(1/2:ℝ)<z) :
    TwoPoint.ratePair G false false (z:ℂ) 0 (TwoPoint.word (axis long) (axis long) a b (x • e)) =
      4*(∑ d:G.ColorIndex,angle d a b)*
        Complex.exp ((z:ℂ)*((Real.log Real.pi-2*Real.log (2*Real.pi):ℝ):ℂ))*
          (continuedValue long z x:ℝ) := by
  let c:ℂ:=4*(∑ d:G.ColorIndex,angle d a b)/(room:ℂ)
  let J:ℝ:=∫ R:ℝ,R^(2*z+1)*(∫ t:ℝ in (0:ℝ)..1,radialValue long z x t R) ∂μhalf
  have hJ : -J/Real.Gamma (z+1)=continuedValue long z x :=
    actual_radial_integral long z x (by linarith)
  unfold TwoPoint.ratePair
  rw [close_physical]
  have hi : (fun R:ℝ=>(R:ℂ)^(2*(z:ℂ)+1)*chop (loopCarpet (cursor false).half
      (TwoPoint.stemPair G false) (z:ℂ) (TwoPoint.word (axis long) (axis long) a b (x • e))) (R,1)) =ᵐ[μhalf]
      (fun R=>c*((R^(2*z+1)*(∫ t:ℝ in (0:ℝ)..1,radialValue long z x t R)):ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with R hR
    rw [actual_chop G long a b z x R hz hR]
    have hp : (R:ℂ)^(2*(z:ℂ)+1)=((R^(2*z+1):ℝ):ℂ) := by
      rw [show 2*(z:ℂ)+1=((2*z+1:ℝ):ℂ) by push_cast; rfl,←Complex.ofReal_cpow hR.le]
    rw [hp]
    change _=c*((R^(2*z+1)*(∫ t:ℝ in (0:ℝ)..1,radialValue long z x t R)):ℝ)
    push_cast
    ring
  rw [integral_congr_ae hi,MeasureTheory.integral_const_mul,integral_complex_ofReal]
  change -feeD (z:ℂ)*(c*(J:ℂ))=_
  rw [←hJ]
  unfold feeD c
  rw [show (z:ℂ)+1=((z+1:ℝ):ℂ) by push_cast; rfl,Complex.Gamma_ofReal]
  have hn : (room:ℂ)≠0 := by exact_mod_cast room_pos.ne'
  push_cast
  field_simp

lemma continued_moment (long:Bool) (z x t:ℝ) :
    (ν t)^(-z)*coeffA long z x t+z*(ν t)^(-z-1)*coeffB long z x t+
      z*(z+1)*(ν t)^(-z-2)*coeffC long z x t =
    prefactor 1 x t*(ν t)^(-z)*GluonGaussian.moment long (4+2*z) (4+2*z)
      (GhostJet.ratio t) (x^2) (gaussS (ν t)) := by
  have hs : GluonGaussian.moment long (4+2*z) (4+2*z) (GhostJet.ratio t) (x^2) (gaussS (ν t)) =
      GluonGaussian.moment long 4 (4+2*z) (GhostJet.ratio t) (x^2) (gaussS (ν t))+
      2*z*gaussS (ν t)*GluonGaussian.radial long (4+2*z) (GhostJet.ratio t) (x^2) (gaussS (ν t))+
      4*z*(z+1)*(gaussS (ν t))^2*GluonGaussian.fourth long (4+2*z) (GhostJet.ratio t) (x^2) (gaussS (ν t)) := by
    cases long
    · exact GluonHeat.split_radial_T ..
    · exact GluonHeat.split_radial_L ..
  rw [hs]
  have h1 : (ν t)^(-z-1)=(ν t)^(-z)/(ν t) := by
    rw [Real.rpow_sub (ν_pos t),Real.rpow_one]
  have h2 : (ν t)^(-z-2)=(ν t)^(-z)/(ν t)^2 := by
    rw [Real.rpow_sub (ν_pos t),Real.rpow_two]
  rw [h1,h2]
  unfold coeffA coeffB coeffC gaussS
  generalize prefactor 1 x t=P
  generalize GluonGaussian.moment long 4 (4+2*z) (GhostJet.ratio t) (x^2) (2*ν t)⁻¹=A
  generalize GluonGaussian.radial long (4+2*z) (GhostJet.ratio t) (x^2) (2*ν t)⁻¹=B
  generalize GluonGaussian.fourth long (4+2*z) (GhostJet.ratio t) (x^2) (2*ν t)⁻¹=C
  have hn:=(ν_pos t).ne'
  field_simp
  ring

end YMReview.NovemberMatching.GluonContinuation
#print axioms YMReview.NovemberMatching.GluonContinuation.actual_force_real
