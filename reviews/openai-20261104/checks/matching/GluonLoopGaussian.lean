import GluonLoopHeat
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open YM YM.MS YM.MS.Arts YM.MS.ScaleForest
open Plane Koszul Heat Flux Landau Book Convolve Motif Halo
open Function Filter Set Finset MeasureTheory Real
open YM.WilsonMS.BetaValue YM.WilsonMS.BetaValue.HeatPapers
open _root_.YM.PertExtension RG FormalOPE FormalOPE.RG10 FormalOPE.RG10.MultiGauge
open SquareShift Papers
namespace YMReview.NovemberMatching.GluonGaussian
open GhostRadial
local notation "V" => HeatPapers.Poly
local notation "e" => TwoPoint.primary 0
variable {α:ℝ} (h:0<α)
set_option quotPrecheck false
local notation "Φ" => Papers.opening mplane (Beam α h)
local notation "s" => gaussS α

lemma e_value (i:Axis) : e i = if i=0 then 1 else 0 := by
  simp [TwoPoint.primary,spray,Pi.single_apply,TwoPoint.zeroDirection,rises,eq_comm]

lemma phi_three (i j k:Axis) : Φ (petal i*petal j*petal k)=0 := by
  rw [stein h ((deriv_petal k i).product (deriv_petal k j))]
  simp [map_add,to_const,from_const,phi_petal]

lemma phi_four (i j k l:Axis) :
    Φ (petal i*petal j*petal k*petal l)=
      s^2*(kk i j*kk k l+kk i k*kk j l+kk i l*kk j k) := by
  rw [stein h (((deriv_petal l i).product (deriv_petal l j)).product (deriv_petal l k))]
  have he : (spring (kk l i)*petal j+petal i*spring (kk l j))*petal k+
      petal i*petal j*spring (kk l k) =
      spring (kk l i)*(petal j*petal k)+spring (kk l j)*(petal i*petal k)+
        spring (kk l k)*(petal i*petal j) := by ring
  rw [he]
  simp only [map_add,from_const,phi_pair]
  rw [kk_comm l i,kk_comm l j,kk_comm l k]
  ring

def sqE (R a x:ℝ) : V := sqPane (a*x) e+spring (R^2)
def core (R a b x:ℝ) : V := sqE R a x*sqE R b x

theorem core_value (R a b x:ℝ) :
    Φ (core R a b x) = squareValue s (a*x) (b*x) 1+
      R^2*(8*s+(a^2+b^2)*x^2)+R^4 := by
  have he : core R a b x = squarePoly e (a*x) (b*x)+
      spring (R^2)*(sqPane (a*x) e+sqPane (b*x) e)+spring (R^4) := by
    unfold core sqE squarePoly
    rw [show spring (R^4)=spring (R^2)*spring (R^2) from by rw [←map_mul]; congr 1; ring]
    ring
  rw [he]
  simp only [map_add,from_const,phi_const,payment_square,pane_value,TwoPoint.primary_sq]
  rw [TwoPoint.primary_sq]
  ring

theorem core_first (R a b x:ℝ) (i:Axis) :
    Φ (core R a b x*petal i) = e i*firstValue s (a*x) (b*x) 1+
      R^2*(2*(a+b)*x*s*e i) := by
  have he : core R a b x*petal i = squarePoly e (a*x) (b*x)*petal i+
      spring (R^2)*(sqPane (a*x) e*petal i+sqPane (b*x) e*petal i)+spring (R^4)*petal i := by
    unfold core sqE squarePoly
    rw [show spring (R^4)=spring (R^2)*spring (R^2) from by rw [←map_mul]; congr 1; ring]
    ring
  rw [he]
  simp only [map_add,from_const,phi_petal,payment_first,pane_first,TwoPoint.primary_sq]
  rw [TwoPoint.primary_sq]
  ring

theorem core_second (R a b x:ℝ) (i j:Axis) :
    Φ (core R a b x*petal i*petal j) =
      s*kk i j*squareValue s (a*x) (b*x) 1+
      s^2*((24*s+2*(a^2+b^2)*x^2)*kk i j+8*a*b*x^2*e i*e j)+
      R^2*s*kk i j*(12*s+(a^2+b^2)*x^2)+R^4*s*kk i j := by
  have he : core R a b x*petal i*petal j = squarePoly e (a*x) (b*x)*petal i*petal j+
      spring (R^2)*(sqPane (a*x) e*petal i*petal j+sqPane (b*x) e*petal i*petal j)+spring (R^4)*(petal i*petal j) := by
    unfold core sqE squarePoly
    rw [show spring (R^4)=spring (R^2)*spring (R^2) from by rw [←map_mul]; congr 1; ring]
    ring
  rw [he]
  simp only [map_add,from_const,phi_pair,payment_second,pane_second,TwoPoint.primary_sq]
  rw [TwoPoint.primary_sq]
  ring

def perp (R:ℝ) : V := rsqP-petal 0*petal 0+spring (R^2)

lemma perp_value (R:ℝ) : Φ (perp R)=3*s+R^2 := by
  simp only [perp,map_sub,map_add,phi_sqP,phi_pair,phi_const,kk_self]
  ring

lemma perp_first (R:ℝ) : Φ (perp R*petal 0)=0 := by
  simp only [perp,sub_mul,add_mul,map_sub,map_add,phi_sq_mul_p,phi_three,from_const,phi_petal]
  ring

lemma perp_second (R:ℝ) (i:Axis) :
    Φ (perp R*petal i*petal i)=(5-2*kk i 0)*s^2+R^2*s := by
  have hp : Φ (rsqP*petal i*petal i)=6*s^2 := by
    have ht:=pane_second h e 0 i i
    simp only [sqPane,mul_zero,zero_mul,zero_pow (by decide : 2≠0),map_zero,add_zero,zero_add,kk_self,mul_one] at ht
    rw [ht]
    ring
  simp only [perp,sub_mul,add_mul,map_sub,map_add,mul_assoc (spring _),from_const,phi_pair,kk_self,hp,phi_four]
  by_cases hi:i=0
  · subst i; norm_num [kk]; ring
  · simp [kk,hi,Ne.symm hi]; ring

lemma sqE_perp (R a x:ℝ) :
    Φ (sqE R a x*perp R)=18*s^2+3*a^2*x^2*s+R^2*(7*s+a^2*x^2)+R^4 := by
  have he : sqE R a x*perp R =
    rsqP*rsqP+spring (2*a*x)*(rsqP*alongP e)+spring (a^2*x^2)*rsqP-
    sqPane (a*x) e*petal 0*petal 0+spring (R^2)*sqPane (a*x) e+
    spring (R^2)*perp R := by
    unfold sqE perp sqPane
    rw [show spring (2*(a*x))=spring (2*a*x) from by congr 1; ring,
      show spring ((a*x)^2*Momentum.sq e)=spring (a^2*x^2) from by rw [TwoPoint.primary_sq]; congr 1; ring]
    ring
  rw [he]
  simp only [map_add,map_sub,from_const,phi_sq_mul_sq,phi_sq_mul_pa,phi_sqP,pane_second,pane_value,
    perp_value,TwoPoint.primary_sq,kk_self]
  ring

def crossPoly (R a b x:ℝ) : V := (sqE R a x+sqE R b x-petal 1*petal 1)*perp R
lemma cross_value (R a b x:ℝ) :
    Φ (crossPoly R a b x)=31*s^2+3*(a^2+b^2)*x^2*s+
      R^2*(13*s+(a^2+b^2)*x^2)+2*R^4 := by
  unfold crossPoly
  rw [sub_mul,add_mul,map_sub,map_add,sqE_perp h,sqE_perp h]
  have he : petal 1*petal 1*perp R=perp R*petal 1*petal 1 := by ring
  rw [he,perp_second h]
  norm_num [kk]
  ring

def speed (c x:ℝ) : V := spring 2*petal 0+spring (c*x)

lemma core_speed (R a b c x:ℝ) :
    Φ (core R a b x*speed c x*speed c x)=
      4*(s*squareValue s (a*x) (b*x) 1+s^2*(24*s+2*(a^2+b^2)*x^2+8*a*b*x^2)+
        R^2*s*(12*s+(a^2+b^2)*x^2)+R^4*s)+
      4*c*x*(firstValue s (a*x) (b*x) 1+R^2*2*(a+b)*x*s)+
      c^2*x^2*(squareValue s (a*x) (b*x) 1+R^2*(8*s+(a^2+b^2)*x^2)+R^4) := by
  have he : core R a b x*speed c x*speed c x =
      spring 4*(core R a b x*petal 0*petal 0)+spring (4*c*x)*(core R a b x*petal 0)+
        spring (c^2*x^2)*core R a b x := by
    unfold speed
    simp only [map_mul,map_pow,map_ofNat]
    ring
  rw [he]
  simp only [map_add,from_const,core_second,core_first,core_value,e_value,kk_self,ite_true]
  ring

lemma perp_speed (R c x:ℝ) :
    Φ (perp R*speed c x*speed c x)=4*(3*s^2+R^2*s)+c^2*x^2*(3*s+R^2) := by
  have he : perp R*speed c x*speed c x = spring 4*(perp R*petal 0*petal 0)+
      spring (4*c*x)*(perp R*petal 0)+spring (c^2*x^2)*perp R := by
    unfold speed
    simp only [map_mul,map_pow,map_ofNat]
    ring
  rw [he]
  simp only [map_add,from_const,perp_second,perp_first,perp_value,kk_self]
  ring

def numeratorPoly (long:Bool) (H R u x:ℝ) : V :=
  if long then spring (H-1)*(core R (-u) (1-u) x*speed (1-2*u) x*speed (1-2*u) x)-
    spring (x^2)*(perp R*speed (1-2*u) x*speed (1-2*u) x)
  else spring 4*(spring (x^2)*crossPoly R (-u) (1-u) x+
    spring (H-1)*(core R (-u) (1-u) x*petal 1*petal 1))

def moment (long:Bool) (D H u X rho:ℝ) :=
  if long then GluonHeat.momentL D H u X rho else GluonHeat.momentT D H u X rho
def radial (long:Bool) (H u X rho:ℝ) :=
  if long then GluonHeat.radialL H u X rho else GluonHeat.radialT H u X rho
def fourth (long:Bool) (H u X rho:ℝ) :=
  if long then GluonHeat.fourthL H u X rho else GluonHeat.fourthT H X rho

theorem numerator_value (long:Bool) (H R u x:ℝ) :
    Φ (numeratorPoly long H R u x)=moment long 4 H u (x^2) s+
      R^2*radial long H u (x^2) s+R^4*fourth long H u (x^2) s := by
  cases long
  · simp only [numeratorPoly,Bool.false_eq_true,if_false,map_add,from_const,core_second,cross_value]
    norm_num only [e_value,kk_self,show ¬(1:Axis)=0 from by decide,if_false]
    unfold GluonGaussian.moment GluonGaussian.radial fourth GluonHeat.momentT GluonHeat.radialT GluonHeat.fourthT squareValue
    simp only [Bool.false_eq_true,if_false]
    ring
  · rw [numeratorPoly,if_pos rfl,map_sub,from_const,from_const,core_speed,perp_speed]
    unfold GluonGaussian.moment GluonGaussian.radial fourth GluonHeat.momentL GluonHeat.radialL GluonHeat.fourthL squareValue firstValue
    simp only [if_true]
    ring

end YMReview.NovemberMatching.GluonGaussian
#print axioms YMReview.NovemberMatching.GluonGaussian.numerator_value
