import GluonLoopFinite

/-! Exact Gaussian moment algebra and compact heat integral.
These lemmas check the explicit analytic expressions. The submitted sewing
to Gaussian-moment bridge is not asserted by this module. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open Function Filter Set Finset MeasureTheory Real
open scoped Topology
namespace YMReview.NovemberMatching.GluonHeat
open GluonLoop GhostInfrared

def momentT (D H u X s:ℝ) :=
  4*(X*((2*D^2+D-5)*s^2+(u^2+(1-u)^2)*X*(D-1)*s)+
    (H-1)*((D+2)*(D+4)*s^3+((D+2)*(u^2+(1-u)^2)-4*u*(1-u))*X*s^2+
      u^2*(1-u)^2*X^2*s))
def momentL (D H u X s:ℝ) :=
  (H-1)*(4*((D+2)*(D+4)*s^3+((D+2)*(u^2+(1-u)^2)-12*u*(1-u))*X*s^2+
    u^2*(1-u)^2*X^2*s)+8*(1-2*u)^2*(D+2)*X*s^2-
    8*u*(1-u)*(1-2*u)^2*X^2*s+(1-2*u)^2*X*
    (D*(D+2)*s^2+(D*(u^2+(1-u)^2)-4*u*(1-u))*X*s+u^2*(1-u)^2*X^2))-
      X*(4*(D-1)*s^2+(1-2*u)^2*X*(D-1)*s)
def radialT (H u X s:ℝ) :=
  4*(X*(13*s+(u^2+(1-u)^2)*X)+(H-1)*(12*s^2+(u^2+(1-u)^2)*X*s))
def fourthT (H X s:ℝ) := 4*(2*X+(H-1)*s)
def radialL (H u X s:ℝ) :=
  (H-1)*(48*s^2+(16*(1-2*u)^2+4*(u^2+(1-u)^2))*X*s+
    (1-2*u)^2*(u^2+(1-u)^2)*X^2)-X*(4*s+(1-2*u)^2*X)
def fourthL (H u X s:ℝ) := (H-1)*(4*s+(1-2*u)^2*X)

theorem split_radial_T (z H u X s:ℝ) :
    momentT (4+2*z) H u X s = momentT 4 H u X s+
      2*z*s*radialT H u X s+4*z*(z+1)*s^2*fourthT H X s := by
  unfold momentT radialT fourthT
  ring
theorem split_radial_L (z H u X s:ℝ) :
    momentL (4+2*z) H u X s = momentL 4 H u X s+
      2*z*s*radialL H u X s+4*z*(z+1)*s^2*fourthL H u X s := by
  unfold momentL radialL fourthL
  ring

def heatT (u X:ℝ) := 144*u*(1-u)^2+
  (98*u-194*u^2+192*u^3-96*u^4)*X+
  (12*u-24*u^2+36*u^3-24*u^4+12*u^5)*X^2
def heatL (u X:ℝ) := 144*u*(1-u)^2+
  (138*u-714*u^2+1152*u^3-576*u^4)*X+
  (9*u-96*u^2+348*u^3-504*u^4+252*u^5)*X^2+
  (6*u^3-30*u^4+48*u^5-24*u^6)*X^3
def heatPolynomial (v u X:ℝ) := (1-v)*heatT u X+v*heatL u X

theorem heat_moment_T (u X:ℝ) :
    (1-u)*heatT u X = 2*u*momentT 4 4 u X ((1-u)/2) := by
  unfold heatT momentT
  ring
theorem heat_moment_L (u X:ℝ) :
    (1-u)*heatL u X = 2*u*momentL 4 4 u X ((1-u)/2) := by
  unfold heatL momentL
  ring

def heatCoeff (v X:ℝ) : Fin 7 → ℝ := ![
  0,
  144+(98+40*v)*X+(12-3*v)*X^2,
  -288+(-194-520*v)*X+(-24-72*v)*X^2,
  144+(192+960*v)*X+(36+312*v)*X^2+6*v*X^3,
  (-96-480*v)*X+(-24-480*v)*X^2-30*v*X^3,
  (12+240*v)*X^2+48*v*X^3,
  -24*v*X^3]
theorem heatPolynomial_coeff (v u X:ℝ) :
    heatPolynomial v u X=∑ n:Fin 7,heatCoeff v X n*u^(n:ℕ) := by
  simp [heatCoeff,Fin.sum_univ_succ,heatPolynomial,heatT,heatL]
  ring
theorem heatPolynomial_integral (v X:ℝ) (hX:X≠0) :
    (∫ u:ℝ in (0:ℝ)..(1/2:ℝ),Real.exp (-X*u)*heatPolynomial v u X)=
      GluonLoop.forceValue v X := by
  simp_rw [heatPolynomial_coeff,Finset.mul_sum,
    show ∀ n:Fin 7,∀ u:ℝ,Real.exp (-X*u)*(heatCoeff v X n*u^(n:ℕ))=
      heatCoeff v X n*(u^(n:ℕ)*Real.exp (-X*u)) from by intros; ring]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul,laplaceMoment X hX]
    simp only [heatCoeff,Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,
      Matrix.cons_val_zero,Matrix.cons_val_succ]
    norm_num [laplacePrimitive,GluonLoop.forceValue]
    rw [show -(X*(1/2))= -X/2 by ring]
    field_simp
    ring
  · intro n _
    exact (show Continuous (fun u:ℝ=>heatCoeff v X n*(u^(n:ℕ)*Real.exp (-X*u))) by fun_prop).intervalIntegrable _ _

end YMReview.NovemberMatching.GluonHeat
#print axioms YMReview.NovemberMatching.GluonHeat.split_radial_T
#print axioms YMReview.NovemberMatching.GluonHeat.split_radial_L
#print axioms YMReview.NovemberMatching.GluonHeat.heatPolynomial_integral
