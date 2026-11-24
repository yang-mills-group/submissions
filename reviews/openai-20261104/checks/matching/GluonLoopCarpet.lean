import GluonLoopYeast
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
open YM YM.MS YM.MS.Arts YM.MS.ScaleForest
open Plane Koszul Heat Flux Landau Book Convolve Motif Halo
open Function Filter Set Finset MeasureTheory Real
open Tone Momentum Frame Wire Color Detect Native Native.Wilsonian City Logarithm Signal
open Landau.Detect.Mark Wind High Knobs Arc Rock Path Oceans Plum Alps Garment Pearl
open YM.WilsonMS.BetaValue YM.WilsonMS.BetaValue.HeatPapers SquareShift
namespace YMReview.NovemberMatching.GluonCarpet
open GluonTrace GluonContraction GluonYeast GhostRadial
local notation "e" => TwoPoint.primary 0

def axis (long:Bool) : L 0 := if long then 0 else 1

def numerator (long:Bool) (H R x:ℝ) (q:SectorP 0) : ℝ :=
  if long then (2*q 0+x)^2*((H-1)*A q R*B q R x-x^2*K q R)
  else 4*(x^2*(A q R+B q R x-(q 1)^2)*K q R+(H-1)*A q R*B q R x*(q 1)^2)

def radialKernel (long:Bool) (z t R x:ℝ) (q:SectorP 0) : ℝ :=
  Pill t (x • e) q*Real.exp (-(ν t*R^2))*numerator long (4+2*z) R x q

lemma lift_primary (x:ℝ) : Left (Nat.le_succ 0) (x • e)=p6 x := by
  ext i
  fin_cases i <;> simp [Left,sends,spray,Pi.single_apply,TwoPoint.primary,
    TwoPoint.zeroDirection,rises,Fin.sum_univ_succ,p6]

lemma slide_six (q:SectorP 0) (R:ℝ) : slideA (Nat.lt_succ_self 0) (q,R)=q6 q R := by
  ext i
  fin_cases i <;> simp [Path.path,Left,sends,spray,Pi.single_apply,hatch,aside,step,rises,
    Fin.sum_univ_succ,q6,Zed]

lemma square_six (q:SectorP 0) (R:ℝ) : (q6 q R).sq=A q R := by
  simp [q6,GluonContraction.A,Momentum.sq,Fin.sum_univ_succ]
  ring
lemma add_square_six (q:SectorP 0) (R x:ℝ) : (q6 q R+p6 x).sq=B q R x := by
  simp [q6,p6,B,Momentum.sq,Fin.sum_univ_succ]
  ring

lemma density_split (t R x:ℝ) (q:SectorP 0) :
    City.brush 1 (q6 q R)*City.brush t (q6 q R+p6 x) =
    Pill t (x • e) q*Real.exp (-(ν t*R^2)) := by
  have hs : (q+x • e).sq=q.sq+2*x*q 0+x^2 := by
    simp [Momentum.sq,Fin.sum_univ_succ,TwoPoint.primary,spray,Pi.single_apply,
      TwoPoint.zeroDirection,rises]
    ring
  unfold Pill City.brush
  rw [square_six,add_square_six,hs]
  simp only [one_pow,one_mul]
  have he : -(A q R)-t^2*B q R x= -q.sq-t^2*(q.sq+2*x*q 0+x^2)-ν t*R^2 := by
    unfold GluonContraction.A B ν
    ring
  have hex : Real.exp (-(A q R))*Real.exp (-(t^2*B q R x)) =
      Real.exp (-q.sq)*Real.exp (-(t^2*(q.sq+2*x*q 0+x^2)))*Real.exp (-(ν t*R^2)) := by
    rw [←Real.exp_add,←Real.exp_add,←Real.exp_add]
    congr 1
  linear_combination t^3*hex

lemma tensor_split (long:Bool) (z t R x:ℝ) (q:SectorP 0) :
    GluonTrace.gaugeTensor t (Left (Nat.le_succ 0) (x • e))
      (slideA (Nat.lt_succ_self 0) (q,R)) (rises (Nat.le_succ 0) (axis long)) +
    2*((z:ℂ)-1)*extraTensor t (Left (Nat.le_succ 0) (x • e))
      (slideA (Nat.lt_succ_self 0) (q,R)) (rises (Nat.le_succ 0) (axis long)) =
      2*(radialKernel long z t R x q:ℝ) := by
  rw [lift_primary,slide_six]
  unfold GluonTrace.gaugeTensor extraTensor
  rw [square_six,add_square_six]
  have hm := congrArg Complex.ofReal (density_split t R x q)
  cases long <;> simp only [axis,Bool.false_eq_true,if_false,if_true]
  · change ((City.brush 1 (q6 q R)*City.brush t (q6 q R+p6 x)*2*tireG (p6 x) (q6 q R) 1:ℝ):ℂ)+_= _
    rw [tire_T]
    unfold radialKernel numerator
    simp only [Bool.false_eq_true,if_false,
      show q6 q R (rises (Nat.le_succ 0) 1)=q 1 from rfl,
      show p6 x (rises (Nat.le_succ 0) 1)=0 from rfl]
    push_cast at hm ⊢
    linear_combination (8*((x:ℂ)^2*((A q R:ℂ)+(B q R x:ℂ)-(q 1:ℂ)^2)*(K q R:ℂ)+
      (3+2*(z:ℂ))*(A q R:ℂ)*(B q R x:ℂ)*(q 1:ℂ)^2))*hm
  · change ((City.brush 1 (q6 q R)*City.brush t (q6 q R+p6 x)*2*tireG (p6 x) (q6 q R) 0:ℝ):ℂ)+_= _
    rw [tire_L]
    unfold radialKernel numerator
    simp only [if_true,
      show q6 q R (rises (Nat.le_succ 0) 0)=q 0 from rfl,
      show p6 x (rises (Nat.le_succ 0) 0)=x from rfl]
    push_cast at hm ⊢
    linear_combination (2*(2*(q 0:ℂ)+(x:ℂ))^2*((3+2*(z:ℂ))*(A q R:ℂ)*(B q R x:ℂ)-
      (x:ℂ)^2*(K q R:ℂ)))*hm

lemma tensor_split_neg (long:Bool) (z t R x:ℝ) (q:SectorP 0) :
    GluonTrace.gaugeTensor t (Left (Nat.le_succ 0) (x • e))
      (-(slideA (Nat.lt_succ_self 0) (q,R))) (rises (Nat.le_succ 0) (axis long)) +
    2*((z:ℂ)-1)*extraTensor t (Left (Nat.le_succ 0) (x • e))
      (-(slideA (Nat.lt_succ_self 0) (q,R))) (rises (Nat.le_succ 0) (axis long)) =
      2*(radialKernel long z t R x (-q):ℝ) := by
  rw [show -(slideA (Nat.lt_succ_self 0) (q,R)) =
    slideA (Nat.lt_succ_self 0) (-q,-R) from (map_neg _ (q,R)).symm,tensor_split]
  simp [radialKernel,numerator,GluonContraction.A,B,K]

lemma actual_inner {G:Gauge} {n:ℕ} (p q:SectorP n) (mu:L n) (a b:G.ColorIndex) (z:ℂ) :
    innerTrace (cursor false).half (TwoPoint.stemPair G false) z q (TwoPoint.word mu mu a b p)=
    (∑ d:G.ColorIndex,angle d a b)*
      (∫ r in (0:ℝ)..1,
        (GluonTrace.gaugeTensor r p q mu+2*(z-n)*extraTensor r p q mu)+
        (GluonTrace.gaugeTensor r p (-q) mu+2*(z-n)*extraTensor r p (-q) mu)) := by
  have hc (q:SectorP n) : Continuous (fun r:ℝ=>GluonTrace.gaugeTensor r p q mu) := by
    unfold GluonTrace.gaugeTensor City.brush
    fun_prop
  have he (q:SectorP n) : Continuous (fun r:ℝ=>extraTensor r p q mu) := by
    unfold extraTensor City.brush
    fun_prop
  unfold innerTrace
  rw [←at_trc,GhostTrace.inside_loop,GluonYeast.actual_yeast]
  simp_rw [GluonTrace.trace_value,intervalIntegral.integral_const_mul]
  have ha (q:SectorP n) : IntervalIntegrable
      (fun r:ℝ=>GluonTrace.gaugeTensor r p q mu+2*(z-n)*extraTensor r p q mu) volume 0 1 :=
    ((hc q).add ((he q).const_mul (2*(z-n)))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (f:=fun r:ℝ=>GluonTrace.gaugeTensor r p q mu+2*(z-n)*extraTensor r p q mu)
      (g:=fun r:ℝ=>GluonTrace.gaugeTensor r p (-q) mu+2*(z-n)*extraTensor r p (-q) mu) (ha q) (ha (-q))]
  rw [intervalIntegral.integral_add (f:=fun r:ℝ=>GluonTrace.gaugeTensor r p q mu)
      (g:=fun r:ℝ=>2*(z-n)*extraTensor r p q mu) ((hc q).intervalIntegrable _ _)
      (((he q).const_mul (2*(z-n))).intervalIntegrable _ _),
    intervalIntegral.integral_add (f:=fun r:ℝ=>GluonTrace.gaugeTensor r p (-q) mu)
      (g:=fun r:ℝ=>2*(z-n)*extraTensor r p (-q) mu) ((hc (-q)).intervalIntegrable _ _)
      (((he (-q)).const_mul (2*(z-n))).intervalIntegrable _ _),
    intervalIntegral.integral_add ((hc q).intervalIntegrable _ _) ((hc (-q)).intervalIntegrable _ _),
    intervalIntegral.integral_add ((he q).intervalIntegrable _ _) ((he (-q)).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_const_mul]
  ring

theorem actual_carpet (G:Gauge) (long:Bool) (a b:G.ColorIndex) (R x z:ℝ) :
    loopCarpet (cursor false).half (TwoPoint.stemPair G false) (z:ℂ)
      (TwoPoint.word (axis long) (axis long) a b e) (R,x) =
    (∑ d:G.ColorIndex,angle d a b)*
      (∫ q:SectorP 0,(∫ t in (0:ℝ)..1,
        2*(radialKernel long z t R x q:ℂ)+2*(radialKernel long z t R x (-q):ℂ)) ∂Px 0) := by
  unfold loopCarpet
  rw [ray_word,lift_word]
  simp_rw [actual_inner,Nat.cast_one,tensor_split,tensor_split_neg]
  rw [MeasureTheory.integral_const_mul]

end YMReview.NovemberMatching.GluonCarpet
#print axioms YMReview.NovemberMatching.GluonCarpet.actual_carpet
