import YM.MS.ScaleForest.Bubbles
import Mathlib.Tactic

/-! Source-connected diagnostics for the vector-polarization trace.
These are trace and source-bridge checks, not a proof of the integrated
finite gluon bubble. The constant metric test need not be an admissible
integrand: it tests innerTrace before integration.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open YM YM.MS YM.MS.Arts
open scoped BigOperators
namespace YMReview.NovemberMatching.GluonPolarization

theorem precision_trace {A : Type} [Fintype A] [DecidableEq A]
    (q : Momentum A) :
    (∑ i : A, Landau.precision i i q) = ((Fintype.card A : ℝ)-1)*q.sq := by
  simp only [Landau.precision, Landau.delta, ↓reduceIte, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h : (∑ i : A, q i*q i) = q.sq := by simp [Momentum.sq, pow_two]
  rw [h]
  ring

theorem projector_trace {A : Type} [Fintype A] [DecidableEq A]
    (q : Momentum A) (hq : q.sq ≠ 0) :
    (∑ i : A, Landau.precision i i q / q.sq) = (Fintype.card A : ℝ)-1 := by
  rw [← Finset.sum_div, precision_trace]
  exact mul_div_cancel_right₀ _ hq

def metricKernel (G : Gauge) (c : G.ColorIndex) : Rip G := fun _ i j _ =>
  match i,j with
  | ((some a,false),x),((some b,false),y) =>
      if x=c ∧ y=c ∧ a=b then 1 else 0
  | _,_ => 0

def metricVertex (G : Gauge) (c : G.ColorIndex) : Mob G := fun _ w =>
  match w with
  | [(((some a,false),x),_),(((some b,false),y),_)] =>
      if x=c ∧ y=c ∧ a=b then 1 else 0
  | _ => 0

theorem metric_yeast (G : Gauge) (c : G.ColorIndex) (m : ℕ) (q : SectorP m) :
    yeast (metricKernel G c) (metricVertex G c) q [] = 1 := by
  simp [yeast, token, fleck, metricKernel, metricVertex, vleg,
    lift, ite_and]

theorem metric_innerTrace (G : Gauge) (c : G.ColorIndex) (m : ℕ)
    (q : SectorP m) (z : ℂ) :
    ScaleForest.innerTrace (metricKernel G c) (metricVertex G c) z q [] = 4+2*z := by
  unfold ScaleForest.innerTrace
  rw [metric_yeast]
  simp [Cfield, Landau.Leg, Landau.Atom, metricKernel, metricVertex,
    Fintype.sum_prod_type, Fintype.sum_option, L, Zed, ite_and]
  ring

theorem innerTrace_difference (G : Gauge) (K : Rip G) (V : Mob G)
    (m : ℕ) (q : SectorP m) (w : Koszul.Legs (Shore G m)) (z z' : ℂ) :
    ScaleForest.innerTrace K V z q w - ScaleForest.innerTrace K V z' q w =
      2*(z-z')*yeast K V q w := by
  unfold ScaleForest.innerTrace
  ring

end YMReview.NovemberMatching.GluonPolarization

#print axioms YMReview.NovemberMatching.GluonPolarization.precision_trace
#print axioms YMReview.NovemberMatching.GluonPolarization.projector_trace
#print axioms YMReview.NovemberMatching.GluonPolarization.metric_yeast
#print axioms YMReview.NovemberMatching.GluonPolarization.metric_innerTrace
#print axioms YMReview.NovemberMatching.GluonPolarization.innerTrace_difference
#check YM.WilsonMS.BetaValue.field_W
#print axioms YM.WilsonMS.BetaValue.field_W
#check YM.MS.ScaleForest.TwoPoint.gauge_hit
#print axioms YM.MS.ScaleForest.TwoPoint.gauge_hit
#check YM.MS.ScaleForest.TwoPoint.trace_value
#print axioms YM.MS.ScaleForest.TwoPoint.trace_value
#check YM.MS.ScaleForest.closeG_integer
#print axioms YM.MS.ScaleForest.closeG_integer
