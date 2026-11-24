import GhostLoopTrace
import Mathlib.Tactic
/-!
# Physical momentum integral with an auxiliary radius

Derives the actual submitted ghost-loop carpet as a compact heat-parameter
integral. Gaussian moment proofs extend the submitted `SquareShift` calculus.
All exchanges of the momentum and heat integrals use explicit integrability
bounds. This is an intermediate step toward the finite-part comparison.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open YM YM.MS YM.MS.Arts YM.MS.ScaleForest
open Plane Koszul Heat Flux Landau Book Convolve Motif Halo
open Function Filter Set Finset MeasureTheory Metric Real
open Tone Momentum Frame Wire Color Detect Native Native.Wilsonian City Logarithm Signal
open Landau.Detect.Mark Wind High Knobs Arc Rock Path Oceans Plum Alps Garment Pearl Train
open YM.WilsonMS.BetaValue YM.WilsonMS.BetaValue.HeatPapers
open scoped BigOperators Topology
namespace YMReview.NovemberMatching.GhostRadial
variable {G : Gauge} {m n : ℕ}

lemma slide_coord (h : m<n) (p : SectorP m) (R : ℝ) (i : L m) :
    slideA h (p,R) (rises h.le i) = p i :=
  congrFun (congrArg Prod.fst (equal0 (p,R) h)) i

lemma slide_sq (h : m<n) (p : SectorP m) (R : ℝ) :
    (slideA h (p,R)).sq = p.sq+R^2 := by
  rw [Momentum.sq,cut_sum h.le]
  simp only [slide_coord]
  have ht (i : Apart m n) : slideA h (p,R) (aside h.le i) =
      R * (if step h=i then 1 else 0) := by
    rw [Path.path,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
      offt (rises h.le) p _ (fun j=>nowhere h.le j i),zero_add]
    simp [spray,hatch,Pi.single_apply,eq_comm]
  simp_rw [ht]
  simp [Momentum.sq,mul_ite]

lemma slide_add (h : m<n) (q p : SectorP m) (R : ℝ) :
    slideA h (q,R) + Left h.le p = slideA h (q+p,R) := by
  simp only [Path.path,map_add]
  abel

lemma lift_word (h : m≤n) (p : SectorP m) (i j : L m) (a b : G.ColorIndex) :
    Arts.lift h (TwoPoint.word i j a b p) =
      TwoPoint.word (rises h i) (rises h j) a b (Left h p) := by
  simp [Arts.lift,TwoPoint.word,vec,at_g,embA]

lemma ray_word (p : SectorP m) (i j : L m) (a b : G.ColorIndex) (x : ℝ) :
    sail (ray (TwoPoint.word i j a b p)) x = TwoPoint.word i j a b (x • p) := by
  simp [ray_go,TwoPoint.word,vec]

/-- Real integrand on the physical momentum plane and the auxiliary radius. -/
def radialKernel (t R : ℝ) (p q : SectorP 0) (i : L 0) : ℝ :=
  Pill t p q * Real.exp (-(ν t * R^2)) *
    (q.sq+R^2) * ((q+p).sq+R^2) * (q+p) i * q i

lemma tensor_split (t R : ℝ) (p q : SectorP 0) (i : L 0) :
    GhostTrace.ghostTensor t (Left (Nat.le_succ 0) p)
      (slideA (Nat.lt_succ_self 0) (q,R)) (rises (Nat.le_succ 0) i) =
      -4 * (radialKernel t R p q i : ℝ) := by
  unfold GhostTrace.ghostTensor radialKernel
  rw [slide_sq, slide_add,slide_sq,slide_coord,slide_coord]
  unfold Pill City.brush
  simp only [slide_sq]
  simp only [one_pow,one_mul]
  have he : Real.exp (-(q.sq+R^2)) * Real.exp (-(t^2*((q+p).sq+R^2))) =
    Real.exp (-q.sq)*Real.exp (-(t^2*(q+p).sq))*Real.exp (-(ν t*R^2)) := by
    rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]
    congr 1
    unfold ν
    ring
  have hf : Real.exp (-(q.sq+R^2)) * (t^3*Real.exp (-(t^2*((q+p).sq+R^2)))) =
    Real.exp (-q.sq)*(t^3*Real.exp (-(t^2*(q+p).sq)))*Real.exp (-(ν t*R^2)) := by
      linear_combination (t^3)*he
  rw [hf]
  push_cast
  ring


lemma tensor_split_neg (t R : ℝ) (p q : SectorP 0) (i : L 0) :
    GhostTrace.ghostTensor t (Left (Nat.le_succ 0) p)
      (-(slideA (Nat.lt_succ_self 0) (q,R))) (rises (Nat.le_succ 0) i) =
      -4 * (radialKernel t R p (-q) i : ℝ) := by
  rw [show -(slideA (Nat.lt_succ_self 0) (q,R)) =
    slideA (Nat.lt_succ_self 0) (-q,-R) from (map_neg _ (q,R)).symm, tensor_split]
  simp [radialKernel]

/-- The source's actual continued-loop integrand, before the radial derivative.
The formula still has its physical momentum integral and compact heat integral. -/
theorem actual_carpet (G : Gauge) (p : SectorP 0) (i : L 0) (a b : G.ColorIndex)
    (R x : ℝ) (z : ℂ) :
    loopCarpet (cursor true).half (TwoPoint.stemPair G true) z
      (TwoPoint.word i i a b p) (R,x) =
    (∑ d : G.ColorIndex, angle d a b) *
      (∫ q : SectorP 0, (∫ t : ℝ in (0:ℝ)..1,
        -4 * (radialKernel t R (x • p) q i : ℂ) +
        -4 * (radialKernel t R (x • p) (-q) i : ℂ)) ∂Px 0) := by
  unfold loopCarpet
  rw [ray_word,lift_word]
  simp_rw [GhostLoopFinite.ghost_innerTrace_no_explicit_z]
  simp_rw [← at_trc, GhostTrace.inside_loop, GhostTrace.trace_value,
    tensor_split,tensor_split_neg,intervalIntegral.integral_const_mul]
  rw [MeasureTheory.integral_const_mul]

open _root_.YM.PertExtension
open RG FormalOPE FormalOPE.RG10 FormalOPE.RG10.MultiGauge
open SquareShift
open Papers
local notation "V" => HeatPapers.Poly

section moments
variable {α : ℝ} (h : 0<α)
set_option quotPrecheck false
local notation "Φ" => Papers.opening mplane (Beam α h)
local notation "s" => gaussS α

lemma pane_value (q : SectorP 0) (a : ℝ) : Φ (sqPane a q) = 4*s+a^2*q.sq := by
  simp only [sqPane,map_add,phi_sqP h,from_const h,phi_along h,phi_const h,mul_zero,add_zero]

lemma pane_first (q : SectorP 0) (a : ℝ) (i : L 0) :
    Φ (sqPane a q * petal i) = 2*a*s*q i := by
  rw [stein h (deriv_pane q i a)]
  simp only [sqD,map_add,map_smul,phi_petal h,phi_const h,smul_zero,zero_add]
  ring

lemma pane_second (q : SectorP 0) (a : ℝ) (i j : L 0) :
    Φ (sqPane a q * petal i * petal j) = s*kk i j*(6*s+a^2*q.sq) := by
  rw [stein h ((deriv_pane q j a).product (deriv_petal j i)),map_add,to_const h,pane_value h]
  simp only [sqD,add_mul,smul_mul_assoc,map_add,map_smul,from_const h,phi_pair h,phi_petal h,
    mul_zero,add_zero,kk_comm j i,smul_eq_mul]
  ring

def lowerPoly (q : SectorP 0) (k a b : ℝ) (i j : L 0) : V :=
  sqPane k q * (petal i+spring (b*q i)) * (petal j+spring (a*q j))

lemma lower_value (q : SectorP 0) (k a b : ℝ) (i j : L 0) :
    Φ (lowerPoly q k a b i j) =
      s*kk i j*(6*s+k^2*q.sq) +
      q i*q j*(2*k*(a+b)*s+a*b*(4*s+k^2*q.sq)) := by
  unfold lowerPoly
  rw [mul_add _ (petal j),map_add,to_const h,mul_add _ (petal i),map_add,to_const h,
    add_mul,map_add,mul_right_comm _ (spring _) (petal j),to_const h,
    pane_second h,pane_first h,pane_first h,pane_value h]
  ring

def lowPair (q : SectorP 0) (a b : ℝ) (i j : L 0) : V :=
  (petal i+spring (b*q i))*(petal j+spring (a*q j))

lemma lowPair_value (q : SectorP 0) (a b : ℝ) (i j : L 0) :
    Φ (lowPair q a b i j) = s*kk i j+a*b*q i*q j := by
  unfold lowPair
  simp only [mul_add,add_mul,map_add,to_const h,from_const h,phi_pair h,phi_petal h,phi_const h]
  ring

def extendedPoly (R : ℝ) (q : SectorP 0) (a b : ℝ) (i j : L 0) : V :=
  (sqPane a q+spring (R^2))*(sqPane b q+spring (R^2))*
    (petal i+spring (b*q i))*(petal j+spring (a*q j))

/-- Exact Gaussian moment retaining the auxiliary radius; no dimensional
interpolation is used. -/
theorem extended_value (R : ℝ) (q : SectorP 0) (a b : ℝ) (i j : L 0) :
    Φ (extendedPoly R q a b i j) =
      pairValue q.sq (q i) (q j) (kk i j) s a b +
      R^2*GhostLoopFinite.radialSquare q.sq (q i*q j) (kk i j) s a b +
      R^4*GhostLoopFinite.radialFourth (q i*q j) (kk i j) s a b := by
  have he : extendedPoly R q a b i j = bothPoly q a b i j +
      spring (R^2)*(lowerPoly q a a b i j+lowerPoly q b a b i j) +
      spring (R^4)*lowPair q a b i j := by
    unfold extendedPoly bothPoly squarePoly lowerPoly lowPair
    rw [show spring (R^4) = spring (R^2)*spring (R^2) from by rw [← map_mul]; congr 1; ring]
    ring
  rw [he,map_add,map_add,payment_both q i j a b h,from_const h,from_const h,
    map_add,lower_value h,lower_value h,lowPair_value h]
  unfold GhostLoopFinite.radialSquare GhostLoopFinite.radialFourth
  ring
end moments


/-- Numerator of the ghost trace in split coordinates. -/
def extendedTensor (R : ℝ) (q : SectorP 0) (i j : L 0) (p : SectorP 0) : ℝ :=
  (p.sq+R^2)*((p+q).sq+R^2)*(p+q) i*p j

lemma extended_sheet (R : ℝ) (q : SectorP 0) (i j : L 0) :
    Sheet (extendedTensor R q i j) :=
  ((((Sheet.heat_sq.add (Sheet.num (R^2))).mul
    ((Sheet.heat_sq.wave q).add (Sheet.num (R^2)))).mul
      ((Sheet.read i).wave q)).mul (Sheet.read j))

lemma at_extended (R : ℝ) (q p : SectorP 0) (a b x : ℝ) (i j : L 0)
    (ht : b=a+x) :
    extendedTensor R (x • q) i j (p+a • q) =
      meterR p (extendedPoly R q a b i j) := by
  unfold extendedTensor extendedPoly
  simp only [add_assoc p,← add_smul,← ht,map_mul,map_add,atR,atP,at_pane,
    Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  rw [ht]
  ring

def extendedHeatValue (R Q p r u x t : ℝ) : ℝ :=
  t^3*Real.exp (slope t*x^2*Q)*volume4 t*
    (pairValue Q p r u (gaussS (ν t)) (slope t*x) ((slope t+1)*x) +
      R^2*GhostLoopFinite.radialSquare Q (p*r) u (gaussS (ν t)) (slope t*x) ((slope t+1)*x) +
      R^4*GhostLoopFinite.radialFourth (p*r) u (gaussS (ν t)) (slope t*x) ((slope t+1)*x))

lemma extended_tune (R : ℝ) (q : SectorP 0) (i j : L 0) (x t : ℝ) :
    tune (x • q) (extendedTensor R (x • q) i j) t =
      extendedHeatValue R q.sq (q i) (q j) (kk i j) x t := by
  unfold tune extendedHeatValue volume4
  let a := slope t*x
  let b := (slope t+1)*x
  let X := extendedPoly R q a b i j
  have he (p : SectorP 0) : extendedTensor R (x • q) i j (p+(slope t*x) • q) = X.val p :=
    at_extended R q p a b x i j (by unfold a b; ring)
  rw [← integral_add_right_eq_self _ ((slope t*x) • q),
    ← extended_value (ν_pos t) R q a b i j, mul_assoc (t^3*_)]
  rw [← net_order (ν_pos t)]
  have hm (v : SectorP 0) : Pill t (x • q) (v+(slope t*x) • q) =
      t^3*Real.exp (slope t*x^2*q.sq)*Real.exp (-(ν t*v.sq)) :=
    SquareShift.moveDensity q v x t
  simp_rw [hm,he,mul_assoc,MeasureTheory.integral_const_mul,← neg_mul]
  exact congr_arg₂ _ rfl (congr_arg₂ _ rfl
    (integral_congr_ae (Eventually.of_forall fun z : SectorP 0 => mul_comm ..)))

lemma radialKernel_as (t R : ℝ) (p q : SectorP 0) (i : L 0) :
    radialKernel t R p q i = Real.exp (-(ν t*R^2)) *
      (Pill t p q * extendedTensor R p i i q) := by
  unfold radialKernel extendedTensor
  ring

lemma weighted_bond (R : ℝ) (p : SectorP 0) (i : L 0) :
    Integrable (fun v : SectorP 0 × ℝ => radialKernel v.2 R p v.1 i) (mplane.prod mint) := by
  have hb := (bond p (extendedTensor R p i i) (extended_sheet R p i i)).norm
  refine hb.mono' ?_ ?_
  · have hc : Continuous (fun v : SectorP 0 × ℝ => radialKernel v.2 R p v.1 i) := by
      unfold radialKernel Pill City.brush ν Momentum.sq
      fun_prop
    exact hc.aestronglyMeasurable
  filter_upwards with v
  rw [radialKernel_as,norm_mul]
  have he : ‖Real.exp (-(ν v.2*R^2))‖ ≤ 1 := by
    rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (ν_pos v.2).le (sq_nonneg R)))
  simpa only [Real.norm_eq_abs,abs_norm,one_mul] using
    mul_le_mul_of_nonneg_right he (norm_nonneg (Pill v.2 p v.1 * extendedTensor R p i i v.1))

/-- Fubini step justified by the Gaussian majorant on the compact heat interval. -/
lemma radial_payment (R x : ℝ) (p : SectorP 0) (i : L 0) :
    (∫ q : SectorP 0, (∫ t : ℝ in (0:ℝ)..1,
      (radialKernel t R (x • p) q i : ℂ) + (radialKernel t R (x • p) (-q) i : ℂ)) ∂mplane) =
      2 * ((∫ t : ℝ in (0:ℝ)..1,
        Real.exp (-(ν t*R^2))*extendedHeatValue R p.sq (p i) (p i) 1 x t) : ℝ) := by
  let Z (q : SectorP 0) : ℝ := ∫ t : ℝ, radialKernel t R (x • p) q i ∂mint
  have hz : Integrable Z mplane := (weighted_bond R (x • p) i).integral_prod_left
  have ht (q : SectorP 0) : Integrable (fun t : ℝ => radialKernel t R (x • p) q i) mint := by
    have hc : Continuous (fun t : ℝ => radialKernel t R (x • p) q i) := by
      unfold radialKernel Pill City.brush ν
      fun_prop
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (hc.intervalIntegrable 0 1)
  have hpoint (q : SectorP 0) : (∫ t : ℝ in (0:ℝ)..1,
      (radialKernel t R (x • p) q i : ℂ) + (radialKernel t R (x • p) (-q) i : ℂ)) =
      (Z q : ℂ)+(Z (-q) : ℂ) := by
    rw [intervalIntegral.integral_of_le zero_le_one]
    change (∫ t : ℝ, (radialKernel t R (x • p) q i : ℂ)+(radialKernel t R (x • p) (-q) i : ℂ) ∂mint) = _
    have ha : Integrable (fun t => (radialKernel t R (x • p) q i : ℂ)) mint := Complex.ofRealCLM.integrable_comp (ht q)
    have hb : Integrable (fun t => (radialKernel t R (x • p) (-q) i : ℂ)) mint := Complex.ofRealCLM.integrable_comp (ht (-q))
    rw [MeasureTheory.integral_add ha hb,
      integral_complex_ofReal,integral_complex_ofReal]
  simp_rw [hpoint]
  have ha : Integrable (fun q => (Z q : ℂ)) mplane := Complex.ofRealCLM.integrable_comp hz
  have hb : Integrable (fun q => (Z (-q) : ℂ)) mplane := Complex.ofRealCLM.integrable_comp hz.comp_neg
  rw [MeasureTheory.integral_add ha hb,integral_complex_ofReal,integral_complex_ofReal,
    integral_neg_eq_self]
  rw [show (∫ q : SectorP 0, Z q ∂mplane) =
    ∫ t : ℝ, (∫ q : SectorP 0, radialKernel t R (x • p) q i ∂mplane) ∂mint from
      integral_integral_swap (weighted_bond R (x • p) i)]
  simp_rw [radialKernel_as,MeasureTheory.integral_const_mul]
  have he (t : ℝ) : (∫ a : SectorP 0, Pill t (x • p) a * extendedTensor R (x • p) i i a ∂mplane) =
      extendedHeatValue R p.sq (p i) (p i) 1 x t := by
    simpa only [kk_self,tune] using! extended_tune R p i i x t
  simp_rw [he,intervalIntegral.integral_of_le zero_le_one]
  ring


/-- Compact-parameter formula for the actual loop carpet, including the
Lebesgue/(2π)^4 conversion and both loop orientations. -/
theorem actual_carpet_evaluated (G : Gauge) (p : SectorP 0) (i : L 0) (a b : G.ColorIndex)
    (R x : ℝ) (z : ℂ) :
    loopCarpet (cursor true).half (TwoPoint.stemPair G true) z
      (TwoPoint.word i i a b p) (R,x) =
    (-8 * (∑ d : G.ColorIndex, angle d a b) / (room : ℂ)) *
      ((∫ t : ℝ in (0:ℝ)..1,
        Real.exp (-(ν t*R^2))*extendedHeatValue R p.sq (p i) (p i) 1 x t) : ℝ) := by
  rw [actual_carpet]
  have hp := radial_payment R x p i
  rw [show mplane = ENNReal.ofReal room • (Px 0) from rfl,
    integral_smul_measure,ENNReal.toReal_ofReal room_pos.le,Complex.real_smul] at hp
  have hn : (room : ℂ) ≠ 0 := by exact_mod_cast room_pos.ne'
  simp_rw [← mul_add,intervalIntegral.integral_const_mul,MeasureTheory.integral_const_mul]
  apply (mul_left_cancel₀ hn)
  calc
    (room:ℂ) * ((∑ d : G.ColorIndex, angle d a b) * (-4 *
      (∫ q : SectorP 0, (∫ t : ℝ in (0:ℝ)..1,
        (radialKernel t R (x • p) q i : ℂ)+(radialKernel t R (x • p) (-q) i : ℂ)) ∂Px 0))) =
      (-4*(∑ d : G.ColorIndex,angle d a b)) *
        ((room:ℂ)*(∫ q : SectorP 0, (∫ t : ℝ in (0:ℝ)..1,
        (radialKernel t R (x • p) q i : ℂ)+(radialKernel t R (x • p) (-q) i : ℂ)) ∂Px 0)) := by ring
    _ = _ := by
      rw [hp]
      generalize (∫ t : ℝ in (0:ℝ)..1,
        Real.exp (-(ν t*R^2))*extendedHeatValue R p.sq (p i) (p i) 1 x t) = J
      field_simp
      ring

/-- Colour reduction uses the submitted Casimir normalization. -/
theorem actual_carpet_simple (G : Gauge) (hG : G.Simple) (p : SectorP 0) (i : L 0)
    (a b : G.ColorIndex) (R x : ℝ) (z : ℂ) :
    loopCarpet (cursor true).half (TwoPoint.stemPair G true) z
      (TwoPoint.word i i a b p) (R,x) =
    (-8 * (if a=b then (G.casimir:ℂ) else 0) / (room : ℂ)) *
      ((∫ t : ℝ in (0:ℝ)..1,
        Real.exp (-(ν t*R^2))*extendedHeatValue R p.sq (p i) (p i) 1 x t) : ℝ) := by
  rw [actual_carpet_evaluated,sums_angles hG]
end YMReview.NovemberMatching.GhostRadial
