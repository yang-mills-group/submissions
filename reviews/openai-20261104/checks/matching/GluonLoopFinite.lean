import GhostLoopSolution
import GluonLoopTrace

/-! Finite-value specification for the submitted gluon bubble, and a certified
primitive for the explicit heat integral. `SubmittedFinitePartTest` is stated
independently of that primitive. This file does not assert that test: the bridge
from the submitted noninteger-dimensional sewing to the explicit heat density
is still an analytic argument, not a theorem in this module.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open YM YM.MS YM.MS.Arts YM.MS.ScaleForest
open Plane Koszul Heat Flux Landau Book Convolve Motif Halo
open Tone Momentum Frame Wire Color Detect Native Native.Wilsonian City Logarithm Signal
open Landau.Detect.Mark Wind High Knobs Arc Rock Path Oceans Plum Alps Garment Pearl Train Shine Hem Mell
open Function Filter Set Finset MeasureTheory Real
open scoped Topology ContDiff
namespace YMReview.NovemberMatching.GluonLoop

def residue (u v : ℂ) : ℂ :=
  ((25/12)*u-(7/3)*v)/(16*(Real.pi:ℂ)^2)
def finitePart (L u v : ℂ) : ℂ :=
  (u*((25/12)*L+89/36)-v*((7/3)*L+107/36))/(16*(Real.pi:ℂ)^2)

def SubmittedFinitePartTest (G : Gauge) : Prop :=
  G.Simple → ∀ mu_bar : ℝ, 0 < mu_bar → ∀ (a b : G.ColorIndex) (p : SectorP 0)
    (i j : L 0), 0 < p.sq →
    Tendsto (fun s : ℝ => Outlook.four 4 (TwoPoint.bubble G false false).instructions.renorm
      (Real.log mu_bar + (Real.eulerMascheroniConstant-Real.log (4*Real.pi))/2,s)
      (TwoPoint.word i j a b p)) atTop
      (𝓝 ((if a=b then (G.casimir:ℂ) else 0)*
        finitePart (Real.log (mu_bar^2/p.sq):ℂ)
          (if i=j then (p.sq:ℂ) else 0) ((p i:ℂ)*(p j:ℂ))))

theorem submitted_finite_reading (G : Gauge) (y s : ℝ) :
    Outlook.four 4 (TwoPoint.bubble G false false).instructions.renorm (y,s) =
      oneLoopFinite 4 (TwoPoint.ratePair G false false) s y 0 := by
  have h := (twoVertex_laurent (interaction G 1) (interaction G 1)
    (cursor false) (cursor false)).2.2 s y
  exact congrArg (fun F:Mob G=>F 0) (YM.MS.Pearl.chosen (n:=0) h).symm

theorem source_price (G : Gauge) : kPrice (TwoPoint.ratePair G false false 0) :=
  (close_form (G:=G) (cursor false)
    (firstResult (interaction G 1) (interaction G 1) (cursor false))).2.price

theorem submitted_finite_derivative (G : Gauge) (s y : ℝ) (m : ℕ)
    (w : List (Shore G m)) :
    HasDerivAt (fun s:ℝ=>oneLoopFinite 4 (TwoPoint.ratePair G false false) s y m w)
      (YM.MS.Alps.plow (-4) s (TwoPoint.ratePair G false false 0) m w) s := by
  exact GhostFlow.finite_derivative _ (source_price G) s y m w

def forceValue (v X : ℝ) : ℝ :=
  (-28+112*v)/X^2+(50-68*v)/X+12-3*v+
    Real.exp (-X/2)*((28-112*v)/X^2+(-36+12*v)/X-101/4+23*v+(-27/8+3*v)*X)
def a (v:ℝ) := 14/3-56*v/3
def b (v:ℝ) := -25/2+17*v
def c (v:ℝ) := -6+3*v/2
def d (v:ℝ) := -14/3+56*v/3
def e (v:ℝ) := 61/6-23*v/3
def f (v:ℝ) := 181/24-23*v/3
def k (v:ℝ) := -25/12+7*v/3
def rationalPart (v X:ℝ) :=
  a v/X^3+b v/X^2+c v/X+
    Real.exp (-X/2)*(d v/X^3+e v/X^2+f v/X)
def primitive (v X:ℝ) := rationalPart v X+k v*GhostMellin.expTail (X/2)
def finiteConstant (v:ℝ) := (-173+179*v)/72+k v*(Real.log 2-Real.eulerMascheroniConstant)

theorem primitive_deriv (v X:ℝ) (hX:X≠0) :
    HasDerivAt (primitive v) (forceValue v X/(2*X^2)) X := by
  have hpow (n:ℕ) (q:ℝ) : HasDerivAt (fun X:ℝ=>q/X^n)
      (-(q*(n:ℝ)*X^(n-1))/((X^n)^2)) X := by
    convert! (hasDerivAt_const X q).div (hasDerivAt_pow n X) (pow_ne_zero _ hX) using 1
    ring
  have he := (((hasDerivAt_id' X).neg.div_const 2).exp)
  have hr := (((hpow 3 (a v)).add (hpow 2 (b v))).add (hpow 1 (c v))).add
    (he.mul (((hpow 3 (d v)).add (hpow 2 (e v))).add (hpow 1 (f v))))
  have ht := (GhostMellin.expTail_deriv (X/2) (div_ne_zero hX (by norm_num))).comp X
    ((hasDerivAt_id' X).div_const 2)
  convert! hr.add (ht.const_mul (k v)) using 1
  · funext Y
    simp only [primitive,rationalPart,Pi.add_apply,Pi.mul_apply,Pi.neg_apply,Function.comp_def,pow_one]
  · unfold a b c d e f k forceValue
    norm_num
    field_simp
    ring

theorem primitive_large (v:ℝ) : Tendsto (primitive v) atTop (𝓝 0) := by
  have h (q:ℝ) (n:ℕ) (hn:n≠0) : Tendsto (fun X:ℝ=>q/X^n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop hn)
  have he : Tendsto (fun X:ℝ=>Real.exp (-X/2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.atBot_div_const (by norm_num : (0:ℝ)<2))
  have hr := (((h (a v) 3 (by decide)).add (h (b v) 2 (by decide))).add
    (h (c v) 1 (by decide))).add (he.mul (((h (d v) 3 (by decide)).add
      (h (e v) 2 (by decide))).add (h (f v) 1 (by decide))))
  have ht := GhostMellin.expTail_large.comp
    (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<2))
  convert! hr.add (ht.const_mul (k v)) using 1
  · funext X
    simp only [primitive,rationalPart,pow_one,Function.comp_def,id_eq]
  · simp

theorem rationalPart_small (v:ℝ) :
    Tendsto (fun X:ℝ=>rationalPart v X+33/(8*X)) (𝓝[>] (0:ℝ))
      (𝓝 ((-173+179*v)/72)) := by
  let N (X:ℝ) := d v+e v*X+f v*X^2
  let P (X:ℝ) := -d v/48+e v/8-f v/2+X*(-e v/48+f v/8)-X^2*f v/48
  have hN : Continuous N := by unfold N; fun_prop
  have hP : Continuous P := by unfold P; fun_prop
  have hh := ((GhostPrimitive.expRemainder_small.mul (hN.tendsto 0)).add
    (hP.tendsto 0)).mono_left (nhdsWithin_le_nhds (s:=Set.Ioi (0:ℝ)))
  have h0 : (0:ℝ)*N 0+P 0=(-173+179*v)/72 := by unfold N P d e f; ring
  rw [h0] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with X hX
  have hx:X≠0 := ne_of_gt hX
  unfold N P rationalPart GhostPrimitive.expRemainder a b c d e f
  field_simp
  ring

theorem primitive_small (v:ℝ) :
    Tendsto (fun X:ℝ=>primitive v X+33/(8*X)+k v*Real.log X)
      (𝓝[>] (0:ℝ)) (𝓝 (finiteConstant v)) := by
  have hX : Tendsto (fun X:ℝ=>X/2) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using ((continuous_id.div_const (2:ℝ)).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with X hX
      change 0<X/2
      exact div_pos hX (by norm_num)
  have ht := ((GhostMellin.expTail_small.comp hX).add_const (Real.log 2)).const_mul (k v)
  have hh := (rationalPart_small v).add ht
  convert! hh.congr' (show (fun X:ℝ=>(rationalPart v X+33/(8*X))+
      k v*((GhostMellin.expTail (X/2)+Real.log (X/2))+Real.log 2)) =ᶠ[𝓝[>] (0:ℝ)]
      (fun X:ℝ=>primitive v X+33/(8*X)+k v*Real.log X) from ?_) using 1
  · unfold finiteConstant
    ring
  filter_upwards [self_mem_nhdsWithin] with X hx
  rw [Real.log_div (ne_of_gt hx) (by norm_num : (2:ℝ)≠0)]
  unfold primitive
  ring

def jet (v:ℝ) := (5/72-35*v/72)+k v*(Real.log 2-Real.log (4*Real.pi))

theorem finite_constants (v y:ℝ) :
    -finiteConstant v+jet v-2*y*k v =
      (25/12-7*v/3)*(2*y-Real.eulerMascheroniConstant+Real.log (4*Real.pi))+
        89/36-107*v/36 := by
  unfold finiteConstant jet k
  ring

end YMReview.NovemberMatching.GluonLoop
#print axioms YMReview.NovemberMatching.GluonLoop.submitted_finite_reading
#print axioms YMReview.NovemberMatching.GluonLoop.submitted_finite_derivative
#print axioms YMReview.NovemberMatching.GluonLoop.primitive_deriv
#print axioms YMReview.NovemberMatching.GluonLoop.primitive_large
#print axioms YMReview.NovemberMatching.GluonLoop.primitive_small
#print axioms YMReview.NovemberMatching.GluonLoop.finite_constants
