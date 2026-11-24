import GhostLoopMellin
/-!
# A normalized primitive for the physical force

Proves the derivative and both endpoint limits of the explicit force
primitive. The small-argument expansion retains the Euler constant and
logarithm needed to compare subtraction conventions.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open Function Filter Set Finset MeasureTheory Metric Real Asymptotics
open scoped BigOperators Topology ContDiff
namespace YMReview.NovemberMatching.GhostPrimitive
open GhostInfrared GhostMellin

def a (v:ℝ) := (-1+4*v)/3
def b (v:ℝ) := 5/24-v/12
def c (v:ℝ) := -5/192-5*v/24
def d (v:ℝ) := -v/64
def e (v:ℝ) := -3/8+3*v/4
def k (v:ℝ) := (1+2*v)/48

def rationalPart (v X:ℝ) :=
  Real.exp (-X/2)*(a v/X^3+b v/X^2+c v/X+d v)-a v/X^3+e v/X^2

def primitive (v X:ℝ) := rationalPart v X+k v*expTail (X/2)
def finiteConstant (v:ℝ) := 53/1152+29*v/576+k v*(Real.log 2-Real.eulerMascheroniConstant)

lemma primitive_deriv (v X:ℝ) (hX:X≠0) :
    HasDerivAt (primitive v) (forceValue v X/(2*X^2)) X := by
  have hpow (n:ℕ) (q:ℝ) : HasDerivAt (fun X:ℝ=>q/X^n)
      (-(q*(n:ℝ)*X^(n-1))/((X^n)^2)) X := by
    convert! (hasDerivAt_const X q).div (hasDerivAt_pow n X) (pow_ne_zero _ hX) using 1
    ring
  have he := (((hasDerivAt_id' X).neg.div_const 2).exp)
  have hr := (((he.mul ((((hpow 3 (a v)).add (hpow 2 (b v))).add (hpow 1 (c v))).add_const (d v))).sub
    (hpow 3 (a v))).add (hpow 2 (e v)))
  have ht := (expTail_deriv (X/2) (div_ne_zero hX (by norm_num))).comp X ((hasDerivAt_id' X).div_const 2)
  convert! hr.add (ht.const_mul (k v)) using 1
  · funext Y
    simp only [primitive,rationalPart,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.neg_apply,Function.comp_def,pow_one]
  · simp only [Pi.add_apply,Pi.neg_apply]
    unfold a b c d e k forceValue
    norm_num
    field_simp
    ring

lemma rationalPart_large (v:ℝ) : Tendsto (rationalPart v) atTop (𝓝 0) := by
  have h (q:ℝ) (n:ℕ) (hn:n≠0) : Tendsto (fun X:ℝ=>q/X^n) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop (tendsto_pow_atTop hn)
  have he : Tendsto (fun X:ℝ=>Real.exp (-X/2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.atBot_div_const (by norm_num : (0:ℝ)<2))
  change Tendsto (fun X:ℝ=>Real.exp (-X/2)*(a v/X^3+b v/X^2+c v/X+d v)-a v/X^3+e v/X^2) atTop (𝓝 0)
  convert! ((he.mul ((((h (a v) 3 (by decide)).add (h (b v) 2 (by decide))).add
    (h (c v) 1 (by decide))).add_const (d v))).sub (h (a v) 3 (by decide))).add
      (h (e v) 2 (by decide)) using 1 <;> simp

lemma primitive_large (v:ℝ) : Tendsto (primitive v) atTop (𝓝 0) := by
  have ht := expTail_large.comp (tendsto_id.atTop_div_const (by norm_num : (0:ℝ)<2))
  convert! (rationalPart_large v).add (ht.const_mul (k v)) using 1
  simp

def expRemainder (X:ℝ) := (Real.exp (-X/2)-1+X/2-X^2/8+X^3/48)/X^3

lemma expRemainder_small : Tendsto expRemainder (𝓝 (0:ℝ)) (𝓝 0) := by
  have he := (Real.exp_sub_sum_range_succ_isLittleO_pow 3).tendsto_div_nhds_zero
  have hX : Tendsto (fun X:ℝ=> -X/2) (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := by
    simpa using ((continuous_id.neg.div_const 2).tendsto (0:ℝ))
  have ht := (he.comp hX).const_mul (-1/8:ℝ)
  norm_num only [mul_zero] at ht
  apply ht.congr'
  apply Eventually.of_forall
  intro X
  simp only [Function.comp_def,Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,
    Nat.factorial_succ,Nat.factorial_zero,Nat.cast_mul,pow_zero]
  unfold expRemainder
  by_cases hx:X=0
  · subst X; simp
  field_simp
  ring

lemma rationalPart_small (v:ℝ) : Tendsto (fun X:ℝ=>rationalPart v X+11/(64*X))
    (𝓝[>] (0:ℝ)) (𝓝 (53/1152+29*v/576)) := by
  let N (X:ℝ) := a v+b v*X+c v*X^2+d v*X^3
  let P (X:ℝ) := (-a v/48+b v/8-c v/2+d v)+
    X*(-b v/48+c v/8-d v/2)+X^2*(-c v/48+d v/8)-X^3*d v/48
  have hN : Continuous N := by unfold N; fun_prop
  have hP : Continuous P := by unfold P; fun_prop
  have hh := ((expRemainder_small.mul (hN.tendsto 0)).add (hP.tendsto 0)).mono_left (nhdsWithin_le_nhds (s:=Set.Ioi (0:ℝ)))
  have h0 : (0:ℝ)*N 0+P 0=53/1152+29*v/576 := by unfold N P a b c d; ring
  rw [h0] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with X hX
  have hx : X≠0 := ne_of_gt hX
  unfold N P rationalPart expRemainder a b c d e
  field_simp
  ring

lemma primitive_small (v:ℝ) : Tendsto
    (fun X:ℝ=>primitive v X+11/(64*X)+k v*Real.log X)
    (𝓝[>] (0:ℝ)) (𝓝 (finiteConstant v)) := by
  have hX : Tendsto (fun X:ℝ=>X/2) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_,?_⟩
    · simpa using ((continuous_id.div_const 2).tendsto (0:ℝ)).mono_left (nhdsWithin_le_nhds (s:=Set.Ioi (0:ℝ)))
    filter_upwards [self_mem_nhdsWithin] with X hx
    change 0<X/2
    exact div_pos hx (by norm_num)
  have ht := ((expTail_small.comp hX).add_const (Real.log 2)).const_mul (k v)
  have hh := (rationalPart_small v).add ht
  convert! hh.congr' (show (fun X:ℝ=>(rationalPart v X+11/(64*X))+
      k v*((expTail (X/2)+Real.log (X/2))+Real.log 2)) =ᶠ[𝓝[>] (0:ℝ)]
      (fun X:ℝ=>primitive v X+11/(64*X)+k v*Real.log X) from ?_) using 1
  · unfold finiteConstant
    ring
  filter_upwards [self_mem_nhdsWithin] with X hx
  rw [Real.log_div (ne_of_gt hx) (by norm_num : (2:ℝ)≠0)]
  unfold primitive
  ring
end YMReview.NovemberMatching.GhostPrimitive
