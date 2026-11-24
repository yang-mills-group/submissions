import GhostConventionCheck
import GhostLoopFiniteEvaluation
import Mathlib.Tactic

/-!
# Ghost-loop contraction in arbitrary auxiliary sectors

Generalizes the submitted physical-sector contraction calculations in
`YM/MS/ScaleForest/TracedCubic.lean`, `LoadB.lean`, and `Bubbles.lean`.
Several intermediate proofs are adapted from those Apache-2.0 source files;
the first cubic-vertex evaluation uses the independent convention check.
The final trace is of the actual submitted vertices and selected lines.
This file does not by itself evaluate the finite renormalized graph.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open YM YM.MS YM.MS.Arts YM.MS.ScaleForest
open Plane Koszul Heat Flux Landau Book Convolve Motif Halo
open scoped BigOperators
namespace YMReview.NovemberMatching.GhostTrace
variable {G : Gauge} {n : ℕ}
abbrev C (G : Gauge) (n : ℕ) := pulseX G 1 n
abbrev W (i : L n) (a : G.ColorIndex) (p : SectorP n) : Shore G n := vec i a p
abbrev U (i : L n) (a : G.ColorIndex) (p : SectorP n) : Shore G n := (onX true (some i,a),p)
abbrev c (a : G.ColorIndex) (p : SectorP n) : Shore G n := (onX false (none,a),p)


lemma cubic_UWc (i j : L n) (a b d : G.ColorIndex) (q p k : SectorP n) :
    C G n [U i a q, W j b p, c d k] = if i=j then rune b d a else 0 := by
  have h := congrArg (fun F : Mob G => F n [U i a q,W j b p,c d k]) (Class_at G 1)
  simp only [χ, map_add, Literal.value_sl, one_pow, one_smul, Pi.add_apply, Pi.sub_apply] at h
  have hz : B₂ G n [U i a q,W j b p,c d k] = 0 := by
    have h2 := YM.WilsonMS.LoopRank.R_action G 2 n
    have he : pulseX G 2 = B₂ G := by simp [pulseX, Literal.hiss, χ]
    rw [he] at h2
    exact h2 _ (by norm_num [mod_int])
  rw [hz, add_zero] at h
  unfold C
  rw [pulse1, h]
  change ploy G 1 n [(onX true (some i,a),q),(onX false (some j,b),p),(onX false (none,d),k)] -
    ploy G 0 n [(onX true (some i,a),q),(onX false (some j,b),p),(onX false (none,d),k)] = _
  rw [GhostCheck.classical_ghost_gluon, GhostCheck.classical_ghost_gluon]
  simp


open YM.WilsonMS.BetaValue
open Function Filter Set Finset MeasureTheory Metric Real
open Tone Momentum Frame Wire Color Detect Native Native.Wilsonian City Logarithm Signal
open Landau.Detect.Mark Wind High Knobs Arc Rock Path Oceans Plum Alps Garment Pearl
open Complex (I)
abbrev Cubic (G : Gauge) : Rack G n := C G n
abbrev HeatLine (G : Gauge) (r : ℝ) : Flux (Cfield G n) (SectorP n) ℂ := radial G r n
lemma dim_cub : Book.rank 3 (Cubic G (n:=n)) := YM.WilsonMS.LoopRank.R_action G 1 n
lemma none_cub (w : Legs (Shore G n)) (hp : w.length ≠ 3) : Cubic G w=0 :=
  dim_cub w (by rw [mod_int]; omega)
lemma cubic_swap (l L : List (Shore G n)) (i j : Shore G n) :
    Cubic G (l ++ i :: j :: L) = cross (parity i.1) (parity j.1) * Cubic G (l ++ j :: i :: L) :=
  (fund_one G n).sym ..
lemma cubic_charge (l : List (Shore G n)) (h : fieldDim ghostNo l ≠ 0) : Cubic G l = 0 :=
  (fund_one G n).ghost l h
lemma cubic_solid : Solid true (Cubic G (n:=n)) 0 :=
  ⟨fun l i j k _ => (fund_one G n).sym l i j k,
   fun v _ hv => (fund_one G n).ghost v hv,
   fun w _ p => congrFun (folk 1 n p) w,
   fun w _ => (fund_one G n).sense w⟩
lemma CAplus (a b d : G.ColorIndex) (p q r : SectorP n) (x y : L n) (_h : p+(q+r)=0) :
    Cubic G [U x a p, W y b q, c d r] = if x=y then fColor a b d else 0 := by
  change C G n _ = _
  rw [cubic_UWc, ← f_att, ← r_clock a b d]

abbrev LaneHeat (G : Gauge) :=
  Flux (Cfield G n) (SectorP n) ℂ
abbrev Exchange (K : LaneHeat G (n:=n)) : Rack G n := tree parity K (Cubic G) (Cubic G)
local notation "γ" => field parity

private lemma pot_grade (l : List (Shore G n)) :
    degree (field parity) l = (if fieldDim ghostNo l % 2 = 1 then true else false) := by
  induction l with
  | nil => simp [fieldDim]
  | cons i w ih =>
    rw [degree_cons, field_cons, ih]
    rcases i with ⟨⟨⟨_ | i, _ | _⟩, u⟩, p⟩
    all_goals
      unfold ghostNo ghostChannel field parity Landau.p
      dsimp only
      split_ifs <;>
        first
        | rfl
        | omega

abbrev HitM (K : LaneHeat G (n:=n)) (F : Rack G n) (l r : Legs (Shore G n)) :=
  attaches parity K (Cubic G) F l r

lemma law_S (r : ℝ) : Reverse (HeatLine G (n:=n) r) parity :=
  reverse_one (id : SectorP n → SectorP n) (L_rev r) (fun _ => rfl)

variable {T P : Rack G n} {K : LaneHeat G (n:=n)}

lemma swap_funding {l v : Legs (Shore G n)} (hp : net l + net v = 0) (h : Reverse K parity)
    (hx : Solid true P 0) (hs : Solid true T 0) :
    attaches parity K P T v l = cross (degree γ v) (degree γ l) * attaches parity K T P l v := by
  rw [convertR h, convertR h, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw (occs := .pos [1]) [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  unfold radius
  dsimp only
  rw [h j i (net v)]
  have hv : (-net v) = net l := by rw [add_eq_zero_iff_eq_neg.mp hp]
  have ht : (-net l) = net v := by rw [add_eq_zero_iff_eq_neg.mp hp, neg_neg]
  rw [hv, ht, hv]
  let q := (j, net l)
  let x := (i, net v)
  have hV : Course true (q :: v) := fun _ => by
    rw [net_cons]
    exact hp
  have hv' : Course true (x :: l) := fun _ => by
    rw [net_cons]
    exact (add_comm _ _).trans hp
  by_cases hL : P (q :: v) = 0
  · rw [show P ((j, net l) :: v) = _ from hL]
    ring
  by_cases hP : T (x :: l) = 0
  · rw [show T ((i, net v) :: l) = _ from hP]
    ring
  have he (w : Legs (Shore G n)) (i : Shore G n) (F : Rack G n) (hF : Solid true F 0)
    (H : Course true (i :: w)) (ht : F (i :: w) ≠ 0) : degree γ w = parity i.1 := by
    have hu : degree γ (i :: w) = false := by
      rw [pot_grade,
        show fieldDim ghostNo (i :: w) = 0 from
          (by
            by_contra hh
            exact ht (hF.ghost _ H hh)),
        if_neg (by decide)]
    cases hi : degree γ w <;> cases hp : parity i.1 <;>
      simp only [degree_cons, hi, show field parity i = _ from hp] at hu
    all_goals
      first
      | rfl
      | contradiction
  rw [he v q P hx hV hL, he l x T hs hv' hP]
  change 2 * (_ * K i j _) * (cross _ _ * _) * _ = cross _ _ * _
  simp only [x, q]
  cases hi : parity i <;> cases hj : parity j <;> simp <;> ring

lemma swap_tree (hp : Reverse K parity) (hx : Solid true P 0) (hs : Solid true T 0)
    (w : List (Shore G n)) (he : net w = 0) : tree parity K P T w = tree parity K T P w := by
  unfold tree
  rw [Motif.swap]
  apply scatter_congr
  intro u v hv
  rw [swap_funding ((split_net hv).trans he) hp hx hs, ← mul_assoc,
    cross_comm (degree γ v) (degree γ u), cross_cross, one_mul]

lemma hit_only (hp : Reverse K parity) (u v : Legs (Shore G n)) (t : u.length ≠ 2) : HitM K T u v = 0 := by
  rw [HitM, convertR hp]
  exact
    Finset.sum_eq_zero fun i _ =>
      Finset.sum_eq_zero fun j _ => by
        unfold radius
        dsimp only
        rw [none_cub (_ :: u)
            (by
              simp
              omega)]
        ring

variable (i j k l m : Shore G n)
local notation "Q(" i "," j ")" => (cross (γ i) (γ j) : ℂ)

lemma grant_four (hp : Reverse K parity) :
    tree parity K (Cubic G) T [i, j, k, l] =
      HitM K T [i, j] [k, l] + Q(j,k) * HitM K T [i, k] [j, l] +
              Q(j,l) * Q(k,l) * HitM K T [i, l] [j, k] +
            Q(i,j) * Q(i,k) * HitM K T [j, k] [i, l] +
          Q(i,j) * Q(i,l) * Q(k,l) * HitM K T [j, l] [i, k] +
        Q(i,k) * Q(i,l) * Q(j,k) * Q(j,l) * HitM K T [k, l] [i, j] := by
  unfold tree
  simp only [scatter_cons, scatter_nil]
  have h u v (he : u.length ≠ 2) : attaches parity K (Cubic G) T u v = 0 := hit_only hp u v he
  rw [h [i, j, k, l] [] (by simp), h [] [i, j, k, l] (by simp), h [i, j, l] _ (by simp),
    h [j, k, l] _ (by simp), h [i, k, l] _ (by simp), h [i, j, k] _ (by simp), h [i] _ (by simp),
    h [j] _ (by simp), h [k] _ (by simp), h [l] _ (by simp)]
  simp_rw [degree_cons, degree_nil, cross_right, cross_false', mul_one]
  unfold HitM
  ring

lemma book_exchange (hp : Reverse K parity) (h : net [i, j, k, l] = 0) :
    Exchange K [i, j, k, l] =
      2 *
        (HitM K (Cubic G) [i, j] [k, l] + Q(j,k) * HitM K (Cubic G) [i, k] [j, l] +
          Q(j,l) * Q(k,l) * HitM K (Cubic G) [i, l] [j, k]) := by
  have ht := cubic_solid (G:=G) (n:=n)
  change Solid true (Cubic G) 0 at ht
  simp only [net_cons, show net ([] : Legs (Shore G n)) = 0 from rfl, add_zero] at h
  rw [Exchange, grant_four i j k l hp]
  have he (a b : List (Shore G n)) (he : net b + net a = 0) : HitM K (Cubic G) a b = _ :=
    swap_funding he hp ht ht
  rw [he [j, k] _
      (by
        simp [net]
        rw [← h]
        abel),
    he [j, l] _
      (by
        simp [net]
        rw [← h]
        abel),
    he [k, l] _
      (by
        simp [net]
        rw [← h]
        abel)]
  cases hi : γ i <;> cases hj : γ j <;> cases hk : γ k <;> cases hl : γ l <;>
    simp only [degree_cons, hi, hj, hk, hl, degree_nil]
  all_goals
    norm_num [cross]
    unfold HitM
    ring




section gather
variable {G : Gauge} (K : LaneHeat G (n:=n)) (hx : Reverse K parity)
variable (r : ℝ) (F : Rack G n) (i j : CI G) (p q : SectorP n) (x y : L n) (w μ : Legs (Shore G n))

abbrev Aℓ (x : L n) (i : CI G) : Cfield G n :=
  (Landau.gauge x, i)

abbrev Uℓ (x : L n) (i : CI G) : Cfield G n :=
  (anti x, i)

abbrev Cℓ (i : CI G) : Cfield G n :=
  (ghost, i)

abbrev Sℓ (i : CI G) : Cfield G n :=
  (gaugeC, i)



lemma sprint (H : Cfield G n → Cfield G n → ℂ) :
    (∑ a, ∑ b, HeatLine G r a b p * H a b) =
      ∑ i : CI G,
        ((∑ a : L n, ∑ b : L n, HeatLine G r (Aℓ a i) (Aℓ b i) p * H (Aℓ a i) (Aℓ b i)) +
          ∑ a : L n,
            (HeatLine G r (Uℓ a i) (Cℓ i) p * H (Uℓ a i) (Cℓ i) +
              HeatLine G r (Cℓ i) (Uℓ a i) p * H (Cℓ i) (Uℓ a i))) := by
  simp only [HeatLine, Landau.choir, Aℓ, Cℓ, Uℓ]
  simp only [↓reduceIte]
  simp only [Fintype.sum_prod_type, Fintype.sum_option, id_eq, ite_mul]
  simp only [Fintype.sum_bool, L0, zero_mul]
  simp only [Landau.gauge, Landau.ghost, Landau.anti]
  simp [Finset.sum_add_distrib]
  simp_rw [Finset.sum_comm (t := Finset.univ (α := G.ColorIndex)) (s := Finset.univ (α := L n))]
  ring

include hx

lemma hit_light (he : net w = 0) (hp : ∀ i j, K i j 0 = 0) : HitM K F w μ = 0 := by
  rw [HitM, convertR hx]
  simp only [radius, he, neg_zero, hp, mul_zero, zero_mul, Finset.sum_const_zero]

lemma hit_fade (l k : Shore G n) :
    HitM K F [l, k] μ = (cross (parity l.1) (parity k.1) : ℂ) * HitM K F [k, l] μ := by
  rw [HitM, HitM, convertR hx, convertR hx, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [radius, radius]
  rw [show net [l, k] = net [k, l] from (by simp [net, add_comm]),
    show degree (field parity) [l, k] = degree (field parity) [k, l] from ?_,
    show Cubic G (_ :: [l, k]) = _ from cubic_swap [(i, -net [k, l])] [] l k]
  simp only [List.cons_append, List.nil_append]
  ring
  exact
    (by
      simp only [degree_cons, degree_nil, Bool.xor_false]
      rw [Bool.xor_comm])
omit hx
local notation "℘" => HeatLine G r
local notation "Z" => net w
local notation "Λ(" a "," b ")" => radius (Landau.parity) ℘ a b (Cubic G) F w μ

lemma group_hit :
    HitM ℘ F w μ =
      ∑ i : CI G,
        ((∑ a : L n, ∑ b : L n, Λ(Aℓ a i,Aℓ b i)) +
          ∑ a : L n, (Λ(Uℓ a i,Cℓ i) + Λ(Cℓ i,Uℓ a i))) := by
  rw [HitM, convertR (law_S r)]
  let H (a b : Cfield G n) : ℂ :=
    2 * (cross (parity b) (degree (field parity) w) * Cubic G ((a, -net w) :: w)) *
      F ((b, -(-net w)) :: μ)
  have hp (a b : Cfield G n) : Λ(a,b) = ℘ a b (-net w) * H a b := by
    unfold H radius
    dsimp only
    ring
  simp_rw [hp]
  exact sprint r (-net w) H



lemma forward_AC (m : CI G) :
    Cubic G [W x i p, U y j q, c m (-(p + q))] = if y = x then fColor j i m else 0 := by
  rw [show Cubic G [W x i p, U y j q, c m (-(p + q))] = Q(W x i p,U y j q) * _ from
      cubic_swap [] [c m (-(p + q))] _ _]
  rw [List.nil_append, CAplus j i m q p _ y x (by abel)]
  exact one_mul _

end gather

section clicks
variable {G : Gauge}
variable (r : ℝ) (F : Rack G n) (i j : CI G) (p q : SectorP n) (x y : L n) (w μ : Legs (Shore G n))
local notation "K" => HeatLine G r

local notation "Ψ(" a "," b "," w ")" => radius parity K a b (Cubic G) F w μ

abbrev press_hit (w : Legs (Shore G n)) :=
  fieldDim ghostNo w
section selection

private lemma lost_hit (a b : Cfield G n) (l : Legs (Shore G n)) (h : ghostNo a + fieldDim ghostNo l ≠ 0) :
    Ψ(a,b,l) = 0 := by
  unfold radius
  dsimp only
  rw [cubic_charge (_ :: l)
      (show fieldDim ghostNo ((a, -net l) :: l) ≠ 0 from
        (by
          rw [field_cons]
          exact h))]
  ring

lemma empty_hit (l : Legs (Shore G n)) (h : fieldDim ghostNo l ≠ 0) (hx : fieldDim ghostNo l ≠ 1)
    (ht : fieldDim ghostNo l ≠ -1) : HitM K F l μ = 0 := by
  rw [group_hit]
  apply Finset.sum_eq_zero
  intro i _
  rw [Finset.sum_eq_zero (s := Finset.univ)
      (fun a _ => Finset.sum_eq_zero (fun b _ => lost_hit r F μ _ _ l ?_)),
    Finset.sum_eq_zero (s := Finset.univ) ?_, add_zero]
  swap
  · change 0 + _ ≠ _
    rwa [zero_add]
  intro a _
  rw [lost_hit r F μ (Uℓ a i) (Cℓ i) _ (show -1 + _ ≠ 0 from (by omega)),
    lost_hit r F μ (Cℓ i) (Uℓ a i) _ (show 1 + fieldDim ghostNo l ≠ 0 from (by omega)), add_zero]

lemma θ_W (l : Legs (Shore G n)) (h : fieldDim ghostNo l = 0) :
    HitM K F l μ = ∑ i : CI G, ∑ a : L n, ∑ b : L n, Ψ(Aℓ a i,Aℓ b i,l) := by
  rw [group_hit]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_zero (f := fun a => Ψ(Uℓ a i,Cℓ i,l) + Ψ(Cℓ i,Uℓ a i,l)) ?_, add_zero]
  intro a _
  rw [lost_hit r F μ (Uℓ a i) (Cℓ i) l (show (-1 : ℤ) + fieldDim ghostNo l ≠ 0 from (by omega)),
    lost_hit r F μ (Cℓ i) (Uℓ a i) l (show (1 : ℤ) + fieldDim ghostNo l ≠ 0 from (by omega)),
    add_zero]

lemma θ_U (l : Legs (Shore G n)) (h : fieldDim ghostNo l = 1) :
    HitM K F l μ = ∑ i : CI G, ∑ a : L n, Ψ(Uℓ a i,Cℓ i,l) := by
  rw [group_hit]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_zero (f := fun a : L n => ∑ b : L n, Ψ(Aℓ a i,Aℓ b i,l)) ?_, zero_add]
  · apply Finset.sum_congr rfl
    intro a _
    rw [lost_hit r F μ (Cℓ i) (Uℓ a i) l (show 1 + fieldDim ghostNo l ≠ 0 from (by omega)), add_zero]
  intro a _
  exact
    Finset.sum_eq_zero fun b _ =>
      lost_hit r F μ (Aℓ a i) (Aℓ b i) l (show 0 + fieldDim ghostNo l ≠ 0 from (by omega))

lemma θ_C (l : Legs (Shore G n)) (h : fieldDim ghostNo l = -1) :
    HitM K F l μ = ∑ i : CI G, ∑ a : L n, Ψ(Cℓ i,Uℓ a i,l) := by
  rw [group_hit]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_zero (f := fun a : L n => ∑ b : L n, Ψ(Aℓ a i,Aℓ b i,l)) ?_, zero_add]
  · apply Finset.sum_congr rfl
    intro a _
    rw [lost_hit r F μ (Uℓ a i) (Cℓ i) l (show -1 + fieldDim ghostNo l ≠ 0 from (by omega)), zero_add]
  intro a _
  exact
    Finset.sum_eq_zero fun b _ =>
      lost_hit r F μ (Aℓ a i) (Aℓ b i) l (show 0 + fieldDim ghostNo l ≠ 0 from (by omega))
end selection
section color

abbrev Lace (r : ℝ) (p : SectorP n) (a b : L n) : ℂ :=
  (City.brush r p * precision a b p : ℝ)

abbrev SpanH (r : ℝ) (p : SectorP n) (a : L n) : ℂ :=
  I * (City.brush r p : ℂ) * (p.sq : ℂ) * p a

lemma atAA (i : CI G) : K (Aℓ x i) (Aℓ y i) p = Lace r p x y :=
  if_pos rfl

lemma atUC (i : CI G) : K (Uℓ x i) (Cℓ i) p = SpanH r p x := by
  simp [HeatLine, Landau.choir, SpanH, L0]
  ring

lemma atCU (i : CI G) : K (Cℓ i) (Uℓ x i) p = SpanH r p x :=
  (show K (Cℓ i) (Uℓ x i) p = K (Uℓ x i) (Cℓ i) p from rfl).trans (atUC ..)
local notation "s" => p + q

lemma clickWW :
    HitM K F [W x i p, W y j q] μ =
      ∑ k : CI G,
        ∑ a : L n,
          ∑ b : L n,
            2 * Lace r (-s) a b * (Cubic G [W a k (-s), W x i p, W y j q]) * F (W b k s :: μ) := by
  let w := [W x i p, W y j q]
  rw [θ_W _ _ μ w rfl]
  simp_rw [radius,
    show net w = s from
      (by
        unfold w
        simp [net, W]),
    neg_neg, atAA (G := G)]
  change
    (∑ k : CI G,
        ∑ a : L n,
          ∑ b : L n, 2 * Lace r _ a b * ((1 : ℂ) * Cubic G ((_, _) :: w)) * F ((Aℓ b k, s) :: μ)) =
      _
  simp only [one_mul]
  rfl

lemma clickWC :
    HitM K F [W x i p, c j q] μ =
      ∑ k : CI G, 2 * SpanH r (-(p + q)) x * (-fColor k i j) * F (c k (p + q) :: μ) := by
  rw [θ_U _ _ μ _ (show fieldDim ghostNo [W x i p, c j q] = 1 from rfl)]
  refine Finset.sum_congr rfl fun k _ => ?_
  let l := [W x i p, c j q]
  have hn : net l = s := by simp [net, l, W, c]
  have ht (a : L n) :
    Ψ(Uℓ a k,Cℓ k,l) = 2 * SpanH r (-s) a * (-(if a = x then fColor k i j else 0)) * F (c k s :: μ) := by
    unfold radius
    dsimp only
    rw [hn, neg_neg, atUC (G := G)]
    change _ * ((-1 : ℂ) * Cubic G [U a k _, W x i p, c j q]) * _ = _
    rw [CAplus k i j (-s) p q a x (by abel), neg_one_mul]
    rfl
  rw [Finset.sum_eq_single x, ht, if_pos rfl]
  intro b _ hB
  rw [ht b, if_neg hB, neg_zero, mul_zero, zero_mul]
  simp


end color
end clicks

lemma wing_CUW (i j k : G.ColorIndex) (p q : SectorP n) (x y : L n) (s : SectorP n)
    (he : p+(q+s)=0) :
    Cubic G [c i p,U y k s,W x j q] = -(if y=x then fColor k j i else 0) := by
  have h1 := cubic_swap (G:=G) [] [W x j q] (c i p) (U y k s)
  have h2 := cubic_swap (G:=G) [U y k s] [] (c i p) (W x j q)
  change Cubic G [c i p,U y k s,W x j q] = (-1:ℂ)*Cubic G [U y k s,c i p,W x j q] at h1
  change Cubic G [U y k s,c i p,W x j q] = (1:ℂ)*Cubic G [U y k s,W x j q,c i p] at h2
  rw [h1,h2,CAplus k j i s q p y x (by abel_nf at he ⊢; exact he)]
  ring


section trace
abbrev Km (r : ℝ) (S : Bool) : Rip G := TwoPoint.Km r S
lemma Span_neg (r : ℝ) (p : SectorP n) (x : L n) : SpanH r (-p) x = -SpanH r p x := by
  simp [SpanH, City.brush]
lemma Km0 (r : ℝ) (σ : Bool) (i j : Cfield G n) : Km r σ n i j 0=0 := by
  unfold Km TwoPoint.Km pickLine
  split
  · rcases i with ⟨⟨_ | a, _ | _⟩, i⟩ <;> rcases j with ⟨⟨_ | b, _ | _⟩, j⟩ <;>
      simp [radial, City.LegsK, Landau.choir, City.L0, Momentum.sq, precision, delta]
  · rfl
variable (r : ℝ) (σ : Bool)
local notation "K₀" => Km (G:=G) r σ n
local notation "℘" => HeatLine G (n:=n) r
private lemma ghost_degrees (l : Legs (Shore G n)) : degree (field parity) l= if fieldDim ghostNo l%2=1 then true else false := by
  induction l with
  | nil => simp [fieldDim]
  | cons i w ih =>
    rw [degree_cons,field_cons,ih]
    rcases i with ⟨⟨⟨_ | i, _ | _⟩, u⟩, p⟩
    all_goals
      unfold ghostNo ghostChannel field parity Landau.p
      dsimp only
      split_ifs <;> first | rfl | omega

theorem cube_parity (p : SectorP n) (i : Cfield G n) (l : Legs (Shore G n)) (ht : parity i ≠ degree (field parity) l) :
    Cubic G ((i,p)::l)=0 := cubic_charge _ (fun h=> by
      have he := ghost_degrees ((i,p)::l); rw [h, if_neg (by decide : ¬ (0:ℤ)%2=1),degree_cons] at he;
      unfold field at he; dsimp only at he; grind)

theorem hit_parity (l v : Legs (Shore G n)) : HitM K₀ (Cubic G) l v =
    if degree (field parity) l=σ then HitM ℘ (Cubic G) l v else 0 := by
  unfold HitM
  rw [convertR (TwoPoint.selected_rev r σ n), convertR (law_S r)]
  have hu (i j : Cfield G n) : radius parity K₀ i j (Cubic G) (Cubic G) l v = if degree (field parity) l=σ then
      radius parity ℘ i j (Cubic G) (Cubic G) l v else 0 := by
    unfold radius Km TwoPoint.Km pickLine; dsimp only
    by_cases he : parity i=degree (field parity) l; · rw [he]; split <;> first| rfl|ring
    rw [cube_parity _ _ _ he]; split <;> simp
  simp_rw [hu]; split <;> simp


variable (p q : SectorP n) (mu x y : L n) (i a b : G.ColorIndex)
theorem ghost_hit : HitM ℘ (Cubic G) [c i q, W mu a p] [U x i (-q), W mu b (-p)] =
    if x=mu then 2* SpanH r (q+p) mu * angle i a b else 0 := by
  rw [hit_fade ℘ (law_S (n:=n) r),clickWC]
  change (1:ℂ) * _=_; rw [one_mul]; simp_rw [add_comm p q,Span_neg]
  simp_rw [show ∀ k:G.ColorIndex, Cubic G (c k (q+p):: [U x i (-q), W mu b (-p)])=_ from
    fun k=> wing_CUW k b i (q+p) (-p) mu x (-q) (by abel)]
  split
  · unfold angle; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _=> ?_; rw [f_att,f_att,angle_flip k a i]; ring
  simp


lemma angle_comm (i a b : G.ColorIndex) : angle i b a=angle i a b := TwoPoint.angle_comm i a b
theorem exchangeC : (2:ℂ)⁻¹ * Exchange K₀ [c i q, U x i (-q), W mu a p, W mu b (-p)] =
    if σ=true ∧ x=mu then 2*angle i a b* (SpanH r (q+p) mu + SpanH r (q+ -p) mu) else 0 := by
  let K:=Km (G:=G) r σ n; obtain hx:= TwoPoint.selected_rev (G:=G) r σ n
  rw [book_exchange _ _ _ _ hx (by simp [net,W,c,U,onX]),hit_light K hx _ _ _ (by simp [net,c,U,onX]) (Km0 r σ), hit_parity, hit_parity, ghost_hit,
      show HitM ℘ (Cubic G) [c i q,W mu b (-p)] [U x i (-q),W mu a p] =_ from (neg_neg p ▸ ghost_hit r (-p) q mu x i b a), angle_comm i a b]
  simp only [show ∀ b c : G.ColorIndex,∀ p q:SectorP n,degree (field parity) [c b p,W mu c q]=true from fun _ _ _ _=> rfl,
    show ∀ b:G.ColorIndex,∀ q:SectorP n, field parity (W mu b q)=false from fun _ _=> rfl,cross_false']; cases σ <;> by_cases h:x=mu <;> simp [h, c, W, vec, onX, field, Landau.parity, Landau.p]
  ring

theorem exchangeSym (u v : Shore G n) (l : Legs (Shore G n)) :
    Exchange K₀ (u::v::l)= cross (parity u.1) (parity v.1)*Exchange K₀ (v::u::l):= by
  exact (tree_sym (TwoPoint.selected_closed r σ n) (fund_one G n).sym (fund_one G n).sym) [] u v l

end trace


section closing
variable (r : ℝ) (p q : SectorP n) (mu x : L n) (a b d : G.ColorIndex)

def ghostTensor (r : ℝ) (p q : SectorP n) (mu : L n) : ℂ :=
  -4 * (City.brush 1 q * City.brush r (q+p) : ℝ) * (q.sq:ℂ) * ((q+p).sq:ℂ) *
    ((q+p) mu:ℂ) * (q mu:ℂ)
lemma ghost_half : 4*SpanH 1 q mu*SpanH r (q+p) mu=ghostTensor r p q mu := by
  unfold ghostTensor SpanH
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring
abbrev connective (r : ℝ) (σ : Bool) (G : Gauge) := TwoPoint.connective r σ G
lemma written (σ : Bool) : connective r σ G n = (2:ℂ)⁻¹ • Exchange (Km r σ n) := by
  unfold connective TwoPoint.connective
  rw [bridgeG_eq (TwoPoint.selected_rev r σ)]
  unfold GraphSum.factor
  rw [if_pos rfl]
  push_cast
  rfl
variable (σ : Bool)
local notation "C_U" => connective r σ G n
local notation "Z" => TwoPoint.word (m:=n) mu mu a b p
private theorem ghost_flip (x : L n) :
    SpanH 1 q x * C_U (U x d q :: c d (-q)::Z)= SpanH 1 (-q) x * C_U (c d (-q)::U x d q:: Z) := by
   have he : C_U (U x d q :: c d (-q):: Z)= -(C_U (c d (-q):: U x d q :: Z)) := by
     rw [written]; simp_rw [Pi.smul_apply, smul_eq_mul]; rw [exchangeSym,show (cross (parity (U x d q).1) (parity (c d (-q)).1):ℂ)=-1 from rfl]; ring
   rw [he, Span_neg]; ring

private theorem charge_r (x:L n) : C_U (c d q :: U x d (-q) :: Z) =
    if σ=true ∧ x=mu then 2*angle d a b* (SpanH r (q+p) mu + SpanH r (q+ -p) mu) else 0 := by
   rw [written]; exact exchangeC ..

private lemma ghost_sum : ∑ x:L n,(SpanH 1 q x * C_U (c d q:: U x d (-q):: Z)+SpanH 1 q x * C_U (U x d q:: c d (-q):: Z))=
     if σ then angle d a b * (ghostTensor r p q mu + ghostTensor r p (-q) mu) else 0:= by
   have hp (x:L n) : C_U (c d (-q):: U x d q :: Z)= _ := neg_neg q ▸ charge_r r p (-q) mu a b d σ x
   simp_rw [ghost_flip r p q mu a b d σ, charge_r,hp]
   by_cases hS : σ=true
   · rw [Finset.sum_eq_single mu];
     · simp only [hS,if_true,and_self]; rw [ ← ghost_half r p q mu, ← ghost_half r p (-q) mu,
         show (-q)+ (-p)= -(q+p) from (by abel), Span_neg r, show q+(-p)= -((-q)+p) from (by abel),
         Span_neg r, Span_neg]; ring
     · intro i _ hi; simp [hi]
     simp
   simp [hS]


end closing

lemma ghost_sprint (r : ℝ) (q : SectorP n) (H : Cfield G n → Cfield G n → ℂ) :
    (∑ i,∑ j, Km r true n i j q * H i j) =
      ∑ a : G.ColorIndex, ∑ x : L n,
        (SpanH r q x * H (Uℓ x a) (Cℓ a) + SpanH r q x * H (Cℓ a) (Uℓ x a)) := by
  let Y (i j : Cfield G n) : ℂ := if parity i=true then H i j else 0
  have he (i j : Cfield G n) : Km r true n i j q * H i j = HeatLine G r i j q * Y i j := by
    unfold Km TwoPoint.Km pickLine Y HeatLine
    split <;> simp
  simp_rw [he]
  rw [sprint]
  simp only [atUC, atCU]
  simp [Y,Aℓ,Uℓ,Cℓ,Landau.parity,Landau.p,Landau.gauge,Landau.ghost,Landau.anti]

lemma trace_value (r : ℝ) (p q : SectorP n) (mu : L n) (a b : G.ColorIndex) :
    trc (Km 1 true n) q (connective r true G n) (TwoPoint.word mu mu a b p) =
      (∑ i : G.ColorIndex, angle i a b) * (ghostTensor r p q mu + ghostTensor r p (-q) mu) := by
  rw [at_trc,ghost_sprint,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d _
  have h := ghost_sum r p q mu a b d true
  simp only [if_true] at h
  rw [← h]
  exact Finset.sum_congr rfl fun x _ => add_comm _ _
open GraphSum

theorem inside_loop (ξ σ : Bool) (q : SectorP n) (w : Legs (Shore G n)) :
    trc ((cursor ξ).half n) q (TwoPoint.stemPair G σ n) w = ∫ r in (0:ℝ)..1, trc (Km 1 ξ n) q (connective r σ G n) w := by
    -- integral at unit upper length, linear- not log-length on first edge
    have hz : (cursor ξ).half= Km (G:=G) 1 ξ:= congr_arg (pickLine ξ) (radial_atOne G)
    rw [hz]
    have hu := (selected_radial σ (interaction G 1) (interaction G 1) 0).1
    let c:ℂ:= (factor true : ℂ); let U(l: Legs (Shore G n))(r:ℝ):= connective r σ G n l
    have ht(l : Legs (Shore G n)) : Continuous (U l) := continuous_const.mul (continuous_pick σ l (interaction G 1).symbol (interaction G 1).symbol)
    have hv(l : Legs (Shore G n)): TwoPoint.stemPair G σ n l=∫ r in (0:ℝ)..1,U l r:= by rw [posing,exp_zero] at hu; exact congr_fun (congr_fun hu n) l
    simp_rw [at_trc,hv]; let f (a b:Cfield G n)(t:ℝ):= Km 1 ξ n a b q * U ((a,q)::(b,-q)::w) t
    have He(a b): Continuous (f a b):= continuous_const.mul (ht _)
    rw [intervalIntegral.integral_finsetSum]; swap; · exact fun i _=> (continuous_finsetSum _ fun j _=> He i j).intervalIntegrable _ _
    refine Finset.sum_congr rfl fun i _=> ?_; rw [intervalIntegral.integral_finsetSum _]
    apply Finset.sum_congr rfl; intro j _; unfold U; rw [intervalIntegral.integral_const_mul]; exact fun j _=> (He i j).intervalIntegrable _ _


end YMReview.NovemberMatching.GhostTrace
