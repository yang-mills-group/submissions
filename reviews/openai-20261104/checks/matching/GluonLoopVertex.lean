import GhostLoopTrace
/-! The actual three-gluon vertex in every auxiliary sector.
Adapted from the submission's Apache-2.0 YM/WilsonMS/Beta/Flash.lean.
-/
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace YMReview.NovemberMatching.GluonVertex
open YM YM.WilsonMS YM.MS YM.MS.Arts YM.MS.ScaleForest
open Function Filter Set Finset MeasureTheory Metric Real
open LoopRank Lattice MS Plane Koszul Heat Flux Landau Tone Momentum Frame Wire Color Detect Native
open Book Convolve City Logarithm Signal Landau.Detect.Mark Wind High Knobs
open LogTime LogTime.IntervalFamily Outlook Land Arc Wire Rock Path Oceans Plum Alps Garment Color
  Pearl
open Arts Motif Halo
open Complex (I)
open scoped Topology ContDiff BigOperators
open YM.WilsonMS.BetaValue
variable {G : Gauge} {n : ℕ}
abbrev W := @GhostTrace.W
abbrev Cubic := @GhostTrace.Cubic
variable (a b c : CI G) (p q r : SectorP n) (x y z : L n)
private lemma Ξ_head (x y : L n) (a : G.ColorIndex) : Book.rank 2 (quill (G := G) x y a) := by
  unfold quill
  rw [chew]
  exact
    Rails.sum _ fun i _ =>
      Rails.sum _ fun j _ =>
        (((mon_leaf (onX false (some x, i))).product (mon_leaf (onX false (some y, j)))).smul _)

private lemma bind_W (t v : L n) :
    quill t v a [W x b p, W y c q] =
      (if x = t ∧ y = v then fColor b c a else 0) - (if x = v ∧ y = t then fColor b c a else 0) := by
  unfold quill
  rw [chew]
  simp only [Finset.sum_apply, Pi.smul_apply]
  simp_rw [pairv (F := Motif.A n G t _) (H := Motif.A n G v _) (mon_leaf _) (mon_leaf _)]
  have hx (u w : L n) (a b : CI G) (p : SectorP n) :
    Motif.A n G u b [W w a p] = if w = u ∧ a = b then 1 else 0 := by
    unfold W GhostTrace.W vec
    simp [Motif.A, lip, Motif.leaf, onX, node1]
  simp_rw [hx]
  have he (x y : L n) (a b c : CI G) :
    ∑ i : CI G,
        ∑ j : CI G,
          rune i j a * (((if x = t ∧ b = i then 1 else 0) : ℂ) * (if y = v ∧ c = j then 1 else 0)) =
      if x = t ∧ y = v then rune b c a else 0 := by
    by_cases ha : x = t
    swap
    · simp [ha]
    subst x
    by_cases hp : y = v
    · subst y
      simp [mul_ite]
    simp [hp]
  simp only [show parity (((W x b p) : Shore G n).1) = false from rfl, field,
    show parity (((W y c q) : Shore G n).1) = false from rfl, cross_false, one_mul, smul_eq_mul,
    mul_add, Finset.sum_add_distrib]
  rw [he, he, ← f_att, r_ortho c b]
  by_cases h : x = v ∧ y = t
  · rw [if_pos h, if_pos (And.symm h), sub_eq_add_neg]
  rw [if_neg h, if_neg (show ¬(y = t ∧ x = v) from (fun hY => h hY.symm)), sub_zero, add_zero]

private lemma hit_α (i : L n) (u v : L n) :
    ∑ a : L n,
        ∑ b : L n,
          polar0 a b i p *
            (((if a = u ∧ b = v then 1 else 0) : ℝ) - (if a = v ∧ b = u then 1 else 0)) =
      2 * (Landau.delta v i (p u) - Landau.delta u i (p v)) := by
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  have h (u v : L n) :
    (∑ a : L n, ∑ b : L n, polar0 a b i p * ((if a = u ∧ b = v then 1 else 0) : ℝ)) =
      polar0 u v i p := by
    rw [Finset.sum_eq_single u]
    · simp [mul_ite]
    · intro z hz hZ
      simp [hZ]
    simp
  rw [h, h]
  unfold polar0 delta
  ring

private lemma hitWS (i j k : Shore G n) (hp : field parity i = false) (hq : field parity j = false)
    (hr : field parity k = false) (F H : Rack G n) (he : Book.rank 1 F) (_h : Book.rank 2 H) :
    (product (field parity) F H) [i, j, k] = F [i] * H [j, k] + F [j] * H [i, k] + F [k] * H [i, j] := by
  rw [scattered ..]
  simp only [scatter_cons, scatter_nil, hp, hq, hr]
  rw [he [i, j, k] (by norm_num), he [i, j] (by norm_num), he [i, k] (by norm_num),
    he [j, k] (by norm_num), he [] (by norm_num)]
  simp only [cross_false, one_mul, add_zero, zero_mul, zero_add]
  ring

private lemma cap_A : cape (blazeV G n) [W x a p, W y b q, W z c r] = 0 := by
  unfold cape
  rw [Finset.sum_apply]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [Pi.smul_apply, scattered]
  simp [scatter_cons, Motif.leaf, Motif.note, Koszul.mono, qnote, W, GhostTrace.W, vec, onX, Landau.gauge]

private lemma scan_W :
    (∑ t : L n,
        ∑ u : L n,
          ∑ i : CI G,
            F₀ (G := G) t u i [W x a p] * quill t u i [W y b q, W z c r]) =
      2 * I * fColor b c a * ((polar0 (n := n) y z x p : ℝ) : ℂ) := by
  simp_rw [bind_W]
  simp_rw [show
      ∀ t u : Arts.L n,
        ∀ i : CI G,
          F₀ (G := G) t u i [W x a p] = if a = i then I * (polar0 (n := n) t u x p : ℝ) else 0
      from fun t u i => f_ref _ _ _ _ _ _]
  simp_rw [ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  let Z (t u : Arts.L n) : ℝ :=
    polar0 (n := n) t u x p *
      (((if t = y ∧ u = z then 1 else 0) : ℝ) - (if t = z ∧ u = y then 1 else 0))
  let c' : ℂ := fColor b c a
  have h :
    (∑ t : L n,
        ∑ u : L n,
          (I * (polar0 (n := n) t u x p : ℂ)) *
            ((if y = t ∧ z = u then c' else 0) - (if y = u ∧ z = t then c' else 0))) =
      I * c' * ((∑ t : L n, ∑ u : L n, Z t u : ℝ) : ℂ) := by
    simp_rw [Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => ?_
    unfold Z
    simp only [show (y = t ∧ z = u) ↔ (t = y ∧ u = z) from and_congr eq_comm eq_comm,
      show (y = u ∧ z = t) ↔ (t = z ∧ u = y) from (and_comm.trans (and_congr eq_comm eq_comm))]
    split_ifs <;>
      ( push_cast
        ring)
  rw [h, show ∑ t : L n, ∑ u : L n, Z t u = 2 * polar0 (n := n) y z x p from hit_α p x y z]
  push_cast
  unfold c'
  ring

private lemma sume_swap (t u : L n) :
    sume (G := G) (quill t u) (F₀ t u) = sume (F₀ t u) (quill t u) := by
  have hp : Motif.Mood false (F₀ (G := G) t u) := by
    simpa [Motif.cur] using curs (G := G) (z := 0) t u
  exact Finset.sum_congr rfl (fun i _ => ((hp.tune i).central _).symm)

/-- Standard three-gluon factor, oriented momenta inwards. -/
def trident (p q r : SectorP n) (x y z : L n) : ℝ :=
  polar0 (n := n) y z x p + polar0 (n := n) z x y q + polar0 (n := n) x y z r

lemma field_W :
    Cubic G [W x a p, W y b q, W z c r] =
      -I * fColor a b c * (trident p q r x y z : ℝ) := by
  let J := W x a p
  let K := W y b q
  let M := W z c r
  rw [Cubic, GhostTrace.Cubic, GhostTrace.C, pulse1]
  change top3 G n _ + cape _ _ = _
  rw [cap_A, add_zero]
  unfold top3
  simp only [Pi.smul_apply, Finset.sum_apply, Pi.add_apply, sume_swap, Finset.sum_add_distrib]
  unfold sume
  simp only [Finset.sum_apply]
  let f (t u : L n) (i : CI G) := F₀ t u i
  let W (t u : L n) (i : CI G) := quill t u i
  have he (t u : L n) (i : CI G) :
    bite n G (f t u i) (W t u i) [J, K, M] =
      f t u i [J] * W t u i [K, M] + f t u i [K] * W t u i [M, J] + f t u i [M] * W t u i [J, K] := by
    rw [bite, hitWS J K M rfl rfl rfl (f t u i) (W t u i) (rank_α t u i) (Ξ_head t u i)]
    rw [show W t u i [J, M] = W t u i [M, J] from ?_]
    have hm := ((Bay.cov (G := G) t).Cartan (Bay.cov u) i).sym [] J M []
    change W t u i [J, M] = 1 * W t u i [M, J] at hm
    rwa [one_mul] at hm
  change
    (-(1 / 4) : ℂ) •
        ((∑ t : L n, ∑ u : L n, ∑ i : CI G, bite n G (f t u i) (W t u i) [J, K, M]) +
          (∑ t : L n, ∑ u : L n, ∑ i : CI G, bite n G (f t u i) (W t u i) [J, K, M])) =
      _
  simp_rw [he, Finset.sum_add_distrib]
  unfold W f J K M
  rw [scan_W, scan_W, scan_W, f_orient c a b, ← f_orient a b c]
  unfold trident
  push_cast
  simp only [smul_eq_mul]
  ring
end YMReview.NovemberMatching.GluonVertex
#print axioms YMReview.NovemberMatching.GluonVertex.field_W
