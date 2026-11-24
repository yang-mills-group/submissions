import GluonLoopVertex
/-! Actual gauge sewing in every auxiliary sector. Adapted from the
submission's Apache-2.0 TracedCubic.lean and LoadB.lean. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open YM YM.MS YM.MS.Arts YM.MS.ScaleForest
open Plane Koszul Heat Flux Landau Book Convolve Motif Halo
open scoped BigOperators
open Function Filter Set Finset MeasureTheory Metric Real
open Tone Momentum Frame Wire Color Detect Native Native.Wilsonian City Logarithm Signal
open Landau.Detect.Mark Wind High Knobs Arc Rock Path Oceans Plum Alps Garment Pearl
open YM.WilsonMS.BetaValue
open Complex (I)
namespace YMReview.NovemberMatching.GluonTrace
open GhostTrace
variable {G : Gauge} {n : ℕ}
abbrev trident := @GluonVertex.trident
lemma cubic_value (a b c:CI G) (p q r:SectorP n) (x y z:L n) :
    GhostTrace.Cubic G [GhostTrace.W x a p,GhostTrace.W y b q,GhostTrace.W z c r] =
      -I*fColor a b c*(trident p q r x y z:ℝ) :=
  GluonVertex.field_W a b c p q r x y z
lemma Lace_neg (r:ℝ) (p:SectorP n) (a b:L n) : GhostTrace.Lace r (-p) a b = GhostTrace.Lace r p a b := by
  simp [GhostTrace.Lace, City.brush, precision, delta]
lemma trident_flip (p q:SectorP n) (x y z:L n) (r:SectorP n) :
    trident (-p) (-q) (-r) x y z = -trident p q r x y z := by
  simp only [trident, GluonVertex.trident, polar0, delta, Pi.neg_apply]
  split_ifs <;> ring
variable (r:ℝ) (σ:Bool) (p q:SectorP n) (mu x y:L n) (i a b:CI G)
local notation "K₀" => Km (G:=G) r σ n
local notation "℘" => GhostTrace.HeatLine G (n:=n) r
def tridentMu (mu : L n) (p q : SectorP n) (x y : L n) := trident (-(q+p)) q p x y mu

def twoG (r : ℝ) (p q : SectorP n) (mu x y : L n) : ℂ := ∑ u:L n,∑ v:L n, GhostTrace.Lace r (q+p) u v *
  (tridentMu mu p q u x:ℂ)*(tridentMu mu p q v y:ℂ)

-- invariant color (NO A factors hidden)
theorem use_color (i a b k : CI G) : fColor k i a * fColor k i b = rune i a k * rune i b k := by
  rw [f_att,f_att,f_orient k i a,f_orient k i b]

theorem gauge_hit : HitM ℘ (Cubic G) [GhostTrace.W x i q, GhostTrace.W mu a p] [GhostTrace.W y i (-q),GhostTrace.W mu b (-p)] =
    2 * angle i a b * twoG r p q mu x y := by
  rw [GhostTrace.clickWW,angle,Finset.mul_sum,Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _=> ?_
  unfold twoG; simp_rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _=> Finset.sum_congr rfl fun l _=> ?_
  rw [cubic_value k i a, cubic_value k i b, ← use_color,Lace_neg,
    show trident (q+p) (-q) (-p) l y mu= -trident (-(q+p)) q p l y mu from ?_]
  · unfold tridentMu; push_cast; ring_nf; rw [Complex.I_sq]; ring
  nth_rw 1 [← neg_neg (q+p)]; exact trident_flip ..

theorem exchangeW : (2:ℂ)⁻¹ * Exchange K₀ [GhostTrace.W x i q, GhostTrace.W y i (-q), GhostTrace.W mu a p,GhostTrace.W mu b (-p)] =
    if σ then 0 else 2* angle i a b * (twoG r p q mu x y+twoG r (-p) q mu x y) := by
  let K := Km (G:=G) r σ n
  obtain hx:= TwoPoint.selected_rev (G:=G) r σ n
  rw [GhostTrace.book_exchange _ _ _ _ hx (by simp [net, GhostTrace.W,vec]),GhostTrace.hit_light K hx _ _ _ (by simp [net,GhostTrace.W,qnote]) (GhostTrace.Km0 r σ), GhostTrace.hit_parity, GhostTrace.hit_parity]
  simp only [gauge_hit r p q mu x y i a b, show HitM ℘ (Cubic G) [W x i q,W mu b (-p)] [W y i (-q),W mu a p]= _ from
    (neg_neg p ▸ gauge_hit r (-p) q mu x y i b a), GhostTrace.angle_comm i a b];
  cases σ
  · change ((2:ℂ)⁻¹) * (2 * ((0+1* (2* _ * twoG r p q mu x y)) + 1*1*(2* _ * twoG r (-p) q mu x y)))=_; rw [if_neg (by decide)]; ring
  change (2:ℂ)⁻¹ * (2 * ((0+1*(if false=true then _ else (0:ℂ)))+1*1*(if false=true then _ else (0:ℂ))))=_; simp


def tireG (p q:SectorP n) (mu:L n) := ∑ u:L n,∑ v:L n,precision u v q *
  ∑ i:L n,∑ j:L n,precision i j (q+p)*tridentMu mu p q i u*tridentMu mu p q j v
def gaugeTensor (r:ℝ) (p q:SectorP n) (mu:L n) : ℂ :=
  (City.brush 1 q * City.brush r (q+p) * 2 * tireG p q mu : ℝ)
theorem flipG : twoG r (-p) q mu x y = twoG r p (-q) mu x y := by
  have he : (-q)+p= -(q+ -p):= by abel
  have hV (a b:L n) : tridentMu mu (-p) q a b= -tridentMu mu p (-q) a b := by
    unfold tridentMu; rw [he]; obtain ht:= trident_flip (-(q + -p)) q a b mu (-p); rw [neg_neg p] at ht; rw [ht,neg_neg]
  unfold twoG; simp_rw [hV,he,Lace_neg]; simp_rw [Complex.ofReal_neg,mul_neg,neg_mul,neg_neg]

theorem gauge_half : 2 * (∑ x:L n,∑ y:L n, GhostTrace.Lace 1 q x y * twoG r p q mu x y) = gaugeTensor r p q mu := by
  unfold gaugeTensor tireG twoG; push_cast; simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _
  refine Finset.sum_congr rfl fun y _=> Finset.sum_congr rfl fun i _=> Finset.sum_congr rfl fun j _=> ?_
  ring


variable (c:CI G)
local notation "C_U" => connective r σ G n
local notation "Z" => TwoPoint.word (m:=n) mu mu a b p
private lemma gaugeSum : (∑ x:L n,∑ y:L n, GhostTrace.Lace 1 q x y * C_U (W x c q :: W y c (-q) :: Z)) =
    if σ then 0 else angle c a b*(gaugeTensor r p q mu + gaugeTensor r p (-q) mu) := by
  have he (x y : L n) : C_U (W x c q::W y c (-q):: Z)= (if σ then 0 else 2*angle c a b * (twoG r p q mu x y+twoG r (-p) q mu x y)) := (by rw [GhostTrace.written]; exact exchangeW r σ p q mu x y c a b)
  simp_rw [he]; split; simp; next h=>
    rw [ ← gauge_half, ← gauge_half]; simp_rw [Lace_neg,flipG r p q,mul_add,Finset.mul_sum,
      Finset.sum_add_distrib];
    exact congr_arg₂ (·+·) (Finset.sum_congr rfl fun _ _=>Finset.sum_congr rfl fun _ _=>by ring)
        (Finset.sum_congr rfl fun _ _=>Finset.sum_congr rfl fun _ _=>by ring)


lemma gauge_sprint (r:ℝ) (q:SectorP n) (H:Cfield G n → Cfield G n → ℂ) :
    (∑ i,∑ j, Km r false n i j q * H i j) =
      ∑ c:G.ColorIndex,∑ x:L n,∑ y:L n,GhostTrace.Lace r q x y * H (GhostTrace.Aℓ x c) (GhostTrace.Aℓ y c) := by
  let Y (i j:Cfield G n) : ℂ := if parity i=false then H i j else 0
  have he (i j:Cfield G n) : Km r false n i j q * H i j = GhostTrace.HeatLine G r i j q * Y i j := by
    unfold Km TwoPoint.Km pickLine Y GhostTrace.HeatLine
    split <;> simp
  simp_rw [he]
  rw [GhostTrace.sprint]
  simp only [GhostTrace.atAA]
  simp [Y,GhostTrace.Aℓ,GhostTrace.Uℓ,GhostTrace.Cℓ,Landau.parity,Landau.p,Landau.gauge,Landau.ghost,Landau.anti]

theorem trace_value (r:ℝ) (p q:SectorP n) (mu:L n) (a b:G.ColorIndex) :
    trc (Km 1 false n) q (connective r false G n) (TwoPoint.word mu mu a b p) =
      (∑ i:G.ColorIndex,angle i a b)*(gaugeTensor r p q mu+gaugeTensor r p (-q) mu) := by
  rw [at_trc,gauge_sprint,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  simpa using gaugeSum r false p q mu a b c
end YMReview.NovemberMatching.GluonTrace
#print axioms YMReview.NovemberMatching.GluonTrace.trace_value
