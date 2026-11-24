import GluonLoopContraction
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
open YM YM.MS YM.MS.Arts YM.MS.ScaleForest
open Plane Koszul Heat Flux Landau Book Convolve Motif Halo
open Function Filter Set Finset MeasureTheory Real
open Tone Momentum Frame Wire Color Detect Native Native.Wilsonian City Logarithm Signal
open Landau.Detect.Mark Wind High Knobs Arc Rock Path Oceans Plum Alps Garment Pearl
open YM.WilsonMS.BetaValue
namespace YMReview.NovemberMatching.GluonYeast
open GhostTrace GluonTrace
variable {G:Gauge} {n:ℕ}

lemma vector_line (r:ℝ) (s t:Bool) (i j:L n) (a b:G.ColorIndex) (q:SectorP n) :
    Km r false n (vleg s i a) (vleg t j b) q =
      if s=false ∧ t=false ∧ a=b then GhostTrace.Lace r q i j else 0 := by
  cases s <;> cases t <;>
    simp [Km,TwoPoint.Km,pickLine,radial,City.LegsK,Landau.choir,vleg,Landau.parity,Landau.p,City.L0,GhostTrace.Lace]

lemma spectator_trident (p q:SectorP n) (mu h i:L n)
    (hp:p h=0) (hq:q h=0) (hm:mu≠h) :
    GluonTrace.tridentMu mu p q i h = if i=h then 2*q mu+p mu else 0 := by
  by_cases hi:i=h
  · subst i
    simp [GluonTrace.tridentMu,GluonVertex.trident,polar0,delta,hp,hq,hm,Ne.symm hm]
    ring
  · simp [GluonTrace.tridentMu,GluonVertex.trident,polar0,delta,hp,hq,hm,Ne.symm hm,hi,Ne.symm hi]

lemma spectator_two (r:ℝ) (p q:SectorP n) (mu h:L n)
    (hp:p h=0) (hq:q h=0) (hm:mu≠h) :
    GluonTrace.twoG r p q mu h h =
      (City.brush r (q+p)*(q+p).sq*(2*q mu+p mu)^2:ℝ) := by
  unfold GluonTrace.twoG
  simp_rw [spectator_trident p q mu h _ hp hq hm]
  rw [Finset.sum_eq_single h]
  · rw [Finset.sum_eq_single h]
    · simp [GhostTrace.Lace,precision,delta,hp,hq]
      push_cast
      ring
    · intro i _ hi
      simp [hi]
    · simp
  · intro i _ hi
    simp [hi]
  · simp

lemma yeast_as (K:Rip G) (F:Mob G) (q:SectorP n) (w:Legs (Shore G n))
    (hK:K=Km 1 false) :
    yeast K F q w = ∑ c:G.ColorIndex,
      GhostTrace.Lace 1 (Left (Nat.le_succ n) q) (hatch (Nat.lt_succ_self n)) (hatch (Nat.lt_succ_self n)) *
      F (n+1) (W (hatch (Nat.lt_succ_self n)) c (Left (Nat.le_succ n) q)::
        W (hatch (Nat.lt_succ_self n)) c (-Left (Nat.le_succ n) q)::Arts.lift (Nat.le_succ n) w) := by
  subst K
  unfold yeast Arts.token fleck
  simp_rw [vector_line]
  simp [hatch,GhostTrace.W,vec,at_g,vleg]

lemma stem_integral (G:Gauge) (σ:Bool) (n:ℕ) (w:Legs (Shore G n)) :
    TwoPoint.stemPair G σ n w=∫ r in (0:ℝ)..1,GhostTrace.connective r σ G n w := by
  have hu := (selected_radial σ (interaction G 1) (interaction G 1) 0).1
  rw [posing,Real.exp_zero] at hu
  exact congr_fun (congr_fun hu n) w

def extraTensor (r:ℝ) (p q:SectorP n) (mu:L n) : ℂ :=
  (2*City.brush 1 q*City.brush r (q+p)*q.sq*(q+p).sq*(2*q mu+p mu)^2:ℝ)

lemma lifted_two (r:ℝ) (p q:SectorP n) (mu:L n) :
    GluonTrace.twoG r (Left (Nat.le_succ n) p) (Left (Nat.le_succ n) q)
      (rises (Nat.le_succ n) mu) (hatch (Nat.lt_succ_self n)) (hatch (Nat.lt_succ_self n)) =
    (City.brush r (q+p)*(q+p).sq*(2*q mu+p mu)^2:ℝ) := by
  rw [spectator_two]
  · simp only [←map_add,City.brush,sq_up,Left,lasts]
  · exact offt _ _ _ (fun i=>nowhere (Nat.le_succ n) i (step (Nat.lt_succ_self n)))
  · exact offt _ _ _ (fun i=>nowhere (Nat.le_succ n) i (step (Nat.lt_succ_self n)))
  · exact nowhere (Nat.le_succ n) mu (step (Nat.lt_succ_self n))

lemma lifted_lace (q:SectorP n) :
    GhostTrace.Lace 1 (Left (Nat.le_succ n) q)
      (hatch (Nat.lt_succ_self n)) (hatch (Nat.lt_succ_self n)) =
    (City.brush 1 q*q.sq:ℝ) := by
  have hz : Left (Nat.le_succ n) q (hatch (Nat.lt_succ_self n))=0 :=
    offt _ _ _ (fun i=>nowhere (Nat.le_succ n) i (step (Nat.lt_succ_self n)))
  simp [GhostTrace.Lace,precision,delta,hz,City.brush,sq_up]

lemma yeast_connective (r:ℝ) (p q:SectorP n) (mu:L n) (a b:G.ColorIndex) :
    yeast (Km 1 false) (fun m=>GhostTrace.connective r false G m) q
      (TwoPoint.word mu mu a b p) =
    (∑ d:G.ColorIndex,angle d a b)*(extraTensor r p q mu+extraTensor r p (-q) mu) := by
  rw [yeast_as _ _ _ _ rfl,GhostRadial.lift_word]
  have he (c:G.ColorIndex) : GhostTrace.connective r false G (n+1)
      (W (hatch (Nat.lt_succ_self n)) c (Left (Nat.le_succ n) q)::
       W (hatch (Nat.lt_succ_self n)) c (-Left (Nat.le_succ n) q)::
       TwoPoint.word (rises (Nat.le_succ n) mu) (rises (Nat.le_succ n) mu) a b (Left (Nat.le_succ n) p)) =
      2*angle c a b*(GluonTrace.twoG r (Left (Nat.le_succ n) p) (Left (Nat.le_succ n) q)
        (rises (Nat.le_succ n) mu) (hatch (Nat.lt_succ_self n)) (hatch (Nat.lt_succ_self n))+
        GluonTrace.twoG r (Left (Nat.le_succ n) p) (Left (Nat.le_succ n) (-q))
        (rises (Nat.le_succ n) mu) (hatch (Nat.lt_succ_self n)) (hatch (Nat.lt_succ_self n))) := by
    rw [GhostTrace.written]
    rw [show ((2:ℂ)⁻¹ • GhostTrace.Exchange (Km r false (n+1))) _ = _ from
      GluonTrace.exchangeW r false (Left (Nat.le_succ n) p) (Left (Nat.le_succ n) q)
        (rises (Nat.le_succ n) mu) (hatch (Nat.lt_succ_self n)) (hatch (Nat.lt_succ_self n)) c a b]
    simp only [Bool.false_eq_true,if_false]
    rw [GluonTrace.flipG,←map_neg]
  simp_rw [he,lifted_two,lifted_lace]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro c _
  unfold extraTensor
  simp only [City.brush,Momentum.sq,Pi.neg_apply,neg_sq]
  push_cast
  ring

lemma yeast_inside (p q:SectorP n) (mu:L n) (a b:G.ColorIndex) :
    yeast (cursor false).half (TwoPoint.stemPair G false) q (TwoPoint.word mu mu a b p) =
      ∫ r in (0:ℝ)..1,yeast (Km 1 false) (fun m=>GhostTrace.connective r false G m) q
        (TwoPoint.word mu mu a b p) := by
  have hz : (cursor false).half=Km (G:=G) 1 false := congr_arg (pickLine false) (radial_atOne G)
  rw [yeast_as _ _ _ _ hz]
  simp_rw [yeast_as _ _ _ _ rfl,stem_integral]
  have hc (c:G.ColorIndex) : Continuous (fun r:ℝ=>
      GhostTrace.Lace 1 (Left (Nat.le_succ n) q) (hatch (Nat.lt_succ_self n)) (hatch (Nat.lt_succ_self n)) *
      GhostTrace.connective r false G (n+1)
        (W (hatch (Nat.lt_succ_self n)) c (Left (Nat.le_succ n) q)::
         W (hatch (Nat.lt_succ_self n)) c (-Left (Nat.le_succ n) q)::
         Arts.lift (Nat.le_succ n) (TwoPoint.word mu mu a b p))) :=
    continuous_const.mul (continuous_const.mul (continuous_pick false _ (interaction G 1).symbol (interaction G 1).symbol))
  rw [intervalIntegral.integral_finsetSum (fun c _=>(hc c).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_const_mul]

lemma actual_yeast (p q:SectorP n) (mu:L n) (a b:G.ColorIndex) :
    yeast (cursor false).half (TwoPoint.stemPair G false) q (TwoPoint.word mu mu a b p) =
      (∑ d:G.ColorIndex,angle d a b)*
        (∫ r in (0:ℝ)..1,extraTensor r p q mu+extraTensor r p (-q) mu) := by
  rw [yeast_inside]
  simp_rw [yeast_connective,intervalIntegral.integral_const_mul]

end YMReview.NovemberMatching.GluonYeast

#print axioms YMReview.NovemberMatching.GluonYeast.actual_yeast
