import YM.MS.ScaleForest.Entry
import YM.MS.ScaleForest.Halves
import YM.MS.ScaleForest.QuarticRule
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Tactic

/-!
Actual four-cubic, ghost-line histories in the submitted order-four list.
Theorems here prove membership, absence of tree counterterms, and the
submitted finite reader. They do NOT assert the final evaluated box constant.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open YM YM.MS YM.MS.ScaleForest YM.MS.ScaleForest.GraphSum
open YM.MS.Arts YM.MS.Train YM.MS.Pearl

namespace YMReview.NovemberMatching.GhostBox

inductive Tree where
  | leaf : Tree
  | join : Tree → Tree → Tree
deriving DecidableEq

def Tree.order : Tree → ℕ
  | .leaf => 1
  | .join a b => a.order + b.order

def Tree.graph (G : Gauge) : Tree → GraphSum G true 4
  | .leaf => vertex (interaction G 1)
  | .join a b => bridge (cursor true) (a.graph G) (b.graph G)

def Tree.symbol (G : Gauge) : Tree → Mob G
  | .leaf => (interaction G 1).symbol
  | .join a b => scaleIntegral 0 4 0
      ((factor true : ℂ) • bridgeG (cursor true).half (a.symbol G) (b.symbol G))

theorem bridge_classical {G : Gauge} (A B : GraphSum G true 4)
    (K : LineRule G) (F H : Mob G)
    (hA : A.instructions.renorm = classicalPage F)
    (hB : B.instructions.renorm = classicalPage H) :
    let S := scaleIntegral 0 4 0 ((factor true : ℂ) • bridgeG K.half F H)
    (bridge K A B).instructions.pole = 0 ∧
    (bridge K A B).instructions.renorm = classicalPage S := by
  intro S
  have hf : (bridge K A B).instructions.force =
      classicalPage ((factor true : ℂ) • bridgeG K.half F H) := by
    change connect true K A.instructions.renorm B.instructions.renorm = _
    rw [hA,hB]
    unfold connect classicalPage collapsed
    rw [bridge_single K.half K.ok.rev,Finsupp.smul_single]
    rfl
  have hp : (bridge K A B).instructions.prep = classicalPage S := by
    change integratePages 4 (bridge K A B).instructions.force = _
    rw [hf]
    unfold classicalPage collapsed
    rw [integrate_single]
    congr 1
    exact funext fun z => scaleZero_invariant z _ _
  have hc : (bridge K A B).instructions.pole = 0 :=
    ct_blind (bridge K A B |>.accepted.force) hp
  exact ⟨hc, by rw [Result.renorm,hc,hp,collapsed,Finsupp.single_zero,add_zero]⟩

theorem tree_result (G : Gauge) (t : Tree) :
    (t.graph G).instructions.renorm = classicalPage (t.symbol G) := by
  induction t with
  | leaf => exact renorm_vertex _
  | join a b ha hb => exact (bridge_classical _ _ _ _ _ ha hb).2

theorem tree_pole (G : Gauge) (t : Tree) : (t.graph G).instructions.pole = 0 := by
  cases t with
  | leaf => rfl
  | join a b => exact (bridge_classical _ _ _ _ _ (tree_result G a) (tree_result G b)).1

theorem order_pos (t : Tree) : 0 < t.order := by
  induction t with
  | leaf => decide
  | join a b ha hb => change 0<a.order+b.order; omega

theorem tree_slots (G : Gauge) (t : Tree) : (t.graph G).slots = (t.order : ℤ)+2 := by
  induction t with
  | leaf => rfl
  | join a b ha hb => simp only [Tree.graph,slots,ha,hb,Tree.order,Nat.cast_add]; ring

theorem tree_member (G : Gauge) (t : Tree) : t.graph G ∈ bulks (bicolor G) t.order := by
  induction t with
  | leaf => exact bulk_node (by decide) (closed_mem _ _ _)
  | join a b ha hb =>
    apply bulk_branch ((parts_mem true _ _ _).2 ⟨rfl,order_pos a,Or.inr (order_pos b)⟩)
    exact every_mem ha hb (by simp [bicolor]) (closed_mem _ _ _)

def closed (G : Gauge) (t : Tree) := loop (cursor true) (t.graph G)

theorem closed_member (G : Gauge) (a b : Tree) :
    closed G (.join a b) ∈ bulks (bicolor G) (a.order+b.order) := by
  apply bulk_branch ((parts_mem true _ _ _).2 ⟨rfl,order_pos a,Or.inr (order_pos b)⟩)
  apply every_mem (K := cursor true) (tree_member G a) (tree_member G b) (by simp [bicolor])
  change closed G (.join a b) ∈ allLoops (bicolor G)
    ((Tree.join a b |>.graph G).slots.toNat / 2) (Tree.join a b |>.graph G)
  have hn : 0 < ((Tree.join a b |>.graph G).slots.toNat / 2) := by
    rw [tree_slots]
    have ha := order_pos a
    have hb := order_pos b
    simp only [Tree.order,Nat.cast_add]
    omega
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  rw [hk]
  exact loop_mem (closed_mem _ _ _) (by simp [bicolor])

def trees : List Tree := [
  .join .leaf (.join .leaf (.join .leaf .leaf)),
  .join .leaf (.join (.join .leaf .leaf) .leaf),
  .join (.join .leaf .leaf) (.join .leaf .leaf),
  .join (.join .leaf (.join .leaf .leaf)) .leaf,
  .join (.join (.join .leaf .leaf) .leaf) .leaf]

def family (G : Gauge) : Hist G true 4 := trees.map (closed G)

theorem family_size (G : Gauge) : (family G).length = 5 := rfl

theorem family_member (G : Gauge) (x : GraphSum G true 4) (hx : x ∈ family G) :
    x ∈ bulks (bicolor G) 4 := by
  simp only [family,trees,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact closed_member G _ _

theorem family_slots (G : Gauge) (x : GraphSum G true 4) (hx : x ∈ family G) :
    x.slots = 4 := by
  simp only [family,trees,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;> rfl

def rate (G : Gauge) (t : Tree) (z : ℂ) := closeG (cursor true).half z 0 (t.symbol G)

theorem finite_reading (G : Gauge) (t : Tree) (y s : ℝ) :
    Outlook.four 4 (closed G t).instructions.renorm (y,s) =
      oneLoopFinite 4 (rate G t) s y 0 := by
  have h := (primitive_laurent (cursor true) (tree_result G t)).2.2 s y
  exact congrArg (fun F : Mob G => F 0) (chosen (n:=0) h).symm

theorem actual_pole (G : Gauge) (t : Tree) :
    (closed G t).instructions.pole = taylorPole 4 (rate G t) :=
  (primitive_laurent (cursor true) (tree_result G t)).2.1

/-- The independently evaluated constant. No submitted evaluator defines it. -/
def finiteConstant : ℝ := 46/15 + (32/15)*Real.log 2 - (81/20)*Real.log 3

def colorMatrix (G : Gauge) (h : G.ColorIndex → ℝ) (i j : G.ColorIndex) : ℂ :=
  ∑ a, (h a : ℂ) * YM.MS.Motif.rune a j i

def colorTraceFourth (G : Gauge) (h : G.ColorIndex → ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, colorMatrix G h i j * colorMatrix G h j k *
    colorMatrix G h k l * colorMatrix G h l i

def word {G : Gauge} (p : SectorP 0) (e : L 0) (a b c d : G.ColorIndex) :=
  [vec e a p, vec e b p, vec e c p, vec e d ((-3 : ℝ) • p)]

def projected (G : Gauge) (h : G.ColorIndex → ℝ) (p : SectorP 0)
    (e : L 0) (y s : ℝ) : ℂ :=
  ∑ a, ∑ b, ∑ c, ∑ d, ((h a*h b*h c*h d : ℝ) : ℂ) *
    Outlook.four 4 (renHistory (family G)) (y,s) (word p e a b c d)

/-- Frozen target for a future fully formal finite-value comparison.
This file defines the proposition but supplies NO theorem proving it.
The polarization is a unit coordinate vector transverse to arbitrary p.
The corresponding analytic derivation is in the assessment, Section 6.
-/
def SubmittedFinitePartTest (G : Gauge) : Prop :=
  ∀ (h : G.ColorIndex → ℝ) (mu : ℝ), 0 < mu →
  ∀ (p : SectorP 0) (e : L 0), 0 < p.sq → p e = 0 →
    Filter.Tendsto (fun s : ℝ => projected G h p e
      (Real.log mu + (Real.eulerMascheroniConstant-Real.log (4*Real.pi))/2) s)
      Filter.atTop (nhds
        ((-3 : ℂ)*colorTraceFourth G h/(64*(Real.pi : ℂ)^2) *
          ((Real.log (mu^2/p.sq)+finiteConstant : ℝ) : ℂ)))

end YMReview.NovemberMatching.GhostBox

#print axioms YMReview.NovemberMatching.GhostBox.tree_result
#print axioms YMReview.NovemberMatching.GhostBox.tree_pole
#print axioms YMReview.NovemberMatching.GhostBox.family_member
#print axioms YMReview.NovemberMatching.GhostBox.family_slots
#print axioms YMReview.NovemberMatching.GhostBox.finite_reading
#print axioms YMReview.NovemberMatching.GhostBox.actual_pole
