import YangMills.WilsonProof.NativeSupport.YM.MS.Motif.Receipt
import YM.MS.ScaleForest.Quotients
import YM.MS.ScaleForest.Optics
import YangMills.WilsonProof.WilsonBridge
import YangMills.PerturbativeMatching.Reference
import Mathlib.Tactic

/-! Additional checks for the seven rows of assessment section 2.3.
The two identities below simplify the actual classical density. The printed
source theorems inspect existing bridges; they are not independent reproofs.
No general conventional forest-equivalence claim is made here. -/
noncomputable section
set_option autoImplicit false
open YM YM.MS
open Motif Plane Koszul Arts
open scoped BigOperators
namespace YMReview.NovemberMatching.Section23

theorem cubic_density (G : Gauge) (n : ℕ) :
    top3 G n = (-(1/2) : ℂ) •
      ∑ i : Arts.L n, ∑ j : Arts.L n, sume (G:=G) (F₀ i j) (quill i j) := by
  have hF (i j : Arts.L n) : Mood (G:=G) false (F₀ (n:=n) i j) := by
    simpa [cur] using (curs (G:=G) (n:=n) 0 i j)
  have hQ (i j : Arts.L n) : Mood (G:=G) false (quill (n:=n) i j) :=
    (realA i).jawn (realA j)
  have hc (i j : Arts.L n) :
      sume (G:=G) (quill (n:=n) i j) (F₀ i j) = sume (F₀ i j) (quill i j) := by
    unfold sume
    apply Finset.sum_congr rfl
    intro a _
    exact ((hQ i j).tune a).central _
  unfold top3
  simp_rw [hc, ← two_smul ℂ, ← Finset.smul_sum]
  rw [smul_smul]
  norm_num

theorem quartic_density (G : Gauge) (n : ℕ) :
    top4 G n = (-(1/4) : ℂ) •
      ∑ i : Arts.L n, ∑ j : Arts.L n, sume (G:=G) (quill i j) (quill i j) := rfl

end YMReview.NovemberMatching.Section23

#print axioms YMReview.NovemberMatching.Section23.cubic_density
#print axioms YMReview.NovemberMatching.Section23.quartic_density
#check YM.Gauge.trace_color
#print axioms YM.Gauge.trace_color
#check YM.Gauge.trace_adjoint
#print axioms YM.Gauge.trace_adjoint
#check YM.MS.Motif.Class_at
#print axioms YM.MS.Motif.Class_at
#check YM.MS.ScaleForest.GraphSum.forest_germ
#print axioms YM.MS.ScaleForest.GraphSum.forest_germ
#check YM.MS.ScaleForest.common_native
#print axioms YM.MS.ScaleForest.common_native
#check YangMills.energy_eq
#print axioms YangMills.energy_eq
#check YangMills.law_eq
#print axioms YangMills.law_eq
#check YangMills.moment_eq
#print axioms YangMills.moment_eq
#check YangMills.PerturbativeMatching.Reference.scheme_unique
#print axioms YangMills.PerturbativeMatching.Reference.scheme_unique
