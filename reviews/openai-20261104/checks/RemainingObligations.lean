import ReflectionPositivity
import ArityGrowth

/-! E0/E1/E2/E3 and corrected E0′ on one fixed selected centered-trace family.
This file defines the E4 predicate and conditional record; CompleteOS.lean
discharges that predicate and supplies the unconditional record. -/
set_option autoImplicit false
noncomputable section
namespace YMOSBridge
open YM MeasureTheory
open scoped Topology BigOperators
variable {G : Gauge} {C : Family G} {o : Extraction.Order} {S : Table C.book}
variable (F : Spec.Final C o S)

/-- The exact E2 predicate, now discharged by E2_reflection_positive. -/
def ReflectionObligation : Prop := ∀ B : BorchersSequence 3,
  (∀ n, tsupport (B.funcs n : NPointDomain 3 n → ℂ) ⊆ OrderedPositiveTimeRegion 3 n) →
  (OSInnerProduct 3 (schwinger F) B B).re ≥ 0

/-- Exactly the target E4 field, with the same state and observable. -/
def ClusterObligation : Prop :=
  ∀ (n m : ℕ) (f : ZeroDiagonalSchwartz 3 n) (g : ZeroDiagonalSchwartz 3 m),
  ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
    ∀ a : SpacetimeDim 3, a 0 = 0 → (∑ i : Fin 3, (a (Fin.succ i))^2) > R^2 →
      ∀ g_a : ZeroDiagonalSchwartz 3 m,
        (∀ x, g_a.1 x = g.1 (fun i => x i - a)) →
        ∀ fg_a : ZeroDiagonalSchwartz 3 (n + m),
          (∀ x, fg_a.1 x = f.1 (splitFirst n m x) * g_a.1 (splitLast n m x)) →
          ‖schwinger F (n + m) fg_a - schwinger F n f * schwinger F m g‖ < ε

/-- The literal group-vendored OSreconstruction record with only E4 remaining
as an explicit premise. E0, E1, E2 and E3 are all theorems of this family. -/
def completeOS (hCluster : ClusterObligation F) :
    OsterwalderSchraderAxioms 3 where
  S := schwinger F
  E0_tempered := E0_tempered F
  E0_linear := E0_linear F
  E0_reality := E0_reality F
  E1_translation_invariant := E1_translation_invariant F
  E1_rotation_invariant := fun n R hR _ => E1_rotation_invariant F n R hR
  E2_reflection_positive := E2_reflection_positive F
  E3_symmetric := E3_symmetric F
  E4_cluster := hCluster

/-- The corrected OS-II growth predicate, now discharged by E0_prime below.
No old fixed-order growth condition is substituted for it. -/
def GrowthObligation (hCluster : ClusterObligation F) : Prop :=
  Nonempty (OSArityLinearGrowthCondition 3 (completeOS F hCluster))

/-- The exact corrected target growth record. E4 occurs only because its OS
record is an argument to the target structure; E0_prime_growth does not use E4. -/
theorem E0_prime (hCluster : ClusterObligation F) : GrowthObligation F hCluster := by
  obtain ⟨s, β, A, hβ, h⟩ := E0_prime_growth F
  refine ⟨{
    normalized_zero := normalized_zero F
    sobolev_index := s
    alpha := 1
    beta := β
    gamma := (A : ℝ)
    alpha_pos := one_pos
    beta_pos := hβ
    growth_estimate := ?_
  }⟩
  intro n f
  simpa only [completeOS, one_mul, Real.rpow_natCast] using h n f

#print axioms E0_prime
#print axioms completeOS
end YMOSBridge
