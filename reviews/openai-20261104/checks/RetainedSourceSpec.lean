import TraceBridge

/-! The October public and contact conclusions retained in our combined target.
The four Properties fields are written explicitly because November changed the
source's Properties wrapper. Its TraceTest now also fixes the stress/unit data.
The independent scalar OS test remains a separate clause in AcceptanceSpec. -/
set_option autoImplicit false
noncomputable section
namespace YMReview.RetainedSource
open YangMills Set MeasureTheory TopologicalSpace
open scoped Distributions
variable {g : GaugeGroup} {C : WilsonFamily g}

structure Properties (T : Hierarchy C) (order : ℕ → ℕ) : Prop where
  wilson : C.Converges order (fun v => T.correlation none (T.project ∘ v))
  reconstruction : T.Reconstructed
  ope : T.OperatorProductExpansion
  nonfree : T.TraceTest

def Contacts (T : Hierarchy C) : Prop :=
  ∀ (s : Option T.Character) (n : ℕ) (v : Fin n → T.Tag),
    ∃ D : _root_.TestFunction (⊤ : Opens (Points n)) ℂ ⊤ →L[ℂ] ℂ,
      ∀ f : _root_.TestFunction (⊤ : Opens (Points n)) ℂ ⊤,
        tsupport f ⊆ WilsonFamily.separated n → D f = ∫ x, f x * T.correlation s v x

end YMReview.RetainedSource
