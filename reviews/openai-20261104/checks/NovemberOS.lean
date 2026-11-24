import NovemberAcceptanceSpec

set_option autoImplicit false
noncomputable section
namespace YMReview.November
open YangMills YM YM.Spec YM.OPE.Orbits
variable {g : GaugeGroup} {C : Family g.core} {o : Extraction.Order} {S : Table C.book}
variable (F : Final C o S) (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)

/-- The public centered trace is the same field used in our independent checks. -/
theorem public_trace_eq : (hierarchy F Q).centeredTrace = Trace.traceField F := by
  change TraceExtension.center F = Trace.traceField F
  exact YMAFBridge.same_center F

theorem public_kernel_eq (n : ℕ) (x : YM.Points n) :
    (hierarchy F Q).correlation (some (hierarchy F Q).selected)
      (fun _ : Fin n => ⟨4, (hierarchy F Q).centeredTrace⟩) x =
        YMOSBridge.scalarKernel F n x := by
  rw [public_trace_eq]
  rfl

theorem public_schwinger_eq : publicSchwinger (hierarchy F Q) = YMOSBridge.schwinger F := by
  funext n f
  rw [YMOSBridge.schwinger_eq_selected_integral]
  unfold publicSchwinger
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  rw [public_kernel_eq]

/-- Exact independent OS axioms and E0′ growth for the public selected hierarchy. -/
theorem public_os : PublicOS (hierarchy F Q) :=
  ⟨YMOSBridge.verifiedOS F, (public_schwinger_eq F Q).symm, YMOSBridge.verifiedOS_growth F⟩

end YMReview.November
