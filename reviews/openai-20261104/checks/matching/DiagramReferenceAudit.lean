import YM.MS.Graphical.CommonGates
import YangMills.WilsonProof.NativeSupport.YM.MS.Motif.Sync
import Mathlib.Tactic

/-!
# November diagram-reference audit

This file does two different jobs. The first two theorems compare the submitted
free gauge line with explicit momentum-space formulas. The remaining commands
record types and axiom dependencies of existing submitted bridge theorems.
Those commands do not independently reprove the bridges or validate all their
definitions. This is not a Comparator target and is not the final matching test.

The gauge propagator is delta_ab (delta_mu_nu/p² - p_mu p_nu/(p²)²).
The source's `halfCov` includes a factor 1/2 and an infrared length filter;
both are made explicit below. No assertion about the value of a distribution
at zero momentum or at coincident positions is intended.
-/

noncomputable section
set_option autoImplicit false
open YM YM.MS

namespace YMReview.NovemberMatching.DiagramAudit

/-- Our explicit transverse free propagator, before the color delta. -/
def expectedGaugeLine {A : Type} [Fintype A] [DecidableEq A]
    (p : Momentum A) (mu nu : A) : ℝ :=
  (if mu = nu then 1 else 0) / p.sq - p mu * p nu / p.sq ^ 2

/-- The submitted unfiltered AA line has the expected transverse normalization. -/
theorem gauge_line {A : Type} [Fintype A] [DecidableEq A]
    (p : Momentum A) (mu nu : A) (hp : p.sq ≠ 0) :
    Swirl.Near.Tail (Landau.gauge mu) (Landau.gauge nu) p =
      (expectedGaugeLine p mu nu : ℂ) := by
  change ((Landau.precision mu nu p / p.sq ^ 2 : ℝ) : ℂ) = _
  apply congrArg Complex.ofReal
  by_cases h : mu = nu <;>
    simp [expectedGaugeLine, Landau.precision, Landau.delta, h] <;>
    field_simp [hp]

/-- The full colored AA covariance through infrared length exp(s).
The factor 2 cancels the half-line convention used for ordered contractions. -/
theorem filtered_gauge_line (G : Gauge) (s : ℝ) (m : ℕ)
    (p : Arts.SectorP m) (mu nu : Arts.L m) (a b : G.ColorIndex) (hp : p.sq ≠ 0) :
    2 * Graphical.halfCov s m ((some mu, false), a) ((some nu, false), b) p =
      if a = b then
        (1 - (((1 + (Real.exp s)^2 * p.sq) *
          Real.exp (-((Real.exp s)^2 * p.sq)) : ℝ) : ℂ)) *
          (expectedGaugeLine p mu nu : ℂ)
      else 0 := by
  unfold Graphical.halfCov Landau.choir
  split_ifs with hab
  · change 2 * ((1 - (Landau.low (Real.exp s) p : ℂ)) *
        Swirl.Near.Tail (Landau.gauge mu) (Landau.gauge nu) p / 2) = _
    rw [gauge_line p mu nu hp, Swirl.Near.lown]
    ring
  · simp

end YMReview.NovemberMatching.DiagramAudit

-- Classical action, BRST consistency, and free Hessian.
#check YM.MS.Motif.Class_at
#check YM.MS.Motif.AllMaster
#check YM.MS.Motif.kernel
#print axioms YM.MS.Motif.Class_at
#print axioms YM.MS.Motif.AllMaster
#print axioms YM.MS.Motif.kernel

-- Propagator integration and dimensional loop normalization.
#check YM.MS.Graphical.length_recovers_line
#check YM.MS.Graphical.radialClose_integer
#check YM.MS.Graphical.pitch_normalization
#print axioms YM.MS.Graphical.length_recovers_line
#print axioms YM.MS.Graphical.radialClose_integer
#print axioms YM.MS.Graphical.pitch_normalization

-- Local subtraction, flow solution, and uniqueness of the coefficient germs.
#check YM.MS.Graphical.block
#check YM.MS.Graphical.ct_polynomial
#check YM.MS.Graphical.Diagram.income_bulk
#check YM.MS.Graphical.Diagram.income_mark
#print axioms YM.MS.Graphical.block
#print axioms YM.MS.Graphical.ct_polynomial
#print axioms YM.MS.Graphical.Diagram.income_bulk
#print axioms YM.MS.Graphical.Diagram.income_mark

-- From many-insertion graph sums to the calibrated coefficient table.
#check YM.MS.Graphical.identification
#check YM.MS.Graphical.calibrated_gates
#print axioms YM.MS.Graphical.identification
#print axioms YM.MS.Graphical.calibrated_gates

#print axioms YMReview.NovemberMatching.DiagramAudit.gauge_line
#print axioms YMReview.NovemberMatching.DiagramAudit.filtered_gauge_line
