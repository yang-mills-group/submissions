import YangMills.PerturbativeMatching
import Mathlib.Tactic

/-!
# Independent specifications for reviewing November perturbative matching

These are review specifications, not a proof that the submission passes them.
The numerical formulas below do not call OpenAI's graph evaluator, free covariance,
scheme conversion, or `bareTriangle`. The adapters at the end expose an actual
submitted correlator and its predicted coefficient for subsequent comparison.

The proved color identities are finite algebra calculations only. In particular,
they do not yet identify the submission's chosen color frame with this convention.
There are no `sorry`s, new axioms, or unproved claims disguised as theorem fields.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators

namespace YMReview.NovemberMatching

abbrev Axis := Fin 4
abbrev Point := Axis → ℝ

def radiusSquared (x : Point) : ℝ := ∑ a, (x a)^2

/-- Closed off-origin formula for ∂a∂b[1/(4π²|x|²)]. This is not a
distributional extension at zero; comparisons must require x ≠ 0. -/
def expectedHessian (x : Point) (a b : Axis) : ℝ :=
  (8 * x a * x b / (radiusSquared x)^3 -
    2 * (if a = b then 1 else 0) / (radiusSquared x)^2) / (4 * Real.pi^2)

/-- Curvature covariance from two curls, including the minus sign from
differentiating the second insertion. Color contributes δAB separately. -/
def expectedCurvature (x : Point) (a b c d : Axis) : ℝ :=
  (if b = c then expectedHessian x a d else 0) -
  (if b = d then expectedHessian x a c else 0) -
  (if a = c then expectedHessian x b d else 0) +
  (if a = d then expectedHessian x b c else 0)

/-- Positive cyclic orientation on three independent color coordinates. -/
def epsilon3 (a b c : Fin 3) : ℝ :=
  if (a = 0 ∧ b = 1 ∧ c = 2) ∨ (a = 1 ∧ b = 2 ∧ c = 0) ∨
      (a = 2 ∧ b = 0 ∧ c = 1) then 1
  else if (a = 0 ∧ b = 2 ∧ c = 1) ∨ (a = 2 ∧ b = 1 ∧ c = 0) ∨
      (a = 1 ∧ b = 0 ∧ c = 2) then -1 else 0

def colorSquare (scale : ℝ) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, (scale * epsilon3 a b c)^2

def adjointCasimir (scale : ℝ) : ℝ := colorSquare scale / 3

theorem colorSquare_eq (scale : ℝ) : colorSquare scale = 6 * scale^2 := by
  simp [colorSquare, epsilon3, Fin.sum_univ_succ]
  ring

theorem adjointCasimir_eq (scale : ℝ) : adjointCasimir scale = 2 * scale^2 := by
  rw [adjointCasimir, colorSquare_eq]
  ring

/-- Conditional convention check: if the chosen bracket constants are 2ε,
these are the color factors. Identification with the submitted color frame remains a task. -/
theorem doubledBracket_values : colorSquare 2 = 24 ∧ adjointCasimir 2 = 8 := by
  rw [colorSquare_eq, adjointCasimir_eq]
  norm_num

/-- An explicit anti-Hermitian Pauli basis, independently specified. -/
def pauli (a : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  if a = 0 then !![0, -Complex.I; -Complex.I, 0]
  else if a = 1 then !![0, -1; 1, 0]
  else !![-Complex.I, 0; 0, Complex.I]

theorem pauli_trace_normalization (a b : Fin 3) :
    -((pauli a * pauli b).trace).re / 2 = (if a = b then 1 else 0) := by
  fin_cases a <;> fin_cases b <;>
    norm_num [pauli, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_succ]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem pauli_bracket (a b : Fin 3) :
    pauli a * pauli b - pauli b * pauli a =
      ∑ c : Fin 3, ((2 * epsilon3 a b c : ℝ) : ℂ) • pauli c := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  fin_cases a <;> fin_cases b <;>
    simp [epsilon3] <;>
    ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [pauli, Matrix.mul_apply, Fin.sum_univ_succ, h20, h21] <;> ring

def connectedThree (moments : Finset (Fin 3) → ℂ) : ℂ :=
  moments Finset.univ - moments {0, 1} * moments {2} -
    moments {0, 2} * moments {1} - moments {1, 2} * moments {0} +
    2 * moments {0} * moments {1} * moments {2}

/-- Require positivity as well as a small parameter; a zero coupling must
not make the proposed coefficient extraction vacuous. -/
structure SmallCoupling (g : ℝ → ℝ) : Prop where
  positive : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < g r
  tendsToZero : Tendsto g (𝓝[>] 0) (𝓝 0)

def firstCoefficient (g : ℝ → ℝ) (actual : ℝ → ℂ) (free expected : ℂ) : Prop :=
  SmallCoupling g ∧
    Tendsto (fun r => (actual r - free) / (g r : ℂ)) (𝓝[>] 0) (𝓝 expected)

def secondCoefficient (g : ℝ → ℝ) (actual : ℝ → ℂ)
    (free first expected : ℂ) : Prop :=
  SmallCoupling g ∧ Tendsto
    (fun r => (actual r - free - (g r : ℂ) * first) / (g r : ℂ)^2)
    (𝓝[>] 0) (𝓝 expected)

/-- Independent remainder formulation for a chosen coefficient array.
`expected` must be supplied by our separate calculation, not by the answer
being tested. Uniformity in phase/center can be encoded in the index type X. -/
def finiteOrderRemainder {X : Type*} (K : Set X) (g : ℝ → ℝ)
    (actual : ℝ → X → ℂ) (expected : ℕ → X → ℂ) (p : ℕ) : Prop :=
  SmallCoupling g ∧ ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
    ∀ x ∈ K, ‖actual r x - ∑ k : Fin (p+1), (g r : ℂ)^k.val * expected k.val x‖ ≤
      A * |g r|^(p+1)

/-- Test an entire finite OPE output, rather than only its vacuum expectation. -/
def finiteOutputRemainder {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (K : Set X) (g : ℝ → ℝ) (actual : ℝ → X → E)
    (expected : ℕ → X → E) (p : ℕ) : Prop :=
  SmallCoupling g ∧ ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ r : ℝ in 𝓝[>] 0,
    ∀ x ∈ K, ‖actual r x - ∑ k : Fin (p+1), (g r : ℂ)^k.val • expected k.val x‖ ≤
      A * |g r|^(p+1)

/-- A finite change of physical length. The plus sign is for increasing
length, the opposite of the usual energy-scale beta convention. This does
not follow from the leading logarithmic asymptotic law alone. -/
def oneLoopStepScaling (g : ℝ → ℝ) (b₀ : ℝ) : Prop :=
  SmallCoupling g ∧ ∀ s : ℝ, 1 < s →
    Tendsto (fun r => (g (s*r) - g r) / (g r)^3)
      (𝓝[>] 0) (𝓝 (b₀ * Real.log s))

/-- An independent derivative formula must agree pointwise off the origin.
This definition does not assert that the candidate satisfies the test. -/
def freeKernelTest (candidate : Point → Axis → Axis → Axis → Axis → ℝ) : Prop :=
  ∀ x : Point, x ≠ 0 → ∀ a b c d, candidate x a b c d = expectedCurvature x a b c d

end YMReview.NovemberMatching

namespace YMReview.NovemberMatching.SubmissionAdapter
open YangMills

variable {g : GaugeGroup} {C : WilsonFamily g} {T : Hierarchy C}

/-- Exposes the actual hierarchy without invoking its matching predicate. -/
def observed {n : ℕ}
    (measurement : PerturbativeMatching.Measurement (maxwellReference g) T)
    (phase : Option T.Character) (center : Spacetime)
    (fields : Fin n → Matching.Label (maxwellReference g)) (r : ℝ) (x : Points n) : ℂ :=
  T.correlation phase
    (fun i => ⟨(fields i).1, measurement.frame r (fields i).1 (fields i).2⟩)
    (WithLp.toLp 2 fun i => center + r • x i)

/-- Right-hand side to compare with independently computed numbers. An
equality to this expression alone is not an independent numerical calculation. -/
def submittedCoefficient {n : ℕ} (reference : PerturbativeMatching.Reference g)
    (fields : Fin n → Matching.Label (maxwellReference g)) (k : ℕ) (x : Points n) : ℂ :=
  reference.scheme.conversion.correlation reference.coefficients k fields x

/-- Sanity check on the adapter only; not a new check of the graph coefficients. -/
theorem observed_eq_public {n : ℕ}
    (measurement : PerturbativeMatching.Measurement (maxwellReference g) T)
    (phase : Option T.Character) (center : Spacetime)
    (fields : Fin n → Matching.Label (maxwellReference g)) (r : ℝ) (x : Points n) :
    observed measurement phase center fields r x =
      PerturbativeMatching.measuredCorrelation measurement phase center fields r x := rfl

end YMReview.NovemberMatching.SubmissionAdapter

#print axioms YMReview.NovemberMatching.colorSquare_eq
#print axioms YMReview.NovemberMatching.adjointCasimir_eq
#print axioms YMReview.NovemberMatching.doubledBracket_values
#print axioms YMReview.NovemberMatching.pauli_trace_normalization
#print axioms YMReview.NovemberMatching.pauli_bracket
#print axioms YMReview.NovemberMatching.SubmissionAdapter.observed_eq_public
