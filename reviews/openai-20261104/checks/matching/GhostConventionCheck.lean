import YM.MS.Graphical.CommonGates
import YM.MS.Motif.Vox
import YangMills.WilsonProof.NativeSupport.YM.MS.Motif.Warp
import Mathlib.Tactic

/-!
# A scalar-antighost dictionary for the submitted Landau symbols

Use Fourier derivatives +i p, the ordered scalar covariance
  <c(p) barc(-p)> = 1/p²,
  <barc(p) c(-p)> = -1/p²,
and identify the vector antifield in physical ghost contractions with
  K_mu(p) = -i p_mu barc(p).
These choices are stated explicitly, so both orientations can test the signs.

The local action check below concerns one ghost, one vector antifield and one
gauge field. It is not a theorem identifying all renormalized diagrams under
gauge fixing, nor a proof that all external-antifield correlators are physical.
The propagator comparison concerns momentum-space symbols, interpreted away
from p² = 0; Lean's totalized inverse at zero is not a distributional extension.
The substitution constrains K to be longitudinal. It does not identify the
unrestricted BV source space with the scalar-antighost field space.
-/

noncomputable section
set_option autoImplicit false
open YM YM.MS YM.MS.Arts

namespace YMReview.NovemberMatching.GhostCheck

def scalarGhost {A : Type} [Fintype A] (p : Momentum A) : ℂ := (p.sq : ℂ)⁻¹

def antighostDerivative {A : Type} [Fintype A] (p : Momentum A) (mu : A) : ℂ :=
  -Complex.I * (p mu : ℂ)

/-- Derivative on the second leg has momentum -p. -/
theorem ghost_to_vector {A : Type} [Fintype A] [DecidableEq A]
    (p : Momentum A) (mu : A) :
    Swirl.Near.Tail Landau.ghost (Landau.anti mu) p =
      scalarGhost p * antighostDerivative (-p) mu := by
  simp [Swirl.Near.Tail, scalarGhost,
    antighostDerivative, div_eq_mul_inv]
  ring

/-- Reversing two odd fields introduces the scalar ghost minus sign. -/
theorem vector_to_ghost {A : Type} [Fintype A] [DecidableEq A]
    (p : Momentum A) (mu : A) :
    Swirl.Near.Tail (Landau.anti mu) Landau.ghost p =
      antighostDerivative p mu * (-scalarGhost p) := by
  simp [Swirl.Near.Tail, scalarGhost,
    antighostDerivative, div_eq_mul_inv]
  ring

open Motif Plane Koszul in
/-- Source vertex in external order (K_mu^a, A_nu^b, c^c), in the
submission's derivative-normalized row convention. No factorial is inserted. -/
theorem source_ghost_gluon (G : Gauge) (n : ℕ) (z : ℂ)
    (mu nu : Arts.L n) (a b c : G.ColorIndex) (q p k : SectorP n) :
    cape (applyS z G n)
      [(onX true (some mu,a),q), (onX false (some nu,b),p),
        (onX false (none,c),k)] =
      z * (if mu = nu then rune b c a else 0) := by
  change (D (onX true (some mu,a),q) (cape (applyS z G n)))
    [(onX false (some nu,b),p), (onX false (none,c),k)] = _
  rw [cape_tick (application z)]
  simp [phase, applyS, convoke, axisP, lock, rowP, moon, cwave, A, lip,
    chew, Motif.leaf, note, mono, scattered, scatter_cons, scatter_nil,
    onX, field, Landau.parity, Landau.p, cross]
  by_cases h : mu = nu
  · subst nu
    simp
  · simp [h, Ne.symm h]

open Motif Plane Koszul in
/-- The curvature-squared part contains no antifields, so the same vertex
is obtained from the full classical log density. -/
theorem classical_ghost_gluon (G : Gauge) (n : ℕ) (z : ℂ)
    (mu nu : Arts.L n) (a b c : G.ColorIndex) (q p k : SectorP n) :
    ploy G z n
      [(onX true (some mu,a),q), (onX false (some nu,b),p),
        (onX false (none,c),k)] =
      z * (if mu = nu then rune b c a else 0) := by
  have hcore := (core_g (G:=G) (n:=n) z).2.1 (some mu,a) q
  have hz := congrFun hcore
    [(onX false (some nu,b),p), (onX false (none,c),k)]
  change core G n z
    [(onX true (some mu,a),q), (onX false (some nu,b),p),
      (onX false (none,c),k)] = 0 at hz
  change core G n z _ + cape (applyS z G n) _ = _
  rw [hz, zero_add, source_ghost_gluon]

open Motif in
/-- Substitute K_mu(q) = -i q_mu barc(q). The external order is
(barc^a(q), A_nu^b(p), c^c(k)); this is a log-density coefficient.
Momentum conservation is imposed separately in a Feynman amplitude. -/
theorem scalar_antighost_vertex (G : Gauge) (n : ℕ) (z : ℂ)
    (nu : Arts.L n) (a b c : G.ColorIndex) (q p k : SectorP n) :
    (∑ mu : Arts.L n, antighostDerivative q mu * ploy G z n
      [(onX true (some mu,a),q), (onX false (some nu,b),p),
        (onX false (none,c),k)]) =
      -Complex.I * z * (q nu : ℂ) * rune b c a := by
  simp only [classical_ghost_gluon, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, antighostDerivative]
  ring

end YMReview.NovemberMatching.GhostCheck

#print axioms YMReview.NovemberMatching.GhostCheck.ghost_to_vector
#print axioms YMReview.NovemberMatching.GhostCheck.vector_to_ghost
#print axioms YMReview.NovemberMatching.GhostCheck.source_ghost_gluon
#print axioms YMReview.NovemberMatching.GhostCheck.classical_ghost_gluon
#print axioms YMReview.NovemberMatching.GhostCheck.scalar_antighost_vertex
