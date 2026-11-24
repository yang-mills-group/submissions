import GhostLoopUnit
/-!
# Covariance and momentum rescaling of the finite amplitude

Uses source rotation covariance and its scale law to pass from unit
diagonal probes to arbitrary tensor components and momenta. The unit
tensor reduction is adapted from the submitted SpinResolve.lean proof.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096
open YM YM.MS YM.MS.Arts YM.MS.ScaleForest
open Spin Plane Koszul Heat Flux Landau Book Convolve Motif Halo
open Function Filter Set Finset MeasureTheory Metric Real
open Tone Momentum Frame Wire Color Detect Native Native.Wilsonian City Logarithm Signal
open Landau.Detect.Mark Wind High Knobs Arc Rock Path Oceans Plum Alps Garment Pearl Train Shine Hem Mell
open YM.WilsonMS.BetaValue YM.WilsonMS.BetaValue.HeatPapers SquareShift
open scoped BigOperators Topology ContDiff
namespace YMReview.NovemberMatching.GhostTensor
open GhostRadial GhostContinuation GhostJet GhostInfrared GhostFlow GhostPrimitive GhostUnit

lemma finite_sturdy (G:Gauge) (s y:ℝ) :
    Sturdy true (oneLoopFinite 4 (TwoPoint.ratePair G true true) s y) := by
  have hf : Form0 true (TwoPoint.ratePair G true true 0) := by
    unfold TwoPoint.ratePair
    rw [closeG_eq]
    exact (torn (by simpa using Town_nat 0) (TwoPoint.stem_form G true) ((cursor true).ok.forms true)).smul _
  have ho : Sturdy true (ordinary 4 (TwoPoint.ratePair G true true) 0) := by
    change ordinary 4 (TwoPoint.ratePair G true true) 0∈sturdy true G
    unfold ordinary lowerTaylor
    simp only [vamp,toll,mul_zero,zero_mul,add_zero,Nat.cast_ofNat]
    exact (sturdy true G).add_mem (need_true.lamp hf.token hf.price (by norm_num))
      (Will.preC (sturdy true G) need_true hf.token hf.price 4 (-4))
  have ht : Sturdy true (highTensor 4 (TwoPoint.ratePair G true true) 0) :=
    Sturdy_scale (need_true.jet hf.token hf.price 4) _
  exact Sturdy_plus (Stays ho _ _) (Sturdy_plus (high_jet_properties G).1 (Sturdy_scale ht _))

/-- Adapted from the submission's `TwoPoint.summation_rule`. On a unit
sphere no homogeneity assumption is needed. -/
lemma unit_tensor {G:Gauge} {W:Mob G} (hs:Sturdy true W) (a b:G.ColorIndex)
    (m:ℕ) (p:SectorP m) (hp:p.sq=1) (i j:L m) :
    TwoPoint.kinetic W a b p i j =
      TwoPoint.tensor2 (TwoPoint.along W a b) (TwoPoint.across W a b) p i j := by
  let k:=TwoPoint.zeroDirection m
  have hS : ∃ S:Spin (L m),S.turn p=TwoPoint.primary m := by
    by_cases hv:p=TwoPoint.primary m
    · exact ⟨⟨ContinuousLinearEquiv.refl ..,fun _ _=>rfl⟩,hv⟩
    exact ⟨tilt _ (sub_ne_zero.mpr hv),turns _ _ hv (by rw [hp,TwoPoint.primary_sq])⟩
  obtain ⟨S,hS⟩:=hS
  let A:=TwoPoint.across W a b
  let B:=TwoPoint.along W a b-A
  have ht (i j:L m) : TwoPoint.kinetic W a b (S.turn p) i j =
      (if i=j then A else 0)+if i=k ∧ j=k then B else 0 := by
    rw [hS]
    by_cases hi:i=j
    · subst j
      by_cases hm:i=k
      · subst i
        rw [TwoPoint.pricing_zero a b hs]
        unfold B A
        simp
      rw [TwoPoint.trans_resolves a b hs i hm]
      unfold A
      simp [hm]
    rw [TwoPoint.diagonal_off a b hs i j k hi]
    simp [hi,show ¬(i=k ∧ j=k) from fun ⟨h,h'⟩=>hi (h.trans h'.symm)]
  have heQ (i:L m) : S.profile i k=p i := by
    have hv:=S.rad (spray i) p
    rw [hS] at hv
    simpa [profile,TwoPoint.primary,pairing,spray,Pi.single_apply,mul_ite,ite_mul,k] using hv
  rw [TwoPoint.axis_parity a b hs S]
  simp_rw [ht]
  let U (l r:L m):=(S.profile i l:ℂ)*(S.profile j r:ℂ)
  calc
    (∑ l:L m,_)= (∑ l:L m,U l l)*A+U k k*B := by
      simp_rw [Finset.mul_sum,mul_add,Finset.sum_add_distrib,mul_ite,mul_zero]
      simp [U,Finset.sum_mul,mul_assoc]
      rw [Finset.sum_eq_single k]
      · simp
      · intro l _ hl; simp [hl]
      · simp
    _ = _ := by
      rw [show (∑ l:L m,U l l)=((if i=j then 1 else 0):ℂ) from ?_]
      · unfold U TwoPoint.tensor2
        rw [heQ,heQ,hp]
        push_cast
        split_ifs <;> unfold A B <;> ring
      have hv:=S.weights i j
      unfold U
      simp_rw [←Complex.ofReal_mul,←Complex.ofReal_sum,hv]
      split_ifs <;> simp

lemma finite_scale (G:Gauge) (s y t:ℝ) :
    plow (-4) t (oneLoopFinite 4 (TwoPoint.ratePair G true true) s y) =
      oneLoopFinite 4 (TwoPoint.ratePair G true true) (s+t) (y-t) := by
  have hj : plow (-4) t (ruby (highTensor 4 (TwoPoint.ratePair G true true)) 1)=
      ruby (highTensor 4 (TwoPoint.ratePair G true true)) 1 := by
    simpa using (high_jet_properties G).2.1 t
  have hh : plow (-4) t (highTensor 4 (TwoPoint.ratePair G true true) 0)=
      highTensor 4 (TwoPoint.ratePair G true true) 0 := by
    simpa only [highTensor,Nat.cast_ofNat] using
      ((Home.tad (source_price G) (n:=4)).smul (-(2⁻¹:ℂ))) t
  unfold oneLoopFinite
  simp only [Nat.cast_ofNat]
  rw [←Alps.cert,map_add,map_add,map_smul]
  simp only [Alps.cert,snow,hj,hh]
  rw [add_comm t s,show y-t+(s+t)=y+s by ring]

lemma finite_scale_word (G:Gauge) (s y x:ℝ) (hx:0<x)
    (p:SectorP 0) (i j:L 0) (a b:G.ColorIndex) :
    oneLoopFinite 4 (TwoPoint.ratePair G true true) s y 0 (TwoPoint.word i j a b (x • p)) =
      (x:ℂ)^2*oneLoopFinite 4 (TwoPoint.ratePair G true true) (s+Real.log x) (y-Real.log x) 0
        (TwoPoint.word i j a b p) := by
  have h := congrFun (congrFun (finite_scale G s y (Real.log x)) 0) (TwoPoint.word i j a b p)
  rw [plow_word,Real.exp_log hx] at h
  have he : Real.exp (-2*Real.log x)=1/x^2 := by
    rw [show -2*Real.log x= -(2*Real.log x) by ring,Real.exp_neg,←GhostUnit.exp_square (Real.log x),Real.exp_log hx]
    simp
  rw [he] at h
  push_cast at h
  have hxc : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [←h]
  field_simp

end YMReview.NovemberMatching.GhostTensor
