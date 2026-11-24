import GluonLoopFinite
/-!
# Covariance and momentum rescaling of the finite amplitude

Uses source rotation covariance and its scale law to pass from unit
diagonal probes to arbitrary tensor components and momenta. The unit
tensor reduction is adapted from the submitted SpinResolve.lean proof.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
open YM YM.MS YM.MS.Arts YM.MS.ScaleForest
open Spin Plane Koszul Heat Flux Landau Book Convolve Motif Halo
open Function Filter Set Finset MeasureTheory Metric Real
open Tone Momentum Frame Wire Color Detect Native Native.Wilsonian City Logarithm Signal
open Landau.Detect.Mark Wind High Knobs Arc Rock Path Oceans Plum Alps Garment Pearl Train Shine Hem Mell
open YM.WilsonMS.BetaValue YM.WilsonMS.BetaValue.HeatPapers SquareShift
open scoped BigOperators Topology ContDiff
namespace YMReview.NovemberMatching.GluonTensor
open GhostRadial GhostContinuation GhostJet GhostInfrared GhostFlow GhostPrimitive GhostUnit

open GluonLoop
lemma high_jet_properties (G : Gauge) :
    Sturdy true (ruby (highTensor 4 (TwoPoint.ratePair G false false)) 1) ∧
    Home (ruby (highTensor 4 (TwoPoint.ratePair G false false)) 1) 4 ∧
    kPrice (ruby (highTensor 4 (TwoPoint.ratePair G false false)) 1) := by
  have hl := (close_form (G:=G) (cursor false)
    (firstResult (interaction G 1) (interaction G 1) (cursor false))).2
  have hh := high_lift hl 4
  have hp := Rub (show Live (highTensor 4 (TwoPoint.ratePair G false false)) from ⟨_,hh⟩) 1
  have hf : ∀ᶠ z in dotty, Form0 true (TwoPoint.ratePair G false false z) := by
    filter_upwards [high0] with z hz
    unfold TwoPoint.ratePair
    rw [closeG_eq]
    exact (torn hz (TwoPoint.stem_form G false) ((cursor false).ok.forms true)).smul _
  refine ⟨pick_sturdy hp ?_,pick_home hp ?_,hp.price⟩
  · filter_upwards [hf] with z hz
    exact Sturdy_scale (need_true.jet hz.token hz.price 4) _
  · filter_upwards [hf] with z hz
    exact (Home.tad hz.price).smul _

lemma finite_sturdy (G:Gauge) (s y:ℝ) :
    Sturdy true (oneLoopFinite 4 (TwoPoint.ratePair G false false) s y) := by
  have hf : Form0 true (TwoPoint.ratePair G false false 0) := by
    unfold TwoPoint.ratePair
    rw [closeG_eq]
    exact (torn (by simpa using Town_nat 0) (TwoPoint.stem_form G false) ((cursor false).ok.forms true)).smul _
  have ho : Sturdy true (ordinary 4 (TwoPoint.ratePair G false false) 0) := by
    change ordinary 4 (TwoPoint.ratePair G false false) 0∈sturdy true G
    unfold ordinary lowerTaylor
    simp only [vamp,toll,mul_zero,zero_mul,add_zero,Nat.cast_ofNat]
    exact (sturdy true G).add_mem (need_true.lamp hf.token hf.price (by norm_num))
      (Will.preC (sturdy true G) need_true hf.token hf.price 4 (-4))
  have ht : Sturdy true (highTensor 4 (TwoPoint.ratePair G false false) 0) :=
    Sturdy_scale (need_true.jet hf.token hf.price 4) _
  exact Sturdy_plus (Stays ho _ _) (Sturdy_plus (high_jet_properties G).1 (Sturdy_scale ht _))

lemma finite_scale (G:Gauge) (s y t:ℝ) :
    plow (-4) t (oneLoopFinite 4 (TwoPoint.ratePair G false false) s y) =
      oneLoopFinite 4 (TwoPoint.ratePair G false false) (s+t) (y-t) := by
  have hj : plow (-4) t (ruby (highTensor 4 (TwoPoint.ratePair G false false)) 1)=
      ruby (highTensor 4 (TwoPoint.ratePair G false false)) 1 := by
    simpa using (high_jet_properties G).2.1 t
  have hh : plow (-4) t (highTensor 4 (TwoPoint.ratePair G false false) 0)=
      highTensor 4 (TwoPoint.ratePair G false false) 0 := by
    simpa only [highTensor,Nat.cast_ofNat] using
      ((Home.tad (GluonLoop.source_price G) (n:=4)).smul (-(2⁻¹:ℂ))) t
  unfold oneLoopFinite
  simp only [Nat.cast_ofNat]
  rw [←Alps.cert,map_add,map_add,map_smul]
  simp only [Alps.cert,snow,hj,hh]
  rw [add_comm t s,show y-t+(s+t)=y+s by ring]

lemma finite_scale_word (G:Gauge) (s y x:ℝ) (hx:0<x)
    (p:SectorP 0) (i j:L 0) (a b:G.ColorIndex) :
    oneLoopFinite 4 (TwoPoint.ratePair G false false) s y 0 (TwoPoint.word i j a b (x • p)) =
      (x:ℂ)^2*oneLoopFinite 4 (TwoPoint.ratePair G false false) (s+Real.log x) (y-Real.log x) 0
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

end YMReview.NovemberMatching.GluonTensor
#print axioms YMReview.NovemberMatching.GluonTensor.finite_sturdy
#print axioms YMReview.NovemberMatching.GluonTensor.finite_scale_word
