import GluonLoopUnit
/-!
# Full independent finite gluon-bubble comparison

The acceptance theorem discharges GluonLoop.SubmittedFinitePartTest,
without any extra finite-part assumption. It covers the actual submitted
renormalized bubble, all nonzero physical momenta, colors, tensor
components, and positive MS-bar scales. This is one gauge-dependent
graph contribution, not an all-order conventional-perturbation theorem.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096
open YM YM.MS YM.MS.Arts YM.MS.ScaleForest
open Plane Koszul Heat Flux Landau Book Convolve Motif Halo
open Function Filter Set Finset MeasureTheory Metric Real
open Tone Momentum Frame Wire Color Detect Native Native.Wilsonian City Logarithm Signal
open Landau.Detect.Mark Wind High Knobs Arc Rock Path Oceans Plum Alps Garment Pearl Train Shine Hem Mell
open YM.WilsonMS.BetaValue YM.WilsonMS.BetaValue.HeatPapers SquareShift
open scoped BigOperators Topology ContDiff
namespace YMReview.NovemberMatching.GluonSolution
open GluonUnit GluonTensor

lemma unit_limit (G:Gauge) (hG:G.Simple) (p:SectorP 0) (hp:p.sq=1)
    (i j:L 0) (a b:G.ColorIndex) (y:ℝ) :
    Tendsto (fun s:ℝ=>oneLoopFinite 4 (TwoPoint.ratePair G false false) s y 0 (TwoPoint.word i j a b p))
      atTop (𝓝 ((if a=b then (G.casimir:ℂ) else 0)*
        GluonLoop.finitePart ((2*y-Real.eulerMascheroniConstant+Real.log (4*Real.pi):ℝ):ℂ)
          (if i=j then (p.sq:ℂ) else 0) ((p i:ℂ)*(p j:ℂ)))) := by
  let A(s:ℝ):=TwoPoint.across (oneLoopFinite 4 (TwoPoint.ratePair G false false) s y) a b
  let B(s:ℝ):=TwoPoint.along (oneLoopFinite 4 (TwoPoint.ratePair G false false) s y) a b
  let C:ℂ:=if a=b then (G.casimir:ℂ) else 0
  let L:ℂ:=((2*y-Real.eulerMascheroniConstant+Real.log (4*Real.pi):ℝ):ℂ)
  have hA : Tendsto A atTop (𝓝 (C*GluonLoop.finitePart L 1 0)) := by
    have h:=GluonUnit.finite_unit_limit G hG false a b y
    simpa only [A,TwoPoint.across,TwoPoint.kinetic,GluonCarpet.axis,GluonInfrared.probeValue,
      Bool.false_eq_true,if_false,Complex.ofReal_zero] using! h
  have hB : Tendsto B atTop (𝓝 (C*GluonLoop.finitePart L 1 1)) := by
    have h:=GluonUnit.finite_unit_limit G hG true a b y
    simpa only [B,TwoPoint.along,TwoPoint.kinetic,GluonCarpet.axis,GluonInfrared.probeValue,
      if_true,Complex.ofReal_one] using! h
  have hD : Tendsto (fun s:ℝ=>if i=j then A s*(p.sq:ℂ) else 0) atTop
      (𝓝 (if i=j then (C*GluonLoop.finitePart L 1 0)*(p.sq:ℂ) else 0)) := by
    split_ifs
    · exact hA.mul_const _
    exact tendsto_const_nhds
  have h:=hD.add (((hB.sub hA).mul_const (p i:ℂ)).mul_const (p j:ℂ))
  convert! h using 1
  · funext s
    exact GhostTensor.unit_tensor (GluonTensor.finite_sturdy G s y) a b 0 p hp i j
  · congr 1
    unfold GluonLoop.finitePart C L
    split_ifs <;> ring

lemma nonzero_limit (G:Gauge) (hG:G.Simple) (p:SectorP 0) (hp:0<p.sq)
    (i j:L 0) (a b:G.ColorIndex) (y:ℝ) :
    Tendsto (fun s:ℝ=>oneLoopFinite 4 (TwoPoint.ratePair G false false) s y 0 (TwoPoint.word i j a b p))
      atTop (𝓝 ((if a=b then (G.casimir:ℂ) else 0)*
        GluonLoop.finitePart ((2*y-Real.eulerMascheroniConstant+Real.log (4*Real.pi)-Real.log p.sq:ℝ):ℂ)
          (if i=j then (p.sq:ℂ) else 0) ((p i:ℂ)*(p j:ℂ)))) := by
  let x:=Real.sqrt p.sq
  let q:=x⁻¹ • p
  have hx : 0<x := Real.sqrt_pos.mpr hp
  have hx2 : x^2=p.sq := Real.sq_sqrt hp.le
  have hq : q.sq=1 := by
    change Momentum.sq (x⁻¹ • p)=1
    rw [Momentum.scaling,←hx2]
    field_simp
  have hxp : x • q=p := by unfold q; rw [smul_smul,mul_inv_cancel₀ hx.ne',one_smul]
  have hlog : 2*Real.log x=Real.log p.sq := by rw [←hx2,Real.log_pow]; norm_num
  have hL : 2*(y-Real.log x)-Real.eulerMascheroniConstant+Real.log (4*Real.pi) =
      2*y-Real.eulerMascheroniConstant+Real.log (4*Real.pi)-Real.log p.sq := by linarith
  have h:=((unit_limit G hG q hq i j a b (y-Real.log x)).comp
      (tendsto_id.atTop_add (tendsto_const_nhds (x:=Real.log x)))).const_mul ((x:ℂ)^2)
  convert! h using 1
  · funext s
    rw [←hxp]
    exact GluonTensor.finite_scale_word G s y x hx q i j a b
  · congr 1
    rw [hL,hq]
    simp only [q,Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_inv]
    have hxc : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hx.ne'
    rw [←hx2]
    push_cast
    unfold GluonLoop.finitePart
    split_ifs <;> field_simp <;> ring

/-- Full independent finite-part benchmark. This is the exact frozen target:
all admissible simple gauge groups, colors, nonzero physical momenta, tensor
components, and positive MS-bar scales. No finite-part hypothesis is assumed. -/
theorem acceptance (G:Gauge) : GluonLoop.SubmittedFinitePartTest G := by
  intro hG mu hmu a b p i j hp
  let y:=Real.log mu+(Real.eulerMascheroniConstant-Real.log (4*Real.pi))/2
  have h:=nonzero_limit G hG p hp i j a b y
  have hL : 2*y-Real.eulerMascheroniConstant+Real.log (4*Real.pi)-Real.log p.sq=
      Real.log (mu^2/p.sq) := by
    rw [Real.log_div (pow_ne_zero _ hmu.ne') hp.ne',Real.log_pow]
    unfold y
    norm_num
    ring
  rw [hL] at h
  convert! h using 1
  funext s
  exact congrFun (GluonLoop.submitted_finite_reading G y s) (TwoPoint.word i j a b p)
end YMReview.NovemberMatching.GluonSolution

#print axioms YMReview.NovemberMatching.GluonSolution.acceptance
