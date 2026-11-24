import GhostLoopInfrared
/-!
# Source scale equation and ultraviolet boundary condition

Relates the actual source ordinary/plow subtraction to its scale derivative
and ultraviolet boundary. The top Taylor term cancels against the explicit
logarithmic subtraction in oneLoopFinite.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
open YM YM.MS YM.MS.Arts YM.MS.ScaleForest
open Plane Koszul Heat Flux Landau Book Convolve Motif Halo
open Function Filter Set Finset MeasureTheory Metric Real
open Tone Momentum Frame Wire Color Detect Native Native.Wilsonian City Logarithm Signal
open Landau.Detect.Mark Wind High Knobs Arc Rock Path Oceans Plum Alps Garment Pearl Train Shine Hem Mell
open YM.WilsonMS.BetaValue YM.WilsonMS.BetaValue.HeatPapers SquareShift
open scoped BigOperators Topology ContDiff
namespace YMReview.NovemberMatching.GhostFlow
open GhostRadial GhostContinuation GhostJet GhostInfrared

lemma density_first (v t:ℝ) : HasDerivAt (fun x:ℝ=>density 0 v t x) 0 0 := by
  let g (y:ℝ) := GhostJet.weight 0 t*Real.exp (-ratio t*y)*
    (GhostLoopFinite.coeffA 4 (ratio t) 1+GhostLoopFinite.coeffB 4 (ratio t) 1 v*y+
     GhostLoopFinite.coeffC 4 (ratio t) 1 v*y^2+GhostLoopFinite.coeffD (ratio t) v*y^3)
  have hg : DifferentiableAt ℝ g ((0:ℝ)^2) := by unfold g; fun_prop
  have h := hg.hasDerivAt.comp (h:=fun x:ℝ=>x^2) (0:ℝ) (hasDerivAt_pow 2 (0:ℝ))
  convert! h using 1
  · funext x
    unfold density g
    simp only [Function.comp_def,mul_zero,add_zero]
    ring
  norm_num

lemma continued_first (v:ℝ) :
    HasDerivAt (fun x:ℝ=>∫ t:ℝ in (0:ℝ)..1,density 0 v t x) 0 0 := by
  have h := compact_derivative _ (density_smooth 0 v) 0
  simp only [(density_first v _).deriv,intervalIntegral.integral_zero] at h
  exact h

lemma continued_zero (v:ℝ) :
    (∫ t:ℝ in (0:ℝ)..1,density 0 v t 0) = logArea*11/64 := by
  simp_rw [density_parameter,mul_assoc (logArea/2),intervalIntegral.integral_const_mul]
  rw [parameter_substitution (fun u:ℝ=>Real.exp (-(0^2)*u)*heatPolynomial v u (0^2)) (by unfold heatPolynomial; fun_prop)]
  have he : (fun u:ℝ=>Real.exp (-(0^2)*u)*heatPolynomial v u (0^2)) = fun u=>6*u-12*u^2+6*u^3 := by
    funext u
    unfold heatPolynomial
    norm_num
    ring
  rw [he,intervalIntegral.integral_add,intervalIntegral.integral_sub]
  · simp only [intervalIntegral.integral_const_mul]
    norm_num [integral_id,integral_pow]
    rw [intervalIntegral.integral_const_mul]
    norm_num [integral_id]
    ring
  all_goals exact (by fun_prop : Continuous _).intervalIntegrable _ _

lemma ordinary_trail {G:Gauge} (W:Coat G) (hW:kPrice (W 0)) :
    Trail (ordinary 4 W 0) (W 0-Tad (W 0) 4) (-4) := by
  have hp := Trail.prog_p (x:=(-4:ℂ)) (n:=5) hW (by norm_num)
  have hc := modular (x:=(-4:ℂ)) (n:=4) hW (by intro i hi; interval_cases i <;> norm_num)
  have h := hp.plus hc
  have he : Hem.clear 5 (W 0)+haze 4 (W 0)=W 0-Tad (W 0) 4 := by
    rw [Hem.clear,show haze 5 (W 0)=haze 4 (W 0)+Tad (W 0) 4 from haze_step _ _]
    abel
  rw [he] at h
  simpa only [ordinary,lowerTaylor,vamp,toll,mul_zero,zero_mul,add_zero,Nat.cast_ofNat] using h

lemma plow_word {G:Gauge} (W:Mob G) (s:ℝ) (p:SectorP 0) (i j:L 0) (a b:G.ColorIndex) :
    plow (-4) s W 0 (TwoPoint.word i j a b p) =
      (Real.exp (-2*s):ℂ)*W 0 (TwoPoint.word i j a b (Real.exp s • p)) := by
  unfold plow
  rw [show mass (TwoPoint.word i j a b p)=2 from rfl]
  norm_num only [Int.cast_ofNat,Nat.cast_ofNat]
  have hs : sr s (TwoPoint.word i j a b p)=TwoPoint.word i j a b (Real.exp s • p) := by
    simp only [sr,TwoPoint.word,vec,List.map_cons,List.map_nil,smul_neg]
  rw [hs]
  congr 1
  simp only [amount]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

lemma tad_word {G:Gauge} (W:Mob G) (p:SectorP 0) (i j:L 0) (a b:G.ColorIndex) (n:ℕ) :
    Tad W (n+2) 0 (TwoPoint.word i j a b p) =
      reading n (fun x:ℝ=>W 0 (TwoPoint.word i j a b (x • p))) := by
  rw [t_bud W (j:=n) (show mass (TwoPoint.word i j a b p)+(n:ℤ)=n+2 by change 2+(n:ℤ)=n+2; ring),torch_at]
  simp only [TwoPoint.word,vec,ray_go,List.map_cons,List.map_nil,smul_neg]

lemma source_tad_two (G:Gauge) (p:SectorP 0) (hp:p.sq=1) (i:L 0) (a b:G.ColorIndex) :
    Tad (TwoPoint.ratePair G true true 0) 2 0 (TwoPoint.word i i a b p) =
      -11/8*(∑ d:G.ColorIndex,angle d a b)*(logArea:ℂ) := by
  rw [show (2:ℕ)=0+2 by rfl,tad_word]
  simp only [reading,iteratedDeriv_zero,Nat.factorial_zero,Nat.cast_one,inv_one,one_smul]
  have h := actual_force_scaled G p i a b (0:ℝ) (by norm_num) 0
  simp only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one,hp,continued_density,continued_zero] at h
  change TwoPoint.kinetic _ a b (0 • p) i i = _
  rw [h]
  push_cast
  ring

lemma source_tad_three (G:Gauge) (p:SectorP 0) (hp:p.sq=1) (i:L 0) (a b:G.ColorIndex) :
    Tad (TwoPoint.ratePair G true true 0) 3 0 (TwoPoint.word i i a b p) = 0 := by
  rw [show (3:ℕ)=1+2 by rfl,tad_word]
  have hh : HasDerivAt (fun x:ℝ=>TwoPoint.ratePair G true true 0 0 (TwoPoint.word i i a b (x • p))) 0 0 := by
    have h := ((Complex.ofRealCLM.hasFDerivAt).comp_hasDerivAt 0 (continued_first (p i*p i))).const_mul
      (-8*∑ d:G.ColorIndex,angle d a b)
    convert! h using 1
    · funext x
      have ht := actual_force_scaled G p i a b (0:ℝ) (by norm_num) x
      simpa only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one,hp,continued_density] using! ht
    simp
  simp only [reading,iteratedDeriv_one,Nat.factorial_one,Nat.cast_one,inv_one,one_smul,hh.deriv]

lemma source_price (G:Gauge) : kPrice (TwoPoint.ratePair G true true 0) :=
  (close_form (G:=G) (cursor true) (firstResult (interaction G 1) (interaction G 1) (cursor true))).2.price


lemma lowerTaylor_unit (G:Gauge) (p:SectorP 0) (hp:p.sq=1) (i:L 0) (a b:G.ColorIndex) (s:ℝ) :
    plow (-4) s (lowerTaylor 4 4 (TwoPoint.ratePair G true true) 0) 0 (TwoPoint.word i i a b p) =
      11/16*(∑ d:G.ColorIndex,angle d a b)*(logArea:ℂ)*(Real.exp (-2*s):ℂ) := by
  let W := TwoPoint.ratePair G true true 0
  have h0 : Tad W 0 0 (TwoPoint.word i i a b p)=0 := t_exc (by change (0:ℤ)<2; norm_num)
  have h1 : Tad W 1 0 (TwoPoint.word i i a b p)=0 := t_exc (by change (1:ℤ)<2; norm_num)
  have h2 := source_tad_two G p hp i a b
  have h3 := source_tad_three G p hp i a b
  unfold lowerTaylor cPos
  simp only [vamp,toll,mul_zero,zero_mul,add_zero,Nat.cast_ofNat]
  rw [←Alps.cert,map_sum]
  simp only [map_smul,Alps.cert,move_tad (source_price G),Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  simp only [Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,zero_add]
  simp only [←show W=TwoPoint.ratePair G true true 0 from rfl,h0,h1,mul_zero,zero_add]
  rw [h2,h3]
  norm_num
  have he : amount (-2) s=(Real.exp (-2*s):ℂ) := by
    rw [amount,Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [he]
  push_cast
  ring

lemma ordinary_boundary (G:Gauge) (p:SectorP 0) (hp:p.sq=1) (i:L 0) (a b:G.ColorIndex) :
    Tendsto (fun s:ℝ=>
      plow (-4) s (ordinary 4 (TwoPoint.ratePair G true true) 0) 0 (TwoPoint.word i i a b p) -
      11/16*(∑ d:G.ColorIndex,angle d a b)*(logArea:ℂ)*(Real.exp (-2*s):ℂ)) atBot (𝓝 0) := by
  have h := frame_lim (W:=TwoPoint.ratePair G true true 0) (x:=(-4:ℂ)) (n:=5) 0 (TwoPoint.word i i a b p)
  convert! h using 1
  funext s
  unfold ordinary
  simp only [vamp,toll,mul_zero,zero_mul,add_zero,Nat.cast_ofNat]
  rw [←Alps.cert,map_add,Alps.cert,Alps.cert]
  simp only [Pi.add_apply]
  rw [lowerTaylor_unit G p hp i a b s]
  ring

/-- The finite reading obeys the actual scale equation, including the
cancellation of the resonant Taylor term by the logarithmic subtraction. -/
lemma finite_derivative {G:Gauge} (W:Coat G) (hW:kPrice (W 0)) (s y:ℝ)
    (m:ℕ) (w:List (Shore G m)) :
    HasDerivAt (fun s:ℝ=>oneLoopFinite 4 W s y m w)
      (plow (-4) s (W 0) m w) s := by
  have h := (ordinary_trail W hW).derive s m w
  have hl : HasDerivAt (fun s:ℝ=>(↑((y+s)*(-2)):ℂ)) (-2) s := by
    convert! Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s
      (((hasDerivAt_id' s).const_add y).mul_const (-2)) using 1 <;> simp
  have ht := h.add ((hl.mul_const (highTensor 4 W 0 m w)).const_add (ruby (highTensor 4 W) 1 m w))
  convert! ht using 1
  have h4 : plow (-4) s (Tad (W 0) 4)=Tad (W 0) 4 := by simpa using (Home.tad hW (n:=4)) s
  rw [←Alps.cert (-4) s (W 0-Tad (W 0) 4),map_sub,Alps.cert,Alps.cert,h4]
  simp only [Pi.sub_apply,highTensor,Pi.smul_apply,smul_eq_mul]
  ring
end YMReview.NovemberMatching.GhostFlow
