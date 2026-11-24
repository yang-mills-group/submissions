import GluonLoopInfrared
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
open YM YM.MS YM.MS.Arts YM.MS.ScaleForest
open Plane Koszul Heat Flux Landau Book Convolve Motif Halo
open Function Filter Set Finset MeasureTheory Real
open Tone Momentum Frame Wire Color Detect Native Native.Wilsonian City Logarithm Signal
open Landau.Detect.Mark Wind High Knobs Arc Rock Path Oceans Plum Alps Garment Pearl Train Shine Hem Mell
open YM.WilsonMS.BetaValue YM.WilsonMS.BetaValue.HeatPapers SquareShift
open scoped Topology ContDiff
namespace YMReview.NovemberMatching.GluonJetParameter
open GluonJet

def j (long:Bool) (u:ℝ) :=
  if long then (138)*u^1+(-858)*u^2+(1440)*u^3+(-720)*u^4
  else (98)*u^1+(-338)*u^2+(480)*u^3+(-240)*u^4

def dj (long:Bool) (u:ℝ) :=
  if long then (158)*u^1+(-962)*u^2+(1608)*u^3+(-804)*u^4
  else (104)*u^1+(-372)*u^2+(536)*u^3+(-268)*u^4

def Q (long:Bool) (u:ℝ) :=
  if long then (1)*u^0+(69)*u^2+(-286)*u^3+(360)*u^4+(-144)*u^5
  else ((-25/3))*u^0+(49)*u^2+((-338/3))*u^3+(120)*u^4+(-48)*u^5

def S (long:Bool) (u:ℝ) :=
  if long then (1)*u^0+(1)*u^1+(70)*u^2+(-216)*u^3+(144)*u^4
  else ((-25/3))*u^0+((-25/3))*u^1+((122/3))*u^2+(-72)*u^3+(48)*u^4

def R (long:Bool) (u:ℝ) :=
  if long then (1)*u^1+((159/2))*u^2+((-892/3))*u^3+(348)*u^4+(-132)*u^5
  else ((-25/3))*u^1+((287/6))*u^2+((-994/9))*u^3+(116)*u^4+(-44)*u^5

def J (long:Bool) (u:ℝ) :=
  if long then (69)*u^2+(-286)*u^3+(360)*u^4+(-144)*u^5
  else (49)*u^2+((-338/3))*u^3+(120)*u^4+(-48)*u^5

lemma Q_deriv (long:Bool) (u:ℝ) : HasDerivAt (Q long) (j long u) u := by
  cases long
  · convert! (((((hasDerivAt_const u ((-25/3):ℝ)).add ((hasDerivAt_pow 2 u).const_mul (49))).add ((hasDerivAt_pow 3 u).const_mul ((-338/3)))).add ((hasDerivAt_pow 4 u).const_mul (120))).add ((hasDerivAt_pow 5 u).const_mul (-48))) using 1
    · funext v; simp only [Q,Bool.false_eq_true,if_false,if_true,Pi.add_apply,Pi.sub_apply]; ring
    · norm_num [Q,j,dj,S]; ring
  · convert! (((((hasDerivAt_const u (1:ℝ)).add ((hasDerivAt_pow 2 u).const_mul (69))).add ((hasDerivAt_pow 3 u).const_mul (-286))).add ((hasDerivAt_pow 4 u).const_mul (360))).add ((hasDerivAt_pow 5 u).const_mul (-144))) using 1
    · funext v; simp only [Q,Bool.false_eq_true,if_false,if_true,Pi.add_apply,Pi.sub_apply]; ring
    · norm_num [Q,j,dj,S]; ring

lemma J_deriv (long:Bool) (u:ℝ) : HasDerivAt (J long) (j long u) u := by
  cases long
  · convert! (((((hasDerivAt_const u (0:ℝ)).add ((hasDerivAt_pow 2 u).const_mul (49))).add ((hasDerivAt_pow 3 u).const_mul ((-338/3)))).add ((hasDerivAt_pow 4 u).const_mul (120))).add ((hasDerivAt_pow 5 u).const_mul (-48))) using 1
    · funext v; simp only [J,Bool.false_eq_true,if_false,if_true,Pi.add_apply,Pi.sub_apply]; ring
    · norm_num [J,j,dj,S]; ring
  · convert! (((((hasDerivAt_const u (0:ℝ)).add ((hasDerivAt_pow 2 u).const_mul (69))).add ((hasDerivAt_pow 3 u).const_mul (-286))).add ((hasDerivAt_pow 4 u).const_mul (360))).add ((hasDerivAt_pow 5 u).const_mul (-144))) using 1
    · funext v; simp only [J,Bool.false_eq_true,if_false,if_true,Pi.add_apply,Pi.sub_apply]; ring
    · norm_num [J,j,dj,S]; ring

lemma R_deriv (long:Bool) (u:ℝ) : HasDerivAt (R long) (dj long u+S long u) u := by
  cases long
  · convert! ((((((hasDerivAt_const u (0:ℝ)).add ((hasDerivAt_pow 1 u).const_mul ((-25/3)))).add ((hasDerivAt_pow 2 u).const_mul ((287/6)))).add ((hasDerivAt_pow 3 u).const_mul ((-994/9)))).add ((hasDerivAt_pow 4 u).const_mul (116))).add ((hasDerivAt_pow 5 u).const_mul (-44))) using 1
    · funext v; simp only [R,Bool.false_eq_true,if_false,if_true,Pi.add_apply,Pi.sub_apply]; ring
    · norm_num [R,j,dj,S]; ring
  · convert! ((((((hasDerivAt_const u (0:ℝ)).add ((hasDerivAt_pow 1 u).const_mul (1))).add ((hasDerivAt_pow 2 u).const_mul ((159/2)))).add ((hasDerivAt_pow 3 u).const_mul ((-892/3)))).add ((hasDerivAt_pow 4 u).const_mul (348))).add ((hasDerivAt_pow 5 u).const_mul (-132))) using 1
    · funext v; simp only [R,Bool.false_eq_true,if_false,if_true,Pi.add_apply,Pi.sub_apply]; ring
    · norm_num [R,j,dj,S]; ring

lemma Q_factor (long:Bool) (u:ℝ) : Q long u=(1-u)*S long u := by
  cases long <;> simp only [Q,S,Bool.false_eq_true,if_false,if_true] <;> ring

def logPrimitive (long:Bool) (u:ℝ) := Q long u*Real.log (1-u)+R long u
lemma logPrimitive_deriv (long:Bool) (u:ℝ) (hu:u<1) :
    HasDerivAt (logPrimitive long) (dj long u+j long u*Real.log (1-u)) u := by
  have hd:=((Q_deriv long u).mul (((hasDerivAt_const u (1:ℝ)).sub (hasDerivAt_id' u)).log (by change 1-u≠0; linarith))).add
    (R_deriv long u)
  apply hd.congr_deriv
  simp only [Pi.sub_apply]
  rw [Q_factor]
  have hn:1-u≠0 := by linarith
  field_simp
  ring

lemma integral_j (long:Bool) : (∫ u:ℝ in (0:ℝ)..(1/2:ℝ),j long u)=if long then -1/2 else 25/6 := by
  have hc : Continuous (j long) := by unfold j; cases long <;> simp only [Bool.false_eq_true,if_false,if_true] <;> fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _=>J_deriv long u) (hc.intervalIntegrable _ _)]
  cases long <;> norm_num [J]

lemma integral_log (long:Bool) :
    (∫ u:ℝ in (0:ℝ)..(1/2:ℝ),dj long u+j long u*Real.log (1-u))=
      if long then 5/6-(1/2)*Real.log 2 else -5/36+(25/6)*Real.log 2 := by
  have hc : ContinuousOn (logPrimitive long) (Icc (0:ℝ) (1/2:ℝ)) := by
    unfold logPrimitive Q R
    cases long <;> simp only [Bool.false_eq_true,if_false,if_true] <;>
      fun_prop (disch:=intros u hu; have ht:=hu.2; linarith)
  have hi : ContinuousOn (fun u:ℝ=>dj long u+j long u*Real.log (1-u)) (Icc (0:ℝ) (1/2:ℝ)) := by
    unfold dj j
    cases long <;> simp only [Bool.false_eq_true,if_false,if_true] <;>
      fun_prop (disch:=intros u hu; have ht:=hu.2; linarith)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num : (0:ℝ)≤1/2) hc
    (fun u hu=>logPrimitive_deriv long u (by linarith [hu.2]))
    (hi.intervalIntegrable_of_Icc (by norm_num))]
  have hl : Real.log ((1:ℝ)/2)= -Real.log 2 := by rw [Real.log_div (by norm_num) (by norm_num)]; simp
  cases long <;> norm_num [logPrimitive,Q,R,hl] <;> ring

def jetParameter (long:Bool) (u:ℝ) := dj long u+j long u*Real.log (1-u)-Real.log (4*Real.pi)*j long u

lemma j_continuous (long:Bool) : Continuous (j long) := by
  unfold j
  cases long <;> simp only [Bool.false_eq_true,if_false,if_true] <;> fun_prop
lemma jetParameter_continuous (long:Bool) : ContinuousOn (jetParameter long) (Icc (0:ℝ) (1/2:ℝ)) := by
  unfold jetParameter dj j
  cases long <;> simp only [Bool.false_eq_true,if_false,if_true] <;>
    fun_prop (disch:=intros u hu;have ht:=hu.2;linarith)

lemma jetParameter_integral (long:Bool) :
    (∫ u:ℝ in (0:ℝ)..(1/2:ℝ),jetParameter long u) = -2*GluonLoop.jet (GluonInfrared.probeValue long) := by
  have hh : ContinuousOn (fun u:ℝ=>dj long u+j long u*Real.log (1-u)) (Icc (0:ℝ) (1/2:ℝ)) := by
    unfold dj j
    cases long <;> simp only [Bool.false_eq_true,if_false,if_true] <;>
      fun_prop (disch:=intros u hu;have ht:=hu.2;linarith)
  have ha : IntervalIntegrable (fun u:ℝ=>dj long u+j long u*Real.log (1-u)) volume 0 (1/2) :=
    hh.intervalIntegrable_of_Icc (by norm_num)
  unfold jetParameter
  rw [intervalIntegral.integral_sub ha (((j_continuous long).const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,integral_log,integral_j]
  cases long <;> norm_num [GluonLoop.jet,GluonLoop.k,GluonInfrared.probeValue] <;> ring

lemma jet_parameter_change (long:Bool) (t:ℝ) :
    GluonJet.jetWithScale long t=logArea/4*jetParameter long (GhostJet.ratio t)*(2*t/(ν t)^2) := by
  have hl : Real.log (1-GhostJet.ratio t)= -Real.log (ν t) := by
    rw [GhostJet.ratio_complement,Real.log_inv]
  unfold GluonJet.jetWithScale jetParameter GluonJet.jetLocal GluonJet.localValue GhostJet.weight
  simp only [neg_zero,Real.rpow_zero,mul_one]
  rw [hl,GhostJet.convention_log]
  unfold GluonJet.localJet GluonJet.c0 GluonJet.c1 j dj volume4 logArea GhostJet.ratio ν
  cases long <;> simp only [Bool.false_eq_true,if_false,if_true]
  all_goals
    generalize Real.log (1+t^2)=l
    generalize Real.log (4*Real.pi)=k
    field_simp
    ring

lemma local_parameter_change (long:Bool) (t:ℝ) :
    GluonJet.localValue long 0 t=logArea/4*j long (GhostJet.ratio t)*(2*t/(ν t)^2) := by
  unfold GluonJet.localValue GhostJet.weight GluonJet.c0 GluonJet.c1 j volume4 logArea GhostJet.ratio ν
  cases long <;> simp only [Bool.false_eq_true,if_false,if_true,neg_zero,Real.rpow_zero,mul_one]
  all_goals field_simp;ring

lemma integrated_jet_value (long:Bool) :
    (∫ t:ℝ in (0:ℝ)..1,GluonJet.jetWithScale long t)= -logArea/2*GluonLoop.jet (GluonInfrared.probeValue long) := by
  simp_rw [jet_parameter_change,mul_assoc (logArea/4),intervalIntegral.integral_const_mul]
  rw [GhostJet.parameter_substitution (jetParameter long) (jetParameter_continuous long),jetParameter_integral]
  ring

lemma integrated_local_value (long:Bool) :
    (∫ t:ℝ in (0:ℝ)..1,GluonJet.localValue long 0 t)= -logArea/2*GluonLoop.k (GluonInfrared.probeValue long) := by
  simp_rw [local_parameter_change,mul_assoc (logArea/4),intervalIntegral.integral_const_mul]
  rw [GhostJet.parameter_substitution (j long) (j_continuous long).continuousOn,integral_j]
  cases long <;> norm_num [GluonLoop.k,GluonInfrared.probeValue] <;> ring

theorem source_high_unit (G:Gauge) (long:Bool) (a b:G.ColorIndex) :
    highTensor 4 (TwoPoint.ratePair G false false) 0 0
      (TwoPoint.word (GluonCarpet.axis long) (GluonCarpet.axis long) a b (TwoPoint.primary 0))=
      (∑ d:G.ColorIndex,angle d a b)*(logArea:ℂ)*(GluonLoop.k (GluonInfrared.probeValue long):ℝ) := by
  have h:=GluonJet.actual_high_real G long a b 0 (by norm_num)
  simp only [Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one,integrated_local_value] at h
  rw [h]
  push_cast
  ring

theorem submitted_jet_unit (G:Gauge) (long:Bool) (a b:G.ColorIndex) :
    ruby (highTensor 4 (TwoPoint.ratePair G false false)) 1 0
      (TwoPoint.word (GluonCarpet.axis long) (GluonCarpet.axis long) a b (TwoPoint.primary 0))=
      (∑ d:G.ColorIndex,angle d a b)*(logArea:ℂ)*(GluonLoop.jet (GluonInfrared.probeValue long):ℝ) := by
  have hl:=(close_form (G:=G) (cursor false)
    (firstResult (interaction G 1) (interaction G 1) (cursor false))).2
  have he:=GhostJet.ruby_real_derivative (high_lift hl 4)
    (TwoPoint.word (GluonCarpet.axis long) (GluonCarpet.axis long) a b (TwoPoint.primary 0)) _
    (GluonJet.actual_high_derivative G long a b)
  change ruby (highTensor 4 (TwoPoint.ratePair G false false)) 1 0 _=_ at he
  rw [he,integrated_jet_value]
  push_cast
  ring

end YMReview.NovemberMatching.GluonJetParameter
#print axioms YMReview.NovemberMatching.GluonJetParameter.integral_log
#print axioms YMReview.NovemberMatching.GluonJetParameter.submitted_jet_unit
#print axioms YMReview.NovemberMatching.GluonJetParameter.source_high_unit
