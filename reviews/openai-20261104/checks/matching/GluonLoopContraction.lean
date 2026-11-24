import GluonLoopHeat
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open YM YM.MS YM.MS.Arts YM.MS.ScaleForest
open Plane Koszul Heat Flux Landau Book Convolve Motif Halo
open Function Filter Set Finset MeasureTheory Real
open YM.WilsonMS.BetaValue
namespace YMReview.NovemberMatching.GluonContraction
open GluonTrace

def p6 (x : ℝ) : SectorP 1 := ![x,0,0,0,0,0]
def q6 (q : SectorP 0) (R : ℝ) : SectorP 1 := ![q 0,q 1,q 2,q 3,R,0]
def A (q : SectorP 0) (R : ℝ) := q.sq+R^2
def B (q : SectorP 0) (R x : ℝ) := q.sq+R^2+2*x*q 0+x^2
def K (q : SectorP 0) (R : ℝ) := q.sq+R^2-(q 0)^2

lemma tire_T (q : SectorP 0) (R x : ℝ) :
    tireG (p6 x) (q6 q R) 1 =
      4*(x^2*(A q R+B q R x-(q 1)^2)*K q R+5*A q R*B q R x*(q 1)^2) := by
  simp [tireG,tridentMu,GluonVertex.trident,polar0,precision,delta,
    Fin.sum_univ_succ,p6,q6,A,B,K,Momentum.sq]
  ring

lemma tire_L (q : SectorP 0) (R x : ℝ) :
    tireG (p6 x) (q6 q R) 0 =
      (2*q 0+x)^2*(5*A q R*B q R x-x^2*K q R) := by
  simp [tireG,tridentMu,GluonVertex.trident,polar0,precision,delta,
    Fin.sum_univ_succ,p6,q6,A,B,K,Momentum.sq]
  ring

end YMReview.NovemberMatching.GluonContraction
#print axioms YMReview.NovemberMatching.GluonContraction.tire_T
#print axioms YMReview.NovemberMatching.GluonContraction.tire_L
