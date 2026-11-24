import YM.MS.ScaleForest.TestScale

/-!
# Inspect the actual pole-insertion and finite-term theorems

These commands record types and axiom dependencies of submitted theorems.
They are not independent reproofs or an independently computed loop amplitude.

`poleK` identifies a pole of the graph built from two cubic vertices;
`ghost_bill` evaluates its AA tensor for two ghost contractions. This is
the ghost-loop contribution to gauge-field self-energy, not a ghost two-point
function. `ghost_input` inserts that actual pole into the regulated complement.
`premature` shows that replacing the complement d(z) by d(0) before multiplying
by 1/z changes the finite limit from H(0) to H(0)-d'(0). The source uses z=-ε.

That formula does not assert d'(0) is nonzero for every component, or that a
change survives all cancellations in a full physical amplitude. `DScaleJet`
describes its change with scale. `final_including` keeps the rest of a forest
sum explicit when extracting an entry, conditional on membership in the sum.

The generic one-loop finite-value and unique-pole theorems retain the first
regulator jet of the divergent Taylor tensor. None of these checks identifies
the complete sector prescription with a separately formalized textbook scheme.
-/

#check YM.MS.ScaleForest.TwoPoint.poleK
#check YM.MS.ScaleForest.TwoPoint.ghost_bill
#check YM.MS.ScaleForest.Triangle.ghost_input
#check YM.MS.ScaleForest.Triangle.premature
#check YM.MS.ScaleForest.Triangle.DScaleJet
#check YM.MS.ScaleForest.simple_finite
#check YM.MS.ScaleForest.simple_pole_rule
#check YM.MS.ScaleForest.final_including

#print axioms YM.MS.ScaleForest.TwoPoint.poleK
#print axioms YM.MS.ScaleForest.TwoPoint.ghost_bill
#print axioms YM.MS.ScaleForest.Triangle.ghost_input
#print axioms YM.MS.ScaleForest.Triangle.premature
#print axioms YM.MS.ScaleForest.Triangle.DScaleJet
#print axioms YM.MS.ScaleForest.simple_finite
#print axioms YM.MS.ScaleForest.simple_pole_rule
#print axioms YM.MS.ScaleForest.final_including
