/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import GrothendieckPeriod

/-!
# Axiom Verification Target

Run lake env lean GrothendieckPeriod/AxiomCheck.lean in CI to verify that all
core theorems in GrothendieckPeriod rely strictly on standard Lean axioms
propext, Classical.choice, Quot.sound) without sorryAx.
-/

#print axioms GrothendieckPeriod.cycle_iff_rational_periods
#print axioms GrothendieckPeriod.GPC_P1_H2
#print axioms GrothendieckPeriod.HasRationalPeriods.pullback
#print axioms GrothendieckPeriod.GPC_SpecQBar_H0
#print axioms GrothendieckPeriod.GPC.directSum
#print axioms GrothendieckPeriod.HasRationalPeriods.tmul
#print axioms GrothendieckPeriod.ComparisonSystem.periodSubalgebra_changeOfBasis_eq
#print axioms GrothendieckPeriod.Grothendieck_iff_Andre_over_Q
#print axioms GrothendieckPeriod.GPC_CM_elliptic_curve
