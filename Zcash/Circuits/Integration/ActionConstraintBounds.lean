import Zcash.Circuits.Action.PlannerTrace
import Zcash.Circuits.Integration.TopLevelGates
import Mathlib.Util.AssertNoSorry

/-!
# Action polynomial bounds

This module supplies the two Action-specific numerical facts in the generic
constraint-bound boundary. Selector allocation follows for every top-level circuit
from its intrinsic configure and gate lawfulness guarantees.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (scalarFieldOrder)

open Halo2 Keygen
open Zcash.Circuits.Action (actionCircuit)

namespace ActionConstraintBounds

/-- The derived Action constraint-system degree is below the Pasta field order. -/
theorem selectorDegree :
    csDegree actionCircuit.constraintSystem < scalarFieldOrder := by
  rw [actionCircuit.constraintSystem_csDegree,
    Zcash.Circuits.Action.actionCircuit_constraintDegree_eq]
  norm_num [scalarFieldOrder]

/-- The circuit-derived Action domain exponent is within Pasta's supported range. -/
theorem domainExponent_lt :
    actionCircuit.domainExponent < 33 := by
  rw [Zcash.Circuits.Action.actionCircuit_domainExponent_eq]
  norm_num

/-- The deployed Orchard Action circuit satisfies the polynomial bridge's numerical
bounds. -/
theorem constraintBounds :
    TopLevelConstraintBounds actionCircuit where
  domainExponent_lt := domainExponent_lt
  selectorDegree := selectorDegree

assert_no_sorry constraintBounds
assert_no_sorry selectorDegree
assert_no_sorry domainExponent_lt

end ActionConstraintBounds

end Zcash.Snark
