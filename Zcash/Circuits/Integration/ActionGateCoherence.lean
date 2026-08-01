import Zcash.Circuits.Integration.ActionGateCoherenceCompute
import Mathlib.Util.AssertNoSorry

/-!
# Action polynomial bounds

This module supplies the two Action-specific numerical facts in the generic
constraint-bound boundary. Selector allocation follows for every top-level circuit
from its intrinsic configure and gate lawfulness guarantees.
-/

namespace Zcash.Snark

open Halo2 Keygen
open Halo2
open Zcash.Circuits.Action (actionCircuit)

namespace ActionGateCoherence

/--
The deployed Orchard Action circuit satisfies the polynomial bridge's numerical
bounds.
-/
theorem constraintBounds :
    TopLevelConstraintBounds actionCircuit where
  domainExponent_lt := domainExponent_lt
  selectorDegree := selectorDegree

assert_no_sorry constraintBounds

end ActionGateCoherence

end Zcash.Snark
