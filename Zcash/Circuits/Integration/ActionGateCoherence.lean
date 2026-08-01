import Zcash.Circuits.Integration.ActionGateCoherenceCompute
import Mathlib.Util.AssertNoSorry

/-!
# Action top-level gate coherence

This module supplies the two Action-specific numerical facts in the generic static
gate-coherence boundary. Selector allocation follows for every top-level circuit from
its intrinsic configure and gate lawfulness guarantees.
-/

namespace Zcash.Snark

open Halo2 Keygen
open Halo2
open Zcash.Circuits.Action (actionCircuit)

namespace ActionGateCoherence

/--
The deployed Orchard Action circuit satisfies the complete static gate boundary
against its own derived verifying key.
-/
theorem topLevel :
    TopLevelGateCoherence actionCircuit where
  domainExponent_lt := domainExponent_lt
  selectorDegree := selectorDegree

assert_no_sorry topLevel

end ActionGateCoherence

end Zcash.Snark
