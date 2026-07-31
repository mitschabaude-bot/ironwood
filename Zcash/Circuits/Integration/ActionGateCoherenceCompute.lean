import Zcash.Circuits.Action.TopLevel
import Zcash.Circuits.Integration.TopLevelGates
import Mathlib.Util.AssertNoSorry

/-!
# Closed computations for Action gate coherence

This small module isolates the remaining numerical computation certificates.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (scalarFieldOrder)

open Halo2 Keygen
open Zcash.Circuits
open Zcash.Circuits.Action (actionCircuit)

namespace ActionGateCoherence

/-- The derived Action constraint-system degree is below the Pasta field order. -/
theorem selectorDegree :
    csDegree actionCircuit.constraintSystem < scalarFieldOrder := by
  native_decide

/-- The circuit-derived Action domain exponent is within Pasta's supported range. -/
theorem domainExponent_lt :
    actionCircuit.domainExponent < 33 := by
  native_decide

/-- Every derived advice query names a column allocated by Action's configure program. -/
theorem adviceQueryColumnsAllocated :
    ∀ entry ∈ actionCircuit.adviceQueryLayout,
      entry.1 < actionCircuit.adviceColumnCount := by
  native_decide

assert_no_sorry selectorDegree
assert_no_sorry domainExponent_lt
assert_no_sorry adviceQueryColumnsAllocated

end ActionGateCoherence

end Zcash.Snark
