import Zcash.Circuits.Action.TopLevel
import Zcash.Circuits.Integration.QueryLayouts
import Mathlib.Util.AssertNoSorry

/-!
# Closed Action public-instance layout facts

The public-instance commitment adapter needs one fact about the synthesis-closed Action
constraint system: the configured `primary` column has a rotation-zero instance query. This
module carries that fact from the circuit's own configure run through synthesis closure.

Both halves are structural. `Action.Circuit.configure_primaryRegistered` establishes the
query at the `enableEquality` that registers it and carries it over the chips configured
afterwards; `QueryLayouts.mem_instanceQueries_constraintSystem` transports it through
closure. Neither evaluates the completed Action constraint system.
-/

namespace Zcash.Snark

open Halo2
open Zcash.Circuits
open Zcash.Circuits.Action (orchardActionTopLevelCircuit)

namespace ActionInstanceCommitment

/-- The configured primary Action instance column is present at rotation zero in the
synthesis-closed constraint system. -/
theorem primaryRegistered :
    ((Action.Circuit.configure
          Specs.Sinsemilla.orchardGenerators {}).1.primary,
        (0 : Rotation)) ∈
      orchardActionTopLevelCircuit.constraintSystem.instanceQueries :=
  QueryLayouts.mem_instanceQueries_constraintSystem _ _
    (Action.Circuit.configure_primaryRegistered _ _)

assert_no_sorry primaryRegistered

end ActionInstanceCommitment

end Zcash.Snark
