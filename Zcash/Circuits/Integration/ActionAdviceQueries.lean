import Zcash.Circuits.Action.TopLevel
import Mathlib.Util.AssertNoSorry

/-!
# Action advice-query allocation

This module isolates the remaining concrete check that every derived advice query
names an allocated Action advice column.
-/

namespace Zcash.Snark

open Halo2
open Zcash.Circuits.Action (actionCircuit)

namespace ActionAdviceQueries

/-- Every derived advice query names a column allocated by Action's configure program. -/
theorem columnsAllocated :
    ∀ entry ∈ actionCircuit.pinnedCS.adviceQueryLayout,
      entry.1 < actionCircuit.constraintSystem.numAdviceColumns := by
  native_decide

assert_no_sorry columnsAllocated

end ActionAdviceQueries

end Zcash.Snark
