import Zcash.Snark.Keygen.Pipeline
import Zcash.Circuits.Integration.ResolverQueryEnvironment

/-!
# Circuit-owned query-layout coverage

Configure-time query registration is append-only. This module transports a
registered fixed or instance query through synthesis closure and selector projection
into the circuit-derived verifying key.
-/

namespace Zcash.Snark

open Halo2

set_option maxHeartbeats 20000

namespace QueryLayouts

variable {F : Type} [Field F] [DecidableEq F]

omit [Field F] [DecidableEq F] in
/-- Registering one queried cell cannot remove an instance query. -/
theorem mem_instanceQueries_registerQueriedCell
    (cs : ConstraintSystem F) (owner : String)
    (expression : Expression F Query)
    (query : Column .instance × Rotation)
    (hquery : query ∈ cs.instanceQueries) :
    query ∈
      (cs.registerQueriedCell owner expression).instanceQueries := by
  cases expression with
  | var atom =>
      cases atom with
      | selector selector =>
          exact hquery
      | fixed column rotation =>
          simp only [Halo2.ConstraintSystem.registerQueriedCell,
            Halo2.ConstraintSystem.queryFixedIndex]
          split <;> exact hquery
      | advice column rotation =>
          simp only [Halo2.ConstraintSystem.registerQueriedCell,
            Halo2.ConstraintSystem.queryAdviceIndex]
          split <;> exact hquery
      | «instance» column rotation =>
          simp only [Halo2.ConstraintSystem.registerQueriedCell]
          unfold Halo2.ConstraintSystem.queryInstanceIndex
          split
          · exact hquery
          · exact List.mem_append_left _ hquery
  | const value =>
      exact hquery
  | add left right =>
      exact hquery
  | mul left right =>
      exact hquery

omit [Field F] [DecidableEq F] in
/-- Registering a queried-cell list cannot remove an instance query. -/
theorem mem_instanceQueries_registerQueriedCells
    (cs : ConstraintSystem F) (owner : String)
    (expressions : List (Expression F Query))
    (query : Column .instance × Rotation)
    (hquery : query ∈ cs.instanceQueries) :
    query ∈
      (cs.registerQueriedCells owner expressions).instanceQueries := by
  induction expressions generalizing cs with
  | nil =>
      exact hquery
  | cons expression expressions ih =>
      apply ih
      exact mem_instanceQueries_registerQueriedCell
        cs owner expression query hquery

omit [Field F] [DecidableEq F] in
/-- A fold of queried-cell registrations cannot remove an instance query. -/
theorem mem_instanceQueries_fold_registerQueriedCells
    {α : Type}
    (entries : List α) (cs : ConstraintSystem F)
    (owner : α → String)
    (expressions : α → List (Expression F Query))
    (query : Column .instance × Rotation)
    (hquery : query ∈ cs.instanceQueries) :
    query ∈
      (entries.foldl
        (fun current entry =>
          current.registerQueriedCells
            (owner entry) (expressions entry))
        cs).instanceQueries := by
  induction entries generalizing cs with
  | nil =>
      exact hquery
  | cons entry entries ih =>
      rw [List.foldl_cons]
      apply ih
      exact mem_instanceQueries_registerQueriedCells
        cs (owner entry) (expressions entry) query hquery

omit [Field F] in
/-- Closing a constraint system under synthesis preserves every configure-registered
instance query. -/
theorem mem_instanceQueries_closeWithOperations_of_mem
    (cs : ConstraintSystem F) (operations : Operations F)
    (query : Column .instance × Rotation)
    (hquery : query ∈ cs.instanceQueries) :
    query ∈ (cs.closeWithOperations operations).instanceQueries := by
  unfold Halo2.ConstraintSystem.closeWithOperations
  apply mem_instanceQueries_fold_registerQueriedCells
  apply mem_instanceQueries_fold_registerQueriedCells
  exact hquery

end QueryLayouts

namespace QueryLayouts

variable
    {G : Type} [AddCommGroup G] [Inhabited G]
    {ConfigInput Config : Type} {Output : TypeMap}
    [CircuitType Output]

/-- A query present in the synthesis-closed top-level constraint system remains in
its derived verifying key's instance-query layout. -/
theorem instanceQueryLayout_of_constraintSystem
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (pp : Keygen.ProofParams) (urs : URS G)
    (column : Column .instance) (rotation : Rotation)
    (hquery :
      (column, rotation) ∈
        top.constraintSystem.instanceQueries) :
    (column.index, rotation) ∈
      (top.toVerifierKey pp urs).instanceQueryLayout := by
  rw [top.toVerifierKey_instanceQueryLayout_derived,
    top.pinnedCS_eq_derive_fp]
  exact
    PinnedConstraintSystem.mem_instanceQueryLayout_derive_of_mem
      top.constraintSystem top.selectorMap column rotation hquery

end QueryLayouts

end Zcash.Snark
