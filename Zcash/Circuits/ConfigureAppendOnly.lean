import Clean.Halo2

/-!
# Append-only configure registration

Every `Configure` primitive grows the constraint system's registration lists by appending;
none of them removes or reorders an entry. This file states that as a relation between two
constraint systems (`ConstraintSystem.Extends`), lifts it to a predicate on configure
programs (`Configure.AppendOnly`), and proves the predicate closed under the monad
operations and under each primitive.

The point is to establish a registration fact at the allocation site that causes it — say,
the rotation-zero instance query that `enableEquality` registers — and then carry it
through every later configure step of the circuit, without evaluating the completed
constraint system or naming the numeric index the column was assigned.

Circuit-level users prove one `AppendOnly` lemma per `configure` definition and compose
them; the Orchard chips are straight-line `do` blocks, so those proofs are `bind` and
primitive rules applied in sequence, with no loop or branch structure to reason about.

This is Clean material staged in Ironwood: it is generic over the field and mentions no
Orchard-specific circuit, so it is written in the `Halo2` namespace and is expected to move
to `Clean/Halo2/Configure.lean` once its consumers are in place.
-/

namespace Halo2

variable {F : Type} {α β : Type}

/-- `after.Extends before`: every registration list of `before` is a prefix of `after`'s.

The `Configure` state also carries allocation counters, which this relation deliberately
says nothing about — it is about the lists that record what was registered, not how many
columns or selectors exist. -/
structure ConstraintSystem.Extends (after before : ConstraintSystem F) : Prop where
  gates : before.gates <+: after.gates
  lookups : before.lookups <+: after.lookups
  permutationColumns : before.permutationColumns <+: after.permutationColumns
  constants : before.constants <+: after.constants
  adviceQueries : before.adviceQueries <+: after.adviceQueries
  fixedQueries : before.fixedQueries <+: after.fixedQueries
  instanceQueries : before.instanceQueries <+: after.instanceQueries
  invalidQueriedCells : before.invalidQueriedCells <+: after.invalidQueriedCells

namespace ConstraintSystem.Extends

@[refl]
theorem refl (cs : ConstraintSystem F) : cs.Extends cs :=
  ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _,
    List.prefix_refl _, List.prefix_refl _, List.prefix_refl _, List.prefix_refl _⟩

theorem trans {a b c : ConstraintSystem F} (hab : b.Extends a) (hbc : c.Extends b) :
    c.Extends a :=
  ⟨hab.gates.trans hbc.gates, hab.lookups.trans hbc.lookups,
    hab.permutationColumns.trans hbc.permutationColumns,
    hab.constants.trans hbc.constants,
    hab.adviceQueries.trans hbc.adviceQueries,
    hab.fixedQueries.trans hbc.fixedQueries,
    hab.instanceQueries.trans hbc.instanceQueries,
    hab.invalidQueriedCells.trans hbc.invalidQueriedCells⟩

/-- A registered instance query is still registered after any append-only step. -/
theorem mem_instanceQueries {after before : ConstraintSystem F} (h : after.Extends before)
    {query : Column .instance × Rotation} (hquery : query ∈ before.instanceQueries) :
    query ∈ after.instanceQueries :=
  h.instanceQueries.subset hquery

end ConstraintSystem.Extends

/-!
## The registration primitives

`queryAdviceIndex`, `queryFixedIndex` and `queryInstanceIndex` either find the query
already present and return the state unchanged, or append it; `registerQueriedCell`
dispatches to one of them or appends to the poison list. All four are therefore
append-only, and the `Configure` primitives inherit it.
-/

theorem ConstraintSystem.extends_queryAdviceIndex (cs : ConstraintSystem F)
    (column : Column .advice) (rotation : Rotation) :
    (cs.queryAdviceIndex column rotation).Extends cs := by
  unfold ConstraintSystem.queryAdviceIndex
  split
  · exact .refl cs
  · exact { Extends.refl cs with adviceQueries := List.prefix_append _ _ }

theorem ConstraintSystem.extends_queryFixedIndex (cs : ConstraintSystem F)
    (column : Column .fixed) :
    (cs.queryFixedIndex column).Extends cs := by
  unfold ConstraintSystem.queryFixedIndex
  split
  · exact .refl cs
  · exact { Extends.refl cs with fixedQueries := List.prefix_append _ _ }

theorem ConstraintSystem.extends_queryInstanceIndex (cs : ConstraintSystem F)
    (column : Column .instance) (rotation : Rotation) :
    (cs.queryInstanceIndex column rotation).Extends cs := by
  unfold ConstraintSystem.queryInstanceIndex
  split
  · exact .refl cs
  · exact { Extends.refl cs with instanceQueries := List.prefix_append _ _ }

theorem ConstraintSystem.extends_queryAnyIndex (cs : ConstraintSystem F) (column : AnyColumn) :
    (cs.queryAnyIndex column).Extends cs := by
  unfold ConstraintSystem.queryAnyIndex
  match column with
  | ⟨.advice, _⟩ => exact cs.extends_queryAdviceIndex _ _
  | ⟨.fixed, _⟩ => exact cs.extends_queryFixedIndex _
  | ⟨.instance, _⟩ => exact cs.extends_queryInstanceIndex _ _

theorem ConstraintSystem.extends_registerQueriedCell (cs : ConstraintSystem F) (owner : String)
    (expression : Expression F Query) :
    (cs.registerQueriedCell owner expression).Extends cs := by
  unfold ConstraintSystem.registerQueriedCell
  split
  · exact cs.extends_queryAdviceIndex _ _
  · exact cs.extends_queryFixedIndex _
  · exact cs.extends_queryInstanceIndex _ _
  · exact { Extends.refl cs with invalidQueriedCells := List.prefix_append _ _ }
  · exact { Extends.refl cs with invalidQueriedCells := List.prefix_append _ _ }

/-- Folding an append-only step over a list is append-only. Both `registerQueriedCells`
and the table-column registration inside `lookup` have this shape. -/
theorem ConstraintSystem.extends_foldl {entry : Type} (entries : List entry)
    (step : ConstraintSystem F → entry → ConstraintSystem F)
    (hstep : ∀ cs e, (step cs e).Extends cs) (cs : ConstraintSystem F) :
    (entries.foldl step cs).Extends cs := by
  induction entries generalizing cs with
  | nil => exact .refl cs
  | cons e entries ih =>
      rw [List.foldl_cons]
      exact (hstep cs e).trans (ih _)

theorem ConstraintSystem.extends_registerQueriedCells (cs : ConstraintSystem F) (owner : String)
    (expressions : List (Expression F Query)) :
    (cs.registerQueriedCells owner expressions).Extends cs :=
  ConstraintSystem.extends_foldl expressions _
    (fun cs expression => cs.extends_registerQueriedCell owner expression) cs

/-!
## Append-only configure programs
-/

/-- A configure program is append-only when running it from any state only appends to that
state's registration lists. -/
def Configure.AppendOnly (program : Configure F α) : Prop :=
  ∀ cs, (program cs).2.Extends cs

namespace Configure.AppendOnly

open ConstraintSystem (Extends)

theorem pure (a : α) : AppendOnly (Pure.pure a : Configure F α) :=
  fun cs => .refl cs

theorem bind {program : Configure F α} {rest : α → Configure F β}
    (hprogram : AppendOnly program) (hrest : ∀ a, AppendOnly (rest a)) :
    AppendOnly (program >>= rest) :=
  fun cs => (hprogram cs).trans (hrest (program cs).1 (program cs).2)

theorem map {program : Configure F α} (f : α → β) (hprogram : AppendOnly program) :
    AppendOnly (f <$> program) :=
  fun cs => hprogram cs

/-! Column and selector allocation touches only the counters, which `Extends` ignores. -/

theorem adviceColumn : AppendOnly (Halo2.adviceColumn : Configure F (Column .advice)) := by
  intro cs; constructor <;> apply List.prefix_refl

theorem fixedColumn : AppendOnly (Halo2.fixedColumn : Configure F (Column .fixed)) := by
  intro cs; constructor <;> apply List.prefix_refl

theorem instanceColumn : AppendOnly (Halo2.instanceColumn : Configure F (Column .instance)) := by
  intro cs; constructor <;> apply List.prefix_refl

theorem selector : AppendOnly (Halo2.selector : Configure F Selector) := by
  intro cs; constructor <;> apply List.prefix_refl

theorem complexSelector : AppendOnly (Halo2.complexSelector : Configure F Selector) := by
  intro cs; constructor <;> apply List.prefix_refl

theorem lookupTableColumn : AppendOnly (Halo2.lookupTableColumn : Configure F TableColumn) := by
  intro cs; constructor <;> apply List.prefix_refl

theorem enableEquality (column : AnyColumn) :
    AppendOnly (Halo2.enableEquality column : Configure F Unit) := by
  intro cs
  unfold Halo2.enableEquality
  refine Extends.trans (cs.extends_queryAnyIndex column) ?_
  dsimp only
  split
  · exact .refl _
  · exact { Extends.refl _ with permutationColumns := List.prefix_append _ _ }

theorem enableConstant (column : Column .fixed) :
    AppendOnly (Halo2.enableConstant column : Configure F Unit) := by
  intro cs
  unfold Halo2.enableConstant
  refine Extends.trans (cs.extends_queryFixedIndex column) ?_
  dsimp only
  split
  · exact { Extends.refl _ with constants := List.prefix_append _ _ }
  · exact ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_append _ _,
      List.prefix_append _ _, List.prefix_refl _, List.prefix_refl _,
      List.prefix_refl _, List.prefix_refl _⟩

theorem createGate (gate : Gate F) : AppendOnly (Halo2.createGate gate : Configure F Unit) := by
  intro cs
  unfold Halo2.createGate
  refine Extends.trans (cs.extends_registerQueriedCells gate.name gate.queriedCells) ?_
  dsimp only
  exact { Extends.refl _ with gates := List.prefix_append _ _ }

theorem lookup (queriedCells : List (Expression F Query))
    (tableMap : List (Expression F Query × TableColumn)) :
    AppendOnly (Halo2.lookup queriedCells tableMap : Configure F Unit) := by
  intro cs
  unfold Halo2.lookup
  dsimp only
  refine Extends.trans (cs.extends_registerQueriedCells "lookup" queriedCells) ?_
  refine Extends.trans
    (ConstraintSystem.extends_foldl tableMap _
      (fun cs entry => cs.extends_queryFixedIndex entry.2.inner) _) ?_
  dsimp only
  exact { Extends.refl _ with lookups := List.prefix_append _ _ }

end Configure.AppendOnly

/-- Discharge a `Configure.AppendOnly` goal for a straight-line configure body by applying
the monad and primitive rules repeatedly.

A chip that composes other chips puts their `AppendOnly` facts in context first
(`have := Child.configure_appendOnly …`); the tactic reaches for those before it tries to
decompose the call, which keeps the proof at the child's interface instead of unfolding
its body. -/
macro "append_only" : tactic =>
  `(tactic|
      repeat' first
        | with_reducible assumption
        | with_reducible apply Configure.AppendOnly.bind
        | with_reducible apply Configure.AppendOnly.pure
        | with_reducible apply Configure.AppendOnly.adviceColumn
        | with_reducible apply Configure.AppendOnly.fixedColumn
        | with_reducible apply Configure.AppendOnly.instanceColumn
        | with_reducible apply Configure.AppendOnly.selector
        | with_reducible apply Configure.AppendOnly.complexSelector
        | with_reducible apply Configure.AppendOnly.lookupTableColumn
        | with_reducible apply Configure.AppendOnly.enableEquality
        | with_reducible apply Configure.AppendOnly.enableConstant
        | with_reducible apply Configure.AppendOnly.createGate
        | with_reducible apply Configure.AppendOnly.lookup
        | with_reducible apply Configure.AppendOnly.map
        | intro _)

/-!
## Establishing an instance query

`enableEquality` registers a rotation-zero query on its column before appending it to the
permutation columns, so an instance column is registered the moment equality is enabled on
it — regardless of which index the column was allocated.
-/

theorem mem_instanceQueries_queryInstanceIndex (cs : ConstraintSystem F)
    (column : Column .instance) (rotation : Rotation) :
    (column, rotation) ∈ (cs.queryInstanceIndex column rotation).instanceQueries := by
  unfold ConstraintSystem.queryInstanceIndex
  split
  · assumption
  · exact List.mem_append_right _ (List.mem_singleton_self _)

/-- Enabling equality on an instance column registers its rotation-zero query. -/
theorem mem_instanceQueries_enableEquality (cs : ConstraintSystem F)
    (column : Column .instance) :
    (column, (0 : Rotation)) ∈
      ((Halo2.enableEquality column.toAny : Configure F Unit) cs).2.instanceQueries := by
  unfold Halo2.enableEquality ConstraintSystem.queryAnyIndex Column.toAny
  dsimp only
  exact mem_instanceQueries_queryInstanceIndex cs column 0

end Halo2
