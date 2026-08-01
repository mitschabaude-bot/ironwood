import Zcash.Circuits.Integration.ResolverQueryEnvironment
import Zcash.Circuits.Integration.ListChunks
import Zcash.Snark.Keygen.Pipeline

/-!
# Permutation compiler round trips

The keygen compiler turns equality-enabled Clean columns into verifier query
references, attaches their global σ-column indices, and splits the result into
permutation chunks. This module proves that the transformation loses no column
information: flattening the chunks and decoding coherent query references
recovers the original permutation-column order.

The result follows from the compiler pipeline itself. It does not inspect a
concrete circuit or use a full-circuit computation certificate.
-/

namespace Zcash.Snark

open Halo2

set_option maxHeartbeats 20000

namespace Configure

/-- Interpreting an append-only configure delta preserves the initial
permutation-column list as a prefix. -/
private theorem apply_permutationColumns_prefix
    {F : Type}
    (delta : ConfigureDelta F) (initial : ConstraintSystem F)
    (counts : ConfigureCounts) :
    List.IsPrefix initial.permutationColumns
      (delta.apply initial counts).permutationColumns := by
  change List.IsPrefix initial.permutationColumns
    (delta.permutationRequests.foldl
      (fun accumulated request =>
        if request ∈ accumulated then accumulated
        else accumulated ++ [request])
      initial.permutationColumns)
  induction delta.permutationRequests generalizing initial with
  | nil => exact List.prefix_refl _
  | cons request requests ih =>
      rw [List.foldl_cons]
      by_cases hrequest : request ∈ initial.permutationColumns
      · simpa [hrequest] using ih initial
      · exact
          (List.prefix_append initial.permutationColumns [request]).trans
            (by simpa [hrequest] using
              ih { initial with
                permutationColumns :=
                  initial.permutationColumns ++ [request] })

/-- Interpreting a configure delta appends no more permutation columns than
the number of raw requests it records. -/
private theorem apply_permutationColumns_length_le
    {F : Type}
    (delta : ConfigureDelta F) (initial : ConstraintSystem F)
    (counts : ConfigureCounts) :
    (delta.apply initial counts).permutationColumns.length ≤
      initial.permutationColumns.length +
        delta.permutationRequests.length := by
  change
    (delta.permutationRequests.foldl
      (fun accumulated request =>
        if request ∈ accumulated then accumulated
        else accumulated ++ [request])
      initial.permutationColumns).length ≤
      initial.permutationColumns.length +
        delta.permutationRequests.length
  induction delta.permutationRequests generalizing initial with
  | nil => simp
  | cons request requests ih =>
      rw [List.foldl_cons]
      by_cases hrequest : request ∈ initial.permutationColumns
      · simp only [hrequest, if_pos]
        have hbound := ih initial
        exact hbound.trans (by simp)
      · simp only [hrequest, if_false]
        have hbound :=
          ih { initial with
            permutationColumns :=
              initial.permutationColumns ++ [request] }
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hbound

/-- Membership in a configure program's final permutation columns is exactly
membership in the initial list or in its append-only request log. -/
theorem mem_permutationColumns_run_iff
    {F A : Type}
    (program : Configure F A) (initial : ConstraintSystem F)
    (column : AnyColumn) :
    column ∈ (program.run initial).2.permutationColumns ↔
      column ∈ initial.permutationColumns ∨
        column ∈
          (program.delta
            (ConfigureCounts.ofConstraintSystem initial)).permutationRequests := by
  simp only [Configure.run, Configure.delta, ConfigureDelta.apply,
    mem_appendFirstEncounters]

@[simp] private theorem ConfigureDelta.queriedCell_permutationRequests
    {F : Type} (owner : String) (cell : Expression F Query) :
    (ConfigureDelta.queriedCell owner cell).permutationRequests = [] := by
  cases cell with
  | var query => cases query <;> rfl
  | const => rfl
  | add => rfl
  | mul => rfl

@[simp] private theorem ConfigureDelta.append_permutationRequests
    {F : Type} (left right : ConfigureDelta F) :
    (left.append right).permutationRequests =
      left.permutationRequests ++ right.permutationRequests :=
  rfl

private theorem foldl_append_permutationRequests
    {F Item : Type} (items : List Item)
    (request : Item → ConfigureDelta F)
    (hrequest :
      ∀ item, (request item).permutationRequests = [])
    (initial : ConfigureDelta F) :
    (items.foldl
      (fun delta item => delta.append (request item))
      initial).permutationRequests =
        initial.permutationRequests := by
  induction items generalizing initial with
  | nil => rfl
  | cons item items ih =>
      rw [List.foldl_cons, ih]
      simp [hrequest]

@[simp] private theorem ConfigureDelta.queriedCells_permutationRequests
    {F : Type} (owner : String) (cells : List (Expression F Query)) :
    (ConfigureDelta.queriedCells owner cells).permutationRequests = [] := by
  unfold ConfigureDelta.queriedCells
  exact foldl_append_permutationRequests cells
    (ConfigureDelta.queriedCell owner)
    (ConfigureDelta.queriedCell_permutationRequests owner) {}

@[simp] private theorem ConfigureDelta.queryAny_permutationRequests
    {F : Type} (column : AnyColumn) :
    (ConfigureDelta.queryAny (F := F) column).permutationRequests = [] := by
  obtain ⟨kind, index⟩ := column
  cases kind <;> rfl

@[simp] private theorem delta_adviceColumn_permutationRequests
    {F : Type} (counts : ConfigureCounts) :
    (Configure.delta (Halo2.adviceColumn : Configure F _) counts).permutationRequests =
      [] :=
  rfl

@[simp] private theorem delta_fixedColumn_permutationRequests
    {F : Type} (counts : ConfigureCounts) :
    (Configure.delta (Halo2.fixedColumn : Configure F _) counts).permutationRequests =
      [] :=
  rfl

@[simp] private theorem delta_instanceColumn_permutationRequests
    {F : Type} (counts : ConfigureCounts) :
    (Configure.delta (Halo2.instanceColumn : Configure F _) counts).permutationRequests =
      [] :=
  rfl

@[simp] private theorem delta_selector_permutationRequests
    {F : Type} (counts : ConfigureCounts) :
    (Configure.delta (Halo2.selector : Configure F _) counts).permutationRequests =
      [] :=
  rfl

@[simp] private theorem delta_complexSelector_permutationRequests
    {F : Type} (counts : ConfigureCounts) :
    (Configure.delta (Halo2.complexSelector : Configure F _) counts).permutationRequests =
      [] :=
  rfl

@[simp] private theorem delta_enableEquality_permutationRequests
    {F : Type} (column : AnyColumn) (counts : ConfigureCounts) :
    (Configure.delta (Halo2.enableEquality (F := F) column) counts).permutationRequests =
      [column] := by
  simp [Configure.delta, Halo2.enableEquality, ConfigureDelta.append]

@[simp] private theorem delta_enableConstant_permutationRequests
    {F : Type} (column : Column .fixed) (counts : ConfigureCounts) :
    (Configure.delta (Halo2.enableConstant (F := F) column) counts).permutationRequests =
      [column.toAny] :=
  rfl

@[simp] private theorem delta_createGate_permutationRequests
    {F : Type} (gate : Gate F) (counts : ConfigureCounts) :
    (Configure.delta (Halo2.createGate gate) counts).permutationRequests = [] := by
  simp [Configure.delta, Halo2.createGate, ConfigureDelta.append]

@[simp] private theorem delta_lookup_permutationRequests
    {F : Type} (queriedCells : List (Expression F Query))
    (tableMap : List (Expression F Query × TableColumn))
    (counts : ConfigureCounts) :
    (Configure.delta (Halo2.lookup queriedCells tableMap) counts).permutationRequests =
      [] := by
  have htables :
      ((tableMap.map Prod.snd).foldl
        (fun (delta : ConfigureDelta F) (table : TableColumn) =>
          delta.append { fixedQueries := [(table.inner, 0)] })
        {}).permutationRequests = [] :=
    foldl_append_permutationRequests _ _ (fun _ => rfl) {}
  simp only [Configure.delta, Halo2.lookup,
    ConfigureDelta.append_permutationRequests,
    ConfigureDelta.queriedCells_permutationRequests, htables,
    List.append_nil]

/-- A configure program only appends to the equality-enabled column list, and
appends at most `bound` entries. This syntactic compiler invariant is
deliberately weaker than column lawfulness: it counts possible appends without
deciding whether duplicate suppression makes them inert. -/
structure PermutationGrowthAtMost
    {F A : Type} (program : Configure F A) (bound : ℕ) : Prop where
  requestBound : ∀ counts,
    (program.delta counts).permutationRequests.length ≤ bound

namespace PermutationGrowthAtMost

theorem preservesPrefix
    {F A : Type} {program : Configure F A} {bound : ℕ}
    (_ : PermutationGrowthAtMost program bound)
    (cs : ConstraintSystem F) :
    List.IsPrefix cs.permutationColumns
      (program cs).2.permutationColumns :=
  apply_permutationColumns_prefix _ _ _

theorem upper
    {F A : Type} {program : Configure F A} {bound : ℕ}
    (hprogram : PermutationGrowthAtMost program bound)
    (cs : ConstraintSystem F) :
    (program cs).2.permutationColumns.length ≤
      cs.permutationColumns.length + bound := by
  exact (apply_permutationColumns_length_le _ _ _).trans
    (Nat.add_le_add_left
      (hprogram.requestBound
        (ConfigureCounts.ofConstraintSystem cs)) _)

theorem weaken
    {F A : Type} {program : Configure F A} {small large : ℕ}
    (hprogram : PermutationGrowthAtMost program small)
    (hbound : small ≤ large) :
    PermutationGrowthAtMost program large := by
  constructor
  intro counts
  exact (hprogram.requestBound counts).trans hbound

theorem pure {F A : Type} (value : A) :
    PermutationGrowthAtMost
      (pure value : Configure F A) 0 := by
  constructor
  intro counts
  simp

theorem bind
    {F A B : Type} {first : Configure F A}
    {next : A → Configure F B} {left right : ℕ}
    (hfirst : PermutationGrowthAtMost first left)
    (hnext : ∀ value, PermutationGrowthAtMost (next value) right) :
    PermutationGrowthAtMost (first >>= next) (left + right) := by
  constructor
  intro counts
  rw [Configure.delta_bind]
  simp only [ConfigureDelta.append]
  rw [List.length_append]
  exact Nat.add_le_add
    (hfirst.requestBound counts)
    ((hnext (first.output counts)).requestBound
      (first.finalCounts counts))

theorem adviceColumn {F : Type} :
    PermutationGrowthAtMost (Halo2.adviceColumn : Configure F _) 0 := by
  constructor
  intro counts
  simp

theorem fixedColumn {F : Type} :
    PermutationGrowthAtMost (Halo2.fixedColumn : Configure F _) 0 := by
  constructor
  intro counts
  simp

theorem instanceColumn {F : Type} :
    PermutationGrowthAtMost (Halo2.instanceColumn : Configure F _) 0 := by
  constructor
  intro counts
  simp

theorem selector {F : Type} :
    PermutationGrowthAtMost (Halo2.selector : Configure F _) 0 := by
  constructor
  intro counts
  simp

theorem complexSelector {F : Type} :
    PermutationGrowthAtMost (Halo2.complexSelector : Configure F _) 0 := by
  constructor
  intro counts
  simp

theorem enableEquality {F : Type} (column : AnyColumn) :
    PermutationGrowthAtMost
      (Halo2.enableEquality (F := F) column) 1 := by
  constructor
  intro counts
  simp

/-- Enabling equality leaves at least its requested column in the permutation
list, whether it was already present or has just been appended. -/
theorem enableEquality_nonempty
    {F : Type} (column : AnyColumn) (cs : ConstraintSystem F) :
    ((Halo2.enableEquality (F := F) column) cs).2.permutationColumns ≠ [] := by
  intro hempty
  have hmem :
      column ∈
        ((Halo2.enableEquality (F := F) column) cs).2.permutationColumns := by
    rw [mem_permutationColumns_run_iff]
    right
    simp [Configure.delta, Halo2.enableEquality,
      ConfigureDelta.append]
  simp [hempty] at hmem

theorem enableConstant {F : Type} (column : Column .fixed) :
    PermutationGrowthAtMost
      (Halo2.enableConstant (F := F) column) 1 := by
  constructor
  intro counts
  simp

theorem lookupTableColumn {F : Type} :
    PermutationGrowthAtMost
      (Halo2.lookupTableColumn : Configure F _) 0 := by
  simpa only [Halo2.lookupTableColumn] using
    (bind (F := F) fixedColumn
      (fun column => pure ({ inner := column } : TableColumn)))

theorem createGate {F : Type} (gate : Gate F) :
    PermutationGrowthAtMost
      (Halo2.createGate gate) 0 := by
  constructor
  intro counts
  simp

theorem lookup {F : Type}
    (queriedCells : List (Expression F Query))
    (tableMap : List (Expression F Query × TableColumn)) :
    PermutationGrowthAtMost
      (Halo2.lookup queriedCells tableMap) 0 := by
  constructor
  intro counts
  simp

end PermutationGrowthAtMost

/-- A typeclass-facing wrapper around `PermutationGrowthAtMost`. Its output
parameter lets instance synthesis calculate a configure program's syntactic
append budget while constructing the compositional proof. -/
class HasPermutationGrowthAtMost
    {F A : Type} (program : Configure F A)
    (bound : outParam ℕ) : Prop where
  law : PermutationGrowthAtMost program bound

namespace HasPermutationGrowthAtMost

open PermutationGrowthAtMost

instance pure {F A : Type} (value : A) :
    HasPermutationGrowthAtMost
      (pure value : Configure F A) 0 :=
  ⟨PermutationGrowthAtMost.pure value⟩

instance bind
    {F A B : Type} {first : Configure F A}
    {next : A → Configure F B} {left right : ℕ}
    [hfirst : HasPermutationGrowthAtMost first left]
    [hnext : ∀ value, HasPermutationGrowthAtMost (next value) right] :
    HasPermutationGrowthAtMost (first >>= next) (left + right) :=
  ⟨PermutationGrowthAtMost.bind hfirst.law
    fun value => (hnext value).law⟩

instance adviceColumn {F : Type} :
    HasPermutationGrowthAtMost
      (Halo2.adviceColumn : Configure F _) 0 :=
  ⟨PermutationGrowthAtMost.adviceColumn⟩

instance fixedColumn {F : Type} :
    HasPermutationGrowthAtMost
      (Halo2.fixedColumn : Configure F _) 0 :=
  ⟨PermutationGrowthAtMost.fixedColumn⟩

instance instanceColumn {F : Type} :
    HasPermutationGrowthAtMost
      (Halo2.instanceColumn : Configure F _) 0 :=
  ⟨PermutationGrowthAtMost.instanceColumn⟩

instance selector {F : Type} :
    HasPermutationGrowthAtMost
      (Halo2.selector : Configure F _) 0 :=
  ⟨PermutationGrowthAtMost.selector⟩

instance complexSelector {F : Type} :
    HasPermutationGrowthAtMost
      (Halo2.complexSelector : Configure F _) 0 :=
  ⟨PermutationGrowthAtMost.complexSelector⟩

instance enableEquality {F : Type} (column : AnyColumn) :
    HasPermutationGrowthAtMost
      (Halo2.enableEquality (F := F) column) 1 :=
  ⟨PermutationGrowthAtMost.enableEquality column⟩

instance enableConstant {F : Type} (column : Column .fixed) :
    HasPermutationGrowthAtMost
      (Halo2.enableConstant (F := F) column) 1 :=
  ⟨PermutationGrowthAtMost.enableConstant column⟩

instance lookupTableColumn {F : Type} :
    HasPermutationGrowthAtMost
      (Halo2.lookupTableColumn : Configure F _) 0 :=
  ⟨PermutationGrowthAtMost.lookupTableColumn⟩

instance createGate {F : Type} (gate : Gate F) :
    HasPermutationGrowthAtMost
      (Halo2.createGate gate) 0 :=
  ⟨PermutationGrowthAtMost.createGate gate⟩

instance lookup {F : Type}
    (queriedCells : List (Expression F Query))
    (tableMap : List (Expression F Query × TableColumn)) :
    HasPermutationGrowthAtMost
      (Halo2.lookup queriedCells tableMap) 0 :=
  ⟨PermutationGrowthAtMost.lookup queriedCells tableMap⟩

end HasPermutationGrowthAtMost

/-- A configure program is guaranteed to request at least one permutation
column. The append-only interpreter turns this local syntactic fact into
nonemptiness of the final permutation-column list. -/
class GuaranteesPermutationNonempty
    {F A : Type} (program : Configure F A) : Prop where
  requests_nonempty : ∀ counts,
    (program.delta counts).permutationRequests ≠ []

namespace GuaranteesPermutationNonempty

theorem nonempty
    {F A : Type} {program : Configure F A}
    (hprogram : GuaranteesPermutationNonempty program)
    (cs : ConstraintSystem F) :
    (program cs).2.permutationColumns ≠ [] := by
  obtain ⟨column, hcolumn⟩ :=
    List.exists_mem_of_ne_nil
      _
      (hprogram.requests_nonempty
        (ConfigureCounts.ofConstraintSystem cs))
  intro hempty
  have hmem : column ∈ (program cs).2.permutationColumns :=
    (mem_permutationColumns_run_iff program cs column).2
      (Or.inr hcolumn)
  simp [hempty] at hmem

instance enableEquality {F : Type} (column : AnyColumn) :
    GuaranteesPermutationNonempty
      (Halo2.enableEquality (F := F) column) :=
  ⟨by
    intro counts
    simp [Configure.delta, Halo2.enableEquality,
      ConfigureDelta.append]⟩

instance enableConstant {F : Type} (column : Column .fixed) :
    GuaranteesPermutationNonempty
      (Halo2.enableConstant (F := F) column) := by
  constructor
  intro counts
  simp [Configure.delta, Halo2.enableConstant]

/-- A request made by the first program remains in the bind's concatenated
request log. -/
instance (priority := 100) bindOfFirst
    {F A B : Type} {first : Configure F A}
    {next : A → Configure F B}
    [hfirst : GuaranteesPermutationNonempty first]
    :
    GuaranteesPermutationNonempty (first >>= next) := by
  constructor
  intro counts
  rw [Configure.delta_bind]
  simp only [ConfigureDelta.append]
  exact List.append_ne_nil_of_left_ne_nil
    (hfirst.requests_nonempty counts) _

/-- Otherwise instance synthesis may find the first request in the
continuation. -/
instance (priority := 90) bindOfNext
    {F A B : Type} {first : Configure F A}
    {next : A → Configure F B}
    [hnext : ∀ value,
      GuaranteesPermutationNonempty (next value)] :
    GuaranteesPermutationNonempty (first >>= next) := by
  constructor
  intro counts
  rw [Configure.delta_bind]
  simp only [ConfigureDelta.append]
  exact List.append_ne_nil_of_right_ne_nil
    _
    ((hnext (first.output counts)).requests_nonempty
      (first.finalCounts counts))

end GuaranteesPermutationNonempty

end Configure

/-- An in-range `findIdx` decodes to the element it searched for. -/
theorem getD_findIdx_eq_target
    {α : Type} [DecidableEq α]
    (xs : List α) (target fallback : α)
    (hin : xs.findIdx (· = target) < xs.length) :
    xs.getD (xs.findIdx (· = target)) fallback = target := by
  rw [List.getD_eq_getElem _ _ hin]
  have hfound :=
    List.findIdx_getElem
      (xs := xs) (p := fun value => value = target) (w := hin)
  simpa using hfound

/-- Reading one inner list is the same as reading the flattened list after the
complete prefix of earlier inner lists. -/
theorem flatten_getD_at_chunk
    {α : Type*} (fallback : α) (chunks : List (List α))
    (chunk column : ℕ)
    (hchunk : chunk < chunks.length)
    (hcolumn : column < (chunks.getD chunk []).length) :
    chunks.flatten.getD
        ((chunks.take chunk).flatten.length + column) fallback =
      (chunks.getD chunk []).getD column fallback := by
  induction chunks generalizing chunk with
  | nil =>
      simp at hchunk
  | cons head tail ih =>
      cases chunk with
      | zero =>
          simp only [List.take_zero, List.flatten_nil, List.length_nil,
            Nat.zero_add, List.getD_cons_zero, List.flatten_cons]
          exact List.getD_append head tail.flatten fallback column hcolumn
      | succ chunk =>
          have hchunkTail : chunk < tail.length := by
            simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hchunk
          have hcolumnTail :
              column < (tail.getD chunk []).length := by
            simpa only [List.getD_cons_succ] using hcolumn
          simp only [List.take_succ_cons, List.flatten_cons,
            List.length_append, List.getD_cons_succ]
          rw [List.getD_append_right]
          · have hindex :
                head.length +
                    (tail.take chunk).flatten.length + column -
                    head.length =
                  (tail.take chunk).flatten.length + column := by
                omega
            rw [hindex]
            exact ih chunk hchunkTail hcolumnTail
          · omega

/--
If decoding flattened compiler chunks yields the source-column list, a local
`(chunk,column)` reference decodes to the source column at its flattened index.
-/
theorem decodedChunkAddress_eq_sourceColumn
    {Reference Address : Type*}
    (decode : Reference → Address)
    (referenceFallback : Reference) (addressFallback : Address)
    (chunks : List (List Reference)) (columns : List Address)
    (hdecoded : chunks.flatten.map decode = columns)
    (chunk column global : ℕ)
    (hchunk : chunk < chunks.length)
    (hcolumn : column < (chunks.getD chunk []).length)
    (hglobal : global < columns.length)
    (hindex :
      (chunks.take chunk).flatten.length + column = global) :
    decode ((chunks.getD chunk []).getD column referenceFallback) =
      columns.getD global addressFallback := by
  have hflatGlobal : global < chunks.flatten.length := by
    have hlength := congrArg List.length hdecoded
    have : chunks.flatten.length = columns.length := by
      simpa only [List.length_map] using hlength
    omega
  have hmapGlobal : global < (chunks.flatten.map decode).length := by
    simpa only [List.length_map] using hflatGlobal
  have hlocal :=
    flatten_getD_at_chunk referenceFallback chunks chunk column hchunk hcolumn
  calc
    decode ((chunks.getD chunk []).getD column referenceFallback) =
        decode (chunks.flatten.getD global referenceFallback) := by
          rw [hindex] at hlocal
          exact congrArg decode hlocal.symm
    _ = (chunks.flatten.map decode).getD global addressFallback := by
          rw [List.getD_eq_getElem _ _ hflatGlobal,
            List.getD_eq_getElem _ _ hmapGlobal]
          simp only [List.getElem_map]
    _ = columns.getD global addressFallback := by rw [hdecoded]

/-- The verifier query reference assigned by the permutation compiler to one
concrete column. -/
def permutationQueryReference
    (adviceQueryLayout fixedQueryLayout instanceQueryLayout :
      List (ℕ × ℤ)) :
    AnyColumn → ColumnRef
  | ⟨.advice, index⟩ =>
      .advice (adviceQueryLayout.findIdx (· = (index, 0)))
  | ⟨.fixed, index⟩ =>
      .fixed (fixedQueryLayout.findIdx (· = (index, 0)))
  | ⟨.instance, index⟩ =>
      .instance (instanceQueryLayout.findIdx (· = (index, 0)))

/-- The verifier CS's variable-width chunking preserves its indexed reference
stream exactly. -/
theorem verifierCS_permutationChunks_flatten
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) :
    top.verifierCS.permutationChunks.flatten =
      (top.permutationColumns.map
        (permutationQueryReference top.adviceQueryLayout
          top.fixedQueryLayout top.instanceQueryLayout)).zipIdx := by
  unfold TopLevelCircuit.verifierCS
  rw [listToChunks_flatten]
  congr 2
  funext column
  rcases column with ⟨kind, index⟩
  cases kind <;> rfl

/-- Halo2's permutation chunk width is positive for every constraint system:
`csDegree` is at least the permutation argument's baseline degree three. -/
theorem constraintSystem_chunkLen_pos (cs : ConstraintSystem Fp) :
    0 < cs.chunkLen := by
  unfold ConstraintSystem.chunkLen csDegree
  dsimp only
  have hdegree :
      3 ≤
        max 3
          (max
            (List.foldl
              (fun m lookup => max m lookup.requiredDegree)
              1 cs.lookups)
            (List.foldl
              (fun m expression => max m expression.degree)
              0 (flatGates cs))) :=
    le_max_left _ _
  omega

/-- The verifier CS emits exactly the circuit-owned ceiling number of chunks. -/
theorem verifierCS_permutationChunks_length
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) :
    top.verifierCS.permutationChunks.length =
      top.permutationSetCount := by
  unfold TopLevelCircuit.verifierCS TopLevelCircuit.permutationSetCount
    TopLevelCircuit.permutationColumnCount TopLevelCircuit.chunkLen
  rw [listToChunks_length _ _
    (constraintSystem_chunkLen_pos top.constraintSystem)]
  simp

/-- A circuit-derived verifying key has exactly the circuit-owned number of
permutation sets. -/
@[simp] theorem _root_.Halo2.TopLevelCircuit.toVerifierKey_permutationChunks_length
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (urs : URS G) :
    (top.toVerifierKey urs).permutationChunks.length =
      top.shape.numPermutationSets := by
  rw [top.toVerifierKey_permutationChunks,
    top.shape_numPermutationSets]
  exact verifierCS_permutationChunks_length top

/-- Each compiler chunk has the standard full-or-final-remainder width. -/
theorem verifierCS_permutationChunks_getD_length
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (i : ℕ) (hi : i < top.verifierCS.permutationChunks.length) :
    (top.verifierCS.permutationChunks.getD i []).length =
      min top.chunkLen
        (top.permutationColumnCount - i * top.chunkLen) := by
  simp only [TopLevelCircuit.verifierCS] at hi ⊢
  have hchunkLen : 0 < top.chunkLen := by
    exact constraintSystem_chunkLen_pos top.constraintSystem
  rw [listToChunks_getD_length top.chunkLen _ hchunkLen i hi]
  simp only [List.length_zipIdx, List.length_map,
    TopLevelCircuit.permutationColumnCount,
    TopLevelCircuit.chunkLen]

/-- Every circuit-derived verifier chunk has the compiler-prescribed width. -/
theorem _root_.Halo2.TopLevelCircuit.toVerifierKey_permutationChunks_getD_length
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (urs : URS G) (i : ℕ)
    (hi : i < (top.toVerifierKey urs).permutationChunks.length) :
    ((top.toVerifierKey urs).permutationChunks.getD i []).length =
      min top.chunkLen
        (top.permutationColumnCount - i * top.chunkLen) := by
  rw [top.toVerifierKey_permutationChunks] at hi ⊢
  exact verifierCS_permutationChunks_getD_length top i hi

/-- Every prefix ending before a valid compiler chunk contains `i * chunkLen`
permutation columns. -/
theorem verifierCS_permutationChunks_take_flatten_length
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (i : ℕ) (hi : i < top.verifierCS.permutationChunks.length) :
    (top.verifierCS.permutationChunks.take i).flatten.length =
      i * top.chunkLen := by
  unfold TopLevelCircuit.verifierCS at hi ⊢
  apply take_flatten_length_of_dropLast_full
  · exact listToChunks_dropLast_full _ _
      (constraintSystem_chunkLen_pos top.constraintSystem)
  · exact hi

/-- Top-level keygen exposes the compiler prefix law without requiring downstream
proofs to unfold a concrete circuit or verifying-key constructor. -/
theorem _root_.Halo2.TopLevelCircuit.toVerifierKey_permutationChunks_take_flatten_length
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (urs : URS G)
    (i : ℕ) (hi : i < (top.toVerifierKey urs).permutationChunks.length) :
    (((top.toVerifierKey urs).permutationChunks.take i).flatten.length) =
      i * (top.toVerifierKey urs).chunkLen := by
  rw [top.toVerifierKey_permutationChunks] at hi ⊢
  rw [top.toVerifierKey_chunkLen]
  exact verifierCS_permutationChunks_take_flatten_length top i hi

/-- The compiler's chunk family has enough total slots for every permutation
column, without requiring the family itself to be nonempty. -/
theorem permutationColumns_length_le_chunks_mul
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) :
    top.permutationColumnCount ≤
      top.verifierCS.permutationChunks.length * top.chunkLen := by
  let source :=
    (top.permutationColumns.map
      (permutationQueryReference top.adviceQueryLayout
        top.fixedQueryLayout top.instanceQueryLayout)).zipIdx
  have hall :
      (source.toChunks top.chunkLen).Forall
        fun chunk => chunk.length ≤ top.chunkLen :=
    listToChunks_all_le top.chunkLen source
      (constraintSystem_chunkLen_pos top.constraintSystem)
  have hbound :=
    flatten_length_le_mul_of_forall
      (source.toChunks top.chunkLen) top.chunkLen hall
  rw [listToChunks_flatten] at hbound
  have hchunks :
      top.verifierCS.permutationChunks =
        source.toChunks top.chunkLen := by
    unfold TopLevelCircuit.verifierCS
    dsimp only
    apply congrArg (List.toChunks top.chunkLen)
    congr 2
    funext column
    rcases column with ⟨kind, index⟩
    cases kind <;> rfl
  rw [hchunks]
  simpa only [source, List.length_zipIdx, List.length_map,
    TopLevelCircuit.permutationColumnCount] using hbound

/-- A coherent compiled query reference decodes to the concrete column from
which the compiler created it. -/
theorem permutationColumnAddress_queryReference
    {shape : CircuitShape} {F G : Type}
    (vk : VerifyingKey shape F G)
    (adviceQueryLayout fixedQueryLayout instanceQueryLayout :
      List (ℕ × ℤ))
    (hadvice : vk.adviceQueryLayout = adviceQueryLayout)
    (hfixed : vk.fixedQueryLayout = fixedQueryLayout)
    (hinstance : vk.instanceQueryLayout = instanceQueryLayout)
    (column : AnyColumn)
    (hcoherent :
      PermutationColumnRef.Coherent vk
        (permutationQueryReference adviceQueryLayout fixedQueryLayout
          instanceQueryLayout column)) :
    permutationColumnAddress vk
        (permutationQueryReference adviceQueryLayout fixedQueryLayout
          instanceQueryLayout column) = column := by
  rcases column with ⟨kind, index⟩
  cases kind with
  | advice =>
      rcases hcoherent with ⟨-, hin, -⟩
      simp only [permutationQueryReference, permutationColumnAddress]
      rw [hadvice] at hin ⊢
      rw [getD_findIdx_eq_target adviceQueryLayout
        (index, 0) (0, 0) hin]
  | fixed =>
      rcases hcoherent with ⟨-, hin, -⟩
      simp only [permutationQueryReference, permutationColumnAddress]
      rw [hfixed] at hin ⊢
      rw [getD_findIdx_eq_target fixedQueryLayout
        (index, 0) (0, 0) hin]
  | «instance» =>
      rcases hcoherent with ⟨-, hin, -⟩
      simp only [permutationQueryReference, permutationColumnAddress]
      rw [hinstance] at hin ⊢
      rw [getD_findIdx_eq_target instanceQueryLayout
        (index, 0) (0, 0) hin]

/--
For every closed top-level circuit, coherent routing makes the permutation
compiler's column encoding a round trip.
-/
theorem topLevelPermutationColumnAddresses_eq
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (urs : URS G)
    (hcoherent :
      PermutationChunkRoutingCoherent (top.toVerifierKey urs)) :
    top.verifierCS.permutationChunks.flatten.map
          (fun reference =>
            permutationColumnAddress (top.toVerifierKey urs) reference.1) =
      (Keygen.permColsOf top.constraintSystem).map
        Halo2.Layout.ColRef.toAny := by
  rw [verifierCS_permutationChunks_flatten]
  change
    List.map
        (permutationColumnAddress (top.toVerifierKey urs) ∘ Prod.fst)
        _ =
      _
  rw [← List.map_map, List.zipIdx_map_fst]
  simp only [Keygen.permColsOf, List.map_map]
  apply List.map_congr_left
  intro column hcolumn
  simp only [Function.comp_apply]
  let referenceOf :=
    permutationQueryReference top.adviceQueryLayout
      top.fixedQueryLayout top.instanceQueryLayout
  let reference := referenceOf column
  have hreference :
      reference ∈
        top.permutationColumns.map referenceOf :=
    List.mem_map.mpr ⟨column, hcolumn, rfl⟩
  have hindexed :
      ∃ indexed ∈
          (top.permutationColumns.map referenceOf).zipIdx,
        indexed.1 = reference := by
    have hfst :
        reference ∈
          ((top.permutationColumns.map referenceOf).zipIdx).map Prod.fst := by
      rw [List.zipIdx_map_fst]
      exact hreference
    simpa only using List.mem_map.mp hfst
  obtain ⟨indexed, hindexed, hindexedReference⟩ := hindexed
  have hindexedFlat :
      indexed ∈
        top.verifierCS.permutationChunks.flatten := by
    rw [verifierCS_permutationChunks_flatten]
    simpa only [referenceOf] using hindexed
  obtain ⟨chunk, hchunk, hindexedChunk⟩ :=
    List.mem_flatten.mp hindexedFlat
  have hrouted := hcoherent chunk (by
    simpa only [top.toVerifierKey_permutationChunks] using hchunk)
    indexed hindexedChunk
  have hreferenceCoherent :
      PermutationColumnRef.Coherent
        (top.toVerifierKey urs) reference := by
    rw [← hindexedReference]
    exact hrouted.1
  have hdecoded :
      permutationColumnAddress (top.toVerifierKey urs) reference =
        column :=
    permutationColumnAddress_queryReference
      (top.toVerifierKey urs)
      top.adviceQueryLayout top.fixedQueryLayout top.instanceQueryLayout
      (top.toVerifierKey_adviceQueryLayout urs)
      (top.toVerifierKey_fixedQueryLayout urs)
      (top.toVerifierKey_instanceQueryLayout urs)
      column hreferenceCoherent
  rcases column with ⟨kind, index⟩
  cases kind <;>
    simpa [reference, referenceOf, permutationQueryReference,
      Halo2.Layout.ColRef.toAny] using hdecoded

end Zcash.Snark
