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

/-- Query registration cannot change the equality-enabled column list. -/
theorem registerQueriedCell_permutationColumns
    {F : Type} (cs : ConstraintSystem F) (owner : String)
    (cell : Expression F Query) :
    (cs.registerQueriedCell owner cell).permutationColumns =
      cs.permutationColumns := by
  cases cell with
  | var query =>
      cases query with
      | selector => rfl
      | fixed column rotation =>
          by_cases h : (column, 0) ∈ cs.fixedQueries <;>
            simp [ConstraintSystem.registerQueriedCell,
              ConstraintSystem.queryFixedIndex, h]
      | advice column rotation =>
          by_cases h : (column, rotation) ∈ cs.adviceQueries <;>
            simp [ConstraintSystem.registerQueriedCell,
              ConstraintSystem.queryAdviceIndex, h]
      | «instance» column rotation =>
          by_cases h : (column, rotation) ∈ cs.instanceQueries <;>
            simp [ConstraintSystem.registerQueriedCell,
              ConstraintSystem.queryInstanceIndex, h]
  | const => rfl
  | add => rfl
  | mul => rfl

/-- Registering a list of query atoms cannot change the equality-enabled
column list. -/
theorem registerQueriedCells_permutationColumns
    {F : Type} (cs : ConstraintSystem F) (owner : String)
    (cells : List (Expression F Query)) :
    (cs.registerQueriedCells owner cells).permutationColumns =
      cs.permutationColumns := by
  induction cells generalizing cs with
  | nil => rfl
  | cons cell cells ih =>
      unfold ConstraintSystem.registerQueriedCells
      rw [List.foldl_cons]
      change
        (List.foldl
          (fun current cell => current.registerQueriedCell owner cell)
          (cs.registerQueriedCell owner cell) cells).permutationColumns =
        cs.permutationColumns
      rw [← ConstraintSystem.registerQueriedCells, ih,
        registerQueriedCell_permutationColumns]

theorem queryFixedIndex_permutationColumns
    {F : Type} (cs : ConstraintSystem F)
    (column : Column .fixed) :
    (cs.queryFixedIndex column).permutationColumns =
      cs.permutationColumns := by
  unfold ConstraintSystem.queryFixedIndex
  split <;> rfl

theorem queryAdviceIndex_permutationColumns
    {F : Type} (cs : ConstraintSystem F)
    (column : Column .advice) (rotation : Rotation) :
    (cs.queryAdviceIndex column rotation).permutationColumns =
      cs.permutationColumns := by
  unfold ConstraintSystem.queryAdviceIndex
  split <;> rfl

theorem queryInstanceIndex_permutationColumns
    {F : Type} (cs : ConstraintSystem F)
    (column : Column .instance) (rotation : Rotation) :
    (cs.queryInstanceIndex column rotation).permutationColumns =
      cs.permutationColumns := by
  unfold ConstraintSystem.queryInstanceIndex
  split <;> rfl

theorem queryAnyIndex_permutationColumns
    {F : Type} (cs : ConstraintSystem F)
    (column : AnyColumn) :
    (cs.queryAnyIndex column).permutationColumns =
      cs.permutationColumns := by
  rcases column with ⟨kind, index⟩
  cases kind with
  | advice =>
      exact queryAdviceIndex_permutationColumns cs ⟨index⟩ 0
  | fixed =>
      exact queryFixedIndex_permutationColumns cs ⟨index⟩
  | «instance» =>
      exact queryInstanceIndex_permutationColumns cs ⟨index⟩ 0

/-- Folding query registration over compiler-discovered arguments preserves
the equality-enabled column list. -/
private theorem fold_registerQueriedCells_permutationColumns
    {F α : Type} (cs : ConstraintSystem F) (items : List α)
    (owner : α → String) (cells : α → List (Expression F Query)) :
    (items.foldl (fun current item =>
      current.registerQueriedCells (owner item) (cells item))
      cs).permutationColumns = cs.permutationColumns := by
  induction items generalizing cs with
  | nil => rfl
  | cons item items ih =>
      rw [List.foldl_cons, ih, registerQueriedCells_permutationColumns]

/-- Synthesis closure only registers queries and appends gates/lookups; it
cannot alter the permutation columns established by `configure`. -/
theorem closeWithOperations_permutationColumns
    {F : Type} [FiniteField F]
    (cs : ConstraintSystem F) (ops : Operations F) :
    (cs.closeWithOperations ops).permutationColumns =
      cs.permutationColumns := by
  unfold ConstraintSystem.closeWithOperations
  change
    (List.foldl _ (List.foldl _ cs _) _).permutationColumns =
      cs.permutationColumns
  rw [fold_registerQueriedCells_permutationColumns,
    fold_registerQueriedCells_permutationColumns]

/-- Closing a top-level circuit under its synthesis operations leaves the
permutation columns computed by `configure` unchanged. -/
theorem _root_.Halo2.TopLevelCircuit.constraintSystem_permutationColumns
    {F ConfigInput Config : Type} [FiniteField F]
    {Output : TypeMap} [CircuitType Output]
    (top : TopLevelCircuit F ConfigInput Config Output) :
    top.constraintSystem.permutationColumns =
      (top.formalCircuit.configure
        top.configInput {}).2.permutationColumns :=
  closeWithOperations_permutationColumns _ _

namespace Configure

/-- A configure program only appends to the equality-enabled column list, and
appends at most `bound` entries. This syntactic compiler invariant is
deliberately weaker than column lawfulness: it counts possible appends without
deciding whether duplicate suppression makes them inert. -/
structure PermutationGrowthAtMost
    {F A : Type} (program : Configure F A) (bound : ℕ) : Prop where
  preservesPrefix : ∀ cs,
    List.IsPrefix cs.permutationColumns
      (program cs).2.permutationColumns
  upper : ∀ cs,
    (program cs).2.permutationColumns.length ≤
      cs.permutationColumns.length + bound

namespace PermutationGrowthAtMost

theorem weaken
    {F A : Type} {program : Configure F A} {small large : ℕ}
    (hprogram : PermutationGrowthAtMost program small)
    (hbound : small ≤ large) :
    PermutationGrowthAtMost program large := by
  constructor
  · exact hprogram.preservesPrefix
  · intro cs
    exact (hprogram.upper cs).trans
      (Nat.add_le_add_left hbound _)

theorem pure {F A : Type} (value : A) :
    PermutationGrowthAtMost
      (pure value : Configure F A) 0 := by
  constructor <;> intro cs
  · exact List.prefix_refl _
  · rfl

theorem bind
    {F A B : Type} {first : Configure F A}
    {next : A → Configure F B} {left right : ℕ}
    (hfirst : PermutationGrowthAtMost first left)
    (hnext : ∀ value, PermutationGrowthAtMost (next value) right) :
    PermutationGrowthAtMost (first >>= next) (left + right) := by
  constructor
  · intro cs
    exact (hfirst.preservesPrefix cs).trans
      ((hnext (first cs).1).preservesPrefix (first cs).2)
  · intro cs
    have hleft := hfirst.upper cs
    have hright :=
      (hnext (first cs).1).upper (first cs).2
    change
      (next (first cs).1 (first cs).2).2.permutationColumns.length ≤
        cs.permutationColumns.length + (left + right)
    omega

theorem adviceColumn {F : Type} :
    PermutationGrowthAtMost (Halo2.adviceColumn : Configure F _) 0 := by
  constructor <;> intro cs
  · exact List.prefix_refl _
  · rfl

theorem fixedColumn {F : Type} :
    PermutationGrowthAtMost (Halo2.fixedColumn : Configure F _) 0 := by
  constructor <;> intro cs
  · exact List.prefix_refl _
  · rfl

theorem instanceColumn {F : Type} :
    PermutationGrowthAtMost (Halo2.instanceColumn : Configure F _) 0 := by
  constructor <;> intro cs
  · exact List.prefix_refl _
  · rfl

theorem selector {F : Type} :
    PermutationGrowthAtMost (Halo2.selector : Configure F _) 0 := by
  constructor <;> intro cs
  · exact List.prefix_refl _
  · rfl

theorem complexSelector {F : Type} :
    PermutationGrowthAtMost (Halo2.complexSelector : Configure F _) 0 := by
  constructor <;> intro cs
  · exact List.prefix_refl _
  · rfl

theorem enableEquality {F : Type} (column : AnyColumn) :
    PermutationGrowthAtMost
      (Halo2.enableEquality (F := F) column) 1 := by
  constructor <;> intro cs
  · simp only [Halo2.enableEquality]
    rw [queryAnyIndex_permutationColumns]
    split
    · exact List.prefix_refl _
    · exact List.prefix_append _ _
  · simp only [Halo2.enableEquality]
    rw [queryAnyIndex_permutationColumns]
    split <;> simp_all

/-- Enabling equality leaves at least its requested column in the permutation
list, whether it was already present or has just been appended. -/
theorem enableEquality_nonempty
    {F : Type} (column : AnyColumn) (cs : ConstraintSystem F) :
    ((Halo2.enableEquality (F := F) column) cs).2.permutationColumns ≠ [] := by
  simp only [Halo2.enableEquality]
  rw [queryAnyIndex_permutationColumns]
  split
  · intro hempty
    rw [hempty] at ‹column ∈ cs.permutationColumns›
    simp_all
  · simp

theorem enableConstant {F : Type} (column : Column .fixed) :
    PermutationGrowthAtMost
      (Halo2.enableConstant (F := F) column) 1 := by
  constructor <;> intro cs
  · simp only [Halo2.enableConstant]
    rw [queryFixedIndex_permutationColumns]
    split
    · exact List.prefix_refl _
    · exact List.prefix_append _ _
  · simp only [Halo2.enableConstant]
    rw [queryFixedIndex_permutationColumns]
    split <;> simp_all

theorem lookupTableColumn {F : Type} :
    PermutationGrowthAtMost
      (Halo2.lookupTableColumn : Configure F _) 0 := by
  simpa only [Halo2.lookupTableColumn] using
    (bind (F := F) fixedColumn
      (fun column => pure ({ inner := column } : TableColumn)))

theorem createGate {F : Type} (gate : Gate F) :
    PermutationGrowthAtMost
      (Halo2.createGate gate) 0 := by
  constructor <;> intro cs
  · simp only [Halo2.createGate]
    rw [registerQueriedCells_permutationColumns]
  · simp only [Halo2.createGate]
    rw [registerQueriedCells_permutationColumns]
    omega

theorem lookup {F : Type}
    (queriedCells : List (Expression F Query))
    (tableMap : List (Expression F Query × TableColumn)) :
    PermutationGrowthAtMost
      (Halo2.lookup queriedCells tableMap) 0 := by
  have heq (cs : ConstraintSystem F) :
      ((Halo2.lookup queriedCells tableMap) cs).2.permutationColumns =
        cs.permutationColumns := by
    simp only [Halo2.lookup]
    let registered := cs.registerQueriedCells "lookup" queriedCells
    have hregistered :
        registered.permutationColumns = cs.permutationColumns :=
      registerQueriedCells_permutationColumns _ _ _
    have hfold :
        ∀ (items : List (Expression F Query × TableColumn))
          (current : ConstraintSystem F),
          (items.foldl
            (fun state item => state.queryFixedIndex item.2.inner)
            current).permutationColumns =
              current.permutationColumns := by
      intro items
      induction items with
      | nil => intro current; rfl
      | cons item items ih =>
          intro current
          rw [List.foldl_cons, ih,
            queryFixedIndex_permutationColumns]
    change
      (tableMap.foldl
        (fun state item => state.queryFixedIndex item.2.inner)
        registered).permutationColumns =
          cs.permutationColumns
    rw [hfold, hregistered]
  constructor <;> intro cs
  · rw [heq]
  · rw [heq]
    omega

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

/-- A configure program is guaranteed to leave a nonempty permutation-column
list. Instance synthesis finds an equality/constant enablement in the program
and uses the compositional prefix invariant for everything that follows it. -/
class GuaranteesPermutationNonempty
    {F A : Type} (program : Configure F A) : Prop where
  nonempty : ∀ cs,
    (program cs).2.permutationColumns ≠ []

namespace GuaranteesPermutationNonempty

instance enableEquality {F : Type} (column : AnyColumn) :
    GuaranteesPermutationNonempty
      (Halo2.enableEquality (F := F) column) :=
  ⟨PermutationGrowthAtMost.enableEquality_nonempty column⟩

instance enableConstant {F : Type} (column : Column .fixed) :
    GuaranteesPermutationNonempty
      (Halo2.enableConstant (F := F) column) := by
  constructor
  intro cs
  simp only [Halo2.enableConstant]
  rw [queryFixedIndex_permutationColumns]
  split
  · intro hempty
    rw [hempty] at ‹column.toAny ∈ cs.permutationColumns›
    simp_all
  · simp

/-- Once the first action has produced a column, the continuation's prefix
property prevents it from being erased. -/
instance (priority := 100) bindOfFirst
    {F A B : Type} {first : Configure F A}
    {next : A → Configure F B} {right : ℕ}
    [hfirst : GuaranteesPermutationNonempty first]
    [hnext : ∀ value,
      HasPermutationGrowthAtMost (next value) right] :
    GuaranteesPermutationNonempty (first >>= next) := by
  constructor
  intro cs
  have hsource := hfirst.nonempty cs
  have hprefix :=
    (hnext (first cs).1).law.preservesPrefix (first cs).2
  apply List.ne_nil_of_length_pos
  exact lt_of_lt_of_le
    (List.length_pos_iff_ne_nil.mpr hsource)
    hprefix.length_le

/-- Otherwise instance synthesis may find the first guaranteed enablement in
the continuation. -/
instance (priority := 90) bindOfNext
    {F A B : Type} {first : Configure F A}
    {next : A → Configure F B}
    [hnext : ∀ value,
      GuaranteesPermutationNonempty (next value)] :
    GuaranteesPermutationNonempty (first >>= next) :=
  ⟨fun cs => (hnext (first cs).1).nonempty (first cs).2⟩

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
    (projected : CsFixture Fp) : AnyColumn → ColumnRef
  | ⟨.advice, index⟩ =>
      .advice (projected.adviceQueryLayout.findIdx (· = (index, 0)))
  | ⟨.fixed, index⟩ =>
      .fixed (projected.fixedQueryLayout.findIdx (· = (index, 0)))
  | ⟨.instance, index⟩ =>
      .instance (projected.instanceQueryLayout.findIdx (· = (index, 0)))

/-- The compiler's variable-width chunking preserves its indexed reference
stream exactly. -/
theorem permutationChunksOf_flatten
    (map : SelCompressMap) (cs : ConstraintSystem Fp) :
    (Keygen.permutationChunksOf map cs).flatten =
      (cs.permutationColumns.map
        (permutationQueryReference (projectCS map cs))).zipIdx := by
  unfold Keygen.permutationChunksOf
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

/-- The compiler emits exactly the ceiling number of chunks recorded in `Shape`. -/
theorem permutationChunksOf_length
    (map : SelCompressMap) (cs : ConstraintSystem Fp) :
    (Keygen.permutationChunksOf map cs).length =
      (cs.permutationColumns.length + cs.chunkLen - 1) / cs.chunkLen := by
  unfold Keygen.permutationChunksOf
  rw [listToChunks_length _ _ (constraintSystem_chunkLen_pos cs)]
  simp

/-- Each compiler chunk has the standard full-or-final-remainder width. -/
theorem permutationChunksOf_getD_length
    (map : SelCompressMap) (cs : ConstraintSystem Fp)
    (i : ℕ) (hi : i < (Keygen.permutationChunksOf map cs).length) :
    ((Keygen.permutationChunksOf map cs).getD i []).length =
      min cs.chunkLen
        (cs.permutationColumns.length - i * cs.chunkLen) := by
  unfold Keygen.permutationChunksOf at hi ⊢
  rw [listToChunks_getD_length _ _
    (constraintSystem_chunkLen_pos cs) i hi]
  simp

/-- Every prefix ending before a valid compiler chunk contains `i * chunkLen`
permutation columns. -/
theorem permutationChunksOf_take_flatten_length
    (map : SelCompressMap) (cs : ConstraintSystem Fp)
    (i : ℕ) (hi : i < (Keygen.permutationChunksOf map cs).length) :
    ((Keygen.permutationChunksOf map cs).take i).flatten.length =
      i * cs.chunkLen := by
  unfold Keygen.permutationChunksOf at hi ⊢
  apply take_flatten_length_of_dropLast_full
  · exact listToChunks_dropLast_full _ _
      (constraintSystem_chunkLen_pos cs)
  · exact hi

/-- Top-level keygen exposes the compiler prefix law without requiring downstream
proofs to unfold a concrete circuit or verifying-key constructor. -/
theorem topLevelPermutationChunks_take_flatten_length
    {G : Type} [AddCommGroup G] [Inhabited G]
    {ConfigInput Config : Type} {Output : TypeMap} [CircuitType Output]
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (pp : Keygen.ProofParams) (urs : URS G)
    (i : ℕ) (hi : i < (top.toVerifierKey pp urs).permutationChunks.length) :
    (((top.toVerifierKey pp urs).permutationChunks.take i).flatten.length) =
      i * (top.toVerifierKey pp urs).chunkLen := by
  exact permutationChunksOf_take_flatten_length
    top.selectorMap top.constraintSystem i hi

/-- The compiler's chunk family has enough total slots for every permutation
column, without requiring the family itself to be nonempty. -/
theorem permutationColumns_length_le_chunks_mul
    (map : SelCompressMap) (cs : ConstraintSystem Fp) :
    cs.permutationColumns.length ≤
      (Keygen.permutationChunksOf map cs).length * cs.chunkLen := by
  let source :=
    (cs.permutationColumns.map
      (permutationQueryReference (projectCS map cs))).zipIdx
  have hall :
      (source.toChunks cs.chunkLen).Forall
        fun chunk => chunk.length ≤ cs.chunkLen :=
    listToChunks_all_le cs.chunkLen source
      (constraintSystem_chunkLen_pos cs)
  have hbound :=
    flatten_length_le_mul_of_forall
      (source.toChunks cs.chunkLen) cs.chunkLen hall
  rw [listToChunks_flatten] at hbound
  have hchunks :
      Keygen.permutationChunksOf map cs =
        source.toChunks cs.chunkLen := by
    simp only [Keygen.permutationChunksOf, source]
    apply congrArg (List.toChunks cs.chunkLen)
    congr 2
    funext column
    rcases column with ⟨kind, index⟩
    cases kind <;> rfl
  rw [hchunks]
  simpa only [source, List.length_zipIdx, List.length_map] using hbound

/-- A coherent compiled query reference decodes to the concrete column from
which the compiler created it. -/
theorem permutationColumnAddress_queryReference
    {shape : Shape} {F G : Type}
    (vk : VerifyingKey shape F G) (projected : CsFixture Fp)
    (hadvice :
      vk.adviceQueryLayout = projected.adviceQueryLayout)
    (hfixed :
      vk.fixedQueryLayout = projected.fixedQueryLayout)
    (hinstance :
      vk.instanceQueryLayout = projected.instanceQueryLayout)
    (column : AnyColumn)
    (hcoherent :
      PermutationColumnRef.Coherent vk
        (permutationQueryReference projected column)) :
    permutationColumnAddress vk
        (permutationQueryReference projected column) = column := by
  rcases column with ⟨kind, index⟩
  cases kind with
  | advice =>
      rcases hcoherent with ⟨-, hin, -⟩
      simp only [permutationQueryReference, permutationColumnAddress]
      rw [hadvice] at hin ⊢
      rw [getD_findIdx_eq_target projected.adviceQueryLayout
        (index, 0) (0, 0) hin]
  | fixed =>
      rcases hcoherent with ⟨-, hin, -⟩
      simp only [permutationQueryReference, permutationColumnAddress]
      rw [hfixed] at hin ⊢
      rw [getD_findIdx_eq_target projected.fixedQueryLayout
        (index, 0) (0, 0) hin]
  | «instance» =>
      rcases hcoherent with ⟨-, hin, -⟩
      simp only [permutationQueryReference, permutationColumnAddress]
      rw [hinstance] at hin ⊢
      rw [getD_findIdx_eq_target projected.instanceQueryLayout
        (index, 0) (0, 0) hin]

/--
For every closed top-level circuit, coherent routing makes the permutation
compiler's column encoding a round trip.
-/
theorem topLevelPermutationColumnAddresses_eq
    {G : Type} [AddCommGroup G] [Inhabited G]
    {ConfigInput Config : Type} {Output : TypeMap} [CircuitType Output]
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (pp : Keygen.ProofParams) (urs : URS G)
    (hcoherent :
      PermutationChunkRoutingCoherent (top.toVerifierKey pp urs)) :
    (Keygen.permutationChunksOf
        top.selectorMap top.constraintSystem).flatten.map
          (fun reference =>
            permutationColumnAddress (top.toVerifierKey pp urs) reference.1) =
      (Keygen.permColsOf top.constraintSystem).map
        Halo2.Layout.ColRef.toAny := by
  rw [permutationChunksOf_flatten]
  change
    List.map
        (permutationColumnAddress (top.toVerifierKey pp urs) ∘ Prod.fst)
        _ =
      _
  rw [← List.map_map, List.zipIdx_map_fst]
  simp only [Keygen.permColsOf, List.map_map]
  apply List.map_congr_left
  intro column hcolumn
  simp only [Function.comp_apply]
  let projected :=
    projectCS top.selectorMap top.constraintSystem
  let reference :=
    permutationQueryReference projected column
  have hreference :
      reference ∈
        top.constraintSystem.permutationColumns.map
          (permutationQueryReference projected) :=
    List.mem_map.mpr ⟨column, hcolumn, rfl⟩
  have hindexed :
      ∃ indexed ∈
          (top.constraintSystem.permutationColumns.map
            (permutationQueryReference projected)).zipIdx,
        indexed.1 = reference := by
    have hfst :
        reference ∈
          ((top.constraintSystem.permutationColumns.map
            (permutationQueryReference projected)).zipIdx).map Prod.fst := by
      rw [List.zipIdx_map_fst]
      exact hreference
    simpa only using List.mem_map.mp hfst
  obtain ⟨indexed, hindexed, hindexedReference⟩ := hindexed
  have hindexedFlat :
      indexed ∈
        (Keygen.permutationChunksOf
          top.selectorMap top.constraintSystem).flatten := by
    rw [permutationChunksOf_flatten]
    simpa only [projected] using hindexed
  obtain ⟨chunk, hchunk, hindexedChunk⟩ :=
    List.mem_flatten.mp hindexedFlat
  have hvkChunks :
      (top.toVerifierKey pp urs).permutationChunks =
        Keygen.permutationChunksOf
          top.selectorMap top.constraintSystem := by
    rfl
  have hrouted := hcoherent chunk (by
    rw [hvkChunks]
    exact hchunk) indexed hindexedChunk
  have hreferenceCoherent :
      PermutationColumnRef.Coherent
        (top.toVerifierKey pp urs) reference := by
    rw [← hindexedReference]
    exact hrouted.1
  have hdecoded :
      permutationColumnAddress (top.toVerifierKey pp urs) reference =
        column :=
    permutationColumnAddress_queryReference
      (top.toVerifierKey pp urs) projected
      (by
        simpa only [projected, top.pinnedCS_eq_derive_fp,
          PinnedConstraintSystem.derive] using
          top.toVerifierKey_adviceQueryLayout_derived pp urs)
      (by
        simpa only [projected, top.pinnedCS_eq_derive_fp,
          PinnedConstraintSystem.derive] using
          top.toVerifierKey_fixedQueryLayout_derived pp urs)
      (by
        simpa only [projected, top.pinnedCS_eq_derive_fp,
          PinnedConstraintSystem.derive] using
          top.toVerifierKey_instanceQueryLayout_derived pp urs)
      column hreferenceCoherent
  rcases column with ⟨kind, index⟩
  cases kind <;>
    simpa [reference, projected, permutationQueryReference,
      Halo2.Layout.ColRef.toAny] using hdecoded

end Zcash.Snark
