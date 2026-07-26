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
