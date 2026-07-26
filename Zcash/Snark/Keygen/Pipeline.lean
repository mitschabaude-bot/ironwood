import CompElliptic.Curves.Pasta
import Zcash.Common.ParMap
import Zcash.Snark.Core.Domain
import Zcash.Arithmetic.Fft
import Zcash.Vendor.CompElliptic.Msm
import Zcash.Circuits.Integration.ExprRich
import Clean.Halo2.Keygen.Layout
import Clean.Halo2.TopLevelKeygen
import Zcash.Snark.Core.Group
import Zcash.Snark.Verifier.Assemble

/-!
# `TopLevelCircuit.toVerifierKey` — the circuit-side half of halo2 `keygen_vk`, generic

The single generic pipeline from a closed circuit (+ a monomial URS) to the full
`VerifyingKey`: Clean's `Halo2.Keygen` supplies the pinned constraint system, domain
exponent and selector map; this module adds the group side — the Lagrange-basis URS by
inverse FFT, the dense fixed columns from the derived layout, the keygen permutation
polynomials, `commit_lagrange` for both commitment families — and assembles the record.

`ProofParams` carries the only two `Shape` counts that are proof-shape rather than
circuit data (batch size, multiopen point sets); `ProofParams.mergeDerived` computes the
rest from the circuit, so `TopLevelCircuit.toVerifierKey` carries its derived `Shape` in
the return type with no lawfulness side condition. The Action instantiation and its
capture certification live in `Derivation.lean` / `Certificate.lean`.

## Rust reference

* Lagrange URS: `poly/commitment.rs:75-88` (`Params::new`'s `g_lagrange`),
  `arithmetic.rs:192` (`best_fft` — bit-reversal + iterative Cooley–Tukey butterflies).
* `commit_lagrange` blind: `poly/commitment.rs:212-216` (`Blind::default() = Blind(F::ONE)`).
* Fixed commitments: `plonk/keygen.rs:230-240` (`keygen_vk`'s `fixed_commitments`).
* Permutation commitments: `plonk/permutation/keygen.rs:102-152` (`Assembly::build_vk`).
-/

namespace Zcash.Snark.Keygen

open Zcash.Snark
open Halo2

variable {G : Type} [AddCommGroup G] [Inhabited G]

/-! ## Generalized Lagrange commitment (`poly/commitment.rs:212-216`) -/

/-- Commit to a zero-padded Lagrange-coefficient column against an arbitrary basis with
`Blind::default () = Blind(F::ONE)` (`poly/commitment.rs:212-216`):
`(∑ᵢ coeffsᵢ • basisᵢ) + w` — the same `+ w` blind convention the existing
`commitLagrange` uses, generalized to an arbitrary basis and coefficient list (the
instance-commitment path through `commitLagrange` is deliberately left untouched). -/
def commitLagrangeWith (blind : G) (basis : List G) (coeffs : List Fp) : G :=
  ((List.range coeffs.length).map
    (fun i => (coeffs.getD i 0).val • basis.getD i 0)).sum + blind

/-! ## Derived fixed columns (`plonk/keygen.rs`)

The sparse fixed-cell reconstruction is the layout recipe `TestVkLayoutAction` certifies
against the Rust dump, driven from fully-derived placements: `V1.starts` region starts
and `V1.constants` allocation over the CS-recorded constants columns, `indexedRegions`
bodies, the derived packed selectors, and `usable = 2^k − (blindingFactors + 1)`. Dense
columns have unassigned cells `0` (`domain.empty_lagrange`), assigned values coerced
back from the `ZMod.val` triples. -/

/-- The derived V1 constants allocation `(value, col, row)` (`v1.rs:79-136`), over the
CS-recorded constants columns (`enable_constant` order). -/
def constantsOf (cs : ConstraintSystem Fp) (ops : Operations Fp) : List (ℕ × ℕ × ℕ) :=
  FloorPlanner.V1.constants (ZMod.val : Fp → ℕ) ops (cs.constants.map (·.index))

/-- The sparse fixed cells `(col, row, ZMod.val value)` at domain size `2^k`: loaded
tables + the constants columns + packed selector columns + region `assign_fixed`s,
deduped and sorted. -/
def fixedSparseOf (selMap : Halo2.SelCompressMap) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp) : List (ℕ × ℕ × ℕ) :=
  Layout.sortFixed (Layout.dedupFixed
    (Layout.tableFixed (ZMod.val : Fp → ℕ) (2 ^ k - (cs.blindingFactors + 1)) ops
      ++ Layout.constantsFixed (constantsOf cs ops)
      ++ Layout.selectorFixed selMap
          (activations (FloorPlanner.V1.starts ops) (indexedRegions ops 0).1)
      ++ Layout.regionAssignFixed (ZMod.val : Fp → ℕ) (FloorPlanner.V1.starts ops)
          (indexedRegions ops 0).1))

/-- Apply one sparse fixed assignment to the dense column accumulator. -/
def scatterDenseColumn (numCols : ℕ) (cols : Array (Array Fp))
    (entry : ℕ × ℕ × ℕ) : Array (Array Fp) :=
  let (column, row, value) := entry
  if column < numCols then
    cols.modify column fun values =>
      values.set! row ((value : ℕ) : Fp)
  else
    cols

/-- Scatter sparse `(col, row, natval)` triples into `numCols` dense length-`n` columns,
default `0` (`domain.empty_lagrange`); the `natval`s are `ZMod.val`s coerced back to `Fp`. -/
def denseColumns (n numCols : ℕ)
    (triples : List (ℕ × ℕ × ℕ)) : List (List Fp) :=
  let initial : Array (Array Fp) :=
    Array.replicate numCols (Array.replicate n 0)
  (triples.foldl (scatterDenseColumn numCols) initial).toList.map
    Array.toList

/-- One scatter step preserves both the number of columns and every column's
row count. -/
private theorem scatterDenseColumn_sized
    {n numCols : ℕ} {cols : Array (Array Fp)}
    (hsize : cols.size = numCols)
    (hrows : ∀ column (hcolumn : column < cols.size),
      cols[column].size = n)
    (entry : ℕ × ℕ × ℕ) :
    let next := scatterDenseColumn numCols cols entry
    next.size = numCols ∧
      ∀ column (hcolumn : column < next.size),
        next[column].size = n := by
  rcases entry with ⟨column, rest⟩
  rcases rest with ⟨row, value⟩
  simp only [scatterDenseColumn]
  split
  next hcolumn =>
    constructor
    · simpa only [Array.size_modify] using hsize
    · intro other hother
      rw [Array.getElem_modify hother]
      split
      next heq =>
        subst other
        simp only [Array.size_set!]
        exact hrows column (by simpa only [hsize] using hcolumn)
      next hne =>
        exact hrows other (by simpa using hother)
  next _ =>
    exact ⟨hsize, hrows⟩

/-- Folding scatter over a rectangular accumulator preserves its shape. -/
private theorem scatterDenseColumns_fold_sized
    {n numCols : ℕ} (triples : List (ℕ × ℕ × ℕ))
    {cols : Array (Array Fp)}
    (hsize : cols.size = numCols)
    (hrows : ∀ column (hcolumn : column < cols.size),
      cols[column].size = n) :
    let result := triples.foldl (scatterDenseColumn numCols) cols
    result.size = numCols ∧
      ∀ column (hcolumn : column < result.size),
        result[column].size = n := by
  induction triples generalizing cols with
  | nil =>
      exact ⟨hsize, hrows⟩
  | cons entry rest ih =>
      simp only [List.foldl_cons]
      have hnext :=
        scatterDenseColumn_sized hsize hrows entry
      exact ih hnext.1 hnext.2

/-- The dense scatter accumulator initialized by `denseColumns` is rectangular. -/
private theorem denseColumns_fold_sized
    (n numCols : ℕ) (triples : List (ℕ × ℕ × ℕ)) :
    let initial : Array (Array Fp) :=
      Array.replicate numCols (Array.replicate n 0)
    let result := triples.foldl (scatterDenseColumn numCols) initial
    result.size = numCols ∧
      ∀ column (hcolumn : column < result.size),
        result[column].size = n := by
  apply scatterDenseColumns_fold_sized triples
  · simp
  · intro column hcolumn
    simp

/-- Dense fixed reconstruction emits exactly the requested number of columns. -/
theorem denseColumns_length
    (n numCols : ℕ) (triples : List (ℕ × ℕ × ℕ)) :
    (denseColumns n numCols triples).length = numCols := by
  let initial : Array (Array Fp) :=
    Array.replicate numCols (Array.replicate n 0)
  let result := triples.foldl (scatterDenseColumn numCols) initial
  have hshape := denseColumns_fold_sized n numCols triples
  simpa [denseColumns, initial, result] using hshape.1

/-- Every in-range dense fixed column has exactly the requested row count. -/
theorem denseColumns_getD_length
    (n numCols : ℕ) (triples : List (ℕ × ℕ × ℕ))
    (column : ℕ) (hcolumn : column < numCols) :
    ((denseColumns n numCols triples).getD column []).length = n := by
  let initial : Array (Array Fp) :=
    Array.replicate numCols (Array.replicate n 0)
  let result := triples.foldl (scatterDenseColumn numCols) initial
  have hshape := denseColumns_fold_sized n numCols triples
  have hresultColumn : column < result.size := by
    rw [hshape.1]
    exact hcolumn
  rw [List.getD_eq_getElem _ _ (by
    simpa only [denseColumns_length] using hcolumn)]
  simp only [denseColumns, List.getElem_map,
    Array.getElem_toList, Array.length_toList]
  exact hshape.2 column hresultColumn

/-- Rectangular dense accumulators used by sparse-scatter read proofs. -/
private def DenseShaped (n numCols : ℕ)
    (cols : Array (Array Fp)) : Prop :=
  cols.size = numCols ∧
    ∀ column (hcolumn : column < cols.size),
      cols[column].size = n

private theorem DenseShaped.initial (n numCols : ℕ) :
    DenseShaped n numCols
      (Array.replicate numCols (Array.replicate n (0 : Fp))) := by
  constructor
  · simp
  · intro column hcolumn
    simp

private theorem DenseShaped.scatter
    {n numCols : ℕ} {cols : Array (Array Fp)}
    (hshape : DenseShaped n numCols cols)
    (entry : ℕ × ℕ × ℕ) :
    DenseShaped n numCols
      (scatterDenseColumn numCols cols entry) :=
  scatterDenseColumn_sized hshape.1 hshape.2 entry

private theorem DenseShaped.fold
    {n numCols : ℕ} (triples : List (ℕ × ℕ × ℕ))
    {cols : Array (Array Fp)}
    (hshape : DenseShaped n numCols cols) :
    DenseShaped n numCols
      (triples.foldl (scatterDenseColumn numCols) cols) :=
  scatterDenseColumns_fold_sized triples hshape.1 hshape.2

private def denseRead
    (cols : Array (Array Fp)) (column row : ℕ) : Fp :=
  (cols.getD column #[]).getD row 0

/-- Scattering an assignment to another cell preserves the selected dense read. -/
private theorem denseRead_scatter_of_ne
    {n numCols : ℕ} {cols : Array (Array Fp)}
    (hshape : DenseShaped n numCols cols)
    (column row : ℕ)
    (hcolumn : column < numCols) (hrow : row < n)
    (entry : ℕ × ℕ × ℕ)
    (hne : entry.1 ≠ column ∨ entry.2.1 ≠ row) :
    denseRead (scatterDenseColumn numCols cols entry) column row =
      denseRead cols column row := by
  rcases entry with ⟨sourceColumn, sourceRow, value⟩
  rcases hshape with ⟨hsize, hrows⟩
  have hcolumn' : column < cols.size := by
    simpa only [hsize] using hcolumn
  simp only at hne
  simp only [denseRead, scatterDenseColumn]
  split
  next hsourceColumn =>
    by_cases hcolumns : sourceColumn = column
    · subst sourceColumn
      have hrowsNe : sourceRow ≠ row :=
        hne.elim (fun h => (h rfl).elim) id
      have hrow' : row < cols[column].size := by
        rw [hrows column hcolumn']
        exact hrow
      have hrowSet :
          row < (cols[column].setIfInBounds sourceRow
            ((value : ℕ) : Fp)).size := by
        simpa only [Array.size_setIfInBounds] using hrow'
      have hset :
          (cols[column].setIfInBounds sourceRow
            ((value : ℕ) : Fp))[row]'hrowSet =
            cols[column][row] :=
        Array.getElem_setIfInBounds_ne hrow' hrowsNe
      simpa [Array.getD, Array.size_modify, hcolumn',
        Array.getElem_modify_self, Array.set!,
        Array.size_setIfInBounds, hrow'] using hset
    · have hmodifiedColumn :=
        Array.getElem_modify_of_ne hcolumns
          (fun (values : Array Fp) =>
            values.set! sourceRow ((value : ℕ) : Fp))
          (by simpa only [Array.size_modify] using hcolumn')
      have hmodifiedRead :=
        congrArg (fun (values : Array Fp) =>
          values.getD row 0) hmodifiedColumn
      simpa [Array.getD, Array.size_modify, hcolumn'] using
        hmodifiedRead
  next _ =>
    rfl

/-- A scatter fold containing no write to a selected cell preserves its value. -/
private theorem denseRead_fold_of_no_target
    {n numCols : ℕ} (triples : List (ℕ × ℕ × ℕ))
    {cols : Array (Array Fp)}
    (hshape : DenseShaped n numCols cols)
    (column row : ℕ)
    (hcolumn : column < numCols) (hrow : row < n)
    (hnoTarget :
      ∀ entry ∈ triples,
        entry.1 ≠ column ∨ entry.2.1 ≠ row) :
    denseRead (triples.foldl (scatterDenseColumn numCols) cols)
        column row =
      denseRead cols column row := by
  induction triples generalizing cols with
  | nil =>
      rfl
  | cons entry rest ih =>
      simp only [List.foldl_cons]
      rw [ih (hshape.scatter entry)]
      · exact denseRead_scatter_of_ne hshape column row
          hcolumn hrow entry (hnoTarget entry (by simp))
      · intro restEntry hrestEntry
        exact hnoTarget restEntry (by simp [hrestEntry])

/-- Scattering directly to an in-range selected cell writes its value. -/
private theorem denseRead_scatter_self
    {n numCols : ℕ} {cols : Array (Array Fp)}
    (hshape : DenseShaped n numCols cols)
    (column row value : ℕ)
    (hcolumn : column < numCols) (hrow : row < n) :
    denseRead
        (scatterDenseColumn numCols cols (column, row, value))
        column row =
      ((value : ℕ) : Fp) := by
  rcases hshape with ⟨hsize, hrows⟩
  have hcolumn' : column < cols.size := by
    simpa only [hsize] using hcolumn
  simp [denseRead, scatterDenseColumn, hcolumn,
    Array.getD, Array.size_modify, hcolumn',
    Array.getElem_modify_self, Array.set!,
    Array.getElem_setIfInBounds_self,
    hrows _ hcolumn', hrow]

/--
Last-write form of the fold invariant: an explicit target write determines the
cell whenever the remaining suffix does not target that cell.
-/
private theorem denseRead_fold_of_last_write
    {n numCols : ℕ} (before after : List (ℕ × ℕ × ℕ))
    {cols : Array (Array Fp)}
    (hshape : DenseShaped n numCols cols)
    (column row value : ℕ)
    (hcolumn : column < numCols) (hrow : row < n)
    (hnoTarget :
      ∀ entry ∈ after,
        entry.1 ≠ column ∨ entry.2.1 ≠ row) :
    denseRead
        ((before ++ (column, row, value) :: after).foldl
          (scatterDenseColumn numCols) cols)
        column row =
      ((value : ℕ) : Fp) := by
  let afterPrefix :=
    before.foldl (scatterDenseColumn numCols) cols
  let afterWrite :=
    scatterDenseColumn numCols afterPrefix (column, row, value)
  have hprefix : DenseShaped n numCols afterPrefix :=
    DenseShaped.fold before hshape
  have hwrite : DenseShaped n numCols afterWrite :=
    hprefix.scatter (column, row, value)
  rw [List.foldl_append, List.foldl_cons]
  change denseRead
      (after.foldl (scatterDenseColumn numCols) afterWrite)
      column row = _
  rw [denseRead_fold_of_no_target after hwrite
    column row hcolumn hrow hnoTarget]
  exact denseRead_scatter_self hprefix column row value hcolumn hrow

/--
An in-range cell not targeted by any sparse assignment retains the dense
initializer's zero.
-/
theorem denseColumns_getD_getD_eq_zero_of_no_target
    (n numCols : ℕ) (triples : List (ℕ × ℕ × ℕ))
    (column row : ℕ)
    (hcolumn : column < numCols) (hrow : row < n)
    (hnoTarget :
      ∀ entry ∈ triples,
        entry.1 ≠ column ∨ entry.2.1 ≠ row) :
    ((denseColumns n numCols triples).getD column []).getD row 0 =
      (0 : Fp) := by
  let initial : Array (Array Fp) :=
    Array.replicate numCols (Array.replicate n 0)
  let result :=
    triples.foldl (scatterDenseColumn numCols) initial
  have hinitial : DenseShaped n numCols initial :=
    DenseShaped.initial n numCols
  have hresult : DenseShaped n numCols result :=
    DenseShaped.fold triples hinitial
  have hcolumnResult : column < result.size := by
    rw [hresult.1]
    exact hcolumn
  have hrowResult : row < result[column].size := by
    rw [hresult.2 column hcolumnResult]
    exact hrow
  have hcolumnDense :
      column < (denseColumns n numCols triples).length := by
    simpa only [denseColumns_length] using hcolumn
  have hcolumnRead :
      (denseColumns n numCols triples).getD column [] =
        (denseColumns n numCols triples)[column] :=
    List.getD_eq_getElem _ _ hcolumnDense
  rw [hcolumnRead]
  have hrowDense :
      row < (denseColumns n numCols triples)[column].length := by
    have hlength :=
      denseColumns_getD_length n numCols triples column hcolumn
    rw [hcolumnRead] at hlength
    rw [hlength]
    exact hrow
  rw [List.getD_eq_getElem _ _ hrowDense]
  simp only [denseColumns, List.getElem_map,
    Array.getElem_toList]
  have hread :=
    denseRead_fold_of_no_target triples hinitial
      column row hcolumn hrow hnoTarget
  simp [denseRead, result, initial, Array.getD,
    hcolumnResult, hrowResult] at hread
  simpa [hcolumn, hrow] using hread

/--
An explicit sparse write determines its in-range dense cell when no later entry
targets that cell.
-/
theorem denseColumns_getD_getD_eq_of_last_write
    (n numCols : ℕ)
    (before after : List (ℕ × ℕ × ℕ))
    (column row value : ℕ)
    (hcolumn : column < numCols) (hrow : row < n)
    (hnoTarget :
      ∀ entry ∈ after,
        entry.1 ≠ column ∨ entry.2.1 ≠ row) :
    ((denseColumns n numCols
        (before ++ (column, row, value) :: after)).getD
      column []).getD row 0 =
      ((value : ℕ) : Fp) := by
  let initial : Array (Array Fp) :=
    Array.replicate numCols (Array.replicate n 0)
  let triples := before ++ (column, row, value) :: after
  let result :=
    triples.foldl (scatterDenseColumn numCols) initial
  have hinitial : DenseShaped n numCols initial :=
    DenseShaped.initial n numCols
  have hresult : DenseShaped n numCols result :=
    DenseShaped.fold triples hinitial
  have hcolumnResult : column < result.size := by
    rw [hresult.1]
    exact hcolumn
  have hrowResult : row < result[column].size := by
    rw [hresult.2 column hcolumnResult]
    exact hrow
  have hcolumnDense :
      column <
        (denseColumns n numCols triples).length := by
    simpa only [denseColumns_length] using hcolumn
  have hcolumnRead :
      (denseColumns n numCols triples).getD column [] =
        (denseColumns n numCols triples)[column] :=
    List.getD_eq_getElem _ _ hcolumnDense
  rw [hcolumnRead]
  have hrowDense :
      row < (denseColumns n numCols triples)[column].length := by
    have hlength :=
      denseColumns_getD_length n numCols triples column hcolumn
    rw [hcolumnRead] at hlength
    rw [hlength]
    exact hrow
  rw [List.getD_eq_getElem _ _ hrowDense]
  simp only [denseColumns, List.getElem_map,
    Array.getElem_toList]
  have hread : denseRead result column row = ((value : ℕ) : Fp) := by
    exact denseRead_fold_of_last_write before after hinitial
      column row value hcolumn hrow hnoTarget
  unfold denseRead at hread
  rw [← Array.getElem_eq_getD (h := hcolumnResult) #[]] at hread
  rw [← Array.getElem_eq_getD (h := hrowResult) 0] at hread
  exact hread

/-- The derived fixed-column commitments at an explicit per-column committer —
`fixedCommitmentsOf` is the default instantiation; concrete evaluation sites may pass a
proven-equal faster committer. -/
def fixedCommitmentsWith (commit : List Fp → G) (selMap : Halo2.SelCompressMap)
    (k : ℕ) (cs : ConstraintSystem Fp) (ops : Operations Fp) : List G :=
  -- `parMap`: one task per column (`parMap_eq_map` — evaluation strategy only)
  (denseColumns (2 ^ k) (PinnedConstraintSystem.derive cs selMap).numFixedColumns
      (fixedSparseOf selMap k cs ops)).parMap commit

/-- Sequential variant of `fixedCommitmentsWith` — same columns, plain `map`. Used by
evaluation sites that must stay single-threaded so nullary-definition sharing of the
committer's basis holds (task fan-outs re-evaluate captured thunks per task in the
`native_decide` tier). -/
def fixedCommitmentsSeqWith (commit : List Fp → G) (selMap : Halo2.SelCompressMap)
    (k : ℕ) (cs : ConstraintSystem Fp) (ops : Operations Fp) : List G :=
  (denseColumns (2 ^ k) (PinnedConstraintSystem.derive cs selMap).numFixedColumns
      (fixedSparseOf selMap k cs ops)).map commit

omit [AddCommGroup G] [Inhabited G] in
theorem fixedCommitmentsSeqWith_eq (commit : List Fp → G) (selMap : Halo2.SelCompressMap)
    (k : ℕ) (cs : ConstraintSystem Fp) (ops : Operations Fp) :
    fixedCommitmentsSeqWith commit selMap k cs ops
      = fixedCommitmentsWith commit selMap k cs ops := by
  simp only [fixedCommitmentsSeqWith, fixedCommitmentsWith, List.parMap_eq_map]

/-- Every dense fixed column has exactly the requested row count. -/
theorem denseColumns_mem_length (n numCols : ℕ) (triples : List (ℕ × ℕ × ℕ)) :
    ∀ c ∈ denseColumns n numCols triples, c.length = n := by
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc
  have hi' : i < numCols := by rwa [denseColumns_length] at hi
  have h := denseColumns_getD_length n numCols triples i hi'
  rwa [List.getD_eq_getElem _ _ hi] at h

omit [AddCommGroup G] [Inhabited G] in
/-- Two committers that agree on FULL-DOMAIN columns give the same fixed commitments: every
dense fixed column has length `2 ^ k`.  This is the hook a concrete evaluation site uses to
swap in a faster committer whose correctness proof needs the column length. -/
theorem fixedCommitmentsSeqWith_congr {f g : List Fp → G} (selMap : Halo2.SelCompressMap)
    (k : ℕ) (cs : ConstraintSystem Fp) (ops : Operations Fp)
    (h : ∀ l : List Fp, l.length = 2 ^ k → f l = g l) :
    fixedCommitmentsSeqWith f selMap k cs ops = fixedCommitmentsSeqWith g selMap k cs ops := by
  simp only [fixedCommitmentsSeqWith]
  exact List.map_congr_left fun c hc => h c (denseColumns_mem_length _ _ _ c hc)

/-- The derived fixed-column commitments — `commit_lagrange` of each dense fixed column
with the default blind (`plonk/keygen.rs:230-240`, `keygen_vk`'s `fixed_commitments`;
Pippenger per MSM, `commitLagrangeFastWith_eq` — evaluation strategy only). The
Lagrange basis is an argument so one FFT serves both commitment families. -/
def fixedCommitmentsOf (blind : G) (lagrange : List G) (selMap : Halo2.SelCompressMap)
    (k : ℕ) (cs : ConstraintSystem Fp) (ops : Operations Fp) : List G :=
  fixedCommitmentsWith
    (Fast.Msm.commitLagrangeFastWith Fast.Msm.defaultWindow blind lagrange)
    selMap k cs ops

/-! ## Derived permutation commitments (`plonk/permutation/keygen.rs:102-152`) -/

/-- The permutation columns as `ColRef`s in `enable_equality` order
(`cs.permutationColumns`) — the order the keygen `Assembly` mapping and the `δ^i` scaling
are indexed by, and the column shape `V1.copyList` resolves cells against. -/
def permColsOf (cs : ConstraintSystem Fp) : List Halo2.Layout.ColRef :=
  cs.permutationColumns.map fun c =>
    match c.kind with
    | .advice => .advice c.index
    | .fixed => .fixed c.index
    | .instance => .instance c.index

/-- `[ω^0, ω^1, …, ω^(n−1)]` (`build_vk`'s `omega_powers`, `permutation/keygen.rs:108-116`;
map form rather than iterated multiplication so entries are `getElem`-transparent for the
σ-row identification — `ZMod` powers are binary-fast, so the cost difference is noise). -/
def omegaPowersArr (omega : Fp) (n : ℕ) : Array Fp :=
  (Array.range n).map (omega ^ ·)

/-- `[δ^0, δ^1, …, δ^(m−1)]` (`build_vk`'s `cur *= DELTA`, `permutation/keygen.rs:118-133`;
map form, see `omegaPowersArr`). -/
def deltaPowersArr (delta : Fp) (m : ℕ) : Array Fp :=
  (Array.range m).map (delta ^ ·)

@[simp] theorem omegaPowersArr_getElem! (omega : Fp) {n j : ℕ} (hj : j < n) :
    (omegaPowersArr omega n)[j]! = omega ^ j := by
  simp [omegaPowersArr, hj]

@[simp] theorem deltaPowersArr_getElem! (delta : Fp) {m j : ℕ} (hj : j < m) :
    (deltaPowersArr delta m)[j]! = delta ^ j := by
  simp [deltaPowersArr, hj]

/-- The permutation columns chunked for the verifier (`permutation/verifier.rs:43-47`:
`columns.chunks(chunk_len)` with global position indices), in the `ColumnRef`
QUERY-INDEX space the verifier resolves evals with (`ColumnRef.resolve`): each column's
cur-rotation query index in the post-compression layouts. -/
def permutationChunksOf (map : Halo2.SelCompressMap) (cs : ConstraintSystem Fp) :
    List (List (Snark.ColumnRef × ℕ)) :=
  let proj := projectCS map cs
  let ref : AnyColumn → Snark.ColumnRef := fun c =>
    match c.kind with
    | .advice => .advice (proj.adviceQueryLayout.findIdx (· = (c.index, 0)))
    | .fixed => .fixed (proj.fixedQueryLayout.findIdx (· = (c.index, 0)))
    | .instance => .instance (proj.instanceQueryLayout.findIdx (· = (c.index, 0)))
  ((cs.permutationColumns.map ref).zipIdx).toChunks cs.chunkLen

/-- The per-column permutation polynomials in Lagrange form:
`p_i[j] = deltaomega[i'][j'] = δ^{i'} · ω^{j'}` where `(i', j') = mapping[i][j]`
(`build_vk`, `permutation/keygen.rs:135-146`), over the keygen `Assembly` mapping
(`Assembly::copy` replay, `Layout.runAssembly`) of the derived V1 copy list. -/
def permPolysOf (k : ℕ) (cs : ConstraintSystem Fp) (ops : Operations Fp) :
    List (List Fp) :=
  let n := 2 ^ k
  let permCols := permColsOf cs
  let copyList := Layout.V1.copyList permCols (FloorPlanner.V1.starts ops) ops
    (constantsOf cs ops)
  let mapping := Layout.runAssembly n permCols.length copyList
  let omegaPows := omegaPowersArr (omegaOf k) n
  let deltaPows := deltaPowersArr deltaFp permCols.length
  (List.range permCols.length).map fun i =>
    (List.range n).map fun j =>
      let pij := (mapping[i]!)[j]!
      deltaPows[pij.1]! * omegaPows[pij.2]!

/-- The derived permutation common commitments at an explicit per-column committer
(see `fixedCommitmentsWith`). -/
def permutationCommitmentsWith (commit : List Fp → G) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp) : List G :=
  -- `parMap`: one task per column (`parMap_eq_map` — evaluation strategy only)
  (permPolysOf k cs ops).parMap commit

/-- Sequential variant of `permutationCommitmentsWith` (see `fixedCommitmentsSeqWith`). -/
def permutationCommitmentsSeqWith (commit : List Fp → G) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp) : List G :=
  (permPolysOf k cs ops).map commit

omit [AddCommGroup G] [Inhabited G] in
theorem permutationCommitmentsSeqWith_eq (commit : List Fp → G) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp) :
    permutationCommitmentsSeqWith commit k cs ops
      = permutationCommitmentsWith commit k cs ops := by
  simp only [permutationCommitmentsSeqWith, permutationCommitmentsWith,
    List.parMap_eq_map]

/-- Every permutation polynomial is a full-domain row vector. -/
theorem permPolysOf_mem_length (k : ℕ) (cs : ConstraintSystem Fp) (ops : Operations Fp) :
    ∀ l ∈ permPolysOf k cs ops, l.length = 2 ^ k := by
  intro l hl
  simp only [permPolysOf, List.mem_map] at hl
  obtain ⟨i, -, rfl⟩ := hl
  simp

omit [AddCommGroup G] [Inhabited G] in
/-- The permutation twin of `fixedCommitmentsSeqWith_congr`. -/
theorem permutationCommitmentsSeqWith_congr {f g : List Fp → G} (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp)
    (h : ∀ l : List Fp, l.length = 2 ^ k → f l = g l) :
    permutationCommitmentsSeqWith f k cs ops = permutationCommitmentsSeqWith g k cs ops := by
  simp only [permutationCommitmentsSeqWith]
  exact List.map_congr_left fun c hc => h c (permPolysOf_mem_length k cs ops c hc)

/-- The derived permutation common commitments — `commit_lagrange` of each permutation
polynomial with the default blind (`build_vk`, `permutation/keygen.rs:147-151`;
Pippenger per MSM, `commitLagrangeFastWith_eq` — evaluation strategy only). -/
def permutationCommitmentsOf (blind : G) (lagrange : List G) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp) : List G :=
  permutationCommitmentsWith
    (Fast.Msm.commitLagrangeFastWith Fast.Msm.defaultWindow blind lagrange)
    k cs ops

/-! ## Assembly -/

end Zcash.Snark.Keygen

namespace Zcash.Snark.VerifyingKey

open Zcash.Snark.Keygen
open Halo2

variable {G : Type} [AddCommGroup G] [Inhabited G]

/-- The verifying key of a circuit given its keygen-view operation stream and a monomial
URS (which must be sized for the circuit, `urs.k = minimalK cs ops` — orchard's
`Params::new(K)`): every field derived — domain scalars from the minimal fitting
exponent, gates/query layouts/lookups from the pinned CS (carried across the
`RichExpression → Expr` boundary), and the two commitment families from the derived
layout over the URS's Lagrange basis. -/
def ofOperations (shape : Shape) (urs : URS G)
    (cs : ConstraintSystem Fp) (ops : Operations Fp) : VerifyingKey shape Fp G :=
  letI : Field Fp := (inferInstance : FiniteField Fp).toField
  letI : DecidableEq Fp := FiniteField.instDecidableEq
  let k := minimalK cs ops
  let selMap := deriveSelCompressMap cs (2 ^ k)
    (activations (FloorPlanner.V1.starts ops) (indexedRegions ops 0).1)
  let pinned := PinnedConstraintSystem.derive cs selMap
  let lagrange := derivedUrsGLagrange urs
  { omega := omegaOf k
    n := 2 ^ k
    blindingFactors := cs.blindingFactors
    delta := deltaFp
    chunkLen := cs.chunkLen
    gates := pinned.gates.map RichExpression.toExpr
    instanceQueryLayout := pinned.instanceQueryLayout
    adviceQueryLayout := pinned.adviceQueryLayout
    fixedQueryLayout := pinned.fixedQueryLayout
    fixedCommitment := fun i =>
      (fixedCommitmentsOf urs.w lagrange selMap k cs ops).getD i 0
    permutationCommonCommitment := fun i =>
      (permutationCommitmentsOf urs.w lagrange k cs ops).getD i.val 0
    permutationChunks := permutationChunksOf selMap cs
    lookupInputExprs := fun l =>
      (pinned.lookupInputExprs.getD l.val []).map RichExpression.toExpr
    lookupTableExprs := fun l =>
      (pinned.lookupTableExprs.getD l.val []).map RichExpression.toExpr }

/-- Projection API for the fixed commitments produced by `ofOperations`.

Downstream proofs should rewrite with this lemma instead of asking definitional
equality to unfold the complete verifying-key constructor. -/
@[simp] theorem ofOperations_fixedCommitment
    (shape : Shape) (urs : URS G)
    (cs : ConstraintSystem Fp) (ops : Operations Fp)
    (column : ℕ) :
    (ofOperations shape urs cs ops).fixedCommitment column =
      (fixedCommitmentsOf urs.w (derivedUrsGLagrange urs)
        (deriveSelCompressMap cs (2 ^ minimalK cs ops)
          (activations (FloorPlanner.V1.starts ops)
            (indexedRegions ops 0).1))
        (minimalK cs ops) cs ops).getD column 0 := by
  simp only [ofOperations]

/-- Projection API for common permutation commitments produced by
`ofOperations`. -/
@[simp] theorem ofOperations_permutationCommonCommitment
    (shape : Shape) (urs : URS G)
    (cs : ConstraintSystem Fp) (ops : Operations Fp)
    (column : Fin shape.numPermutationColumns) :
    (ofOperations shape urs cs ops).permutationCommonCommitment column =
      (permutationCommitmentsOf urs.w (derivedUrsGLagrange urs)
        (minimalK cs ops) cs ops).getD column.val 0 := by
  simp only [ofOperations]

/-- **A verifying key whose gate list is a derivation's evaluates like the source
circuit.** The verifier holds `Zcash.Snark.Expr` gates while the derivation produces
`Halo2.RichExpression` gates, so the hypothesis follows keygen's construction direction:
`vk.gates = (.derive cs map).gates.map RichExpression.toExpr`. Given that and selector
coverage, the `j`-th VK gate — at query families interpreting the derivation walk's
layout — evaluates to the `j`-th flattened Clean gate expression under the
selector-replacement valuation. -/
theorem gates_eval_of_gates_eq
    {shape : Shape} {G' : Type*} (vk : VerifyingKey shape Fp G')
    (cs : ConstraintSystem Fp) (map : Halo2.SelCompressMap)
    (hgates : vk.gates =
      (PinnedConstraintSystem.derive cs map).gates.map
        RichExpression.toExpr)
    (fE aE iE : ℕ → Fp) (v : Query → Fp)
    (hcov : ∀ p ∈ flatGates cs,
      p.selectorsCovered (fun i => (map.lookup i).isSome) = true)
    (hint : Interprets
      (eraseGates ((flatGates cs).map (substSelectorMap map.lookup))
        (queryWalkInit map cs)).2 fE aE iE v)
    (j : ℕ) (hg : j < vk.gates.length) (hp : j < (flatGates cs).length) :
    Expr.eval fE aE iE vk.gates[j]
      = Expression.eval (substValuation map.lookup v) (flatGates cs)[j] := by
  have hg' : j < (PinnedConstraintSystem.derive cs map).gates.length := by
    rw [hgates, List.length_map] at hg
    exact hg
  have key := PinnedConstraintSystem.derive_gates_eval cs map fE aE iE v hcov hint j hg' hp
  rw [List.getElem_of_eq hgates hg, List.getElem_map,
    RichExpression.eval_toExpr]
  exact key

end Zcash.Snark.VerifyingKey

namespace Zcash.Snark.Keygen

open Zcash.Snark
open Halo2

variable {G : Type} [AddCommGroup G] [Inhabited G]

/-- Transporting `ofOperations` along a shape equality is `ofOperations` at the other
shape — the record mentions the shape only in its `Fin`-domain types, never in a field
value. -/
theorem ofOperations_cast {s₁ s₂ : Shape} (hs : s₁ = s₂) (urs : URS G)
    (cs : ConstraintSystem Fp) (ops : Operations Fp) :
    hs ▸ VerifyingKey.ofOperations s₁ urs cs ops
      = VerifyingKey.ofOperations s₂ urs cs ops := by
  cases hs; rfl

/-! ## The method form -/

/-- The two `Shape` counts that are genuinely proof-shape rather than circuit data: the
batch size and the multiopen point-set count. Everything else merges in derived
(`ProofParams.mergeDerived`). -/
structure ProofParams where
  numProofs : ℕ
  numPointSets : ℕ
deriving DecidableEq, Repr

/-- The `Shape` of a top-level circuit's proofs: the proof-shape counts merged with
everything the circuit derives — the domain exponent (`TopLevelCircuit.domainExponent`),
column/lookup/permutation counts from the configure-recorded constraint system, the
query counts from the derived pinned CS layouts (`TopLevelCircuit.pinnedCS`), the
verifier's permutation chunking `⌈columns / chunkLen⌉` (`permutation/verifier.rs:43-47`),
and the quotient split `cs.degree() − 1` (`vk.domain.get_quotient_poly_degree()`). -/
def ProofParams.mergeDerived (pp : ProofParams)
    {ConfigInput Config : Type} {Output : TypeMap} [CircuitType Output]
    (top : TopLevelCircuit Fp ConfigInput Config Output) : Shape :=
  let cs := top.constraintSystem
  let pinned := top.pinnedCS
  { k := top.domainExponent
    numProofs := pp.numProofs
    numAdviceColumns := cs.numAdviceColumns
    numLookups := cs.lookups.length
    numPermutationSets :=
      (cs.permutationColumns.length + cs.chunkLen - 1) / cs.chunkLen
    numPermutationColumns := cs.permutationColumns.length
    numQuotientPieces := csDegree cs - 1
    numInstanceQueries := pinned.instanceQueryLayout.length
    numAdviceQueries := pinned.adviceQueryLayout.length
    numFixedQueries := pinned.fixedQueryLayout.length
    numPointSets := pp.numPointSets }

end Zcash.Snark.Keygen

namespace Halo2.TopLevelCircuit

open Zcash.Snark
open Zcash.Snark.Keygen
open Halo2

variable {G : Type} [AddCommGroup G] [Inhabited G]
variable {ConfigInput Config : Type} {Output : TypeMap} [CircuitType Output]

/-- The dense fixed rows keygen commits for a closed circuit. -/
def fixedRows
    (top : TopLevelCircuit Fp ConfigInput Config Output) : List (List Fp) :=
  denseColumns (2 ^ top.domainExponent)
    (PinnedConstraintSystem.derive
      top.constraintSystem top.selectorMap).numFixedColumns
    (fixedSparseOf top.selectorMap top.domainExponent
      top.constraintSystem (top.operations 0))

/-- Keygen produces one dense row vector for every derived fixed column. -/
theorem fixedRows_length
    (top : TopLevelCircuit Fp ConfigInput Config Output) :
    top.fixedRows.length = top.pinnedCS.numFixedColumns := by
  change
    (denseColumns (2 ^ top.domainExponent)
      (PinnedConstraintSystem.derive
        top.constraintSystem top.selectorMap).numFixedColumns
      _).length = top.pinnedCS.numFixedColumns
  rw [denseColumns_length]
  rfl

/-- Every derived fixed row vector spans the complete keygen domain. -/
theorem fixedRows_getD_length
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (column : ℕ) (hcolumn : column < top.pinnedCS.numFixedColumns) :
    (top.fixedRows.getD column []).length = 2 ^ top.domainExponent := by
  apply denseColumns_getD_length
  simpa only [top.pinnedCS_eq_derive] using hcolumn

/-- The derived fixed-column commitments of a closed circuit against a URS. -/
def fixedCommitments
    (top : TopLevelCircuit Fp ConfigInput Config Output) (urs : URS G) : List G :=
  top.fixedRows.parMap
    (Fast.Msm.commitLagrangeFastWith Fast.Msm.defaultWindow urs.w
      (derivedUrsGLagrange urs))

/-- The named top-level fixed-row view is exactly the fixed-commitment computation
used by generic keygen. -/
@[simp] theorem fixedCommitments_eq_fixedCommitmentsOf
    (top : TopLevelCircuit Fp ConfigInput Config Output) (urs : URS G) :
    top.fixedCommitments urs =
      fixedCommitmentsOf urs.w (derivedUrsGLagrange urs)
        top.selectorMap top.domainExponent
        top.constraintSystem (top.operations 0) := by
  simp only [fixedCommitments, fixedRows, fixedCommitmentsOf, fixedCommitmentsWith]

/-- The derived permutation common commitments of a closed circuit against a URS. -/
def permutationCommitments
    (top : TopLevelCircuit Fp ConfigInput Config Output) (urs : URS G) : List G :=
  permutationCommitmentsOf urs.w (derivedUrsGLagrange urs) top.domainExponent
    top.constraintSystem (top.operations 0)

/-- The verifying key of a closed circuit at an explicitly-given `Shape` (the
shape-explicit core `Certificate.lean` certifies; `toVerifierKey` below supplies the
derived shape). -/
def verifierKeyAt
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (shape : Shape) (urs : URS G) : VerifyingKey shape Fp G :=
  .ofOperations shape urs top.constraintSystem (top.operations 0)

/-- Projection API for the fixed commitments of the shape-explicit top-level key. -/
@[simp] theorem verifierKeyAt_fixedCommitment
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (shape : Shape) (urs : URS G) (column : ℕ) :
    (top.verifierKeyAt shape urs).fixedCommitment column =
      (top.fixedCommitments urs).getD column 0 := by
  simp only [verifierKeyAt, VerifyingKey.ofOperations_fixedCommitment,
    fixedCommitments_eq_fixedCommitmentsOf, domainExponent, selectorMap,
    selectorActivations, regionStarts]

/-- **The verifying key of a closed top-level circuit**: the `TopLevelCircuit` carries
its own `configInput` and unit input, so the only remaining inputs are the proof-shape
counts and the URS — `keygen_vk` at the `TopLevelCircuit` level, with the derived
`Shape` in the return type. -/
def toVerifierKey
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (pp : ProofParams) (urs : URS G) :
    VerifyingKey (pp.mergeDerived top) Fp G :=
  top.verifierKeyAt (pp.mergeDerived top) urs

/-- The derived key uses the circuit-owned fitting domain size. -/
@[simp]
theorem toVerifierKey_n
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).n = 2 ^ top.domainExponent := by
  simp [toVerifierKey, verifierKeyAt, VerifyingKey.ofOperations,
    TopLevelCircuit.domainExponent]

/-- The derived key preserves the closed constraint system's blinding count. -/
@[simp]
theorem toVerifierKey_blindingFactors
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).blindingFactors = top.blindingFactors := by
  simp [toVerifierKey, verifierKeyAt, VerifyingKey.ofOperations,
    TopLevelCircuit.blindingFactors]

/-- The derived key exposes the fixed commitments computed from its own dense rows. -/
theorem toVerifierKey_fixedCommitment
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (pp : ProofParams) (urs : URS G) (column : ℕ) :
    (top.toVerifierKey pp urs).fixedCommitment column =
      (top.fixedCommitments urs).getD column 0 := by
  simp only [toVerifierKey, verifierKeyAt_fixedCommitment]

/-- The derived key exposes the common permutation commitments computed from
its own keygen permutation rows. -/
theorem toVerifierKey_permutationCommonCommitment
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (pp : ProofParams) (urs : URS G)
    (column : Fin (pp.mergeDerived top).numPermutationColumns) :
    (top.toVerifierKey pp urs).permutationCommonCommitment column =
      (top.permutationCommitments urs).getD column.val 0 := by
  simp only [toVerifierKey, verifierKeyAt,
    VerifyingKey.ofOperations_permutationCommonCommitment,
    permutationCommitments, domainExponent]

/-- The derived key exposes exactly the advice-query layout of its selector-map
derivation. -/
theorem toVerifierKey_adviceQueryLayout_derived
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).adviceQueryLayout =
      top.pinnedCS.adviceQueryLayout := by
  rfl

/-- The derived key exposes exactly the fixed-query layout of its selector-map
derivation. -/
theorem toVerifierKey_fixedQueryLayout_derived
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).fixedQueryLayout =
      top.pinnedCS.fixedQueryLayout := by
  rfl

/-- The derived key exposes exactly the instance-query layout of its selector-map
derivation. -/
theorem toVerifierKey_instanceQueryLayout_derived
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).instanceQueryLayout =
      top.pinnedCS.instanceQueryLayout := by
  rfl

/-- The derived key exposes exactly the gate polynomials of its circuit-owned pinned
constraint system. -/
theorem toVerifierKey_gates_derived
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).gates =
      top.pinnedCS.gates.map RichExpression.toExpr := by
  rfl

/-- Over `Fp`, the finite-field and Pasta decidable-equality instances produce the
same pinned projection. This keeps the circuit-owned `pinnedCS` API stable across
the two existing instance entry points without recomputing a concrete circuit. -/
theorem pinnedCS_eq_derive_fp
    (top : TopLevelCircuit Fp ConfigInput Config Output) :
    top.pinnedCS =
      PinnedConstraintSystem.derive
        top.constraintSystem top.selectorMap := by
  rw [top.pinnedCS_eq_derive]
  have hdec :
      (FiniteField.instDecidableEq : DecidableEq Fp) =
        (inferInstance : DecidableEq Fp) :=
    Subsingleton.elim _ _
  rw [hdec]

/-- The derived key's advice-query layout has the shape count computed from the same
top-level pinned constraint system. -/
theorem toVerifierKey_adviceQueryCount
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).adviceQueryLayout.length =
      (pp.mergeDerived top).numAdviceQueries := by
  rw [top.toVerifierKey_adviceQueryLayout_derived]
  change top.pinnedCS.adviceQueryLayout.length =
    top.pinnedCS.adviceQueryLayout.length
  rfl

/-- The derived key's fixed-query layout has the shape count computed from the same
top-level pinned constraint system. -/
theorem toVerifierKey_fixedQueryCount
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).fixedQueryLayout.length =
      (pp.mergeDerived top).numFixedQueries := by
  rw [top.toVerifierKey_fixedQueryLayout_derived]
  change top.pinnedCS.fixedQueryLayout.length =
    top.pinnedCS.fixedQueryLayout.length
  rfl

/-- The derived key's instance-query layout has the shape count computed from the same
top-level pinned constraint system. -/
theorem toVerifierKey_instanceQueryCount
    (top : TopLevelCircuit Fp ConfigInput Config Output)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).instanceQueryLayout.length =
      (pp.mergeDerived top).numInstanceQueries := by
  rw [top.toVerifierKey_instanceQueryLayout_derived]
  change top.pinnedCS.instanceQueryLayout.length =
    top.pinnedCS.instanceQueryLayout.length
  rfl

end Halo2.TopLevelCircuit
