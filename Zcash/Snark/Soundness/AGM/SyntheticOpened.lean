import Zcash.Snark.Soundness.AGM.DeployedValueUnbatch
import Zcash.Snark.Soundness.Multiopen.Opened

/-!
# Offline compatibility with the opened-batch interface

Represented columns form power combinations at any distinct interpolation points locally, so this
file packages them as a *synthetic* `OpenedBatchOpenings` — algebraic calculations, not accepting
transcripts.  Its canonical Vandermonde decode returns the original AGM coordinates exactly, so
deterministic downstream constraints are reused without the old rewind loss.
-/

namespace Zcash.Snark

open Classical
open Zcash.Arithmetic (scalarFieldOrder)

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- `n + 1` distinct interpolation points with index `0` pinned to `x`.

`toSyntheticOpened` needs an injective point family containing the actual batching challenge, and
the points are extractor-side data — nothing forces them to be oracle answers, so they can simply
walk up from the challenge. -/
def pinnedPoints (x : Fp) (n : Nat) : Fin (n + 1) -> Fp := fun j => x + ((j : Nat) : Fp)

@[simp] theorem pinnedPoints_zero (x : Fp) (n : Nat) : pinnedPoints x n 0 = x := by
  simp [pinnedPoints]

/-- The walk stays injective while it is shorter than the field's characteristic. -/
theorem pinnedPoints_injective (x : Fp) {n : Nat} (hn : n < scalarFieldOrder) :
    Function.Injective (pinnedPoints x n) := by
  intro a b hab
  have hcast : (((a : Nat) : Fp)) = (((b : Nat) : Fp)) := by
    have h := hab
    unfold pinnedPoints at h
    exact add_left_cancel h
  have ha : (a : Nat) < scalarFieldOrder :=
    lt_of_le_of_lt (Nat.lt_succ_iff.mp a.isLt) hn
  have hb : (b : Nat) < scalarFieldOrder :=
    lt_of_le_of_lt (Nat.lt_succ_iff.mp b.isLt) hn
  have hval := congrArg ZMod.val hcast
  rw [ZMod.val_cast_of_lt ha, ZMod.val_cast_of_lt hb] at hval
  exact Fin.ext hval

/-- Build an opened-batch compatibility object locally from a represented algebraic power batch,
with one interpolation point pinned to the actual batching challenge. -/
def AlgebraicPowerBatch.toSyntheticOpened
    {urs : URS G} {numColumns : Nat} {columnCommitments : Fin numColumns -> G}
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW challenge : Fp}
    (batch : AlgebraicPowerBatch urs columnCommitments aggregate aggregateU aggregateW challenge)
    (b : Fin (2 ^ urs.k) -> Fp) (columnEvals : Fin numColumns -> Fp)
    (hvalues : forall i, commitGen b (batch.coeffs i) = columnEvals i)
    (points : Fin numColumns -> Fp) (hpoints : Function.Injective points)
    (current : Fin numColumns) (hcurrent : points current = challenge) :
    OpenedBatchOpenings urs b columnCommitments columnEvals aggregate aggregateU aggregateW := by
  let cols : AlgebraicColumnRepresentations urs columnCommitments :=
    { coeffs := batch.coeffs
      uComp := batch.uComp
      wComp := batch.wComp
      commitment := batch.commitment }
  refine
    { batchChallenge := points
      challengesDistinct := hpoints
      batched := fun r => ∑ i : Fin numColumns, points r ^ (i : Nat) • batch.coeffs i
      batchedU := fun r => ∑ i : Fin numColumns, points r ^ (i : Nat) * batch.uComp i
      batchedW := fun r => ∑ i : Fin numColumns, points r ^ (i : Nat) * batch.wComp i
      current := current
      current_eq := ?_
      currentU_eq := ?_
      currentW_eq := ?_
      commitment := ?_
      value := ?_ }
  · rw [hcurrent]
    exact batch.reconstruct.symm
  · rw [hcurrent]
    exact batch.reconstructU.symm
  · rw [hcurrent]
    exact batch.reconstructW.symm
  · intro r
    exact cols.power_commitment (points r)
  · intro r
    rw [commitGen_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [commitGen_smul_left, hvalues, smul_eq_mul]

/-- Canonically decoding a synthetic opened batch returns the original AGM witness coordinate. -/
theorem AlgebraicPowerBatch.openedColumnDecode_toSyntheticOpened_coeffs
    {urs : URS G} {numColumns : Nat} {columnCommitments : Fin numColumns -> G}
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW challenge : Fp}
    (batch : AlgebraicPowerBatch urs columnCommitments aggregate aggregateU aggregateW challenge)
    (b : Fin (2 ^ urs.k) -> Fp) (columnEvals : Fin numColumns -> Fp)
    (hvalues : forall i, commitGen b (batch.coeffs i) = columnEvals i)
    (points : Fin numColumns -> Fp) (hpoints : Function.Injective points)
    (current : Fin numColumns) (hcurrent : points current = challenge) (i : Fin numColumns) :
    (openedColumnDecode
      (batch.toSyntheticOpened b columnEvals hvalues points hpoints current hcurrent)).coeffs i =
        batch.coeffs i := by
  change (∑ r : Fin numColumns, (Matrix.vandermonde points)⁻¹ i r •
    (∑ j : Fin numColumns, points r ^ (j : Nat) • batch.coeffs j)) = batch.coeffs i
  exact vandermonde_decode_map
    ((Matrix.vandermonde points)⁻¹ : Matrix (Fin numColumns) (Fin numColumns) Fp)
    (fun i j => vandermonde_inv_left points hpoints i j) (fun _ => rfl) i

/-- Canonically decoding a synthetic opened batch returns the original AGM `U` coordinate. -/
theorem AlgebraicPowerBatch.openedColumnDecode_toSyntheticOpened_uComp
    {urs : URS G} {numColumns : Nat} {columnCommitments : Fin numColumns -> G}
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW challenge : Fp}
    (batch : AlgebraicPowerBatch urs columnCommitments aggregate aggregateU aggregateW challenge)
    (b : Fin (2 ^ urs.k) -> Fp) (columnEvals : Fin numColumns -> Fp)
    (hvalues : forall i, commitGen b (batch.coeffs i) = columnEvals i)
    (points : Fin numColumns -> Fp) (hpoints : Function.Injective points)
    (current : Fin numColumns) (hcurrent : points current = challenge) (i : Fin numColumns) :
    (openedColumnDecode
      (batch.toSyntheticOpened b columnEvals hvalues points hpoints current hcurrent)).uComp i =
        batch.uComp i := by
  change (∑ r : Fin numColumns, (Matrix.vandermonde points)⁻¹ i r •
    (∑ j : Fin numColumns, points r ^ (j : Nat) * batch.uComp j)) = batch.uComp i
  exact vandermonde_decode_map
    ((Matrix.vandermonde points)⁻¹ : Matrix (Fin numColumns) (Fin numColumns) Fp)
    (fun i j => vandermonde_inv_left points hpoints i j) (fun _ => rfl) i

/-- Canonically decoding a synthetic opened batch returns the original AGM `W` coordinate. -/
theorem AlgebraicPowerBatch.openedColumnDecode_toSyntheticOpened_wComp
    {urs : URS G} {numColumns : Nat} {columnCommitments : Fin numColumns -> G}
    {aggregate : Fin (2 ^ urs.k) -> Fp} {aggregateU aggregateW challenge : Fp}
    (batch : AlgebraicPowerBatch urs columnCommitments aggregate aggregateU aggregateW challenge)
    (b : Fin (2 ^ urs.k) -> Fp) (columnEvals : Fin numColumns -> Fp)
    (hvalues : forall i, commitGen b (batch.coeffs i) = columnEvals i)
    (points : Fin numColumns -> Fp) (hpoints : Function.Injective points)
    (current : Fin numColumns) (hcurrent : points current = challenge) (i : Fin numColumns) :
    (openedColumnDecode
      (batch.toSyntheticOpened b columnEvals hvalues points hpoints current hcurrent)).wComp i =
        batch.wComp i := by
  change (∑ r : Fin numColumns, (Matrix.vandermonde points)⁻¹ i r •
    (∑ j : Fin numColumns, points r ^ (j : Nat) * batch.wComp j)) = batch.wComp i
  exact vandermonde_decode_map
    ((Matrix.vandermonde points)⁻¹ : Matrix (Fin numColumns) (Fin numColumns) Fp)
    (fun i j => vandermonde_inv_left points hpoints i j) (fun _ => rfl) i

end Zcash.Snark
