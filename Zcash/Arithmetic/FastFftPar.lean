/-
Copyright (c) 2026 Ironwood Contributors.
Released under the Apache License, Version 2.0.
-/
import Zcash.Arithmetic.FastFft
import Zcash.Common.ParMap

/-!
# Round-parallel fast group FFT, with a proven equality to `bestFftGFast`

`bestFftGFast` (`Fast/FastFft.lean`) is the sequential Vesta-concrete fast group FFT: `logN`
rounds of butterflies, each round touching `n/2` disjoint index pairs `(aIdx, bIdx)`. Within a
round every butterfly is independent of every other — no butterfly reads an index another
butterfly writes — so a round is embarrassingly parallel. This module exploits that on the proven
parallel-map machinery of `Zcash/Common/ParMap.lean` (`List.parMap` / `parMapChunked`, certified
by `parMap_eq_map`), keeping the house discipline: `bestFftGParFast` is certified by a *proven*
equality `bestFftGParFast_eq` to `bestFftGFast`, and hence (chaining `bestFftGFast_eq`) by
`bestFftGParFast_eq_spec` to the transparent Rust-mirroring spec `bestFftG`.

## Shape of the parallel round

Rather than one task per butterfly *chunk* (which would leave the last `log₂ nproc` rounds — the
ones with few, large chunks — essentially sequential), `roundPar` parallelizes at butterfly
granularity, uniformly across all rounds, in two parallel phases:

1. all `(n/chunk)·half = n/2` twiddled points `t = smulFast twdl.val a[bIdx]` (the projective
   scalar multiplications — essentially all of a round's group work) are computed by
   `parMapChunked` over the flat butterfly index `p = c·half + j`;
2. the output array is a pure per-index gather `aIdx ↦ a[aIdx] + t`, `bIdx ↦ a[aIdx] − t` from
   the original array and the phase-1 table, again through `parMapChunked`.

Total group-operation work is identical to the sequential round (each `t` is computed once).

## Shape of the proof

`fftWith round` abstracts the FFT over its round function; `fftWith roundSeq = bestFftGFast`
holds by `rfl`, because `roundSeq` is the round body of `bestFftGFast` extracted verbatim. The
real content is `roundPar_eq_roundSeq`: the imperative round — a nested `for`/`set!` loop over
chunks and butterflies — equals the pure two-phase gather. The imperative loop is first rewritten
as a `List.foldl` of single-butterfly steps (`roundSeq_eq_foldl`, via the core `forIn`-to-`foldl`
lemmas), and then a fold invariant (`Inv`) tracks, butterfly by butterfly, that

* every index already written holds its final gathered value (`gOut`), and
* every index not yet written still holds its original value —

which is exactly the disjointness argument: each butterfly reads only the two indices it is
itself about to write, and no two butterflies of a round touch a common index (`tile_inj`). All
indexing is by `getElem!`/`set!` (as in `bestFftGFast` itself), so the equality holds
*unconditionally* — also for degenerate inputs where the FFT's index arithmetic runs out of
bounds.
-/

open Zcash.Snark
open Zcash.Snark.Keygen
open CompElliptic
open CompElliptic.Curves.Pasta

namespace Zcash.Snark.Keygen.Fast

/-- `bestFftG` requires `[Inhabited G]` (for `Array.get!`); the affine group has a canonical `0`
(the same local instance as in `Fast/FastFft.lean`). -/
local instance : Inhabited GVes := ⟨0⟩

/-- The twiddled point of butterfly `(c, j)` of a round at width `half`, read from the original
(pre-round) array: `smulFast tw[j * twiddleChunk].val a[bIdx]` with `bIdx = c * chunk + half + j`.
This is the expensive part of a butterfly (one projective scalar multiplication). -/
def twiddledPoint (n half : ℕ) (tw : Array Fp) (a : Array GVes) (c j : ℕ) : GVes :=
  Projective.PVes.smulFast (tw[j * (n / (2 * half))]!).val a[c * (2 * half) + half + j]!

/-- A single butterfly `(c, j)` as a pure array step: read `aOld = a[aIdx]` and the twiddled
point `t`, then write `aIdx ↦ aOld + t` and `bIdx ↦ aOld − t`. Definitionally the inner loop
body of `bestFftGFast`/`roundSeq`. -/
def butterfly (n half : ℕ) (tw : Array Fp) (c j : ℕ) (a : Array GVes) : Array GVes :=
  (a.set! (c * (2 * half) + j) (a[c * (2 * half) + j]! + twiddledPoint n half tw a c j)).set!
    (c * (2 * half) + half + j) (a[c * (2 * half) + j]! - twiddledPoint n half tw a c j)

/-- One FFT round in imperative form — the round body of `bestFftGFast`, extracted verbatim
(so that `fftWith roundSeq = bestFftGFast` holds by `rfl`). -/
def roundSeq (n half : ℕ) (tw : Array Fp) (a0 : Array GVes) : Array GVes := Id.run do
  let mut a := a0
  let chunk := 2 * half
  let twiddleChunk := n / chunk
  for c in [0:n / chunk] do
    let s := c * chunk
    for j in [0:half] do
      let twdl := tw[j * twiddleChunk]!
      let aIdx := s + j
      let bIdx := s + half + j
      let aOld := a[aIdx]!
      let t := Projective.PVes.smulFast twdl.val a[bIdx]!
      a := a.set! aIdx (aOld + t)
      a := a.set! bIdx (aOld - t)
  return a

/-- One FFT round in parallel form: phase 1 evaluates the `twiddledPoint`s in parallel over the
flat butterfly index `p = c·half + j` (batches of 16 scalar multiplications per task);
phase 2 gathers the output array per index, also in parallel (batches of 64). Both phases run on
the proven `parMapChunked` (= `List.map`, by `parMapChunked_eq_map`). -/
def roundPar (n half : ℕ) (tw : Array Fp) (a : Array GVes) : Array GVes :=
  let m := n / (2 * half)
  let ts := (parMapChunked 15 (fun p => twiddledPoint n half tw a (p / half) (p % half))
    (List.range (m * half))).toArray
  (parMapChunked 63 (fun i =>
    if i / (2 * half) < m then
      if i % (2 * half) < half then
        a[i]! + ts[i / (2 * half) * half + i % (2 * half)]!
      else
        a[i - half]! - ts[i / (2 * half) * half + (i % (2 * half) - half)]!
    else a[i]!) (List.range a.size)).toArray

/-- `bestFftGFast` with the round abstracted: bit-reversal permutation and twiddle table exactly
as in `bestFftGFast` (both cheap, kept sequential), then `logN` rounds of `round`. -/
def fftWith (round : ℕ → ℕ → Array Fp → Array GVes → Array GVes)
    (a0 : Array GVes) (omega : Fp) (logN : ℕ) : Array GVes := Id.run do
  let n := a0.size
  let mut a := a0
  -- bit-reversal permutation (`arithmetic.rs:207-212`)
  for k in [0:n] do
    let rk := bitreverse k logN
    if k < rk then
      let ak := a[k]!
      let ark := a[rk]!
      a := (a.set! k ark).set! rk ak
  -- precompute twiddles `[omega^0 … omega^(n/2 − 1)]` (`arithmetic.rs:215-221`)
  let mut tw : Array Fp := Array.mkEmpty (n / 2)
  let mut w : Fp := 1
  for _ in [0:n / 2] do
    tw := tw.push w
    w := w * omega
  -- `log_n` rounds of butterflies (`arithmetic.rs:223-252`)
  let mut half := 1
  for _ in [0:logN] do
    a := round n half tw a
    half := 2 * half
  return a

/-- **Round-parallel fast FFT**: `bestFftGFast` with every round's butterflies evaluated through
the proven parallel map. Certified against `bestFftGFast` by `bestFftGParFast_eq` and against the
transparent spec `bestFftG` by `bestFftGParFast_eq_spec`. -/
def bestFftGParFast (a0 : Array GVes) (omega : Fp) (logN : ℕ) : Array GVes :=
  fftWith roundPar a0 omega logN

/-- The factored FFT at the verbatim sequential round *is* `bestFftGFast`. -/
theorem fftWith_roundSeq (a0 : Array GVes) (omega : Fp) (logN : ℕ) :
    fftWith roundSeq a0 omega logN = bestFftGFast a0 omega logN := rfl

/-! ## The sequential round as a fold of butterflies -/

/-- The imperative round is the fold of its butterfly steps, chunk by chunk, butterfly by
butterfly. -/
theorem roundSeq_eq_foldl (n half : ℕ) (tw : Array Fp) (a0 : Array GVes) :
    roundSeq n half tw a0 =
      (List.range (n / (2 * half))).foldl
        (fun a c => (List.range half).foldl (fun a j => butterfly n half tw c j a) a) a0 := by
  show (forIn (m := Id) [0:n / (2 * half)] a0 (fun c a =>
      ForInStep.yield <$> forIn (m := Id) [0:half] a (fun j a =>
        pure (ForInStep.yield (butterfly n half tw c j a)))) : Id _) = _
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', List.forIn_pure_yield_eq_foldl,
    map_pure]
  rfl

/-! ## Disjointness of the butterfly index pairs -/

private theorem tile_div {d q r : ℕ} (hr : r < d) : (q * d + r) / d = q := by
  rw [Nat.mul_comm q d, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, Nat.add_zero]

private theorem tile_mod {d q r : ℕ} (hr : r < d) : (q * d + r) % d = r := by
  rw [Nat.mul_comm q d, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

/-- Uniqueness of the `(quotient, remainder)` tiling: the workhorse behind "no two butterflies
of a round touch a common index". -/
private theorem tile_inj {d q r q' r' : ℕ} (hr : r < d) (hr' : r' < d)
    (h : q * d + r = q' * d + r') : q = q' ∧ r = r' :=
  ⟨by rw [← tile_div (q := q) hr, h, tile_div hr'],
   by rw [← tile_mod (q := q) hr, h, tile_mod hr']⟩

/-- `Written half c jc i`: index `i` has been written after processing all butterflies strictly
before position `(c, jc)` of a round at width `half` (chunks `< c` entirely, chunk `c` up to
butterfly `jc`). -/
private def Written (half c jc i : ℕ) : Prop :=
  ∃ c' j', j' < half ∧ (c' < c ∨ (c' = c ∧ j' < jc)) ∧
    (i = c' * (2 * half) + j' ∨ i = c' * (2 * half) + half + j')

/-- The `aIdx` of the current butterfly is still unwritten when its turn comes. -/
private theorem not_written_a {half c jc : ℕ} (hjc : jc < half) :
    ¬ Written half c jc (c * (2 * half) + jc) := by
  rintro ⟨c', j', hj', horder, heq | heq⟩
  · obtain ⟨rfl, rfl⟩ := tile_inj (by omega) (by omega) heq.symm
    rcases horder with h | ⟨-, h⟩ <;> omega
  · rw [show c' * (2 * half) + half + j' = c' * (2 * half) + (half + j') from by omega] at heq
    obtain ⟨-, h⟩ := tile_inj (by omega) (by omega) heq.symm
    omega

/-- The `bIdx` of the current butterfly is still unwritten when its turn comes. -/
private theorem not_written_b {half c jc : ℕ} (hjc : jc < half) :
    ¬ Written half c jc (c * (2 * half) + half + jc) := by
  rintro ⟨c', j', hj', horder, heq | heq⟩
  · rw [show c * (2 * half) + half + jc = c * (2 * half) + (half + jc) from by omega] at heq
    obtain ⟨-, h⟩ := tile_inj (by omega) (by omega) heq.symm
    omega
  · rw [show c * (2 * half) + half + jc = c * (2 * half) + (half + jc) from by omega,
      show c' * (2 * half) + half + j' = c' * (2 * half) + (half + j') from by omega] at heq
    obtain ⟨rfl, h⟩ := tile_inj (by omega) (by omega) heq.symm
    rcases horder with h2 | ⟨-, h2⟩ <;> omega

/-- Advancing one butterfly extends the written set by exactly its two indices. -/
private theorem written_succ {half c jc i : ℕ} (hjc : jc < half) :
    Written half c (jc + 1) i ↔
      Written half c jc i ∨ i = c * (2 * half) + jc ∨ i = c * (2 * half) + half + jc := by
  constructor
  · rintro ⟨c', j', hj', horder, heq⟩
    rcases horder with hlt | ⟨rfl, hj⟩
    · exact Or.inl ⟨c', j', hj', Or.inl hlt, heq⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact Or.inl ⟨c', j', hj', Or.inr ⟨rfl, hj⟩, heq⟩
      · rcases heq with rfl | rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
  · rintro (⟨c', j', hj', horder, heq⟩ | rfl | rfl)
    · refine ⟨c', j', hj', ?_, heq⟩
      rcases horder with h | ⟨rfl, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨rfl, Nat.lt_succ_of_lt h⟩
    · exact ⟨c, jc, hjc, Or.inr ⟨rfl, Nat.lt_succ_self _⟩, Or.inl rfl⟩
    · exact ⟨c, jc, hjc, Or.inr ⟨rfl, Nat.lt_succ_self _⟩, Or.inr rfl⟩

/-- Finishing chunk `c` (`jc = half`) leaves the same written set as starting chunk `c + 1`. -/
private theorem written_roll {half c i : ℕ} :
    Written half c half i ↔ Written half (c + 1) 0 i := by
  constructor
  · rintro ⟨c', j', hj', horder, heq⟩
    refine ⟨c', j', hj', Or.inl ?_, heq⟩
    rcases horder with h | ⟨rfl, h⟩ <;> omega
  · rintro ⟨c', j', hj', horder, heq⟩
    refine ⟨c', j', hj', ?_, heq⟩
    rcases horder with h | ⟨-, h⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
      · exact Or.inl h
      · exact Or.inr ⟨rfl, hj'⟩
    · omega

/-- After the whole round, the written set is exactly `{i | i / chunk < n / chunk}`. -/
private theorem written_final {n half i : ℕ} :
    Written half (n / (2 * half)) 0 i ↔ i / (2 * half) < n / (2 * half) ∧ 0 < half := by
  constructor
  · rintro ⟨c', j', hj', horder, heq⟩
    have hc' : c' < n / (2 * half) := by rcases horder with h | ⟨-, h⟩ <;> omega
    refine ⟨?_, by omega⟩
    rcases heq with rfl | rfl
    · rw [tile_div (by omega)]; exact hc'
    · rw [show c' * (2 * half) + half + j' = c' * (2 * half) + (half + j') from by omega,
        tile_div (by omega)]
      exact hc'
  · rintro ⟨hdiv, hhalf⟩
    have hmod : i % (2 * half) < 2 * half := Nat.mod_lt _ (by omega)
    have hi : i = i / (2 * half) * (2 * half) + i % (2 * half) := by
      rw [Nat.mul_comm]; exact (Nat.div_add_mod i (2 * half)).symm
    by_cases hlt : i % (2 * half) < half
    · exact ⟨i / (2 * half), i % (2 * half), hlt, Or.inl hdiv, Or.inl hi⟩
    · exact ⟨i / (2 * half), i % (2 * half) - half, by omega, Or.inl hdiv, Or.inr (by omega)⟩

/-! ## The gathered value of a written index -/

/-- The final (post-round) value of a written index `i`, gathered from the original array: the
`+`-leg for the first half of `i`'s chunk, the `−`-leg for the second half. -/
private def gOut (n half : ℕ) (tw : Array Fp) (a : Array GVes) (i : ℕ) : GVes :=
  if i % (2 * half) < half then
    a[i]! + twiddledPoint n half tw a (i / (2 * half)) (i % (2 * half))
  else
    a[i - half]! - twiddledPoint n half tw a (i / (2 * half)) (i % (2 * half) - half)

private theorem gOut_a {n half : ℕ} {tw : Array Fp} {a : Array GVes} {c jc : ℕ}
    (hjc : jc < half) :
    gOut n half tw a (c * (2 * half) + jc) =
      a[c * (2 * half) + jc]! + twiddledPoint n half tw a c jc := by
  rw [gOut, tile_mod (by omega), tile_div (by omega), if_pos hjc]

private theorem gOut_b {n half : ℕ} {tw : Array Fp} {a : Array GVes} {c jc : ℕ}
    (hjc : jc < half) :
    gOut n half tw a (c * (2 * half) + half + jc) =
      a[c * (2 * half) + jc]! - twiddledPoint n half tw a c jc := by
  rw [gOut, show c * (2 * half) + half + jc = c * (2 * half) + (half + jc) from by omega,
    tile_mod (by omega), tile_div (by omega), if_neg (by omega),
    show c * (2 * half) + (half + jc) - half = c * (2 * half) + jc from by omega,
    show half + jc - half = jc from by omega]

/-! ## The fold invariant -/

/-- `getElem!` through `set!`, in unconditional form. -/
private theorem getElem!_set' (r : Array GVes) (p i : ℕ) (v : GVes) :
    (r.set! p v)[i]! = if p = i ∧ p < r.size then v else r[i]! := by
  by_cases hi : i < r.size
  · rw [getElem!_pos (r.set! p v) i (by simpa using hi), getElem!_pos r i hi]
    simp only [Array.set!_eq_setIfInBounds]
    by_cases hpi : p = i
    · subst hpi; simp [hi]
    · rw [if_neg (fun hc => hpi hc.1)]
      exact Array.getElem_setIfInBounds_ne hi hpi
  · rw [getElem!_neg (r.set! p v) i (by simpa using hi), getElem!_neg r i hi,
      if_neg (by omega)]

/-- The two writes of one butterfly, seen through `getElem!`. -/
private theorem getElem!_butterfly {n half : ℕ} {tw : Array Fp} {c j : ℕ} (r : Array GVes) (i : ℕ) :
    (butterfly n half tw c j r)[i]! =
      if c * (2 * half) + half + j = i ∧ c * (2 * half) + half + j < r.size then
        r[c * (2 * half) + j]! - twiddledPoint n half tw r c j
      else if c * (2 * half) + j = i ∧ c * (2 * half) + j < r.size then
        r[c * (2 * half) + j]! + twiddledPoint n half tw r c j
      else r[i]! := by
  rw [butterfly, getElem!_set', getElem!_set']
  simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

/-- The invariant carried butterfly-by-butterfly through a round's fold: written indices hold
their gathered value, unwritten indices their original value. -/
private structure Inv (n half : ℕ) (tw : Array Fp) (a : Array GVes) (c jc : ℕ)
    (r : Array GVes) : Prop where
  size_eq : r.size = a.size
  written : ∀ i, i < a.size → Written half c jc i → r[i]! = gOut n half tw a i
  fresh : ∀ i, ¬ Written half c jc i → r[i]! = a[i]!

/-- The invariant survives one butterfly: the butterfly reads only its own two (fresh) indices,
so its writes install exactly the gathered values. -/
private theorem inv_step {n half : ℕ} {tw : Array Fp} {a : Array GVes} {c jc : ℕ}
    {r : Array GVes} (hjc : jc < half) (h : Inv n half tw a c jc r) :
    Inv n half tw a c (jc + 1) (butterfly n half tw c jc r) := by
  have hra : r[c * (2 * half) + jc]! = a[c * (2 * half) + jc]! :=
    h.fresh _ (not_written_a hjc)
  have hrb : r[c * (2 * half) + half + jc]! = a[c * (2 * half) + half + jc]! :=
    h.fresh _ (not_written_b hjc)
  have htP : twiddledPoint n half tw r c jc = twiddledPoint n half tw a c jc := by
    rw [twiddledPoint, twiddledPoint, hrb]
  have hsize : (butterfly n half tw c jc r).size = a.size := by
    rw [butterfly]; simpa using h.size_eq
  refine ⟨hsize, ?_, ?_⟩
  · intro i hi hw
    rcases (written_succ hjc).mp hw with hw' | rfl | rfl
    · have hia : c * (2 * half) + jc ≠ i := fun he =>
        not_written_a hjc (by rw [he]; exact hw')
      have hib : c * (2 * half) + half + jc ≠ i := fun he =>
        not_written_b hjc (by rw [he]; exact hw')
      rw [getElem!_butterfly, if_neg (fun hc => hib hc.1), if_neg (fun hc => hia hc.1)]
      exact h.written i hi hw'
    · rw [getElem!_butterfly, if_neg (fun hc => absurd hc.1 (by omega)),
        if_pos ⟨rfl, by rw [h.size_eq]; exact hi⟩, hra, htP, gOut_a hjc]
    · rw [getElem!_butterfly, if_pos ⟨rfl, by rw [h.size_eq]; exact hi⟩, hra, htP, gOut_b hjc]
  · intro i hnw
    have hia : c * (2 * half) + jc ≠ i := fun he =>
      hnw ((written_succ hjc).mpr (Or.inr (Or.inl he.symm)))
    have hib : c * (2 * half) + half + jc ≠ i := fun he =>
      hnw ((written_succ hjc).mpr (Or.inr (Or.inr he.symm)))
    rw [getElem!_butterfly, if_neg (fun hc => hib hc.1), if_neg (fun hc => hia hc.1)]
    exact h.fresh i fun hw => hnw ((written_succ hjc).mpr (Or.inl hw))

/-- The invariant survives the tail of a chunk's butterflies. -/
private theorem inv_inner {n half : ℕ} {tw : Array Fp} {a : Array GVes} {c : ℕ} :
    ∀ (k jc : ℕ) (r : Array GVes), jc + k ≤ half → Inv n half tw a c jc r →
      Inv n half tw a c (jc + k)
        ((List.range' jc k).foldl (fun b j => butterfly n half tw c j b) r)
  | 0, jc, r, _, h => by simpa using h
  | k + 1, jc, r, hk, h => by
    rw [List.range'_succ]
    simp only [List.foldl_cons]
    have h2 := inv_inner k (jc + 1) (butterfly n half tw c jc r) (by omega) (inv_step (by omega) h)
    rw [show jc + (k + 1) = jc + 1 + k from by omega]
    exact h2

/-- The invariant survives a whole chunk. -/
private theorem inv_chunk {n half : ℕ} {tw : Array Fp} {a : Array GVes} {c : ℕ}
    {r : Array GVes} (h : Inv n half tw a c 0 r) :
    Inv n half tw a (c + 1) 0
      ((List.range half).foldl (fun b j => butterfly n half tw c j b) r) := by
  have h1 := inv_inner (c := c) half 0 r (by omega) h
  rw [List.range_eq_range' (n := half)]
  have h2 : Inv n half tw a c half ((List.range' 0 half).foldl
      (fun b j => butterfly n half tw c j b) r) := by simpa using h1
  exact ⟨h2.size_eq,
    fun i hi hw => h2.written i hi (written_roll.mpr hw),
    fun i hnw => h2.fresh i fun hw => hnw (written_roll.mp hw)⟩

/-- The invariant survives any run of chunks. -/
private theorem inv_outer {n half : ℕ} {tw : Array Fp} {a : Array GVes} :
    ∀ (k c : ℕ) (r : Array GVes), Inv n half tw a c 0 r →
      Inv n half tw a (c + k) 0
        ((List.range' c k).foldl
          (fun b c' => (List.range half).foldl (fun b' j => butterfly n half tw c' j b') b) r)
  | 0, c, r, h => by simpa using h
  | k + 1, c, r, h => by
    rw [List.range'_succ]
    simp only [List.foldl_cons]
    have h3 := inv_outer k (c + 1) _ (inv_chunk h)
    rw [show c + (k + 1) = c + 1 + k from by omega]
    exact h3

private theorem inv_init (n half : ℕ) (tw : Array Fp) (a : Array GVes) :
    Inv n half tw a 0 0 a :=
  ⟨rfl,
   fun _ _ hw => by
     rcases hw with ⟨c', j', -, horder, -⟩
     rcases horder with h | ⟨-, h⟩ <;> omega,
   fun _ _ => rfl⟩

/-- The full characterization of the sequential round: sizes agree, and every cell holds either
its gathered value (if the round writes it) or its original value. -/
private theorem roundSeq_inv (n half : ℕ) (tw : Array Fp) (a : Array GVes) :
    Inv n half tw a (n / (2 * half)) 0 (roundSeq n half tw a) := by
  rw [roundSeq_eq_foldl, List.range_eq_range' (n := n / (2 * half))]
  have h := inv_outer (n / (2 * half)) 0 a (inv_init n half tw a)
  simpa using h

/-! ## The parallel round equals the sequential round -/

/-- Reading the phase-1 table at flat index `c·half + j` gives `twiddledPoint c j`. -/
private theorem ts_read {n half : ℕ} {tw : Array Fp} {a : Array GVes} {c j : ℕ}
    (hc : c < n / (2 * half)) (hj : j < half) :
    (((List.range (n / (2 * half) * half)).map fun p =>
        twiddledPoint n half tw a (p / half) (p % half)).toArray)[c * half + j]! =
      twiddledPoint n half tw a c j := by
  have hlt : c * half + j < n / (2 * half) * half :=
    calc c * half + j < c * half + half := by omega
    _ = (c + 1) * half := (Nat.succ_mul c half).symm
    _ ≤ n / (2 * half) * half := Nat.mul_le_mul_right _ hc
  rw [getElem!_pos _ _ (by simpa using hlt)]
  simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
  rw [tile_div hj, tile_mod hj]

/-- **The crux**: within a round, the parallel two-phase gather computes exactly the sequential
nested `for`/`set!` loop. -/
theorem roundPar_eq_roundSeq (n half : ℕ) (tw : Array Fp) (a : Array GVes) :
    roundPar n half tw a = roundSeq n half tw a := by
  have hinv := roundSeq_inv n half tw a
  rw [roundPar]
  simp only [parMapChunked_eq_map]
  apply Array.ext
  · simp [hinv.size_eq]
  · intro i hL hR
    have hi : i < a.size := by simpa using hL
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_range]
    rw [← getElem!_pos (roundSeq n half tw a) i hR]
    by_cases hw : i / (2 * half) < n / (2 * half) ∧ 0 < half
    · rw [hinv.written i hi (written_final.mpr hw), gOut, if_pos hw.1]
      have hmod : i % (2 * half) < 2 * half := Nat.mod_lt _ (by omega)
      by_cases hlt : i % (2 * half) < half
      · rw [if_pos hlt, if_pos hlt, ts_read hw.1 hlt]
      · rw [if_neg hlt, if_neg hlt, ts_read hw.1 (by omega)]
    · rw [hinv.fresh i fun hww => hw (written_final.mp hww)]
      have hnd : ¬ i / (2 * half) < n / (2 * half) := by
        intro hdiv
        rcases Nat.eq_zero_or_pos half with h0 | hpos
        · subst h0; simp at hdiv
        · exact hw ⟨hdiv, hpos⟩
      rw [if_neg hnd]

/-! ## Certification -/

/-- **Certification of the round-parallel FFT against the sequential fast FFT.** The two differ
only in evaluation strategy: each round's butterflies run as parallel tasks instead of a
sequential loop. -/
theorem bestFftGParFast_eq (a0 : Array GVes) (omega : Fp) (logN : ℕ) :
    bestFftGParFast a0 omega logN = bestFftGFast a0 omega logN := by
  have hround : roundPar = roundSeq := by
    funext n half tw a
    exact roundPar_eq_roundSeq n half tw a
  rw [bestFftGParFast, hround]
  exact fftWith_roundSeq a0 omega logN

/-- **Certification against the transparent Rust-mirroring spec** `bestFftG`, chaining
`bestFftGParFast_eq` with `bestFftGFast_eq`. -/
theorem bestFftGParFast_eq_spec (a0 : Array GVes) (omega : Fp) (logN : ℕ) :
    bestFftGParFast a0 omega logN = bestFftG a0 omega logN := by
  rw [bestFftGParFast_eq, bestFftGFast_eq]

/-- Fast parallel twin of `derivedUrsGLagrange` (matching `derivedUrsGLagrangeFast`, with the
round-parallel FFT). -/
def derivedUrsGLagrangeParFast (urs : URS GVes) : List GVes :=
  let monomial := List.ofFn urs.g
  let minv : Fp := ((2 : Fp) ^ urs.k)⁻¹
  (bestFftGParFast monomial.toArray (omegaInvOf urs.k) urs.k).toList.map
    fun point => minv.val • point

/-- The parallel Lagrange derivation agrees with `derivedUrsGLagrange`. -/
theorem derivedUrsGLagrangeParFast_eq (urs : URS GVes) :
    derivedUrsGLagrangeParFast urs = derivedUrsGLagrange urs := by
  simp only [derivedUrsGLagrangeParFast, derivedUrsGLagrange, bestFftGParFast_eq_spec]

end Zcash.Snark.Keygen.Fast
