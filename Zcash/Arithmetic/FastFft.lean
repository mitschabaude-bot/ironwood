/-
Copyright (c) 2026 Ironwood Contributors.
Released under the Apache License, Version 2.0.
-/
import Zcash.Arithmetic.Fft
import Zcash.Vendor.CompElliptic.Projective

/-!
# Vesta-specialized fast Lagrange-basis group FFT

`bestFftG` (`Zcash.Arithmetic.Fft`) is the Rust-mirroring, group-generic radix-2 DIT FFT
used to derive the Lagrange basis. Every butterfly evaluates `twiddle.val • point`, which for the
affine group `G = SWPoint Vesta.curve` is a binary double-and-add over affine points — each affine
add pays one field inversion (~255 field muls). At domain size `2^k` the FFT does `Θ(k·2^k)`
butterflies, so on the deployed sizes the inversions dominate and a single evaluation costs minutes.

This module provides a Vesta-concrete twin `bestFftGFast` that swaps the affine scalar action for
`Projective.PVes.smulFast` — the same `n • point`, but computed through the complete
Renes–Costello–Batina projective addition formulas, paying the inversion once per scalar
multiplication instead of once per addition (`Fast/Projective.lean`). The house discipline is kept:
the transparent `bestFftG` stays the statement surface, and the fast implementation is certified by
a *proven* pointwise equality `bestFftGFast_eq`, discharged from `Projective.PVes.smulFast_eq`.

The proof factors through `bestFftGWith`, an FFT whose butterfly scalar action is an explicit
parameter `smul : ℕ → G → G`. Both `bestFftGFast = bestFftGWith smulFast` and
`bestFftG = bestFftGWith (· • ·)` hold by `rfl` (the loop bodies are textually identical up to the
`smul` call), so the whole equality reduces to `funext`-ing `smulFast_eq`.
-/

open Zcash.Snark
open Zcash.Snark.Keygen
open CompElliptic
open CompElliptic.Curves.Pasta

namespace Zcash.Snark.Keygen.Fast

/-- The concrete Vesta affine group `SWPoint Vesta.curve` (as in `Fast/Projective.lean`). -/
abbrev GVes := Projective.G

/-- `bestFftG` requires `[Inhabited G]` (for `Array.get!`); the affine group has a canonical `0`. -/
local instance : Inhabited GVes := ⟨0⟩

/-- The radix-2 DIT group FFT of `bestFftG`, but with the butterfly scalar action abstracted into an
explicit parameter `smul : ℕ → G → G`. Instantiating `smul := (· • ·)` recovers `bestFftG`;
instantiating `smul := Projective.PVes.smulFast` recovers `bestFftGFast`. -/
def bestFftGWith (smul : ℕ → GVes → GVes) (a0 : Array GVes) (omega : Fp) (logN : ℕ) :
    Array GVes := Id.run do
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
    let chunk := 2 * half
    let twiddleChunk := n / chunk
    for c in [0:n / chunk] do
      let s := c * chunk
      for j in [0:half] do
        let twdl := tw[j * twiddleChunk]!
        let aIdx := s + j
        let bIdx := s + half + j
        let aOld := a[aIdx]!
        let t := smul twdl.val a[bIdx]!
        a := a.set! aIdx (aOld + t)
        a := a.set! bIdx (aOld - t)
    half := chunk
  return a

/-- Vesta-concrete fast twin of `bestFftG`: textually identical to `bestFftG`'s body except the
butterfly `twdl.val • a[bIdx]!` becomes `Projective.PVes.smulFast twdl.val a[bIdx]!`. -/
def bestFftGFast (a0 : Array GVes) (omega : Fp) (logN : ℕ) : Array GVes := Id.run do
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
    half := chunk
  return a

/-- `bestFftGFast` is `bestFftGWith` instantiated at the fast projective scalar action (`rfl`: the
bodies coincide after `β`-reducing the `smul` call). -/
theorem bestFftGFast_eq_with (a0 : Array GVes) (omega : Fp) (logN : ℕ) :
    bestFftGFast a0 omega logN = bestFftGWith Projective.PVes.smulFast a0 omega logN := rfl

/-- `bestFftG` (instantiated at Vesta) is `bestFftGWith` at the genuine group action `(· • ·)`
(`rfl`: the bodies coincide after `β`-reducing the `smul` call). -/
theorem bestFftG_eq_with (a0 : Array GVes) (omega : Fp) (logN : ℕ) :
    bestFftG a0 omega logN = bestFftGWith (fun n p => n • p) a0 omega logN := rfl

/-- **Certification of the fast FFT.** `bestFftGFast` computes exactly `bestFftG`: the only
difference is the butterfly scalar action, and `Projective.PVes.smulFast n = (n • ·)` pointwise. -/
theorem bestFftGFast_eq (a0 : Array GVes) (omega : Fp) (logN : ℕ) :
    bestFftGFast a0 omega logN = bestFftG a0 omega logN := by
  rw [bestFftGFast_eq_with, bestFftG_eq_with]
  have hsmul : Projective.PVes.smulFast = (fun n p => n • p : ℕ → GVes → GVes) := by
    funext n p; exact Projective.PVes.smulFast_eq n p
  rw [hsmul]

/-- Fast twin of `derivedUrsGLagrange`, using `bestFftGFast` for the inverse group FFT. -/
def derivedUrsGLagrangeFast (urs : URS GVes) : List GVes :=
  let monomial := List.ofFn urs.g
  let minv : Fp := ((2 : Fp) ^ urs.k)⁻¹
  (bestFftGFast monomial.toArray (omegaInvOf urs.k) urs.k).toList.map
    fun point => minv.val • point

/-- The fast Lagrange derivation agrees with `derivedUrsGLagrange`. -/
theorem derivedUrsGLagrangeFast_eq (urs : URS GVes) :
    derivedUrsGLagrangeFast urs = derivedUrsGLagrange urs := by
  simp only [derivedUrsGLagrangeFast, derivedUrsGLagrange, bestFftGFast_eq]

end Zcash.Snark.Keygen.Fast
