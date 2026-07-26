/-
Copyright (c) 2026 Ironwood Contributors.
Released under the Apache License, Version 2.0.
-/
import Zcash.Vendor.CompPoly.Montgomery.Native64x8Defs

/-!
# The radix-2 DIT FFT over the scalar field: runtime definitions (core-only)

The **scalar** twin of `Zcash.Vendor.CompElliptic.ProjectiveMontDefs`' group FFT: the very same
bit-reversal-plus-butterflies loop nest, with the group operations replaced by the field
operations of the Vesta scalar field (`= PALLAS_BASE_CARD`, the Pallas *base* field in the
Pasta naming) over eight-limb Montgomery residues — a twiddle multiply where the group
version runs a 256-step double-and-add ladder, and field add/sub where it runs complete
projective addition.

The certificate uses it to trade the group-side inverse FFT that builds the derived Lagrange
basis for a scalar-side one on the commitment coefficients
(`Zcash.Snark.Keygen.commitLagrangeSpec_derivedUrsGLagrange`).

Like its group sibling this module is core-only: it is part of the `FastFieldNative`
precompiled lane, so it must import nothing beyond Lean core.  All proofs live in
`Zcash.Arithmetic.ScalarFftEquiv`.
-/

namespace Zcash.Vendor.ScalarMont

open Montgomery.Native64x8 (Limbs8)
open Montgomery.Native64x8.PallasFq

/-- Bit-reversal permutation index (mirrors `PM.bitreverse`). -/
def bitreverse (n l : Nat) : Nat := Id.run do
  let mut r := 0
  let mut m := n
  for _ in [0:l] do
    r := (r <<< 1) ||| (m &&& 1)
    m := m >>> 1
  return r

/-- In-place radix-2 DIT FFT over the scalar field (mirrors `PM.fft` butterfly for butterfly):
bit-reversal permutation, then `logN` rounds of butterflies against the Montgomery-form
twiddles `tw`, with `mul`/`add`/`sub` where the group version has `pnsmul`/`padd`/`pneg`. -/
def fft (a0 : Array Limbs8) (tw : Array Limbs8) (logN : Nat) : Array Limbs8 := Id.run do
  let n := a0.size
  let mut a := a0
  for k in [0:n] do
    let rk := bitreverse k logN
    if k < rk then
      let ak := a[k]!
      let ark := a[rk]!
      a := (a.set! k ark).set! rk ak
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
        let t := mul twdl a[bIdx]!
        a := a.set! aIdx (add aOld t)
        a := a.set! bIdx (sub aOld t)
    half := chunk
  return a

end Zcash.Vendor.ScalarMont
