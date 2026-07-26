/-
Copyright (c) 2026 Ironwood Contributors.
Released under the Apache License, Version 2.0.
-/
import Zcash.Snark.Core.Domain
import Zcash.Snark.Core.Group

/-!
# The Rust-mirroring group FFT and the derived Lagrange basis

`bestFftG` is halo2's `best_fft` (`arithmetic.rs:192-256`) over an arbitrary `Fp`-module `G`:
the bit-reversal permutation (`bitreverse`), a precomputed twiddle table, and `log_n` rounds of
decimation-in-time butterflies. `derivedUrsGLagrange` runs it at the inverse root `omegaInvOf`
and scales by `n⁻¹` to obtain the Lagrange-basis generators of a monomial URS
(`Params::new`, `poly/commitment.rs:75-88`).

These are pure arithmetic: they mention only `Fp`, `URS` and the module action, and nothing
from the Clean circuit layer. They live in `Zcash/Arithmetic` so that the fast twins
(`Arithmetic/FastFft.lean`, `Arithmetic/FastFftPar.lean`) and the kernel transplants under
`Zcash/Vendor` can certify against them without importing the keygen pipeline.
`Zcash/Snark/Keygen/Pipeline.lean` imports this file and uses `derivedUrsGLagrange` to build
the Lagrange URS; the DFT specification of `bestFftG` is `Zcash/Snark/Keygen/FftSpec.lean`.
-/

namespace Zcash.Snark.Keygen

open Zcash.Snark

variable {G : Type} [AddCommGroup G] [Inhabited G]

/-! ## Lagrange URS derivation (`poly/commitment.rs:75-88`, `arithmetic.rs:192`) -/

/-- `bitreverse(n, l)` — reverse the low `l` bits of `n` (`best_fft`'s local `bitreverse`,
`arithmetic.rs:193-200`). -/
def bitreverse (n l : ℕ) : ℕ := Id.run do
  let mut r := 0
  let mut m := n
  for _ in [0:l] do
    r := (r <<< 1) ||| (m &&& 1)
    m := m >>> 1
  return r

/-- The size-`2^k` root of unity's inverse, `omega⁻¹ = omega^(2^k − 1)` (order `2^k`).
This is halo2's `alpha_inv` (`ROOT_OF_UNITY_INV` squared `S − k` times,
`poly/commitment.rs:76-79`), computed here from `omegaOf` since both are the same
primitive `2^k`-th root. -/
def omegaInvOf (k : ℕ) : Fp := powFast (omegaOf k) (2 ^ k - 1)

/-- In-place radix-2 DIT FFT over the group `G` with `Fp` twiddles, mirroring
`best_fft(a, omega, log_n)` (`arithmetic.rs:192-256`): bit-reversal permutation, precomputed
twiddle powers `[omega^0 … omega^(n/2−1)]`, then `log_n` rounds of decimation-in-time
butterflies `(a, b) ↦ (a + tw·b, a − tw·b)`. The scalar action `tw·b` is the same
`ZMod.val • point` convention `commitLagrange` uses (Rust's iterative and recursive
`best_fft` branches compute this identical result; we mirror the iterative one,
`arithmetic.rs:223-252`). -/
def bestFftG (a0 : Array G) (omega : Fp) (logN : ℕ) : Array G := Id.run do
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
        let t := twdl.val • a[bIdx]!
        a := a.set! aIdx (aOld + t)
        a := a.set! bIdx (aOld - t)
    half := chunk
  return a

/-- The Lagrange-basis generators derived from a monomial URS by inverse FFT and
`n⁻¹` scaling, exactly as in halo2's `Params::new`. -/
def derivedUrsGLagrange (urs : URS G) : List G :=
  let monomial := List.ofFn urs.g
  let minv : Fp := ((2 : Fp) ^ urs.k)⁻¹
  (bestFftG monomial.toArray (omegaInvOf urs.k) urs.k).toList.map
    fun point => minv.val • point

end Zcash.Snark.Keygen
