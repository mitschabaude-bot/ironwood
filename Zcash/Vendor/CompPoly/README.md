# Vendored CompPoly material (temporary)

This directory holds code that is destined for **CompPoly** and lives here only until the
ironwood pin can provide it. Nothing outside this directory should be added to it, and it
must not import anything from `Zcash/Vendor/CompElliptic/` or from the rest of ironwood.

**Delete this directory** when ironwood's CompPoly pin moves past both
[CompPoly#258](https://github.com/…/CompPoly/pull/258) (the eight-limb Montgomery field) and
[CompPoly#274](https://github.com/…/CompPoly/pull/274) (the scalar FFT); the only changes
needed then are the import paths.

## `Montgomery/` — eight-limb Montgomery field

A **temporary vendoring** of the CompPoly branch `fast_multilimb_fields` (commit `b3850f0`,
https://github.com/…/CompPoly), which adds eight-limb (8 × 32-bit in `UInt64`) Montgomery
arithmetic for 255-bit prime moduli next to the existing single-word `Montgomery/Native32*`.
On landing, the import paths become `Zcash.Vendor.CompPoly.Montgomery.X` →
`CompPoly.Fields.Montgomery.X`, and `Pasta.lean` is dropped (see below).

| File | Upstream original | Change |
|---|---|---|
| `Basic.lean` | `CompPoly/Fields/Montgomery/Basic.lean` | none |
| `Native64x8Defs.lean` | `CompPoly/Fields/Montgomery/Native64x8.lean` (definitions) | split out, `ℕ` → `Nat`, plus the Pasta constants and monomorphic entry points |
| `Native64x8.lean` | `CompPoly/Fields/Montgomery/Native64x8.lean` (theorems) | imports the split-out definitions; two `norm_num` calls dropped (Lean 4.30 vs 4.31 `simp` drift) |
| `Native64x8Mul.lean` | same name | import path; one `norm_num` dropped |
| `Native64x8Field.lean` | same name | import path |
| `Pasta.lean` | `CompPoly/Fields/Pasta/{Basic,Fast}.lean` | **rewritten**: reuses `CompElliptic.Fields.Pasta`'s primes and Pratt certificates instead of vendoring a second copy, so the repo keeps exactly one `Field (ZMod PALLAS_SCALAR_CARD)` instance and the Montgomery carrier bridges directly into `Zcash.Snark.Keygen.Fast.Projective.Fq` |

The definition/proof split exists for the precompiled lane: `Native64x8Defs.lean` imports
nothing beyond Lean core, so it can be native-compiled (`FastFieldNative`) without dragging a
mathlib import closure through codegen. Keep it that way — the OOM note in
`/root/bin/lake-capped` is why. Upstream has since **also** adopted the same
definitions/proofs split, so the vendored copy and upstream have converged on the same
shape; the eventual migration is an import-path rewrite rather than a restructuring.

Namespaces are unchanged from upstream (`Montgomery.Native64x8`); the pinned CompPoly predates
the `Montgomery` directory, so nothing clashes.

## `ScalarFftDefs.lean` — radix-2 DIT FFT over the scalar field

Developed in ironwood, destined for **CompPoly#274**. It is the scalar twin of the group FFT
in `Zcash/Vendor/CompElliptic/ProjectiveMontDefs.lean`: the same bit-reversal-plus-butterflies
loop nest with the group operations replaced by eight-limb Montgomery field operations. Like
`Montgomery/Native64x8Defs.lean` it is core-only, so it can sit in the `FastFieldNative`
precompiled lane. Its correctness proof is *not* here: it is mathlib-side and therefore
ironwood-permanent, in `Zcash/Arithmetic/ScalarFftEquiv.lean`.
