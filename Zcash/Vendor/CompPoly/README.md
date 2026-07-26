# Vendored CompPoly material (temporary)

This directory holds code that is destined for **CompPoly** and lives here only until the
ironwood pin can provide it. Nothing outside this directory should be added to it, and it
must not import anything from the rest of ironwood.

**Delete this directory** when ironwood's CompPoly pin moves past
[CompPoly#274](https://github.com/…/CompPoly/pull/274) (the scalar FFT); the only changes
needed then are the import paths.

The eight-limb Montgomery field that used to be vendored here as `Montgomery/` now comes from
the CompElliptic pin (`CompElliptic.Vendor.CompPoly.Montgomery.*`, same `Montgomery.Native64x8`
namespaces), which vendors it on the same terms until CompPoly#258 lands.

## `ScalarFftDefs.lean` — radix-2 DIT FFT over the scalar field

Developed in ironwood, destined for **CompPoly#274**. It is the scalar twin of the group FFT
that the CompElliptic pin used to carry: the same bit-reversal-plus-butterflies loop nest with
the group operations replaced by eight-limb Montgomery field operations. Like the pin's
`Native64x8Defs.lean` it is core-only, so it can sit in the `FastFieldNative` precompiled lane.
Keep it that way — codegen runs over the whole import closure, and one mathlib-side import is
what OOM-crashed a 16 GB box on 2026-07-24 (see the note in `/root/bin/lake-capped`). Its
correctness proof is *not* here: it is mathlib-side and therefore ironwood-permanent, in
`Zcash/Arithmetic/ScalarFftEquiv.lean`.

Namespaces here are *not* aligned with upstream yet: CompPoly#274 puts the scalar FFT in
`Montgomery.ScalarFft`, parameterized over the modulus `(q, negInv)` rather than monomorphized
at the Pasta scalar field as this copy is. Aligning is part of the migration, not of the
vendoring.
