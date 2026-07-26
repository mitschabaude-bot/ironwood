/-
Copyright (c) 2026 Ironwood Contributors.
Released under the Apache License, Version 2.0.
-/
import CompElliptic.Vendor.CompPoly.Montgomery.Native64x8Defs
import CompElliptic.Curves.Pasta.Fast.ProjectiveMontDefs
import Zcash.Vendor.CompPoly.ScalarFftDefs

/-!
# The precompiled native lane

Root module of the `Zcash.FastFieldNative` library: the only `precompileModules` target in this
repository.  It exists so that the shared library Lake emits
(`.lake/build/lib/libZcash_Zcash_FastFieldNative.so`) carries an initializer whose name matches
the library — Lean's dynlib loader derives the expected `initialize_…` symbol from the file name.

The library name is namespaced rather than a bare `FastFieldNative`, which is what the
CompElliptic pin calls its own precompiled lane.  Lean module names are global across the build,
so two `FastFieldNative.lean` roots collide — and they collide *silently*: `lake build` stays
green while Lake emits no ironwood shared object at all and `Zcash.Arithmetic.ScalarFftEquiv`
is handed only the pin's plugin, leaving `ScalarFftDefs` interpreted.  A dotted `lean_lib` name
works fine (the symbol becomes `initialize_Zcash_Zcash_FastFieldNative`) and keeps the two lanes
distinguishable by construction.

Its import closure is core-only by construction: the field definitions
(`CompElliptic.Vendor.CompPoly.Montgomery.Native64x8Defs`), the Vesta point definitions
(`CompElliptic.Curves.Pasta.Fast.ProjectiveMontDefs`) and the scalar FFT
(`Zcash.Vendor.CompPoly.ScalarFftDefs`) import nothing beyond Lean core, so native compilation
stays at a handful of modules instead of a mathlib closure.  The first two are natively
compiled by the pin's own lane and only crossed into here; this library's glob covers just this
root and `ScalarFftDefs`.
-/
