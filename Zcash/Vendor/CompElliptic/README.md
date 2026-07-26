# Fast Vesta group arithmetic, destined for CompElliptic (temporary)

## Provenance

Unlike `Zcash/Vendor/CompPoly/Montgomery/`, none of this is vendored from elsewhere: it was
**developed in ironwood**, for the Action verifying-key commitment certificate. It lives under
`Zcash/Vendor/` because it is *not* ironwood-specific — it is generic projective Pasta
arithmetic that belongs in **CompElliptic**, and a PR upstreaming it is the next step.

| File | Contents |
|---|---|
| `Projective.lean` | RCB complete addition and the projective Vesta point type (`PVes`) over raw canonical field elements, plus the statement-surface functions the rest of the tree is proven against |
| `Msm.lean` | Pippenger multi-scalar multiplication (bucket method), field-generic |
| `MsmProj.lean` | the projective instantiation of `Msm` |
| `NatKernel.lean` | zero-import (`Nat`-carrier) transplant of the projective arithmetic, ladder, Pippenger and radix-2 DIT FFT |
| `NatKernelEquiv.lean` | proves `NatKernel` equals the statement-surface functions operation for operation |
| `ProjectiveMontDefs.lean` | the same kernel again on eight-limb Montgomery residues; core-only, so it can be native-compiled in the `FastFieldNative` precompiled lane |
| `ProjectiveMontEquiv.lean` | transports the `NatKernel` simulation proofs to the Montgomery kernel |

## Deletion criterion

**Delete this directory** once ironwood's CompElliptic pin provides this code; the only
changes needed then are the import paths. Until then, treat it as upstream-shaped: keep it
free of ironwood-specific assumptions so the eventual PR is a move rather than a rewrite.

## Layering

CompElliptic requires CompPoly upstream. This tree mirrors that dependency direction:

- `Zcash/Vendor/CompElliptic/` **may** import `Zcash/Vendor/CompPoly/`
  (`ProjectiveMontDefs.lean` imports the eight-limb Montgomery field).
- `Zcash/Vendor/CompPoly/` must **never** import `Zcash/Vendor/CompElliptic/`.

Violating that would make the CompPoly migration (#258/#274) depend on the CompElliptic one,
so the two trees could no longer be deleted independently.

The mathlib-side glue that consumes this tree from ironwood's side — the kernel adapters, the
fast FFT drivers and the scalar inverse-DFT bridge — is ironwood-permanent and lives in
`Zcash/Arithmetic/`, not here.
