import Zcash.Vendor.CompElliptic.ProjectiveMontEquiv
import Zcash.Arithmetic.NatKernelAdapter

/-!
# Native-lane adapters: the eight-limb Montgomery kernel behind the keygen spellings

`Zcash.Vendor.CompElliptic.ProjectiveMontDefs` is the core-only twin of the group kernels (RCB addition,
double-and-add, scatter Pippenger, radix-2 FFT) over the **proven eight-limb Montgomery
field**, compiled to native code through the `FastFieldNative` `precompileModules` leaf.
This module (mathlib-side, NOT in that leaf's glob) provides the `ZMod`-typed entry points
the certificate evaluates — coordinates into Montgomery form, kernel, affine reading back —
and the PROVEN equalities to the statement-surface functions, chaining the kernel's
simulation theorems (`msmM_spec`, `fftM_spec`) into the existing `_eq` ladders.

It is the Montgomery twin of `Zcash.Arithmetic.NatKernelAdapter`, mirroring it
declaration for declaration.
-/

namespace Zcash.Snark.Keygen.Fast

open Zcash.Snark
open Zcash.Vendor
open Zcash.Vendor.ProjectiveMont
open Zcash.Vendor.ProjectiveMont (PM)
open Montgomery.Native64x8
open Zcash.Snark.Keygen.Fast.Projective
open Zcash.Snark.Keygen.Fast.Projective.PVes

local instance : Inhabited G := ⟨0⟩

/-- `PVes → PM`: each coordinate's canonical representative, entered into Montgomery form. -/
def ofPVesM (P : PVes) : PM :=
  ⟨VestaFq.ofNat P.X.val, VestaFq.ofNat P.Y.val, VestaFq.ofNat P.Z.val⟩

theorem wfp_ofPVesM (P : PVes) : WFP (ofPVesM P) :=
  ⟨wf_ofNat (ZMod.val_lt _), wf_ofNat (ZMod.val_lt _), wf_ofNat (ZMod.val_lt _)⟩

theorem toPVesM_ofPVesM (P : PVes) : toPVesM (ofPVesM P) = P := by
  cases P with
  | mk X Y Z =>
    simp only [toPVesM, ofPVesM, PVes.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;>
      rw [montVal_ofNat (ZMod.val_lt _)]
    exacts [ZMod.natCast_rightInverse X, ZMod.natCast_rightInverse Y, ZMod.natCast_rightInverse Z]

theorem toGM_ofPVesM_ofAffine (g : G) : toGM (ofPVesM (ofAffine g)) = g := by
  rw [toGM, toPVesM_ofPVesM, toAffine_ofAffine]

theorem valid_toPVesM_ofPVesM_ofAffine (g : G) : Valid (toPVesM (ofPVesM (ofAffine g))) := by
  rw [toPVesM_ofPVesM]
  exact valid_ofAffine g

/-- Entering Montgomery form and reading back is the identity, pointwise along a list.  Stated
and proved by `rw` alone: the elaborator must never be asked for a *definitional* comparison
across `ofPVesM`, since unfolding it exposes the CIOS rounds. -/
theorem map_toGM_ofPVesM_ofAffine :
    ∀ l : List G, (l.map fun g => ofPVesM (ofAffine g)).map toGM = l
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.map_cons, map_toGM_ofPVesM_ofAffine l, toGM_ofPVesM_ofAffine]

/-- `commit_lagrange` through the Montgomery-lane kernel MSM. -/
def commitLagrangeMontWith (c : ℕ) (blind : G) (basis : List G)
    (coeffs : List Fp) : G :=
  toGM (PM.msm c
    ((coeffs.zip (basis ++ List.replicate (coeffs.length - basis.length) 0)).map
      fun t => (t.1.val, ofPVesM (ofAffine t.2)))) + blind

/-- **The Montgomery committer equals the naive `commit_lagrange` spec.** -/
theorem commitLagrangeMontWith_eq (c : ℕ) (hc : 0 < c)
    (blind : G) (basis : List G) (coeffs : List Fp) :
    commitLagrangeMontWith c blind basis coeffs
      = Msm.commitLagrangeSpec blind basis coeffs := by
  unfold commitLagrangeMontWith
  rw [toGM, ProjectiveMont.msmM_spec c hc _
    (by intro t ht
        rw [List.mem_map] at ht
        obtain ⟨s, -, rfl⟩ := ht
        exact wfp_ofPVesM _)
    (by intro t ht
        rw [List.mem_map] at ht
        obtain ⟨s, -, rfl⟩ := ht
        exact valid_toPVesM_ofPVesM_ofAffine s.2)
    (by intro t ht
        rw [List.mem_map] at ht
        obtain ⟨s, -, rfl⟩ := ht
        exact val_lt_two_pow_256 s.1)]
  have hterms :
      ((coeffs.zip (basis ++ List.replicate (coeffs.length - basis.length) 0)).map
          fun t => (t.1.val, ofPVesM (ofAffine t.2))).map
        (fun t => (t.1, toAffine (toPVesM t.2)))
      = (coeffs.zip (basis ++ List.replicate (coeffs.length - basis.length) 0)).map
          fun t => (t.1.val, t.2) := by
    rw [List.map_map]
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, toPVesM_ofPVesM, toAffine_ofAffine]
  rw [hterms, Msm.zip_terms_eq, Msm.pippenger_eq_msm c hc, List.map_map]
  rfl

/-- The Lagrange-basis derivation through the Montgomery-lane kernel FFT. -/
def derivedUrsGLagrangeMont (urs : URS G) : List G :=
  let monomial := List.ofFn urs.g
  let minv : Fp := ((2 : Fp) ^ urs.k)⁻¹
  let a0 : Array PM := (monomial.map fun g => ofPVesM (ofAffine g)).toArray
  let tw : Array ℕ :=
    (Array.range (2 ^ urs.k / 2)).map fun i => ((omegaInvOf urs.k) ^ i : Fp).val
  ((PM.fft a0 tw urs.k).map toGM).toList.map
    fun point => minv.val • point

/-- **The Montgomery Lagrange derivation is `derivedUrsGLagrange`.** -/
theorem derivedUrsGLagrangeMont_eq (urs : URS G) :
    derivedUrsGLagrangeMont urs = derivedUrsGLagrange urs := by
  simp only [derivedUrsGLagrangeMont, derivedUrsGLagrange]
  have hfft := ProjectiveMont.fftM_spec
    ((List.ofFn urs.g).map fun g => ofPVesM (ofAffine g)).toArray
    ((Array.range (2 ^ urs.k / 2)).map
      fun i => ((omegaInvOf urs.k) ^ i : Fp).val)
    (omegaInvOf urs.k) urs.k
    (by intro p hp
        rw [List.mem_toArray, List.mem_map] at hp
        obtain ⟨g, -, rfl⟩ := hp
        exact wfp_ofPVesM _)
    (by intro p hp
        rw [List.mem_toArray, List.mem_map] at hp
        obtain ⟨g, -, rfl⟩ := hp
        exact valid_toPVesM_ofPVesM_ofAffine g)
    (by simp)
    (by intro i hi
        simp only [List.size_toArray, List.length_map, List.length_ofFn] at hi
        simp [hi])
  rw [hfft]
  have ha0 : (((List.ofFn urs.g).map fun g => ofPVesM (ofAffine g)).toArray.map
      toGM) = (List.ofFn urs.g).toArray := by
    rw [List.map_toArray, map_toGM_ofPVesM_ofAffine]
  rw [ha0]

end Zcash.Snark.Keygen.Fast
