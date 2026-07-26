import Zcash.Vendor.CompElliptic.NatKernelEquiv
import Zcash.Vendor.CompElliptic.MsmProj
import Zcash.Arithmetic.FastFft

/-!
# Native-lane adapters: the zero-import `NatKernel` behind the keygen spellings

`Zcash.Vendor.CompElliptic.NatKernel` is the core-only twin of the group kernels (RCB addition,
double-and-add, scatter Pippenger, radix-2 FFT over canonical `ℕ` representatives).
This module provides its `ZMod`-typed entry points — coordinates out via `ZMod.val`,
kernel, cast back — and the PROVEN equalities to the statement-surface functions,
chaining the kernel's simulation theorems (`msm_spec`, `fft_spec`) into the existing
`_eq` ladders. The certificate now evaluates the Montgomery lane instead
(`MontKernelAdapter`), whose correctness proofs transport through these entry points;
they are proof infrastructure, not an evaluation path.
-/

namespace Zcash.Snark.Keygen.Fast

open Zcash.Snark
open Zcash.Vendor
open Zcash.Vendor.NatKernel (P3)
open Zcash.Snark.Keygen.Fast.Projective
open Zcash.Snark.Keygen.Fast.Projective.PVes

local instance : Inhabited G := ⟨0⟩

/-- `PVes → P3`: canonical `ℕ` representatives of the projective coordinates. -/
def ofPVes (P : PVes) : P3 := ⟨P.X.val, P.Y.val, P.Z.val⟩

theorem toPVes_ofPVes (P : PVes) : NatKernel.toPVes (ofPVes P) = P := by
  cases P with
  | mk X Y Z =>
    simp only [NatKernel.toPVes, ofPVes]
    rw [ZMod.natCast_rightInverse X, ZMod.natCast_rightInverse Y,
      ZMod.natCast_rightInverse Z]

theorem toG_ofPVes_ofAffine (g : G) : NatKernel.toG (ofPVes (ofAffine g)) = g := by
  rw [NatKernel.toG_eq, Function.comp_apply, toPVes_ofPVes, toAffine_ofAffine]

theorem valid_toPVes_ofPVes_ofAffine (g : G) : Valid (NatKernel.toPVes (ofPVes (ofAffine g))) := by
  rw [toPVes_ofPVes]
  exact valid_ofAffine g

/-- Every `Fp` value's canonical representative is a 256-bit scalar. -/
theorem val_lt_two_pow_256 (a : Fp) : a.val < 2 ^ 256 :=
  lt_of_lt_of_le (ZMod.val_lt a) (by decide)

/-- `commit_lagrange` through the native-lane kernel MSM. -/
def commitLagrangeKernelWith (c : ℕ) (blind : G) (basis : List G)
    (coeffs : List Fp) : G :=
  NatKernel.toG (NatKernel.msm c
    ((coeffs.zip (basis ++ List.replicate (coeffs.length - basis.length) 0)).map
      fun t => (t.1.val, ofPVes (ofAffine t.2)))) + blind

/-- **The kernel committer equals the naive `commit_lagrange` spec.** -/
theorem commitLagrangeKernelWith_eq (c : ℕ) (hc : 0 < c)
    (blind : G) (basis : List G) (coeffs : List Fp) :
    commitLagrangeKernelWith c blind basis coeffs
      = Msm.commitLagrangeSpec blind basis coeffs := by
  unfold commitLagrangeKernelWith
  rw [NatKernel.toG_eq, Function.comp_apply, NatKernel.msm_spec c hc _
    (by intro t ht
        rw [List.mem_map] at ht
        obtain ⟨s, -, rfl⟩ := ht
        exact valid_toPVes_ofPVes_ofAffine s.2)
    (by intro t ht
        rw [List.mem_map] at ht
        obtain ⟨s, -, rfl⟩ := ht
        exact val_lt_two_pow_256 s.1)]
  have hterms :
      ((coeffs.zip (basis ++ List.replicate (coeffs.length - basis.length) 0)).map
          fun t => (t.1.val, ofPVes (ofAffine t.2))).map
        (fun t => (t.1, toAffine (NatKernel.toPVes t.2)))
      = (coeffs.zip (basis ++ List.replicate (coeffs.length - basis.length) 0)).map
          fun t => (t.1.val, t.2) := by
    rw [List.map_map]
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, toPVes_ofPVes, toAffine_ofAffine]
  rw [hterms, Msm.zip_terms_eq, Msm.pippenger_eq_msm c hc, List.map_map]
  rfl

/-- The Lagrange-basis derivation through the native-lane kernel FFT. -/
def derivedUrsGLagrangeKernel (urs : URS G) : List G :=
  let monomial := List.ofFn urs.g
  let minv : Fp := ((2 : Fp) ^ urs.k)⁻¹
  let a0 : Array P3 := (monomial.map fun g => ofPVes (ofAffine g)).toArray
  let tw : Array ℕ :=
    (Array.range (2 ^ urs.k / 2)).map fun i => ((omegaInvOf urs.k) ^ i : Fp).val
  ((NatKernel.fft a0 tw urs.k).map NatKernel.toG).toList.map
    fun point => minv.val • point

/-- **The kernel Lagrange derivation is `derivedUrsGLagrange`.** -/
theorem derivedUrsGLagrangeKernel_eq (urs : URS G) :
    derivedUrsGLagrangeKernel urs = derivedUrsGLagrange urs := by
  simp only [derivedUrsGLagrangeKernel, derivedUrsGLagrange]
  have hfft := NatKernel.fft_spec
    ((List.ofFn urs.g).map fun g => ofPVes (ofAffine g)).toArray
    ((Array.range (2 ^ urs.k / 2)).map
      fun i => ((omegaInvOf urs.k) ^ i : Fp).val)
    (omegaInvOf urs.k) urs.k
    (by intro p hp
        rw [List.mem_toArray, List.mem_map] at hp
        obtain ⟨g, -, rfl⟩ := hp
        exact valid_toPVes_ofPVes_ofAffine g)
    (by simp)
    (by intro i hi
        simp only [List.size_toArray, List.length_map, List.length_ofFn] at hi
        simp [hi])
  rw [hfft]
  have ha0 : (((List.ofFn urs.g).map fun g => ofPVes (ofAffine g)).toArray.map
      NatKernel.toG) = (List.ofFn urs.g).toArray := by
    rw [List.map_toArray, List.map_map]
    refine congrArg List.toArray ?_
    conv_rhs => rw [← List.map_id (List.ofFn urs.g)]
    exact List.map_congr_left fun g _ => toG_ofPVes_ofAffine g
  rw [ha0]

end Zcash.Snark.Keygen.Fast
