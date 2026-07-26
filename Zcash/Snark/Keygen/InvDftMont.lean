/-
Copyright (c) 2026 Ironwood Contributors.
Released under the Apache License, Version 2.0.
-/
import Zcash.Arithmetic.ScalarFftEquiv
import Zcash.Snark.Keygen.InvDft
import Zcash.Arithmetic.MontKernelAdapter
import Zcash.Arithmetic.VestaModule

/-!
# Native-lane adapters: committing through the scalar inverse DFT

`Zcash.Snark.Keygen.commitLagrangeSpec_derivedUrsGLagrange` trades the group-side inverse FFT
that builds the derived Lagrange basis for a scalar-side one on the commitment coefficients.
This module supplies the evaluation-tier spelling of the right-hand side and proves it equal
to the statement surface:

* `invDftScalarsMont` — the scaled inverse DFT run entirely on eight-limb Montgomery
  residues (`ScalarMont.fft`, in the `FastFieldNative` precompiled lane), read back as the
  canonical `ℕ` scalars an MSM consumes.  No `ZMod` inversion appears on the hot path: leaving
  Montgomery form is one reduction (`PallasFq.toLimbs8`).
* `msmMontPre` — the Montgomery-lane MSM against a basis that is **already** in Montgomery
  form, so a nullary sharing site can pay the coordinate conversion once for all columns
  instead of once per column.
* `commitInvDftMontWith` — the two composed: the per-column committer the certificate runs.

Everything is proven against `Fast.Msm.commitLagrangeSpec`, the naive `commit_lagrange`, which
is where the bilinearity theorem lives.
-/

namespace Zcash.Snark.Keygen.Fast

open Zcash.Snark
open Zcash.Vendor
open Zcash.Vendor.ProjectiveMont
open Zcash.Vendor.ProjectiveMont (PM)
open Zcash.Vendor.ScalarMont (WFs montValS)
open Montgomery.Native64x8
open Montgomery.Native64x8 (Limbs8)
open Zcash.Snark.Keygen.Fast.Projective
open Zcash.Snark.Keygen.Fast.Projective.PVes

local instance : Inhabited G := ⟨0⟩

/-! ## The scalar inverse DFT on Montgomery limbs -/

/-- The input array of the scalar FFT: the coefficients entered into Montgomery form. -/
def invDftInputMont (coeffs : List Fp) : Array Limbs8 :=
  (coeffs.map fun e => PallasFq.ofNat e.val).toArray

/-- The twiddle table of the scalar FFT: `ω⁻¹` powers in Montgomery form. -/
def invDftTwiddlesMont (k : ℕ) : Array Limbs8 :=
  (Array.range (2 ^ k / 2)).map fun i => PallasFq.ofNat ((omegaInvOf k ^ i : Fp).val)

/-- The `n⁻¹` scale factor of the inverse DFT, in Montgomery form. -/
def invDftScaleMont (k : ℕ) : Limbs8 := PallasFq.ofNat ((((2 : Fp) ^ k)⁻¹).val)

/-- **The scaled inverse DFT of the coefficients, on the Montgomery lane**, read back as the
canonical `ℕ` scalars of an MSM: the kernel FFT, then the `n⁻¹` scaling as one further
Montgomery multiply, then one Montgomery reduction per cell.

The twiddle table and the scale factor are PARAMETERS, not recomputed from `k`: both are
loop-invariant across the columns of a commitment family, so a caller that commits many
columns shares them through its own nullary definitions. -/
def invDftScalarsMontWith (tw : Array Limbs8) (minv : Limbs8) (k : ℕ)
    (coeffs : List Fp) : List ℕ :=
  ((ScalarMont.fft (invDftInputMont coeffs) tw k).map
    fun x => (PallasFq.toLimbs8 (PallasFq.mul minv x)).toNat).toList

private theorem wfs_of_val (e : Fp) : WFs (PallasFq.ofNat e.val) :=
  ScalarMont.wfs_ofNat (ZMod.val_lt e)

private theorem montValS_of_val (e : Fp) : montValS (PallasFq.ofNat e.val) = e := by
  rw [ScalarMont.montValS_ofNat (ZMod.val_lt e), ZMod.natCast_rightInverse e]

/-- **The Montgomery-lane inverse DFT is `scalarInvDft`**, in canonical `ℕ` form. -/
theorem invDftScalarsMontWith_eq (tw : Array Limbs8) (minv : Limbs8) (k : ℕ)
    (htw : tw = invDftTwiddlesMont k) (hminv : minv = invDftScaleMont k)
    (coeffs : List Fp) (hlen : coeffs.length = 2 ^ k) :
    invDftScalarsMontWith tw minv k coeffs = (scalarInvDft k coeffs).map ZMod.val := by
  subst htw
  subst hminv
  have hsize : (invDftInputMont coeffs).size = 2 ^ k := by
    simp [invDftInputMont, hlen]
  have ha0 : (invDftInputMont coeffs).map montValS = coeffs.toArray := by
    rw [invDftInputMont, List.map_toArray, List.map_map]
    refine congrArg List.toArray ?_
    conv_rhs => rw [← List.map_id coeffs]
    exact List.map_congr_left fun e _ => montValS_of_val e
  have hwtw : ∀ i : ℕ, WFs (invDftTwiddlesMont k)[i]! := by
    intro i
    by_cases hi : i < 2 ^ k / 2
    · rw [getElem!_pos _ i (by simp [invDftTwiddlesMont, hi])]
      simp only [invDftTwiddlesMont, Array.getElem_map, Array.getElem_range]
      exact wfs_of_val _
    · rw [getElem!_neg _ i (by simp [invDftTwiddlesMont]; omega)]
      exact ScalarMont.wfs_default
  have htw : ∀ i, i < (invDftInputMont coeffs).size / 2 →
      montValS (invDftTwiddlesMont k)[i]! = omegaInvOf k ^ i := by
    intro i hi
    rw [hsize] at hi
    rw [getElem!_pos _ i (by simp [invDftTwiddlesMont, hi])]
    simp only [invDftTwiddlesMont, Array.getElem_map, Array.getElem_range]
    exact montValS_of_val _
  obtain ⟨hwfOut, hmap⟩ := ScalarMont.fftS_spec (invDftInputMont coeffs)
    (invDftTwiddlesMont k) (omegaInvOf k) k
    (by intro x hx
        rw [invDftInputMont, List.mem_toArray, List.mem_map] at hx
        obtain ⟨e, -, rfl⟩ := hx
        exact wfs_of_val e)
    hwtw (by simp [invDftTwiddlesMont, hsize]) htw
  rw [ha0] at hmap
  rw [invDftScalarsMontWith, invDftScaleMont, scalarInvDft, List.map_map, ← hmap, Array.toList_map,
    Array.toList_map, List.map_map]
  refine List.map_congr_left fun x hx => ?_
  have hwx : WFs x := hwfOut x (by simpa using hx)
  have hmv : WFs (PallasFq.ofNat ((((2 : Fp) ^ k)⁻¹).val)) := wfs_of_val _
  rw [ScalarMont.toNat_toLimbs8 (ScalarMont.wfs_mul hmv hwx),
    ScalarMont.montValS_mul hmv hwx, montValS_of_val]
  simp only [Function.comp_apply]
  rw [← Nat.cast_smul_eq_nsmul Fp ((((2 : Fp) ^ k)⁻¹).val) (montValS x),
    ZMod.natCast_rightInverse, smul_eq_mul]

/-! ## The MSM against a pre-converted basis -/

/-- The Montgomery-lane MSM against a basis **already** held as Montgomery-form projective
points, plus the blind.  The basis conversion is the caller's, so it can be shared. -/
def msmMontPre (c : ℕ) (blind : G) (basisM : List PM) (scalars : List ℕ) : G :=
  toGM (PM.msm c (scalars.zip basisM)) + blind

/-- **The pre-converted MSM is the naive `commit_lagrange` spec**, for a coefficient list as
long as the basis. -/
theorem msmMontPre_eq (c : ℕ) (hc : 0 < c) (blind : G) (basis : List G) (coeffs : List Fp)
    (hlen : coeffs.length = basis.length) :
    msmMontPre c blind (basis.map fun g => ofPVesM (ofAffine g)) (coeffs.map ZMod.val)
      = Msm.commitLagrangeSpec blind basis coeffs := by
  unfold msmMontPre
  rw [toGM, ProjectiveMont.msmM_spec c hc _
    (by intro t ht
        obtain ⟨-, h2⟩ := List.of_mem_zip ht
        rw [List.mem_map] at h2
        obtain ⟨g, -, hg⟩ := h2
        rw [← hg]
        exact wfp_ofPVesM _)
    (by intro t ht
        obtain ⟨-, h2⟩ := List.of_mem_zip ht
        rw [List.mem_map] at h2
        obtain ⟨g, -, hg⟩ := h2
        rw [← hg]
        exact valid_toPVesM_ofPVesM_ofAffine g)
    (by intro t ht
        obtain ⟨h1, -⟩ := List.of_mem_zip ht
        rw [List.mem_map] at h1
        obtain ⟨e, -, he⟩ := h1
        rw [← he]
        exact val_lt_two_pow_256 e)]
  have hterms :
      ((coeffs.map ZMod.val).zip (basis.map fun g => ofPVesM (ofAffine g))).map
          (fun t => (t.1, toAffine (toPVesM t.2)))
        = (coeffs.zip (basis ++ List.replicate (coeffs.length - basis.length) 0)).map
            fun t => (t.1.val, t.2) := by
    rw [hlen, Nat.sub_self, List.replicate_zero, List.append_nil, List.zip_map, List.map_map]
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, toPVesM_ofPVesM,
      toAffine_ofAffine]
  rw [hterms, Msm.zip_terms_eq, Msm.pippenger_eq_msm c hc, List.map_map]
  rfl

/-- The pre-converted committer at `Fp` coefficients. -/
def commitMontPre (c : ℕ) (blind : G) (basisM : List PM) (coeffs : List Fp) : G :=
  msmMontPre c blind basisM (coeffs.map ZMod.val)

theorem commitMontPre_eq (c : ℕ) (hc : 0 < c) (blind : G) (basis : List G) (coeffs : List Fp)
    (hlen : coeffs.length = basis.length) :
    commitMontPre c blind (basis.map fun g => ofPVesM (ofAffine g)) coeffs
      = Msm.commitLagrangeSpec blind basis coeffs :=
  msmMontPre_eq c hc blind basis coeffs hlen

/-! ## The composed per-column committer -/

/-- **The certificate's per-column committer**: the scalar inverse DFT on the Montgomery lane,
then one MSM against the pre-converted MONOMIAL basis.  No group FFT anywhere. -/
def commitInvDftMontWith (c : ℕ) (tw : Array Limbs8) (minv : Limbs8) (k : ℕ) (blind : G)
    (basisM : List PM) (coeffs : List Fp) : G :=
  msmMontPre c blind basisM (invDftScalarsMontWith tw minv k coeffs)

/-- **The composed committer IS `commit_lagrange` at the derived Lagrange basis** — the
bilinearity theorem, run through the Montgomery lane on both halves. -/
theorem commitInvDftMontWith_eq (c : ℕ) (hc : 0 < c) (tw : Array Limbs8) (minv : Limbs8)
    (urs : URS G) (hk : urs.k ≤ 32) (htw : tw = invDftTwiddlesMont urs.k)
    (hminv : minv = invDftScaleMont urs.k)
    (coeffs : List Fp) (hlen : coeffs.length = 2 ^ urs.k) :
    commitInvDftMontWith c tw minv urs.k urs.w
        ((List.ofFn urs.g).map fun g => ofPVesM (ofAffine g)) coeffs
      = Msm.commitLagrangeSpec urs.w (derivedUrsGLagrange urs) coeffs := by
  haveI := vestaFpModuleDef
  rw [commitInvDftMontWith, invDftScalarsMontWith_eq tw minv urs.k htw hminv coeffs hlen,
    msmMontPre_eq c hc urs.w (List.ofFn urs.g) _
      (by rw [scalarInvDft_length, hlen, List.length_ofFn]),
    ← commitLagrangeSpec_derivedUrsGLagrange urs hk urs.w coeffs hlen]

/-! ## The Lagrange prefix without a group FFT -/

/-- **A prefix of the derived Lagrange basis as monomial MSMs**, on the Montgomery lane: the
`m`-generator prefix costs `m` MSMs against the same pre-converted monomial basis the columns
use, instead of the full `2 ^ k`-point group FFT. -/
theorem take_derivedUrsGLagrange_montPre (c : ℕ) (hc : 0 < c) (urs : URS G) (hk : urs.k ≤ 32)
    (m : ℕ) (hm : m ≤ 2 ^ urs.k) :
    (derivedUrsGLagrange urs).take m
      = List.ofFn fun j : Fin m =>
          commitMontPre c 0 ((List.ofFn urs.g).map fun g => ofPVesM (ofAffine g))
            (lagrangeRow urs.k (j : ℕ)) := by
  haveI := vestaFpModuleDef
  rw [derivedUrsGLagrange_take urs hk m hm]
  refine congrArg List.ofFn (funext fun j => ?_)
  rw [commitMontPre_eq c hc 0 (List.ofFn urs.g) _
    (by rw [lagrangeRow_length, List.length_ofFn])]

end Zcash.Snark.Keygen.Fast
