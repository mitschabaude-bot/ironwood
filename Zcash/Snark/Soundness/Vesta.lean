import Mathlib.Tactic
import Zcash.Snark.Soundness.Main
import CompElliptic.Curves.Pasta
import CompElliptic.Curves.PastaOrder

/-!
# Vesta support for the deployed verifier

This module pins the verifier group to the actual Vesta curve and supplies the
concrete-to-abstract MSM bridge and IPA witness identities used by the
straight-line soundness stack.

The only structure the `Fp` action needs that the curve does not already carry
is the Vesta group order: every point is `p`-torsion for
`p = scalarFieldOrder`. `CompElliptic` supplies the pinned point-count result.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm Msm.evalNat_eq_eval scalarFieldOrder)
open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass
  CompElliptic.CurveOrder

/-- The deployed verifier group `E_q`, concretely the points of `y² = x³ + 5`. -/
abbrev VestaG := SWPoint Vesta.curve

/-- Every Vesta point is `p`-torsion for `p = scalarFieldOrder`. -/
abbrev VestaOrder : Prop := ∀ P : VestaG, (scalarFieldOrder : ℕ) • P = 0

/-- Derive the Vesta group order from CompElliptic's pinned point count. -/
theorem vestaOrder : VestaOrder := by
  intro P
  have hcard : Nat.card VestaG = scalarFieldOrder := Vesta.card_eq
  rw [← hcard]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_natCard P)

/-- Install the proved Vesta order for the `Fp`-module instance. -/
instance : Fact VestaOrder := ⟨vestaOrder⟩

/-- Give Vesta its scalar-field module structure. -/
instance vestaFpModule [h : Fact VestaOrder] : Module Fp VestaG :=
  AddCommGroup.zmodModule h.out

/-- Natural-scalar MSM evaluation agrees with the module-theoretic evaluation
used by the soundness development. -/
theorem Msm.evalNat_eq_eval_vesta (urs : URS VestaG)
    (m : Msm urs.k Fp VestaG) : m.evalNat urs = m.eval urs :=
  Msm.evalNat_eq_eval urs m

/-- The powers evaluation vector has leading entry `1`. -/
theorem evalVector_zero {F : Type*} [Field F] (k : ℕ) (x : F) :
    evalVector k x 0 = 1 := by
  simp [evalVector]

/-- The IPA witness after folding in the value term and synthetic blinder. -/
def adjustedWitness {k : ℕ} (aMulti s : Fin (2 ^ k) → Fp) (v ξ : Fp) :
    Fin (2 ^ k) → Fp :=
  aMulti - Pi.single 0 v + ξ • s

/-- The adjusted witness commits to halo2's adjusted commitment. -/
theorem commit_adjustedWitness {G : Type*} [AddCommGroup G] [Module Fp G]
    (urs : URS G) (aMulti s : Fin (2 ^ urs.k) → Fp) (v ξ : Fp) :
    commit urs (adjustedWitness aMulti s v ξ) =
      commit urs aMulti - v • urs.g 0 + ξ • commit urs s := by
  have csub : ∀ a a' : Fin (2 ^ urs.k) → Fp,
      commit urs (a - a') = commit urs a - commit urs a' := by
    intro a a'
    simp only [commit, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  rw [adjustedWitness, commit_add, csub, commit_single, commit_smul]

/-- The single-entry value term in the adjusted commitment is `-v • g 0`. -/
theorem sum_getD_single {k : ℕ} {G : Type*} [AddCommGroup G] [Module Fp G]
    (gg : Fin (2 ^ k) → G) (v : Fp) :
    (∑ i, ([-v].getD i.val 0 : Fp) • gg i) = -v • gg 0 := by
  rw [Finset.sum_eq_single (0 : Fin (2 ^ k))]
  · simp
  · intro i _ hi
    have hival : i.val ≠ 0 := Fin.val_ne_zero_iff.mpr hi
    rw [List.getD_eq_default, zero_smul]
    simp only [List.length_cons, List.length_nil, Nat.zero_add]
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

end Zcash.Snark
