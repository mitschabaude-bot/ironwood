import Mathlib
import Zcash.Snark.Soundness.Forking.Oracle
import Zcash.Snark.Soundness.Forking.Tree

/-!
# Probability form of the forking lemma

The deterministic assembly consumes three accepting continuations at each IPA round. This module
proves when such a tree exists: acceptance above the knowledge-error threshold under uniform
challenges forces a full `(3,…,3)` accepting tree.

The main results are:

* `uniformOfFintype_toOuterMeasure_finset`: a finite event under a uniform distribution has
  probability `|E| / |domain|`.
* `extractable_of_prob`: if acceptance exceeds `kerr / |domain|`, an `Extractable` tree exists.

The proof uses the multi-round `kerr` count directly. It does not compound a per-round cubic loss.
`Forking.Oracle` describes the remaining adversary and random-oracle assumptions.
-/

namespace Zcash.Snark

open scoped ENNReal

variable {α : Type*}

/-- A finite event under the uniform distribution has probability `|E| / |α|`. -/
theorem uniformOfFintype_toOuterMeasure_finset [Fintype α] [Nonempty α] (E : Finset α) :
    (PMF.uniformOfFintype α).toOuterMeasure E = (E.card : ℝ≥0∞) / Fintype.card α := by
  rw [PMF.toOuterMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- A bijection maps the uniform distribution on `A` to the uniform distribution on `B`. -/
theorem map_uniformOfFintype_equiv {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (e : A ≃ B) : (PMF.uniformOfFintype A).map e = PMF.uniformOfFintype B := by
  refine PMF.ext (fun b => ?_)
  rw [PMF.map_apply, tsum_eq_single (e.symm b) (fun a ha => ?_)]
  · simp only [PMF.uniformOfFintype_apply, Equiv.apply_symm_apply, if_pos, Fintype.card_congr e]
  · rw [if_neg]
    intro hb
    exact ha (e.injective ((e.apply_symm_apply b).symm ▸ hb.symm))

/-- Reading a uniform random function at finitely many distinct points gives independent uniform
answers. -/
theorem uniformOfFintype_map_eval_injective {ι T α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq T]
    [Fintype α] [Nonempty α] (φ : ι → T) (hφ : Function.Injective φ) :
    (PMF.uniformOfFintype (↥(Set.range φ) → α)).map (fun O i => O (Equiv.ofInjective φ hφ i))
      = PMF.uniformOfFintype (ι → α) :=
  map_uniformOfFintype_equiv (Equiv.arrowCongr (Equiv.ofInjective φ hφ).symm (Equiv.refl α))

/-- If uniform acceptance exceeds the `kerr` probability, a full accepting fork tree exists. -/
theorem extractable_of_prob [Fintype α] [DecidableEq α] [Zero α] [Nonempty α] {d : ℕ}
    (acc : (Fin d → α) → Prop) [DecidablePred acc]
    (h : (kerr (Fintype.card α) d : ℝ≥0∞) / Fintype.card (Fin d → α)
       < (PMF.uniformOfFintype (Fin d → α)).toOuterMeasure (Finset.univ.filter acc)) :
    Extractable acc := by
  apply extractable_of_kerr_lt
  by_contra hle
  push_neg at hle
  have hmono : (PMF.uniformOfFintype (Fin d → α)).toOuterMeasure (Finset.univ.filter acc)
      ≤ (kerr (Fintype.card α) d : ℝ≥0∞) / Fintype.card (Fin d → α) := by
    rw [uniformOfFintype_toOuterMeasure_finset]
    gcongr
  exact absurd h (not_lt.mpr hmono)

end Zcash.Snark
