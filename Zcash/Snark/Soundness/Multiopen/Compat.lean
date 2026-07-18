import Mathlib
import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.Forking.Probability
import Zcash.Snark.Soundness.Multiopen.Decode

/-!
# Compatibility layer for the multiopen decode reconstruction

`fs-adversary` carries the augmented binding reduction as *computed data*
(`NontrivialRelation`, `NontrivialRelation.ofDeployedTree`), whereas the multiopen-decode
development (`Multiopen/Decode.lean`, `Multiopen/Deployed.lean`, `Multiopen/DecodeFixture.lean`)
was written against the *propositional* interface `HasNontrivialRelation` / `deployed_to_acceptV`.

This module re-exposes that propositional interface on top of the structure-based API, ports the two
small spine lemmas the decode proofs need (`Msm.eval_{zero,scale,add}` and
`exists_injective_accepting_of_measure`), and states the decoded-column constraint bridges
(`hasNontrivialRelation_of_two_openings`, `decoded_constraint_of_relation_and_batch`,
`decoded_constraint_of_opening_or_relation`).
-/

namespace Zcash.Snark

namespace Msm

/-- The zero MSM evaluates to the group identity. -/
theorem eval_zero {F G : Type*} [Field F] [AddCommGroup G] [Module F G] (urs : URS G) :
    (Msm.zero urs.k F G).eval urs = 0 := by
  simp [eval, zero]

/-- Scaling an MSM scales its evaluation. -/
theorem eval_scale {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (urs : URS G) (c : F) (m : Msm urs.k F G) :
    (m.scale c).eval urs = c • m.eval urs := by
  simp only [eval, scale, smul_add, Finset.smul_sum, List.smul_sum, List.map_map,
    Function.comp_def, mul_smul]

/-- Adding two MSMs adds their evaluations. -/
theorem eval_add {F G : Type*} [Field F] [AddCommGroup G] [Module F G]
    (urs : URS G) (m₁ m₂ : Msm urs.k F G) :
    (m₁.add m₂).eval urs = m₁.eval urs + m₂.eval urs := by
  simp only [eval, add, add_smul, Finset.sum_add_distrib, List.map_append, List.sum_append]
  abel

end Msm

open scoped ENNReal in
/-- **The single-squeeze forking count.** If one accepting challenge is in hand and the accept event's
uniform measure beats `n / |α|`, then `n + 1` pairwise-distinct accepting challenges exist, with the given
one in slot `0`. The one-challenge analogue of `extractable_of_prob` (there the event is a whole round
*vector* and beating `kerr` forces the `(3,…,3)` tree; here beating `n/|α|` forces `n` rewound accepting
values beside the current one) — the counting core of the multiopen `x₄` rewinding
(`Soundness.Multiopen.Deployed`). -/
theorem exists_injective_accepting_of_measure {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {n : ℕ}
    {acc : α → Prop} [DecidablePred acc] {x₀ : α} (hx₀ : acc x₀)
    (hprob : (n : ℝ≥0∞) / Fintype.card α
      < (PMF.uniformOfFintype α).toOuterMeasure (Finset.univ.filter acc)) :
    ∃ ξ : Fin (n + 1) → α, Function.Injective ξ ∧ ξ 0 = x₀ ∧ ∀ r, acc (ξ r) := by
  have hcard : n < (Finset.univ.filter acc).card := by
    by_contra hle
    push_neg at hle
    have hmono : (PMF.uniformOfFintype α).toOuterMeasure (Finset.univ.filter acc)
        ≤ (n : ℝ≥0∞) / Fintype.card α := by
      rw [uniformOfFintype_toOuterMeasure_finset]
      exact ENNReal.div_le_div_right (by exact_mod_cast hle) _
    exact absurd hprob (not_lt.mpr hmono)
  have hx₀mem : x₀ ∈ Finset.univ.filter acc := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx₀⟩
  have herase : n ≤ ((Finset.univ.filter acc).erase x₀).card := by
    rw [Finset.card_erase_of_mem hx₀mem]
    omega
  obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq herase
  let f : Fin n → α := fun i => (S.equivFin.symm (Fin.cast hScard.symm i) : α)
  have hfinj : Function.Injective f := fun i j hij => by
    have h1 := S.equivFin.symm.injective (Subtype.val_injective hij)
    exact Fin.val_injective (by simpa using congrArg Fin.val h1)
  have hfS : ∀ i, f i ∈ S := fun i => (S.equivFin.symm (Fin.cast hScard.symm i)).2
  refine ⟨Fin.cons x₀ f, ?_, rfl, ?_⟩
  · refine (Fin.cons_injective_iff).mpr ⟨?_, hfinj⟩
    rintro ⟨i, hfi⟩
    exact Finset.ne_of_mem_erase (hS (hfS i)) hfi
  · intro r
    cases r using Fin.cases with
    | zero => simpa using hx₀
    | succ i =>
        have hmem := hS (hfS i)
        have := Finset.mem_of_mem_erase hmem
        simpa using (Finset.mem_filter.mp this).2

section Binding

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- A nontrivial discrete-log relation among the augmented generators `(g, U, W)`: scalars `(a, α, β)`
not all zero with `⟨a, g⟩ + α • U + β • W = 0`. Such a relation always *exists* in a prime-order group;
the content of the reduction below is that breaking binding *produces* one, which DLR hardness forbids. -/
def HasNontrivialRelation {n : ℕ} (g : Fin n → G) (U W : G) : Prop :=
  ∃ (a : Fin n → F) (α β : F), (a ≠ 0 ∨ α ≠ 0 ∨ β ≠ 0) ∧ commitGen g a + α • U + β • W = 0

/-- Bridge from `fs-adversary`'s computed `NontrivialRelation` datum to the propositional
`HasNontrivialRelation`. `commitGen g a` is `∑ i, a i • g i` by definition, so the structure's
`relation` field is the required equation. -/
theorem HasNontrivialRelation.of_nontrivialRelation {n : ℕ} {g : Fin n → G} {U W : G}
    (r : NontrivialRelation (F := F) g U W) : HasNontrivialRelation (F := F) g U W :=
  ⟨r.a, r.α, r.β, r.nontrivial, by simpa [commitGen] using r.relation⟩

/-- The deployed recursion peels to the clean `IpaAcceptV`, or exhibits a nontrivial relation.
Propositional form of `NontrivialRelation.ofDeployedTree`: either the clean IPA transcript accepts,
or the structure-based constructor (fed the negation) yields a relation datum, which
`of_nontrivialRelation` demotes to the `HasNontrivialRelation` branch. Binding enters only as that
branch — the reduction, not an assumed independence. -/
theorem deployed_to_acceptV {U W : G} {z : F} (hz : z ≠ 0)
    {d : ℕ} (g : Fin (2 ^ d) → G) (b : Fin (2 ^ d) → F) (P : G) (v blind : F)
    (t : DeployedIpaTreeV F G d) (h : DeployedIpaAcceptV g b U W z P v blind t) :
    IpaAcceptV g b P v (projTree t) ∨ HasNontrivialRelation (F := F) g U W := by
  classical
  by_cases hacc : IpaAcceptV g b P v (projTree t)
  · exact Or.inl hacc
  · exact Or.inr (HasNontrivialRelation.of_nontrivialRelation
      (NontrivialRelation.ofDeployedTree hz g b P v blind t h hacc))

end Binding

section Decoded

variable {G : Type*} [AddCommGroup G] [Module Fp G]

theorem hasNontrivialRelation_of_two_openings (urs : URS G) {a a' : Fin (2 ^ urs.k) → Fp}
    (hne : a ≠ a') (hcollision : commit urs a = commit urs a') :
    HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  refine ⟨a - a', 0, 0, Or.inl (sub_ne_zero.mpr hne), ?_⟩
  have hsub : commitGen (F := Fp) urs.g (a - a') = commit urs a - commit urs a' := by
    simp only [commit, commitGen, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  rw [hsub, hcollision]
  simp

open Polynomial in
/-- Turn a final multiopen relation plus same-witness batch rewinds into the decoded-column SNARK
relation. This is the terminal constraint-side bridge used by the probability/AGM capstones: the circuit is
checked on columns recovered from the verifier-opened multiopen relation, not through an arbitrary
`decodeAdvice`/`decodeInstance` function. `hquot`/`hgood` are stated for the canonical decode
`decodedCols hbatch` — the family this proof constructs — and are dischargeable only with `x` the opened
point (see the `MultiopenDecode` scope section). -/
theorem decoded_constraint_of_relation_and_batch {urs : URS G} {P : G}
    {b : Fin (2 ^ urs.k) → Fp} {v : Fp}
    {numColumns numAdvice numInstance : ℕ}
    (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp)
    (adviceIndex : Fin numAdvice → Fin numColumns) (instanceIndex : Fin numInstance → Fin numColumns)
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    {a : Fin (2 ^ urs.k) → Fp}
    (hrel : IpaRelation urs P b v a)
    (hbatch : BatchOpeningsForWitness urs b columnCommitments columnEvals a)
    (hquot : quotientCheck
      (combineGates fixedCols (selectedPolys (decodedCols hbatch) adviceIndex)
        (selectedPolys (decodedCols hbatch) instanceIndex) y gates) hpoly deg x)
    (hgood : combineGates fixedCols (selectedPolys (decodedCols hbatch) adviceIndex)
        (selectedPolys (decodedCols hbatch) instanceIndex) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (selectedPolys (decodedCols hbatch) adviceIndex)
        (selectedPolys (decodedCols hbatch) instanceIndex) y gates
          - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a cols,
      SnarkRelationWithDecodedColumns urs P b v columnCommitments columnEvals adviceIndex instanceIndex
        fixedCols y gates hpoly deg a cols → S) :
    S := by
  have hsat : circuitSatViaGates fixedCols
      (selectedPolysDecode (k := urs.k) (decodedCols hbatch) adviceIndex)
      (selectedPolysDecode (k := urs.k) (decodedCols hbatch) instanceIndex) y gates hpoly deg a :=
    circuitSatViaGates_of_check fixedCols
      (selectedPolysDecode (k := urs.k) (decodedCols hbatch) adviceIndex)
      (selectedPolysDecode (k := urs.k) (decodedCols hbatch) instanceIndex) y gates hpoly deg a x
      hquot hgood
  exact hencodes a (decodedCols hbatch)
    { opens := hrel
      batchOpenings := hbatch
      decodedColumns := decodedCols_spec hbatch
      satisfiesCircuit := hsat }

open Polynomial in
/-- Lift an opening-or-DLR terminal capstone to the decoded-column constraint endpoint, provided the
multiopen batch rewinding output is available for the final relation witness. Conditional interface: the
batch family is assumed via `MultiopenRewindForRelation` (see its docstring), and `hquot`/`hgood` are
stated for the canonical decode of the batch supplied at each relation witness. -/
theorem decoded_constraint_of_opening_or_relation {urs : URS G} {P : G}
    {b : Fin (2 ^ urs.k) → Fp} {v : Fp}
    {numColumns numAdvice numInstance : ℕ}
    (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp)
    (adviceIndex : Fin numAdvice → Fin numColumns) (instanceIndex : Fin numInstance → Fin numColumns)
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hopening : (∃ a, IpaRelation urs P b v a) ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (hbatch : MultiopenRewindForRelation urs P b v columnCommitments columnEvals)
    (hquot : ∀ a (hrel : IpaRelation urs P b v a),
      quotientCheck
        (combineGates fixedCols (selectedPolys (decodedCols (hbatch a hrel)) adviceIndex)
          (selectedPolys (decodedCols (hbatch a hrel)) instanceIndex) y gates) hpoly deg x)
    (hgood : ∀ a (hrel : IpaRelation urs P b v a),
      combineGates fixedCols (selectedPolys (decodedCols (hbatch a hrel)) adviceIndex)
          (selectedPolys (decodedCols (hbatch a hrel)) instanceIndex) y gates
        ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (selectedPolys (decodedCols (hbatch a hrel)) adviceIndex)
          (selectedPolys (decodedCols (hbatch a hrel)) instanceIndex) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a cols,
      SnarkRelationWithDecodedColumns urs P b v columnCommitments columnEvals adviceIndex instanceIndex
        fixedCols y gates hpoly deg a cols → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rcases hopening with ⟨a, hrel⟩ | hrel
  · exact Or.inl (decoded_constraint_of_relation_and_batch columnCommitments columnEvals adviceIndex
      instanceIndex fixedCols y gates hpoly deg x hrel (hbatch a hrel) (hquot a hrel) (hgood a hrel)
      hencodes)
  · exact Or.inr hrel

end Decoded

end Zcash.Snark
