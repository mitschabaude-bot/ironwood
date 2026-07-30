import Mathlib.Tactic

/-!
# The grand-product-to-multiset kernel (permutation & lookup soundness)

The shared algebraic core that both halo2's permutation and lookup *argument* soundness reduce to.
Both arguments enforce their relation by a **grand product of factors linear in the challenges**, and
the soundness step is the same: such a product, equal at the random challenge, forces the underlying
multiset identity.

This file isolates that core over Mathlib `Polynomial`. Nothing here needs computability. The proof
leans on Mathlib's roots / unique-factorization theory:

* `prod_X_add_u_inj` (**products can represent multisets**): equal products of the monic linear
  factors `X + uᵢ` force equal multisets `{uᵢ}` — a product is determined by its roots.
* `card_eval_prod_eq_le` (**univariate Schwartz–Zippel at a point**): for distinct multisets, the
  challenges where the field products collide form a bad set of size `≤ max |s| |t|`.
* `prod_pair_inj` (**products can represent multisets of pairs**): the same for factors carrying
  `(value, name)` pairs, by running the first lemma over `R = F[β]` — what the permutation
  argument needs; the lookup argument uses `prod_X_add_u_inj` twice with independent `β`, `γ`.

The per-argument wrappers — telescoping the running product over the domain, the boundary / blinding-row
rules, and (for lookup) the permuted-column structure — build on this in `Permutation.lean` /
`Lookup.lean`, where the structural steps are proven and the telescoping step remains open.
-/

namespace Zcash.Snark

open Polynomial

/-- Helper to view `X + u` terms as `X - (-u)`, so that Mathlib lemmas apply. -/
theorem map_X_add_u_eq {R : Type*} [CommRing R] (m : Multiset R) :
    m.map (fun u => X + C u) = (m.map (fun u => -u)).map (fun a => X - C a) := by
  rw [Multiset.map_map]
  exact Multiset.map_congr rfl (fun u _ => by simp [Function.comp, sub_neg_eq_add])

/-- The roots of `∏ (X + uᵢ)` are the negated elements `{-uᵢ}` (over a domain). -/
theorem roots_prod_X_add_u {R : Type*} [CommRing R] [IsDomain R] (m : Multiset R) :
    (m.map (fun u => X + C u)).prod.roots = m.map (fun u => -u) := by
  rw [map_X_add_u_eq, roots_multiset_prod_X_sub_C]

/-- Evaluating the polynomial product at `β` gives the field product of the shifted factors:
`(∏ (X + uᵢ)).eval β = ∏ (β + uᵢ)`. The bridge from the polynomial world (where `prod_X_add_u_inj`
lives) to the verifier's field-element products. -/
theorem eval_prod_X_add_u {R : Type*} [CommRing R] (m : Multiset R) (β : R) :
    ((m.map (fun u => X + C u)).prod).eval β = (m.map (fun x => β + x)).prod := by
  rw [eval_multiset_prod, Multiset.map_map]
  exact congrArg Multiset.prod
    (Multiset.map_congr rfl (fun u _ => by simp [Function.comp, eval_add, eval_X, eval_C]))

/-- `∏ (X + uᵢ)` has degree `|m|` (a product of `|m|` monic linear factors). -/
theorem natDegree_prod_X_add_u {R : Type*} [CommRing R] [IsDomain R] (m : Multiset R) :
    ((m.map (fun u => X + C u)).prod).natDegree = Multiset.card m := by
  rw [map_X_add_u_eq, natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map]

/-- **Multiset-from-product, over an integral domain.**
Products of the monic linear factors `X + uᵢ` are equal iff the multisets of the `uᵢ` agree — the
reusable kernel behind both the permutation and lookup soundness arguments. Idea: over a domain a
product is determined by its roots, here `{-uᵢ}`, and negation is injective. -/
theorem prod_X_add_u_inj {R : Type*} [CommRing R] [IsDomain R] {s t : Multiset R}
    (h : (s.map (fun u => X + C u)).prod = (t.map (fun u => X + C u)).prod) : s = t := by
  have heq : s.map (fun u => -u) = t.map (fun u => -u) := by
    rw [← roots_prod_X_add_u s, ← roots_prod_X_add_u t, h]
  exact Multiset.map_injective neg_injective heq

/-- **Univariate Schwartz–Zippel at a point.** For `s ≠ t` over a finite field, the challenges `β`
at which the shifted-factor products `∏ (xᵢ + β)` agree form a "bad set" of size `≤ max |s| |t|` —
the roots of the (nonzero, by `prod_X_add_u_inj`) difference polynomial. That is, product-equality
at a random `β` forces the multiset identity except on a negligible bad set. -/
theorem card_eval_prod_eq_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {s t : Multiset F} (hst : s ≠ t) :
    (Finset.univ.filter
      (fun β => (s.map (fun x => β + x)).prod = (t.map (fun x => β + x)).prod)).card
      ≤ max (Multiset.card s) (Multiset.card t) := by
  -- the difference polynomial is nonzero, since `s ≠ t` (`prod_X_add_u_inj` contrapositive)
  have hD : (s.map (fun u => X + C u)).prod - (t.map (fun u => X + C u)).prod ≠ 0 :=
    fun h0 => hst (prod_X_add_u_inj (sub_eq_zero.mp h0))
  calc (Finset.univ.filter
          (fun β => (s.map (fun x => β + x)).prod = (t.map (fun x => β + x)).prod)).card
      ≤ ((s.map (fun u => X + C u)).prod
          - (t.map (fun u => X + C u)).prod).roots.toFinset.card := by
        -- every "bad" β is a root of the difference polynomial
        apply Finset.card_le_card
        intro β hβ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hβ
        rw [Multiset.mem_toFinset, mem_roots']
        refine ⟨hD, ?_⟩
        show ((s.map (fun u => X + C u)).prod - (t.map (fun u => X + C u)).prod).eval β = 0
        rw [eval_sub, eval_prod_X_add_u s β, eval_prod_X_add_u t β, hβ, sub_self]
    _ ≤ Multiset.card ((s.map (fun u => X + C u)).prod
          - (t.map (fun u => X + C u)).prod).roots := Multiset.toFinset_card_le _
    _ ≤ ((s.map (fun u => X + C u)).prod - (t.map (fun u => X + C u)).prod).natDegree :=
          card_roots' _
    _ ≤ max ((s.map (fun u => X + C u)).prod).natDegree
            ((t.map (fun u => X + C u)).prod).natDegree := natDegree_sub_le _ _
    _ = max (Multiset.card s) (Multiset.card t) := by
          rw [natDegree_prod_X_add_u s, natDegree_prod_X_add_u t]

/-- Encode a pair `(v, n)` as the `F[β]`-element `v + n·β` (here `β = X` in `Polynomial F`).
Injective, since `v` and `n` are its degree-0 and degree-1 coefficients. -/
noncomputable def encPair {F : Type*} [Field F] (p : F × F) : Polynomial F := C p.1 + C p.2 * X

theorem encPair_injective {F : Type*} [Field F] : Function.Injective (encPair (F := F)) := by
  intro p q hpq
  refine Prod.ext_iff.mpr ⟨?_, ?_⟩
  · simpa [encPair, coeff_add, coeff_C, coeff_C_mul, coeff_X_zero] using
      congrArg (Polynomial.coeff · 0) hpq
  · simpa [encPair, coeff_add, coeff_C, coeff_C_mul, coeff_X_one] using
      congrArg (Polynomial.coeff · 1) hpq

/-- **Multisets of pairs.** `∏ (vᵢ + nᵢ·β + γ) = ∏ (cⱼ + dⱼ·β + γ) ⟹ {(vᵢ,nᵢ)} = {(cⱼ,dⱼ)}`.
The factor `vᵢ + nᵢ·β + γ` is `X + C (encPair (vᵢ,nᵢ))` over `R = F[β]` (variable `X = γ`), so this is
just `prod_X_add_u_inj` over the domain `F[β]` followed by `encPair`-injectivity. This is the multiset
identity the permutation argument needs (pairs of `(value, name)`, not just sums). -/
theorem prod_pair_inj {F : Type*} [Field F] {sp tp : Multiset (F × F)}
    (h : (sp.map (fun p => X + C (encPair p))).prod
       = (tp.map (fun p => X + C (encPair p))).prod) : sp = tp := by
  have conv : ∀ (m : Multiset (F × F)),
      (m.map (fun p => X + C (encPair p))).prod = ((m.map encPair).map (fun u => X + C u)).prod := by
    intro m; simp only [Multiset.map_map, Function.comp_def]
  rw [conv sp, conv tp] at h
  exact Multiset.map_injective encPair_injective (prod_X_add_u_inj h)

end Zcash.Snark
