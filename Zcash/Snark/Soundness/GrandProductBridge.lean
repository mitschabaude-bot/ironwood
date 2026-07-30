import Mathlib.Tactic
import Zcash.Snark.Soundness.GrandProduct
import Zcash.Snark.Soundness.RunningProduct
import Zcash.Snark.Soundness.Permutation
import Zcash.Snark.Soundness.PermutationConstruction
import Zcash.Snark.Soundness.Constraints

/-!
# From the verifier's product check to the multiset identity

`GrandProduct` proves that a product of linear factors determines a multiset — but over polynomials,
with `β` and `γ` as indeterminates. The verifier does not check a polynomial identity. It checks one
field element, the product evaluated at the two challenges it actually sampled.

This module is that bridge, and it costs two Schwartz–Zippel steps, one per challenge:

* `map_eq_of_prod_eval_eq` — a good `γ` turns the field product identity into equality of the
  multisets of `value + β·name`. The bad set is the roots of the difference in `γ`.
* `multiset_pair_eq_of_map_eq` — a good `β` turns that into equality of the multisets of
  `(value, name)` *pairs*. The bad set is the roots of one coefficient of `pairProdDiff`, the
  difference `prod_pair_inj` shows is nonzero whenever the pairs differ.
* `multiset_pair_eq_of_prod_eval_eq` — the two composed, which is what the permutation argument
  consumes: a product identity at the sampled challenges gives the multiset of pairs that
  `perm_copy_constraints` turns into the copy constraints.

Both bad sets are root sets of nonzero polynomials of degree at most the multiset sizes, so each is
counted by `szBadSet_card_le` exactly like the vanishing check's.

The nested `Polynomial (Polynomial Fp)` differences (`pairProdDiff`, `lookupProdDiff`) carry `β` and
`γ` as separate indeterminates and exist only to be reasoned about. What the bad sets range over is
their coefficient families, which are computable: a `γ` coefficient is an elementary symmetric
polynomial in the `β`-linear encodings, guarded to zero above the multiset size where the monic
product has no coefficients left.
-/

namespace Zcash.Snark

open CompPoly CompPoly.CPolynomial

/-- A monic product of `card` linear factors has no coefficients above `card`. -/
private theorem coeff_prod_X_add_C_eq_zero {R : Type*} [CommRing R] [Nontrivial R]
    {σ : Type*} (m : Multiset σ) (r : σ → R) {j : ℕ} (hj : Multiset.card m < j) :
    ((m.map (fun p => Polynomial.X + Polynomial.C (r p))).prod).coeff j = 0 := by
  refine Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (le_of_eq ?_) hj)
  rw [Polynomial.natDegree_multiset_prod_of_monic]
  · simp [Multiset.map_map]
  · intro f hf
    obtain ⟨p, _, rfl⟩ := Multiset.mem_map.mp hf
    exact Polynomial.monic_X_add_C _

/-- The `β`-linear encoding of a `(value, name)` pair. -/
def encPairC (p : Fp × Fp) : CPoly := C p.1 + C p.2 * X

@[simp] theorem toPoly_encPairC (p : Fp × Fp) : (encPairC p).toPoly = encPair p := by
  simp [encPairC, encPair]

/-- The difference of the two pair-encoded products, a polynomial in `γ` with coefficients in
`Fp[β]`. -/
noncomputable def pairProdDiff (sp tp : Multiset (Fp × Fp)) : Polynomial (Polynomial Fp) :=
  (sp.map (fun p => Polynomial.X + Polynomial.C (encPair p))).prod
    - (tp.map (fun p => Polynomial.X + Polynomial.C (encPair p))).prod

/-- The `j`-th `γ` coefficient of the pair difference: an elementary symmetric polynomial in the
`β`-linear pair encodings on each side, zero above that side's multiset size. -/
def pairProdDiffCoeff (sp tp : Multiset (Fp × Fp)) (j : ℕ) : CPoly :=
  (if j ≤ Multiset.card sp then (sp.map encPairC).esymm (Multiset.card sp - j) else 0)
    - (if j ≤ Multiset.card tp then (tp.map encPairC).esymm (Multiset.card tp - j) else 0)

theorem toPoly_pairProdDiffCoeff (sp tp : Multiset (Fp × Fp)) (j : ℕ) :
    (pairProdDiffCoeff sp tp j).toPoly = (pairProdDiff sp tp).coeff j := by
  rw [pairProdDiffCoeff, toPoly_sub, pairProdDiff, Polynomial.coeff_sub]
  congr 1
  · split <;> rename_i hj
    · rw [toPoly_multiset_esymm, Multiset.prod_X_add_C_coeff' sp encPair hj]
      simp [Multiset.map_map]
    · rw [toPoly_zero, coeff_prod_X_add_C_eq_zero sp encPair (not_le.mp hj)]
  · split <;> rename_i hj
    · rw [toPoly_multiset_esymm, Multiset.prod_X_add_C_coeff' tp encPair hj]
      simp [Multiset.map_map]
    · rw [toPoly_zero, coeff_prod_X_add_C_eq_zero tp encPair (not_le.mp hj)]

/-- The difference is nonzero whenever the multisets of pairs differ — this is `prod_pair_inj` read
contrapositively, and it is what makes the `β` bad set below a genuine root set. -/
theorem pairProdDiff_ne_zero {sp tp : Multiset (Fp × Fp)} (h : sp ≠ tp) :
    pairProdDiff sp tp ≠ 0 :=
  fun h0 => h (prod_pair_inj (sub_eq_zero.mp h0))

/-- The difference of the two `γ`-products once `β` is fixed. -/
def linProdDiff (s t : Multiset Fp) : CPoly :=
  (s.map (fun u => X + C u)).prod - (t.map (fun u => X + C u)).prod

theorem toPoly_linProdDiff (s t : Multiset Fp) :
    (linProdDiff s t).toPoly =
      (s.map (fun u => Polynomial.X + Polynomial.C u)).prod
        - (t.map (fun u => Polynomial.X + Polynomial.C u)).prod := by
  rw [linProdDiff, toPoly_sub, toPoly_multiset_prod, toPoly_multiset_prod]
  simp [Multiset.map_map]

/-- Evaluating a product of linear factors is the product of the shifted points. -/
theorem eval_cprod_X_add_u (m : Multiset Fp) (x : Fp) :
    eval x (m.map (fun u => X + C u)).prod = (m.map (fun u => x + u)).prod := by
  rw [eval_toPoly, toPoly_multiset_prod]
  have hfac : (m.map (fun u => X + C u)).map CPolynomial.toPoly
      = m.map (fun u => Polynomial.X + Polynomial.C u) := by
    simp [Multiset.map_map]
  rw [hfac]
  exact eval_prod_X_add_u m x

/-- **The `γ` step.** A challenge outside the difference's roots turns the verifier's field product
identity into equality of the multisets of `value + β·name`. -/
theorem map_eq_of_prod_eval_eq {sp tp : Multiset (Fp × Fp)} {β γ : Fp}
    (hgoodγ : γ ∉ szBadSet (linProdDiff (sp.map (fun p => p.1 + p.2 * β))
      (tp.map (fun p => p.1 + p.2 * β))))
    (h : (sp.map (fun p => γ + (p.1 + p.2 * β))).prod
       = (tp.map (fun p => γ + (p.1 + p.2 * β))).prod) :
    sp.map (fun p => p.1 + p.2 * β) = tp.map (fun p => p.1 + p.2 * β) := by
  set s := sp.map (fun p => p.1 + p.2 * β) with hs
  set t := tp.map (fun p => p.1 + p.2 * β) with ht
  by_contra hne
  have hD : linProdDiff s t ≠ 0 := by
    rw [Ne, ← toPoly_eq_zero_iff, toPoly_linProdDiff]
    intro h0
    exact hne (prod_X_add_u_inj (sub_eq_zero.mp h0))
  refine (not_mem_szBadSet.mp hgoodγ) hD ?_
  have hsv : (s.map (fun x => γ + x)).prod = (t.map (fun x => γ + x)).prod := by
    simpa [hs, ht, Multiset.map_map, Function.comp_def] using h
  rw [eval_toPoly, toPoly_linProdDiff, Polynomial.eval_sub, eval_prod_X_add_u s γ,
    eval_prod_X_add_u t γ, hsv, sub_self]

/-- **The `β` step.** A challenge outside the roots of every coefficient of `pairProdDiff` turns
equality of the `value + β·name` multisets into equality of the `(value, name)` pairs. -/
theorem multiset_pair_eq_of_map_eq {sp tp : Multiset (Fp × Fp)} {β : Fp}
    (hgoodβ : ∀ j, β ∉ szBadSet (pairProdDiffCoeff sp tp j))
    (h : sp.map (fun p => p.1 + p.2 * β) = tp.map (fun p => p.1 + p.2 * β)) :
    sp = tp := by
  by_contra hne
  have hD : pairProdDiff sp tp ≠ 0 := pairProdDiff_ne_zero hne
  obtain ⟨j, hj⟩ : ∃ j, (pairProdDiff sp tp).coeff j ≠ 0 := by
    by_contra hall
    exact hD (Polynomial.ext fun j => by simpa using not_exists.mp hall j)
  have hjC : pairProdDiffCoeff sp tp j ≠ 0 := by
    rw [Ne, ← toPoly_eq_zero_iff, toPoly_pairProdDiffCoeff]
    exact hj
  refine (not_mem_szBadSet.mp (hgoodβ j)) hjC ?_
  have hmapped : (pairProdDiff sp tp).map (Polynomial.evalRingHom β) = 0 := by
    have hconv : ∀ m : Multiset (Fp × Fp),
        ((m.map (fun p => Polynomial.X + Polynomial.C (encPair p))).prod).map
            (Polynomial.evalRingHom β)
          = ((m.map (fun p => p.1 + p.2 * β)).map
              (fun u => Polynomial.X + Polynomial.C u)).prod := by
      intro m
      rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
      refine congrArg Multiset.prod (Multiset.map_congr rfl fun p _ => ?_)
      simp [encPair, Polynomial.map_add, Polynomial.map_mul]
    rw [pairProdDiff, Polynomial.map_sub, hconv sp, hconv tp, h, sub_self]
  have hcoeff := congrArg (fun q => Polynomial.coeff q j) hmapped
  rw [eval_toPoly, toPoly_pairProdDiffCoeff]
  simpa [Polynomial.coeff_map] using hcoeff

/-- **The bridge.** The verifier's product identity at the sampled challenges gives the multiset of
`(value, name)` pairs, provided both challenges avoid their bad sets. This is what the permutation
argument feeds to `perm_copy_constraints`. -/
theorem multiset_pair_eq_of_prod_eval_eq {sp tp : Multiset (Fp × Fp)} {β γ : Fp}
    (hgoodγ : γ ∉ szBadSet (linProdDiff (sp.map (fun p => p.1 + p.2 * β))
      (tp.map (fun p => p.1 + p.2 * β))))
    (hgoodβ : ∀ j, β ∉ szBadSet (pairProdDiffCoeff sp tp j))
    (h : (sp.map (fun p => γ + (p.1 + p.2 * β))).prod
       = (tp.map (fun p => γ + (p.1 + p.2 * β))).prod) :
    sp = tp :=
  multiset_pair_eq_of_map_eq hgoodβ (map_eq_of_prod_eval_eq hgoodγ h)

/-- The `γ` bad set is small: at most the larger multiset's size. -/
theorem szBadSet_linProdDiff_card_le (s t : Multiset Fp) :
    (szBadSet (linProdDiff s t)).card ≤ max (Multiset.card s) (Multiset.card t) := by
  refine (szBadSet_card_le _).trans ?_
  rw [natDegree_toPoly, toPoly_linProdDiff]
  refine (Polynomial.natDegree_sub_le _ _).trans ?_
  rw [natDegree_prod_X_add_u s, natDegree_prod_X_add_u t]

/-! ## The lookup argument's product

The lookup factors are `(input + β)·(table + γ)` with the two challenges on *separate* columns, not
`value + β·name + γ`. So the product splits into two independent univariate products, and the
kernel applies twice rather than through `encPair`. The `γ`-leading coefficient of the difference is
the difference of the two `β`-products, which is what separates the input columns from the table
columns. -/

/-- The difference of the two lookup products, in `γ` over `Fp[β]`. The input columns enter as
constants in `γ`; the table columns as the linear factors. -/
noncomputable def lookupProdDiff (a s inp tbl : Multiset Fp) : Polynomial (Polynomial Fp) :=
  Polynomial.C (a.map (fun u => Polynomial.X + Polynomial.C u)).prod
      * (s.map (fun u => Polynomial.X + Polynomial.C (Polynomial.C u))).prod
    - Polynomial.C (inp.map (fun u => Polynomial.X + Polynomial.C u)).prod
      * (tbl.map (fun u => Polynomial.X + Polynomial.C (Polynomial.C u))).prod

/-- A `γ` coefficient of the lookup difference, without constructing a nested polynomial. -/
def lookupProdDiffCoeff (a s inp tbl : Multiset Fp) (j : ℕ) : CPoly :=
  (a.map (fun u => X + C u)).prod
      * (if j ≤ Multiset.card s then (s.map C).esymm (Multiset.card s - j) else 0)
    - (inp.map (fun u => X + C u)).prod
      * (if j ≤ Multiset.card tbl then (tbl.map C).esymm (Multiset.card tbl - j) else 0)

theorem toPoly_lookupProdDiffCoeff (a s inp tbl : Multiset Fp) (j : ℕ) :
    (lookupProdDiffCoeff a s inp tbl j).toPoly = (lookupProdDiff a s inp tbl).coeff j := by
  rw [lookupProdDiffCoeff, toPoly_sub, toPoly_mul, toPoly_mul, toPoly_multiset_prod,
    toPoly_multiset_prod, lookupProdDiff, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
    Polynomial.coeff_C_mul]
  have hfac : ∀ m : Multiset Fp,
      (m.map (fun u => X + C u)).map CPolynomial.toPoly
        = m.map (fun u => Polynomial.X + Polynomial.C u) := by
    intro m; simp [Multiset.map_map]
  rw [hfac, hfac]
  congr 1
  · split <;> rename_i hj
    · rw [toPoly_multiset_esymm,
        Multiset.prod_X_add_C_coeff' s (fun u => Polynomial.C u) hj]
      simp [Multiset.map_map]
    · rw [toPoly_zero,
        coeff_prod_X_add_C_eq_zero s (fun u => Polynomial.C u) (not_le.mp hj), MulZeroClass.mul_zero]
  · split <;> rename_i hj
    · rw [toPoly_multiset_esymm,
        Multiset.prod_X_add_C_coeff' tbl (fun u => Polynomial.C u) hj]
      simp [Multiset.map_map]
    · rw [toPoly_zero,
        coeff_prod_X_add_C_eq_zero tbl (fun u => Polynomial.C u) (not_le.mp hj), MulZeroClass.mul_zero]

/-- The lookup difference after fixing `β`, as a polynomial in `γ`. -/
def lookupProdDiffGamma (a s inp tbl : Multiset Fp) (beta : Fp) : CPoly :=
  C (eval beta (a.map (fun u => X + C u)).prod) * (s.map (fun u => X + C u)).prod
    - C (eval beta (inp.map (fun u => X + C u)).prod) * (tbl.map (fun u => X + C u)).prod

theorem toPoly_lookupProdDiffGamma (a s inp tbl : Multiset Fp) (beta : Fp) :
    (lookupProdDiffGamma a s inp tbl beta).toPoly =
      (lookupProdDiff a s inp tbl).map (Polynomial.evalRingHom beta) := by
  have hconv : ∀ m : Multiset Fp,
      ((m.map (fun u => Polynomial.X + Polynomial.C (Polynomial.C u))).prod).map
          (Polynomial.evalRingHom beta) =
        (m.map (fun u => Polynomial.X + Polynomial.C u)).prod := by
    intro m
    rw [Polynomial.map_multiset_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl fun u _ => ?_)
    simp [Polynomial.map_add]
  have hfac : ∀ m : Multiset Fp,
      (m.map (fun u => X + C u)).map CPolynomial.toPoly
        = m.map (fun u => Polynomial.X + Polynomial.C u) := by
    intro m; simp [Multiset.map_map]
  rw [lookupProdDiffGamma, toPoly_sub, toPoly_mul, toPoly_mul, C_toPoly, C_toPoly,
    toPoly_multiset_prod, toPoly_multiset_prod, hfac, hfac, lookupProdDiff,
    Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, hconv s, hconv tbl,
    Polynomial.map_C, Polynomial.map_C]
  rw [eval_toPoly, eval_toPoly, toPoly_multiset_prod, toPoly_multiset_prod, hfac, hfac]
  rfl

/-- Evaluating the lookup difference at the sampled challenges is the verifier's own product
comparison. -/
theorem eval_lookupProdDiff (a s inp tbl : Multiset Fp) (β γ : Fp) :
    eval γ (lookupProdDiffGamma a s inp tbl β)
      = (a.map (fun u => β + u)).prod * (s.map (fun u => γ + u)).prod
        - (inp.map (fun u => β + u)).prod * (tbl.map (fun u => γ + u)).prod := by
  rw [lookupProdDiffGamma]
  simp only [eval_sub, eval_mul, eval_C]
  rw [eval_cprod_X_add_u a β, eval_cprod_X_add_u inp β, eval_cprod_X_add_u s γ,
    eval_cprod_X_add_u tbl γ]

/-- **The lookup product's multiset content.** With both challenges outside their bad sets, the
verifier's field product identity forces the input columns and the table columns to match as
multisets, separately. -/
theorem lookup_multisets_of_prod_eval_eq {a s inp tbl : Multiset Fp} {β γ : Fp}
    (hgoodγ : γ ∉ szBadSet (lookupProdDiffGamma a s inp tbl β))
    (hgoodβ : ∀ j, β ∉ szBadSet (lookupProdDiffCoeff a s inp tbl j))
    (h : (a.map (fun u => β + u)).prod * (s.map (fun u => γ + u)).prod
       = (inp.map (fun u => β + u)).prod * (tbl.map (fun u => γ + u)).prod) :
    lookupProdDiff a s inp tbl = 0 := by
  have hev : eval γ (lookupProdDiffGamma a s inp tbl β) = 0 := by
    rw [eval_lookupProdDiff, h, sub_self]
  have hmap : (lookupProdDiff a s inp tbl).map (Polynomial.evalRingHom β) = 0 := by
    by_contra hne
    refine (not_mem_szBadSet.mp hgoodγ) ?_ hev
    rw [Ne, ← toPoly_eq_zero_iff, toPoly_lookupProdDiffGamma]
    exact hne
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, (lookupProdDiff a s inp tbl).coeff j ≠ 0 := by
    by_contra hall
    exact hne (Polynomial.ext fun j => by simpa using not_exists.mp hall j)
  have hjC : lookupProdDiffCoeff a s inp tbl j ≠ 0 := by
    rw [Ne, ← toPoly_eq_zero_iff, toPoly_lookupProdDiffCoeff]
    exact hj
  refine (not_mem_szBadSet.mp (hgoodβ j)) hjC ?_
  have hcoeff := congrArg (fun q => Polynomial.coeff q j) hmap
  rw [eval_toPoly, toPoly_lookupProdDiffCoeff]
  simpa [Polynomial.coeff_map] using hcoeff

/-- **The lookup product separates the columns.** The `γ`-leading coefficient of each side is that
side's `β`-product, so the difference vanishing forces the input columns to match and then, after
cancelling, the table columns. -/
theorem lookup_multisets_of_diff_eq_zero {a s inp tbl : Multiset Fp}
    (h : lookupProdDiff a s inp tbl = 0) : a = inp ∧ s = tbl := by
  have hmonic : ∀ m : Multiset Fp,
      (m.map (fun u => Polynomial.X + Polynomial.C (Polynomial.C u))).prod.Monic := fun m =>
    Polynomial.monic_multiset_prod_of_monic _ _ fun u _ => Polynomial.monic_X_add_C _
  have hne : ∀ m : Multiset Fp,
      (m.map (fun u => Polynomial.X + Polynomial.C u)).prod ≠ 0 := fun m =>
    (Polynomial.monic_multiset_prod_of_monic _ _ fun u _ => Polynomial.monic_X_add_C u).ne_zero
  have heq : Polynomial.C (a.map (fun u => Polynomial.X + Polynomial.C u)).prod
        * (s.map (fun u => Polynomial.X + Polynomial.C (Polynomial.C u))).prod
      = Polynomial.C (inp.map (fun u => Polynomial.X + Polynomial.C u)).prod
        * (tbl.map (fun u => Polynomial.X + Polynomial.C (Polynomial.C u))).prod :=
    sub_eq_zero.mp h
  have hlead := congrArg Polynomial.leadingCoeff heq
  rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
    Polynomial.leadingCoeff_C, (hmonic s).leadingCoeff, (hmonic tbl).leadingCoeff,
    _root_.mul_one, _root_.mul_one] at hlead
  refine ⟨prod_X_add_u_inj hlead, ?_⟩
  rw [hlead] at heq
  have hCne : (Polynomial.C (inp.map (fun u => Polynomial.X + Polynomial.C u)).prod :
      Polynomial (Polynomial Fp)) ≠ 0 :=
    Polynomial.C_ne_zero.mpr (hne inp)
  have hQ := mul_left_cancel₀ hCne heq
  have hmap : (s.map Polynomial.C).map (fun v => Polynomial.X + Polynomial.C v)
      = s.map (fun u => Polynomial.X + Polynomial.C (Polynomial.C u)) := by
    simp [Multiset.map_map]
  have hmapt : (tbl.map Polynomial.C).map (fun v => Polynomial.X + Polynomial.C v)
      = tbl.map (fun u => Polynomial.X + Polynomial.C (Polynomial.C u)) := by
    simp [Multiset.map_map]
  have hstep : (((s.map Polynomial.C)).map (fun v => Polynomial.X + Polynomial.C v)).prod
      = (((tbl.map Polynomial.C)).map (fun v => Polynomial.X + Polynomial.C v)).prod := by
    rw [hmap, hmapt]; exact hQ
  exact Multiset.map_injective (Polynomial.C_injective (R := Fp)) (prod_X_add_u_inj hstep)

/-! ## The permutation argument, from the row recurrence to the copy constraints

Composing the two halves. `RunningProduct` turns the verifier's per-row recurrence into a product
over every cell; the bridge above turns that product into the multiset of `(value, name)` pairs;
`Soundness.Permutation.perm_copy_constraints` turns the multiset into the copy constraints. One
branch survives all the way: a vanishing factor, meaning the running product ended at zero or a
`value + β·name + γ` collided. It stays in the conclusion rather than being assumed away. -/

/-- The `(value, name)` pair of every cell of an `m × k` table. -/
def cellPairs (m k : ℕ) (value nm : ℕ → ℕ → Fp) : Multiset (Fp × Fp) :=
  (Finset.univ : Finset (Fin m × Fin k)).val.map
    (fun c => (value (c.1 : ℕ) (c.2 : ℕ), nm (c.1 : ℕ) (c.2 : ℕ)))

/-- A cell of a variable-width chunked table: a chunk, a row, and a column valid for that chunk. -/
abbrev ChunkCell (nc m : ℕ) (width : ℕ → ℕ) :=
  Σ c : Fin nc, Fin m × Fin (width c)

/-- The `(value, name)` pair of every cell across a variable-width chunked table. -/
def chunkedCellPairs (nc m : ℕ) (width : ℕ → ℕ)
    (value nm : ℕ → ℕ → ℕ → Fp) : Multiset (Fp × Fp) :=
  (Finset.univ : Finset (ChunkCell nc m width)).val.map
    (fun c => (value c.1 c.2.1 c.2.2, nm c.1 c.2.1 c.2.2))

open Finset in
/-- A product over the cell pairs is the row-by-row product the telescoping produces. -/
theorem prod_map_cellPairs (m k : ℕ) (value nm : ℕ → ℕ → Fp) (f : Fp × Fp → Fp) :
    ((cellPairs m k value nm).map f).prod
      = ∏ i ∈ range m, ∏ j ∈ range k, f (value i j, nm i j) := by
  rw [cellPairs, Multiset.map_map, ← Finset.prod_eq_multiset_prod, Fintype.prod_prod_type]
  simp only [Function.comp_apply]
  rw [← Fin.prod_univ_eq_prod_range (fun i => ∏ j ∈ range k, f (value i j, nm i j)) m]
  exact prod_congr rfl fun i _ => Fin.prod_univ_eq_prod_range
    (fun j => f (value (i : ℕ) j, nm (i : ℕ) j)) k

open Finset in
/-- A product over variable-width chunked cells is the chunk-by-row product used by stitching. -/
theorem prod_map_chunkedCellPairs (nc m : ℕ) (width : ℕ → ℕ)
    (value nm : ℕ → ℕ → ℕ → Fp) (f : Fp × Fp → Fp) :
    ((chunkedCellPairs nc m width value nm).map f).prod
      = ∏ c ∈ range nc, ∏ i ∈ range m, ∏ j ∈ range (width c),
          f (value c i j, nm c i j) := by
  rw [chunkedCellPairs, Multiset.map_map, ← Finset.prod_eq_multiset_prod, Fintype.prod_sigma]
  simp only [Function.comp_apply]
  simp_rw [Fintype.prod_prod_type]
  rw [Fin.prod_univ_eq_prod_range
    (fun c => ∏ i : Fin m, ∏ j : Fin (width c),
      f (value c i j, nm c i j)) nc]
  refine prod_congr rfl fun c _ => ?_
  rw [Fin.prod_univ_eq_prod_range
    (fun i => ∏ j : Fin (width c), f (value c i j, nm c i j)) m]
  refine prod_congr rfl fun i _ => ?_
  exact Fin.prod_univ_eq_prod_range
    (fun j => f (value c i j, nm c i j)) (width c)

open Finset in
/-- **The permutation argument's multiset identity.** The verifier's per-row recurrence on the
running product, with the boundary values it also checks, gives equality of the `(value, name)`
multisets — *either* that, *or* one of the identity-side factors vanished. -/
theorem cellPairs_eq_of_running_product {m k : ℕ} (z : ℕ → Fp)
    (value nm sigmaName : ℕ → ℕ → Fp) (β γ : Fp)
    (hrec : ∀ i < m, z (i + 1) * ∏ j ∈ range k, (value i j + β * sigmaName i j + γ)
        = z i * ∏ j ∈ range k, (value i j + β * nm i j + γ))
    (hz0 : z 0 = 1) (hzm : z m = 0 ∨ z m = 1)
    (hgoodγ : γ ∉ szBadSet (linProdDiff
      ((cellPairs m k value sigmaName).map (fun p => p.1 + p.2 * β))
      ((cellPairs m k value nm).map (fun p => p.1 + p.2 * β))))
    (hgoodβ : ∀ j, β ∉ szBadSet
      (pairProdDiffCoeff (cellPairs m k value sigmaName) (cellPairs m k value nm) j)) :
    cellPairs m k value sigmaName = cellPairs m k value nm
      ∨ ∃ p ∈ range m ×ˢ range k, value p.1 p.2 + β * nm p.1 p.2 + γ = 0 := by
  rcases grandProduct_eq_or_cell_eq_zero z
      (fun i j => value i j + β * nm i j + γ) (fun i j => value i j + β * sigmaName i j + γ)
      hrec hz0 hzm with hprod | hzero
  · refine Or.inl (multiset_pair_eq_of_prod_eval_eq hgoodγ hgoodβ ?_)
    rw [prod_map_cellPairs, prod_map_cellPairs]
    rw [← prod_range_prod_range (fun i j => value i j + β * sigmaName i j + γ),
      ← prod_range_prod_range (fun i j => value i j + β * nm i j + γ)] at hprod
    calc ∏ i ∈ range m, ∏ j ∈ range k, (γ + (value i j + sigmaName i j * β))
        = ∏ i ∈ range m, ∏ j ∈ range k, (value i j + β * sigmaName i j + γ) := by
          exact prod_congr rfl fun i _ => prod_congr rfl fun j _ => by ring
      _ = ∏ i ∈ range m, ∏ j ∈ range k, (value i j + β * nm i j + γ) := hprod
      _ = ∏ i ∈ range m, ∏ j ∈ range k, (γ + (value i j + nm i j * β)) := by
          exact prod_congr rfl fun i _ => prod_congr rfl fun j _ => by ring
  · exact Or.inr hzero

open Finset in
/-- **The variable-width permutation multiset identity.** Per-chunk row recurrences and the
inter-chunk running-product chain give equality of the `(value, name)` multisets over the complete
chunked table, or expose an identity-side factor that vanished. -/
theorem chunkedCellPairs_eq_of_running_product {nc m : ℕ} (width : ℕ → ℕ)
    (Z : ℕ → ℕ → Fp) (value nm sigmaName : ℕ → ℕ → ℕ → Fp) (β γ : Fp)
    (hrec : ∀ c < nc, ∀ i < m,
      Z c (i + 1) * ∏ j ∈ range (width c),
          (value c i j + β * sigmaName c i j + γ)
        = Z c i * ∏ j ∈ range (width c), (value c i j + β * nm c i j + γ))
    (hchain : ∀ c < nc, Z (c + 1) 0 = Z c m)
    (hz0 : Z 0 0 = 1) (hzend : Z nc 0 = 0 ∨ Z nc 0 = 1)
    (hgoodγ : γ ∉ szBadSet (linProdDiff
      ((chunkedCellPairs nc m width value sigmaName).map (fun p => p.1 + p.2 * β))
      ((chunkedCellPairs nc m width value nm).map (fun p => p.1 + p.2 * β))))
    (hgoodβ : ∀ j, β ∉ szBadSet (pairProdDiffCoeff (chunkedCellPairs nc m width value sigmaName) (chunkedCellPairs nc m width value nm) j)) :
    chunkedCellPairs nc m width value sigmaName = chunkedCellPairs nc m width value nm
      ∨ ∃ c ∈ range nc, ∃ i ∈ range m, ∃ j ∈ range (width c),
          value c i j + β * nm c i j + γ = 0 := by
  rcases chunkedGrandProduct_eq_or_cell_eq_zero Z
      (fun c i j => value c i j + β * nm c i j + γ)
      (fun c i j => value c i j + β * sigmaName c i j + γ)
      width hrec hchain hz0 hzend with hprod | hzero
  · refine Or.inl (multiset_pair_eq_of_prod_eval_eq hgoodγ hgoodβ ?_)
    rw [prod_map_chunkedCellPairs, prod_map_chunkedCellPairs]
    calc
      ∏ c ∈ range nc, ∏ i ∈ range m, ∏ j ∈ range (width c),
          (γ + (value c i j + sigmaName c i j * β))
          = ∏ c ∈ range nc, ∏ i ∈ range m, ∏ j ∈ range (width c),
              (value c i j + β * sigmaName c i j + γ) := by
                exact prod_congr rfl fun c _ => prod_congr rfl fun i _ =>
                  prod_congr rfl fun j _ => by ring
      _ = ∏ c ∈ range nc, ∏ i ∈ range m, ∏ j ∈ range (width c),
              (value c i j + β * nm c i j + γ) := hprod
      _ = ∏ c ∈ range nc, ∏ i ∈ range m, ∏ j ∈ range (width c),
          (γ + (value c i j + nm c i j * β)) := by
            exact prod_congr rfl fun c _ => prod_congr rfl fun i _ =>
              prod_congr rfl fun j _ => by ring
  · exact Or.inr hzero

open Finset in
/-- **The copy constraints, from the verifier's checks.** Cells in the same cycle of `σ` hold equal
values. `hσ` says the left-hand names are the `σ`-relabelled ones, `hnm` is the name distinctness the
keygen provides, and the surviving branch is a vanishing factor. This is the permutation argument's
soundness statement with the product step supplied rather than assumed. -/
theorem perm_copy_constraints_of_running_product {m k : ℕ} (z : ℕ → Fp)
    (value nm sigmaName : ℕ → ℕ → Fp) (β γ : Fp) (σ : Equiv.Perm (Fin m × Fin k))
    (hσ : ∀ c : Fin m × Fin k,
      sigmaName (c.1 : ℕ) (c.2 : ℕ) = nm ((σ c).1 : ℕ) ((σ c).2 : ℕ))
    (hnm : Function.Injective fun c : Fin m × Fin k => nm (c.1 : ℕ) (c.2 : ℕ))
    (hrec : ∀ i < m, z (i + 1) * ∏ j ∈ range k, (value i j + β * sigmaName i j + γ)
        = z i * ∏ j ∈ range k, (value i j + β * nm i j + γ))
    (hz0 : z 0 = 1) (hzm : z m = 0 ∨ z m = 1)
    (hgoodγ : γ ∉ szBadSet (linProdDiff
      ((cellPairs m k value sigmaName).map (fun p => p.1 + p.2 * β))
      ((cellPairs m k value nm).map (fun p => p.1 + p.2 * β))))
    (hgoodβ : ∀ j, β ∉ szBadSet
      (pairProdDiffCoeff (cellPairs m k value sigmaName) (cellPairs m k value nm) j))
    {c d : Fin m × Fin k} (hcd : σ.SameCycle c d) :
    value (c.1 : ℕ) (c.2 : ℕ) = value (d.1 : ℕ) (d.2 : ℕ)
      ∨ ∃ p ∈ range m ×ˢ range k, value p.1 p.2 + β * nm p.1 p.2 + γ = 0 := by
  rcases cellPairs_eq_of_running_product z value nm sigmaName β γ hrec hz0 hzm hgoodγ hgoodβ with
    hmulti | hzero
  · have hmulti' : cellPairs m k value nm = cellPairs m k value sigmaName := hmulti.symm
    simp only [cellPairs] at hmulti'
    refine Or.inl (perm_copy_constraints σ hnm (fun c => value (c.1 : ℕ) (c.2 : ℕ)) ?_ hcd)
    calc (Finset.univ : Finset (Fin m × Fin k)).val.map
            (fun c => (value (c.1 : ℕ) (c.2 : ℕ), nm (c.1 : ℕ) (c.2 : ℕ)))
        = (Finset.univ : Finset (Fin m × Fin k)).val.map
            (fun c => (value (c.1 : ℕ) (c.2 : ℕ), sigmaName (c.1 : ℕ) (c.2 : ℕ))) := hmulti'
      _ = _ := Multiset.map_congr rfl fun c _ => by rw [hσ c]
  · exact Or.inr hzero

open Finset in
/-- **Global copy constraints across variable-width chunks.** Unlike the single-chunk wrapper, this
uses the verifier's chain between running products and one permutation over all chunked cells, so
cycles may cross chunk boundaries. -/
theorem perm_copy_constraints_of_chunked_running_product {nc m : ℕ} (width : ℕ → ℕ)
    (Z : ℕ → ℕ → Fp) (value nm sigmaName : ℕ → ℕ → ℕ → Fp) (β γ : Fp)
    (σ : Equiv.Perm (ChunkCell nc m width))
    (hσ : ∀ c : ChunkCell nc m width,
      sigmaName c.1 c.2.1 c.2.2 = nm (σ c).1 (σ c).2.1 (σ c).2.2)
    (hnm : Function.Injective fun c : ChunkCell nc m width => nm c.1 c.2.1 c.2.2)
    (hrec : ∀ c < nc, ∀ i < m,
      Z c (i + 1) * ∏ j ∈ range (width c),
          (value c i j + β * sigmaName c i j + γ)
        = Z c i * ∏ j ∈ range (width c), (value c i j + β * nm c i j + γ))
    (hchain : ∀ c < nc, Z (c + 1) 0 = Z c m)
    (hz0 : Z 0 0 = 1) (hzend : Z nc 0 = 0 ∨ Z nc 0 = 1)
    (hgoodγ : γ ∉ szBadSet (linProdDiff
      ((chunkedCellPairs nc m width value sigmaName).map (fun p => p.1 + p.2 * β))
      ((chunkedCellPairs nc m width value nm).map (fun p => p.1 + p.2 * β))))
    (hgoodβ : ∀ j, β ∉ szBadSet (pairProdDiffCoeff (chunkedCellPairs nc m width value sigmaName) (chunkedCellPairs nc m width value nm) j))
    {c d : ChunkCell nc m width} (hcd : σ.SameCycle c d) :
    value c.1 c.2.1 c.2.2 = value d.1 d.2.1 d.2.2
      ∨ ∃ c ∈ range nc, ∃ i ∈ range m, ∃ j ∈ range (width c),
          value c i j + β * nm c i j + γ = 0 := by
  rcases chunkedCellPairs_eq_of_running_product width Z value nm sigmaName β γ
      hrec hchain hz0 hzend hgoodγ hgoodβ with hmulti | hzero
  · have hmulti' : chunkedCellPairs nc m width value nm
        = chunkedCellPairs nc m width value sigmaName := hmulti.symm
    simp only [chunkedCellPairs] at hmulti'
    refine Or.inl (perm_copy_constraints σ hnm
      (fun c => value c.1 c.2.1 c.2.2) ?_ hcd)
    calc
      (Finset.univ : Finset (ChunkCell nc m width)).val.map
          (fun c => (value c.1 c.2.1 c.2.2, nm c.1 c.2.1 c.2.2))
        = (Finset.univ : Finset (ChunkCell nc m width)).val.map
          (fun c => (value c.1 c.2.1 c.2.2, sigmaName c.1 c.2.1 c.2.2)) := hmulti'
      _ = _ := Multiset.map_congr rfl fun c _ => by rw [hσ c]
  · exact Or.inr hzero


open Finset in
/-- **The circuit's declared equalities are enforced.** The same chain with the permutation taken to
be the one the keygen builds from the circuit's copy constraints: by `build_correct` its cycles are
exactly the classes those constraints force, so the conclusion is about the circuit's own declared
equalities rather than about an arbitrary permutation. -/
theorem declared_equalities_of_running_product {m k : ℕ} (z : ℕ → Fp)
    (value nm sigmaName : ℕ → ℕ → Fp) (β γ : Fp)
    (cs : List ((Fin m × Fin k) × (Fin m × Fin k)))
    (hσ : ∀ c : Fin m × Fin k, sigmaName (c.1 : ℕ) (c.2 : ℕ)
      = nm ((PermConstruction.build cs c).1 : ℕ) ((PermConstruction.build cs c).2 : ℕ))
    (hnm : Function.Injective fun c : Fin m × Fin k => nm (c.1 : ℕ) (c.2 : ℕ))
    (hrec : ∀ i < m, z (i + 1) * ∏ j ∈ range k, (value i j + β * sigmaName i j + γ)
        = z i * ∏ j ∈ range k, (value i j + β * nm i j + γ))
    (hz0 : z 0 = 1) (hzm : z m = 0 ∨ z m = 1)
    (hgoodγ : γ ∉ szBadSet (linProdDiff
      ((cellPairs m k value sigmaName).map (fun p => p.1 + p.2 * β))
      ((cellPairs m k value nm).map (fun p => p.1 + p.2 * β))))
    (hgoodβ : ∀ j, β ∉ szBadSet
      (pairProdDiffCoeff (cellPairs m k value sigmaName) (cellPairs m k value nm) j))
    {x y : Fin m × Fin k} (hxy : Relation.EqvGen (fun u v => (u, v) ∈ cs) x y) :
    value (x.1 : ℕ) (x.2 : ℕ) = value (y.1 : ℕ) (y.2 : ℕ)
      ∨ ∃ p ∈ range m ×ˢ range k, value p.1 p.2 + β * nm p.1 p.2 + γ = 0 :=
  perm_copy_constraints_of_running_product z value nm sigmaName β γ (PermConstruction.build cs)
    hσ hnm hrec hz0 hzm hgoodγ hgoodβ ((PermConstruction.build_correct cs x y).mpr hxy)

end Zcash.Snark
