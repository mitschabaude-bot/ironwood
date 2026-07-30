import Mathlib.LinearAlgebra.Lagrange
import Zcash.Snark.Soundness.Constraints

/-!
# Canonical row polynomials on the `ω` domain

The verifier-native half of the polynomial/row adapter: the canonical
coefficient-form polynomial interpolating supplied rows on the multiplicative `ω`
domain, its evaluation and degree facts, and the zero-padded public-instance
polynomial. The Clean-facing environments built on top live in
`Zcash.Circuits.Integration.PolynomialEnvironment`.

The constructions are plain `def`s on `Zcash.CPoly`; the interpolation facts are borrowed from
Mathlib's `Lagrange` theory across `toPoly`, which is a ring isomorphism.
-/

namespace Zcash.Snark

open CompPoly CompPoly.CPolynomial

set_option maxHeartbeats 20000

/--
The canonical coefficient-form polynomial whose values on the `omega` domain are
the supplied rows.
-/
def rowBasisPolynomial {n : ℕ} (omega : Fp) (i : Fin n) : CPoly :=
  (List.ofFn fun j : Fin n =>
    if j = i then 1
    else C ((omega ^ (i : ℕ) - omega ^ (j : ℕ))⁻¹) * (X - C (omega ^ (j : ℕ)))).prod

def rowPolynomial {n : ℕ} (omega : Fp) (values : Fin n → Fp) : CPoly :=
  (List.ofFn fun i : Fin n => C (values i) * rowBasisPolynomial omega i).sum

theorem toPoly_rowBasisPolynomial {n : ℕ} (omega : Fp) (i : Fin n) :
    (rowBasisPolynomial omega i).toPoly =
      Lagrange.basis Finset.univ (fun j : Fin n => omega ^ (j : ℕ)) i := by
  rw [rowBasisPolynomial, toPoly_list_prod, List.map_ofFn, List.prod_ofFn]
  simp only [Function.comp_def, apply_ite CPolynomial.toPoly, toPoly_one, toPoly_mul,
    toPoly_sub, C_toPoly, X_toPoly]
  rw [Lagrange.basis]
  simp only [Lagrange.basisDivisor]
  classical
  simp only [Finset.prod_ite, Finset.prod_const_one, _root_.one_mul]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩

theorem toPoly_rowPolynomial {n : ℕ} (omega : Fp) (values : Fin n → Fp) :
    (rowPolynomial omega values).toPoly =
      Lagrange.interpolate Finset.univ (fun i : Fin n => omega ^ (i : ℕ)) values := by
  rw [rowPolynomial, toPoly_list_sum, List.map_ofFn, List.sum_ofFn,
    Lagrange.interpolate_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Function.comp_def, toPoly_mul, C_toPoly, toPoly_rowBasisPolynomial]

/-- A row polynomial evaluates back to the supplied value at every domain row. -/
theorem rowPolynomial_eval {n : ℕ}
    {omega : Fp} {values : Fin n → Fp}
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ))
    (i : Fin n) :
    (rowPolynomial omega values).eval (omega ^ (i : ℕ)) = values i := by
  rw [eval_toPoly, toPoly_rowPolynomial]
  exact Lagrange.eval_interpolate_at_node _ hrows.injOn (Finset.mem_univ i)

/-- A nonempty evaluation-domain row polynomial has degree below the domain size. -/
theorem rowPolynomial_natDegree_lt {n : ℕ}
    {omega : Fp} {values : Fin n → Fp}
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ))
    (hn : 0 < n) :
    (rowPolynomial omega values).natDegree < n := by
  rw [natDegree_toPoly]
  have hdegree :
      (rowPolynomial omega values).toPoly.degree < (n : WithBot ℕ) := by
    have hinterpolate := Lagrange.degree_interpolate_lt
      (s := (Finset.univ : Finset (Fin n)))
      (v := fun i : Fin n => omega ^ (i : ℕ))
      (r := values) hrows.injOn
    simpa [toPoly_rowPolynomial, Finset.card_univ, Fintype.card_fin] using hinterpolate
  by_cases hzero : (rowPolynomial omega values).toPoly = 0
  · rw [hzero, Polynomial.natDegree_zero]
    exact hn
  · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr hdegree

/-- Zero-pad a finite public-instance column to the evaluation-domain size. -/
def zeroPaddedRows {n : ℕ} (values : List Fp) : Fin n → Fp :=
  fun i => values.getD (i : ℕ) 0

/-- The coefficient-form instance polynomial for a zero-padded public column. -/
def instanceRowPolynomial (n : ℕ)
    (omega : Fp) (values : List Fp) : CPoly :=
  rowPolynomial omega (zeroPaddedRows (n := n) values)

/-- The zero-padded instance polynomial reads back the supplied list on every row. -/
theorem instanceRowPolynomial_eval {n : ℕ}
    {omega : Fp} {values : List Fp}
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ))
    (i : Fin n) :
    (instanceRowPolynomial n omega values).eval (omega ^ (i : ℕ)) =
      values.getD (i : ℕ) 0 :=
  rowPolynomial_eval hrows i

end Zcash.Snark
