import Mathlib.LinearAlgebra.Lagrange
import Zcash.Snark.Soundness.Constraints

/-!
# Canonical row polynomials on the `ω` domain

The verifier-native half of the polynomial/row adapter: the canonical
coefficient-form polynomial interpolating supplied rows on the multiplicative `ω`
domain, its evaluation and degree facts, and the zero-padded public-instance
polynomial. The Clean-facing environments built on top live in
`Zcash.Circuits.Integration.PolynomialEnvironment`.
-/

namespace Zcash.Snark

open Polynomial

set_option maxHeartbeats 20000

/--
The canonical coefficient-form polynomial whose values on the `omega` domain are
the supplied rows.
-/
def rowBasisPolynomial {n : ℕ} (omega : Fp) (i : Fin n) : Polynomial Fp :=
  ComputablePolynomial.prodList (List.ofFn fun j : Fin n =>
    if j = i then ComputablePolynomial.const 1
    else
      ComputablePolynomial.mul
        (ComputablePolynomial.const ((omega ^ (i : ℕ) - omega ^ (j : ℕ))⁻¹))
        (ComputablePolynomial.sub ComputablePolynomial.X
          (ComputablePolynomial.const (omega ^ (j : ℕ)))))

def rowPolynomial {n : ℕ}
    (omega : Fp) (values : Fin n → Fp) : Polynomial Fp :=
  ComputablePolynomial.sumList (List.ofFn fun i : Fin n =>
    ComputablePolynomial.mul (ComputablePolynomial.const (values i))
      (rowBasisPolynomial omega i))

theorem rowBasisPolynomial_eq_lagrange {n : ℕ} (omega : Fp) (i : Fin n) :
    rowBasisPolynomial omega i =
      Lagrange.basis Finset.univ (fun j : Fin n => omega ^ (j : ℕ)) i := by
  rw [rowBasisPolynomial, ComputablePolynomial.prodList_eq, List.prod_ofFn]
  simp only [ComputablePolynomial.const_eq, ComputablePolynomial.mul_eq,
    ComputablePolynomial.sub_eq, ComputablePolynomial.X_eq]
  rw [Lagrange.basis]
  simp only [Lagrange.basisDivisor]
  classical
  simp only [Finset.prod_ite, map_one, Finset.prod_const_one, one_mul]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  exact ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩

theorem rowPolynomial_eq_lagrange {n : ℕ} (omega : Fp) (values : Fin n → Fp) :
    rowPolynomial omega values =
      Lagrange.interpolate Finset.univ (fun i : Fin n => omega ^ (i : ℕ)) values := by
  rw [rowPolynomial, ComputablePolynomial.sumList_eq, List.sum_ofFn,
    Lagrange.interpolate_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [ComputablePolynomial.mul_eq, ComputablePolynomial.const_eq,
    rowBasisPolynomial_eq_lagrange]

/-- A row polynomial evaluates back to the supplied value at every domain row. -/
theorem rowPolynomial_eval {n : ℕ}
    {omega : Fp} {values : Fin n → Fp}
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ))
    (i : Fin n) :
    (rowPolynomial omega values).eval (omega ^ (i : ℕ)) = values i := by
  rw [rowPolynomial_eq_lagrange]
  exact Lagrange.eval_interpolate_at_node _ hrows.injOn (Finset.mem_univ i)

/-- A nonempty evaluation-domain row polynomial has degree below the domain size. -/
theorem rowPolynomial_natDegree_lt {n : ℕ}
    {omega : Fp} {values : Fin n → Fp}
    (hrows : Function.Injective fun i : Fin n => omega ^ (i : ℕ))
    (hn : 0 < n) :
    (rowPolynomial omega values).natDegree < n := by
  have hdegree :
      (rowPolynomial omega values).degree < (n : WithBot ℕ) := by
    have hinterpolate := Lagrange.degree_interpolate_lt
      (s := (Finset.univ : Finset (Fin n)))
      (v := fun i : Fin n => omega ^ (i : ℕ))
      (r := values) hrows.injOn
    simpa [rowPolynomial_eq_lagrange, Finset.card_univ, Fintype.card_fin] using hinterpolate
  by_cases hzero : rowPolynomial omega values = 0
  · rw [hzero, Polynomial.natDegree_zero]
    exact hn
  · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr hdegree

/-- Zero-pad a finite public-instance column to the evaluation-domain size. -/
def zeroPaddedRows {n : ℕ} (values : List Fp) : Fin n → Fp :=
  fun i => values.getD (i : ℕ) 0

/-- The coefficient-form instance polynomial for a zero-padded public column. -/
def instanceRowPolynomial (n : ℕ)
    (omega : Fp) (values : List Fp) : Polynomial Fp :=
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
