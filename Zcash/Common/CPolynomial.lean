import Zcash.Arithmetic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import CompPoly.Univariate.ToPoly
import CompPoly.Univariate.Linear
import CompPoly.Univariate.Roots.Enumeration
import CompPoly.Univariate.DivisionCorrectness
import CompPoly.Univariate.Lagrange

/-!
# General theory for the computable polynomial representation

`CompPoly.CPolynomial R` is `{ p : Array R // no trailing zeros }`: a canonical representation, so
`DecidableEq` is available and every ring operation is executable.  `CPolynomial.toPoly` is one
half of a proven ring isomorphism onto Mathlib's `Polynomial R`, which is what lets the two views
be identified freely.

This file collects the theory the Zcash development needs on top of what CompPoly already proves.
Everything in the `CompPoly.CPolynomial` namespace below is stated generically and is intended to
be upstreamed; it is kept here only so the migration does not block on an external repository.
The Zcash-specific part is the `Fp` instantiation at the end.

## Why this exists at all

Mathlib's `Polynomial` instances live in a `noncomputable section`.  A definition that touches
one becomes `noncomputable`, and that marker propagates through every downstream definition
without being visible at any of their definition sites.  Nothing here is `noncomputable`.
-/

namespace CompPoly.CPolynomial

variable {R : Type*}

/-! ## Evaluation algebra

CompPoly proves `eval_C`, `eval_mul`, `eval_one` and `eval_sub`; the additive and `X`/`pow` cases
are proved here.  Together they form a simp set that discharges the evaluation inductions in the
verifier layer without any manual transport to the Mathlib image. -/

@[simp]
theorem eval_zero [Semiring R] [BEq R] [LawfulBEq R] (x : R) :
    (0 : CPolynomial R).eval x = 0 := by
  rw [eval_toPoly, toPoly_zero, Polynomial.eval_zero]

@[simp]
theorem eval_add [Semiring R] [BEq R] [LawfulBEq R] (x : R) (p q : CPolynomial R) :
    (p + q).eval x = p.eval x + q.eval x := by
  rw [eval_toPoly, toPoly_add, Polynomial.eval_add, ← eval_toPoly, ← eval_toPoly]

@[simp]
theorem eval_neg [Ring R] [BEq R] [LawfulBEq R] (x : R) (p : CPolynomial R) :
    (-p).eval x = -p.eval x := by
  rw [eval_toPoly, toPoly_neg, Polynomial.eval_neg, ← eval_toPoly]

@[simp]
theorem eval_X [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (x : R) :
    (X : CPolynomial R).eval x = x := by
  rw [eval_toPoly, X_toPoly, Polynomial.eval_X]

@[simp]
theorem eval_pow [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (x : R) (p : CPolynomial R) (n : ℕ) :
    (p ^ n).eval x = p.eval x ^ n := by
  induction n with
  | zero => simp [eval_one]
  | succ n ih => rw [pow_succ, pow_succ, eval_mul, ih]

theorem eval_finsetSum {ι : Type*} [DecidableEq ι] [CommSemiring R] [BEq R] [LawfulBEq R]
    [Nontrivial R] (s : Finset ι) (f : ι → CPolynomial R) (x : R) :
    (∑ i ∈ s, f i).eval x = ∑ i ∈ s, (f i).eval x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, eval_add, ih]

theorem eval_prod {ι : Type*} [DecidableEq ι] [CommSemiring R] [BEq R] [LawfulBEq R]
    [Nontrivial R] (s : Finset ι) (f : ι → CPolynomial R) (x : R) :
    (∏ i ∈ s, f i).eval x = ∏ i ∈ s, (f i).eval x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [eval_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, eval_mul, ih]

attribute [simp] eval_C eval_mul eval_one eval_sub

/-! ## Transport to the Mathlib image

These are the `simp` lemmas that push `toPoly` inwards, so a goal about the computable
representation becomes a goal about `Polynomial R` in one `simp` call. -/

attribute [simp] toPoly_add toPoly_mul toPoly_sub toPoly_neg toPoly_one toPoly_zero
  C_toPoly X_toPoly

/-- `toPoly` of a list product.  CompPoly has the `Finset` versions (`toPoly_prod`, `toPoly_sum`);
the row-polynomial constructions build their products over `List.ofFn`, where a `Finset` reindexing
would only be noise. -/
theorem toPoly_list_prod [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (l : List (CPolynomial R)) : l.prod.toPoly = (l.map toPoly).prod :=
  map_list_prod (ringEquiv : CPolynomial R ≃+* Polynomial R) l

/-- `toPoly` of a list sum. -/
theorem toPoly_list_sum [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (l : List (CPolynomial R)) : l.sum.toPoly = (l.map toPoly).sum :=
  map_list_sum (ringEquiv : CPolynomial R ≃+* Polynomial R) l

/-- `toPoly` of a multiset product. -/
theorem toPoly_multiset_prod [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (m : Multiset (CPolynomial R)) : m.prod.toPoly = (m.map toPoly).prod :=
  map_multiset_prod (ringEquiv : CPolynomial R ≃+* Polynomial R) m

/-- `toPoly` of a multiset sum. -/
theorem toPoly_multiset_sum [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (m : Multiset (CPolynomial R)) : m.sum.toPoly = (m.map toPoly).sum :=
  map_multiset_sum (ringEquiv : CPolynomial R ≃+* Polynomial R) m

/-- `toPoly` of an elementary symmetric polynomial in a multiset of polynomials.  `Multiset.esymm`
is a sum of products, so it commutes with any ring hom. -/
theorem toPoly_multiset_esymm [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (m : Multiset (CPolynomial R)) (n : ℕ) :
    (m.esymm n).toPoly = (m.map toPoly).esymm n := by
  simp only [Multiset.esymm, Multiset.powersetCard_map, Multiset.map_map, Function.comp_def]
  refine (map_multiset_sum (ringEquiv : CPolynomial R ≃+* Polynomial R) _).trans ?_
  rw [Multiset.map_map]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun t _ => ?_)
  exact map_multiset_prod (ringEquiv : CPolynomial R ≃+* Polynomial R) t

/-- `toPoly` is injective.  CompPoly states this as `toPolyLinearEquiv.injective`, whose hypothesis
is phrased through the bundled coercion; this restates it directly on `toPoly` so callers do not
need a `change` at every use. -/
theorem toPoly_injective [Semiring R] [BEq R] [LawfulBEq R] {p q : CPolynomial R}
    (h : p.toPoly = q.toPoly) : p = q :=
  toPolyLinearEquiv.injective h

/-! ## Coefficients -/

theorem coeff_finsetSum {ι : Type*} [DecidableEq ι] [CommSemiring R] [BEq R] [LawfulBEq R]
    [Nontrivial R] (s : Finset ι) (f : ι → CPolynomial R) (n : ℕ) :
    (∑ i ∈ s, f i).coeff n = ∑ i ∈ s, (f i).coeff n := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, coeff_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, coeff_add, ih]

theorem coeff_eq_zero_of_natDegree_lt [Semiring R] [BEq R] [LawfulBEq R] {p : CPolynomial R}
    {n : ℕ} (h : p.natDegree < n) : p.coeff n = 0 := by
  rw [coeff_toPoly]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rwa [← natDegree_toPoly])

theorem coeff_X_pow [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (k n : ℕ) :
    ((X : CPolynomial R) ^ k).coeff n = if n = k then 1 else 0 := by
  rw [coeff_toPoly, toPoly_pow, X_toPoly, Polynomial.coeff_X_pow]

theorem natDegree_sum_le_of_forall_le {ι : Type*} [DecidableEq ι] [CommSemiring R] [BEq R]
    [LawfulBEq R] [Nontrivial R] (s : Finset ι) (f : ι → CPolynomial R) {n : ℕ}
    (h : ∀ i ∈ s, (f i).natDegree ≤ n) : (∑ i ∈ s, f i).natDegree ≤ n := by
  rw [natDegree_toPoly, toPoly_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
  rw [← natDegree_toPoly]
  exact h i hi

theorem natDegree_le_iff_coeff_eq_zero [Semiring R] [BEq R] [LawfulBEq R]
    {p : CPolynomial R} {n : ℕ} :
    p.natDegree ≤ n ↔ ∀ m : ℕ, n < m → p.coeff m = 0 := by
  rw [natDegree_toPoly, Polynomial.natDegree_le_iff_coeff_eq_zero]
  exact forall_congr' fun m => forall_congr' fun _ => by rw [coeff_toPoly]

/-! ## Degree arithmetic -/

theorem natDegree_sub_le [Ring R] [BEq R] [LawfulBEq R] (p q : CPolynomial R) :
    (p - q).natDegree ≤ max p.natDegree q.natDegree := by
  rw [natDegree_toPoly, natDegree_toPoly, natDegree_toPoly, toPoly_sub]
  exact Polynomial.natDegree_sub_le _ _

theorem natDegree_mul_le [Semiring R] [BEq R] [LawfulBEq R] {p q : CPolynomial R} :
    (p * q).natDegree ≤ p.natDegree + q.natDegree := by
  rw [natDegree_toPoly, natDegree_toPoly, natDegree_toPoly, toPoly_mul]
  exact Polynomial.natDegree_mul_le

theorem natDegree_X_pow_le [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (n : ℕ) :
    ((X : CPolynomial R) ^ n).natDegree ≤ n := by
  rw [natDegree_toPoly, toPoly_pow, X_toPoly]
  simp

theorem natDegree_one_le [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] :
    (1 : CPolynomial R).natDegree ≤ 0 := by
  rw [natDegree_toPoly, toPoly_one]
  simp

@[simp]
theorem natDegree_zero [Semiring R] [BEq R] [LawfulBEq R] :
    (0 : CPolynomial R).natDegree = 0 := by
  rw [natDegree_toPoly, toPoly_zero, Polynomial.natDegree_zero]

@[simp]
theorem natDegree_one [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] :
    (1 : CPolynomial R).natDegree = 0 := by
  rw [natDegree_toPoly, toPoly_one, Polynomial.natDegree_one]

@[simp]
theorem natDegree_X [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] :
    (X : CPolynomial R).natDegree = 1 := by
  rw [natDegree_toPoly, X_toPoly, Polynomial.natDegree_X]

theorem natDegree_X_le [Semiring R] [BEq R] [LawfulBEq R] [Nontrivial R] :
    (X : CPolynomial R).natDegree ≤ 1 := natDegree_X.le

@[simp]
theorem natDegree_neg [Ring R] [BEq R] [LawfulBEq R] (p : CPolynomial R) :
    (-p).natDegree = p.natDegree := by
  rw [natDegree_toPoly, natDegree_toPoly, toPoly_neg, Polynomial.natDegree_neg]

theorem natDegree_pow_le [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    {p : CPolynomial R} {n : ℕ} : (p ^ n).natDegree ≤ n * p.natDegree := by
  rw [natDegree_toPoly, natDegree_toPoly, toPoly_pow]
  exact Polynomial.natDegree_pow_le

theorem natDegree_C_mul_le [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (a : R) (p : CPolynomial R) : (C a * p).natDegree ≤ p.natDegree := by
  rw [natDegree_toPoly, natDegree_toPoly, toPoly_mul, C_toPoly]
  exact Polynomial.natDegree_C_mul_le a p.toPoly

theorem natDegree_prod_le {ι : Type*} [DecidableEq ι] [CommSemiring R] [BEq R] [LawfulBEq R]
    [Nontrivial R] (s : Finset ι) (f : ι → CPolynomial R) :
    (∏ i ∈ s, f i).natDegree ≤ ∑ i ∈ s, (f i).natDegree := by
  rw [natDegree_toPoly, toPoly_prod]
  simpa [natDegree_toPoly] using Polynomial.natDegree_prod_le s (fun i => (f i).toPoly)

theorem natDegree_sum_le {ι : Type*} [DecidableEq ι] [Semiring R] [BEq R] [LawfulBEq R]
    (s : Finset ι) (f : ι → CPolynomial R) :
    (∑ i ∈ s, f i).natDegree ≤ s.fold max 0 fun i => (f i).natDegree := by
  rw [natDegree_toPoly, toPoly_sum]
  simpa [Function.comp_def, natDegree_toPoly] using
    Polynomial.natDegree_sum_le s (fun i => (f i).toPoly)

/-! ## Divisibility and division by a monic polynomial

`toPoly` is a ring isomorphism, so divisibility transports.  `modByMonic` is CompPoly's own
executable remainder; the algebra it satisfies is Mathlib's, read across the isomorphism. -/

theorem dvd_iff_toPoly_dvd [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    {p q : CPolynomial R} : p ∣ q ↔ p.toPoly ∣ q.toPoly :=
  (map_dvd_iff (ringEquiv : CPolynomial R ≃+* Polynomial R)).symm

theorem zero_modByMonic [Field R] [BEq R] [LawfulBEq R] {r : CPolynomial R} (hr : r.monic) :
    modByMonic 0 r = 0 := by
  apply toPoly_injective
  simp [modByMonic_toPoly_eq_modByMonic _ _ hr, Polynomial.zero_modByMonic]

theorem add_modByMonic [Field R] [BEq R] [LawfulBEq R] (p q : CPolynomial R)
    {r : CPolynomial R} (hr : r.monic) :
    modByMonic (p + q) r = modByMonic p r + modByMonic q r := by
  apply toPoly_injective
  simp only [toPoly_add, modByMonic_toPoly_eq_modByMonic _ _ hr, Polynomial.add_modByMonic]

theorem C_mul_modByMonic [Field R] [BEq R] [LawfulBEq R] (a : R) (p : CPolynomial R)
    {r : CPolynomial R} (hr : r.monic) :
    modByMonic (C a * p) r = C a * modByMonic p r := by
  apply toPoly_injective
  simp only [toPoly_mul, C_toPoly, modByMonic_toPoly_eq_modByMonic _ _ hr,
    ← Polynomial.smul_eq_C_mul, Polynomial.smul_modByMonic]

theorem modByMonic_eq_zero_iff_dvd [Field R] [BEq R] [LawfulBEq R] {p r : CPolynomial R}
    (hr : r.monic) : modByMonic p r = 0 ↔ r ∣ p := by
  rw [← toPoly_eq_zero_iff, modByMonic_toPoly_eq_modByMonic _ _ hr, dvd_iff_toPoly_dvd]
  exact Polynomial.modByMonic_eq_zero_iff_dvd ((monic_toPoly_iff r).mp hr)

/-! ## Bundled homomorphisms

Mathlib's `Polynomial.C` and `Polynomial.evalRingHom` are bundled; CompPoly's `C` and `eval` are
bare functions.  Every `eval₂`-shaped construction, and every ring-hom transport in the verifier
layer, needs the bundled forms. -/

/-- The constant embedding as a ring hom. -/
def CRingHom [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] : R →+* CPolynomial R where
  toFun := C
  map_one' := by apply toPoly_injective; simp
  map_mul' := by intro a b; apply toPoly_injective; simp
  map_zero' := by apply toPoly_injective; simp
  map_add' := by intro a b; apply toPoly_injective; simp

/-- `C` is multiplicative and respects powers.  The bundled `CRingHom` says so; these are the
unbundled spellings.  Deliberately not `simp`: pushing `C` inwards turns `C (ω ^ m)` into
`C ω ^ m`, which no longer matches the rotation lemmas. -/
theorem C_mul [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (a b : R) :
    (C (a * b) : CPolynomial R) = C a * C b := by
  apply toPoly_injective; simp

@[simp]
theorem C_add [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (a b : R) :
    (C (a + b) : CPolynomial R) = C a + C b := by
  apply toPoly_injective; simp

theorem C_pow [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (a : R) (n : ℕ) :
    (C (a ^ n) : CPolynomial R) = C a ^ n := by
  apply toPoly_injective; simp [toPoly_pow]

attribute [simp] natDegree_C

@[simp]
theorem coe_CRingHom [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] :
    ⇑(CRingHom : R →+* CPolynomial R) = C := rfl

/-- Evaluation at `x` as a ring hom. -/
def evalRingHom [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (x : R) :
    CPolynomial R →+* R where
  toFun := eval x
  map_one' := eval_one x
  map_mul' := fun p q => eval_mul p q x
  map_zero' := eval_zero x
  map_add' := eval_add x

@[simp]
theorem coe_evalRingHom [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (x : R) :
    ⇑(evalRingHom x) = eval x := rfl

/-! ## Composition

CompPoly has `eval₂` but no `comp`.  With the constant embedding bundled, composition is `eval₂`
at that hom, and the Mathlib characterisation follows from `eval₂_toPoly` together with
`Polynomial.hom_eval₂` transported along `ringEquiv`. -/

/-- Polynomial composition: `comp p q` is `p ∘ q`. -/
def comp [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] (p q : CPolynomial R) :
    CPolynomial R :=
  eval₂ CRingHom q p

theorem toPoly_comp [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p q : CPolynomial R) : (comp p q).toPoly = p.toPoly.comp q.toPoly := by
  have hring :
      ((ringEquiv : CPolynomial R ≃+* Polynomial R) : CPolynomial R →+* Polynomial R).comp
          CRingHom = Polynomial.C := by
    refine RingHom.ext fun c => ?_
    show (C c : CPolynomial R).toPoly = Polynomial.C c
    exact C_toPoly c
  rw [comp, eval₂_toPoly]
  have h := Polynomial.hom_eval₂ p.toPoly CRingHom
    ((ringEquiv : CPolynomial R ≃+* Polynomial R) : CPolynomial R →+* Polynomial R) q
  rw [hring] at h
  exact h.trans rfl

theorem eval_comp [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p q : CPolynomial R) (x : R) :
    (comp p q).eval x = p.eval (eval x q) := by
  rw [eval_toPoly, toPoly_comp, Polynomial.eval_comp, ← eval_toPoly, ← eval_toPoly]

theorem natDegree_comp [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] [NoZeroDivisors R]
    (p q : CPolynomial R) :
    (comp p q).natDegree = p.natDegree * q.natDegree := by
  rw [natDegree_toPoly, toPoly_comp, Polynomial.natDegree_comp, ← natDegree_toPoly,
    ← natDegree_toPoly]

/-! ## Rotation

Composition with `C w * X` is the column rotation the halo2 verifier performs; it is worth naming
because both of its properties are used at every rotated-column site. -/

/-- Evaluating a rotated column rescales the point. -/
theorem eval_comp_C_mul_X [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
    (p : CPolynomial R) (w x : R) :
    (comp p (C w * X)).eval x = p.eval (w * x) := by
  rw [eval_comp, eval_mul, eval_C, eval_X]

/-- Rotation by a nonzero factor preserves degree. -/
theorem natDegree_comp_C_mul_X [Field R] [DecidableEq R] [BEq R] [LawfulBEq R]
    (p : CPolynomial R) {w : R} (hw : w ≠ 0) :
    (comp p (C w * X)).natDegree = p.natDegree := by
  have hq : ((C w * X : CPolynomial R)).natDegree = 1 := by
    rw [natDegree_toPoly, toPoly_mul, C_toPoly, X_toPoly, Polynomial.natDegree_C_mul hw,
      Polynomial.natDegree_X]
  rw [natDegree_comp, hq, Nat.mul_one]

/-! ## Roots

`Polynomial.roots` is a `Multiset` obtained by repeated factorisation and is `noncomputable`.  Over
an enumerable field the set of *distinct* roots is a filter over the enumeration, so it can be a
plain `def`.  Keeping it computable costs nothing and means it can never poison a downstream
definition — the failure mode that motivated this migration.

To be clear about what "computable" buys: nobody *runs* this.  The enumeration has
`scalarFieldOrder` elements, so evaluating it would exhaust memory.  It only ever appears inside
`Prop`s, where the bad-set predicate is decided by a single evaluation instead
(`Zcash.Snark.decidableMemSzBadSet`).  The point is that a `def` mentioning it stays a `def`.

The guard at zero preserves Mathlib's convention that the zero polynomial has no roots, which is
what makes `roots_eq_toFinset` an unconditional equality. -/

open Roots.FiniteField in
/-- The distinct roots of a computable polynomial over an enumerated field. -/
def rootsBy [Field R] [DecidableEq R] [BEq R] [LawfulBEq R] (e : FieldEnumeration R)
    (p : CPolynomial R) : Finset R :=
  if p = 0 then ∅ else (rootsInFieldByEnumeration e p).toList.toFinset

open Roots.FiniteField in
@[simp]
theorem rootsBy_zero [Field R] [DecidableEq R] [BEq R] [LawfulBEq R] (e : FieldEnumeration R) :
    rootsBy e (0 : CPolynomial R) = ∅ := by
  simp [rootsBy]

open Roots.FiniteField in
theorem mem_rootsBy [Field R] [DecidableEq R] [BEq R] [LawfulBEq R] {e : FieldEnumeration R}
    {p : CPolynomial R} {x : R} (hp : p ≠ 0) :
    x ∈ rootsBy e p ↔ p.eval x = 0 := by
  rw [rootsBy, if_neg hp, List.mem_toFinset]
  exact ⟨fun h => rootsInFieldByEnumeration_sound h,
    fun h => rootsInFieldByEnumeration_complete _ h⟩

open Roots.FiniteField in
/-- The bridge to the Mathlib image: the two agree, so every Mathlib root theorem transfers. -/
theorem rootsBy_eq_toFinset [Field R] [DecidableEq R] [BEq R] [LawfulBEq R] (e : FieldEnumeration R)
    (p : CPolynomial R) : rootsBy e p = p.toPoly.roots.toFinset := by
  by_cases hp : p = 0
  · simp [hp]
  · ext x
    rw [mem_rootsBy hp, Multiset.mem_toFinset,
      Polynomial.mem_roots (by rwa [Ne, toPoly_eq_zero_iff]),
      Polynomial.IsRoot.def, ← eval_toPoly]

open Roots.FiniteField in
/-- **Root counting.** A polynomial has at most `natDegree` distinct roots. -/
theorem card_rootsBy_le [Field R] [DecidableEq R] [BEq R] [LawfulBEq R] (e : FieldEnumeration R)
    (p : CPolynomial R) : (rootsBy e p).card ≤ p.natDegree := by
  rw [rootsBy_eq_toFinset, natDegree_toPoly]
  exact le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' _)

end CompPoly.CPolynomial

/-! ## The `Fp` instantiation -/

namespace Zcash

open CompPoly
open Zcash.Arithmetic (scalarFieldOrder)

/-- The computable polynomial ring over the scalar field. -/
abbrev CPoly := CPolynomial Fp

/-- `Fp` enumerated by its residues. -/
def fpEnumeration : CPolynomial.Roots.FiniteField.FieldEnumeration Fp where
  size := scalarFieldOrder
  elem := fun i => (i.val : Fp)
  complete := fun a => ⟨⟨a.val, ZMod.val_lt a⟩, by simp⟩

/-- The distinct roots of a polynomial over the scalar field.

Irreducible on purpose: unfolding it exposes a filter over an enumeration of the whole scalar
field, which a stray `simp [szBadSet]` will try to evaluate.  The lemmas below are the interface. -/
@[irreducible] def roots (p : CPoly) : Finset Fp := CPolynomial.rootsBy fpEnumeration p

@[simp] theorem roots_zero : roots (0 : CPoly) = ∅ := by
  rw [roots]; exact CPolynomial.rootsBy_zero _

theorem mem_roots {p : CPoly} {x : Fp} (hp : p ≠ 0) :
    x ∈ roots p ↔ CPolynomial.eval x p = 0 := by
  rw [roots]; exact CPolynomial.mem_rootsBy hp

theorem roots_eq_toFinset (p : CPoly) : roots p = p.toPoly.roots.toFinset := by
  rw [roots]; exact CPolynomial.rootsBy_eq_toFinset _ p

theorem card_roots_le (p : CPoly) : (roots p).card ≤ p.natDegree := by
  rw [roots]; exact CPolynomial.card_rootsBy_le _ p

end Zcash
