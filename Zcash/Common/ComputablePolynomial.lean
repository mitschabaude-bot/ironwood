import Zcash.Arithmetic
import Mathlib.Algebra.Ring.MinimalAxioms

/-!
# Executable operations on `Polynomial Fp`

Mathlib intentionally declares its sparse-polynomial instances in a `noncomputable section`.
The underlying representation is nevertheless finite coefficient data.  This file supplies the
same operations directly on that data, together with kernel-checked equalities used as compiler
substitutions by the executable soundness finders.
-/

namespace Zcash.Snark.ComputablePolynomial

open Polynomial Finset

variable {R : Type*} [CommRing R] [DecidableEq R]

@[inline] def coeff (p : Polynomial R) (i : Nat) : R := p.toFinsupp.toFun i

@[inline] def support (p : Polynomial R) : Finset Nat := p.toFinsupp.support

/-- Construct a polynomial from a coefficient function and a finite support bound. -/
def ofSupport (s : Finset Nat) (a : Nat → R)
    (ha : ∀ i, a i ≠ 0 → i ∈ s) : Polynomial R :=
  ⟨
    { support := s.filter fun i => a i ≠ 0
      toFun := a
      mem_support_toFun := by
        intro i
        simp only [Finset.mem_filter]
        exact ⟨And.right, fun hi => ⟨ha i hi, hi⟩⟩ }
  ⟩

@[simp] theorem coeff_ofSupport (s : Finset Nat) (a : Nat → R)
    (ha : ∀ i, a i ≠ 0 → i ∈ s) (i : Nat) :
    coeff (ofSupport s a ha) i = a i := rfl

def zero : Polynomial R := ofSupport ∅ (fun _ => 0) (by simp)

def const (a : R) : Polynomial R :=
  ofSupport {0} (fun i => if i = 0 then a else 0) (by
    intro i hi
    have hi0 : i = 0 := by
      by_contra hine
      exact hi (if_neg hine)
    exact Finset.mem_singleton.mpr hi0)

def X : Polynomial R :=
  ofSupport {1} (fun i => if i = 1 then 1 else 0) (by
    intro i hi
    have hi1 : i = 1 := by
      by_contra hine
      exact hi (if_neg hine)
    exact Finset.mem_singleton.mpr hi1)

def add (p q : Polynomial R) : Polynomial R :=
  ofSupport (support p ∪ support q) (fun i => coeff p i + coeff q i) (by
    intro i hi
    by_contra hmem
    simp only [Finset.mem_union, not_or] at hmem
    have hp : coeff p i = 0 := Finsupp.notMem_support_iff.mp hmem.1
    have hq : coeff q i = 0 := Finsupp.notMem_support_iff.mp hmem.2
    apply hi
    change coeff p i + coeff q i = 0
    rw [hp, hq, add_zero])

def neg (p : Polynomial R) : Polynomial R :=
  ofSupport (support p) (fun i => -coeff p i) (by
    intro i hi
    exact Finsupp.mem_support_iff.mpr (neg_ne_zero.mp hi))

def sub (p q : Polynomial R) : Polynomial R :=
  ofSupport (support p ∪ support q) (fun i => coeff p i - coeff q i) (by
    intro i hi
    by_contra hmem
    simp only [Finset.mem_union, not_or] at hmem
    have hp : coeff p i = 0 := Finsupp.notMem_support_iff.mp hmem.1
    have hq : coeff q i = 0 := Finsupp.notMem_support_iff.mp hmem.2
    apply hi
    change coeff p i - coeff q i = 0
    rw [hp, hq, sub_zero])

def mulCoeff (p q : Polynomial R) (n : Nat) : R :=
  ∑ ij ∈ Finset.antidiagonal n, coeff p ij.1 * coeff q ij.2

def mulSupport (p q : Polynomial R) : Finset Nat :=
  (support p).biUnion fun i => (support q).image fun j => i + j

def mul (p q : Polynomial R) : Polynomial R :=
  ofSupport (mulSupport p q) (mulCoeff p q) (by
    intro n hn
    by_contra hmem
    apply hn
    unfold mulCoeff
    apply Finset.sum_eq_zero
    intro ij hij
    by_cases hp : coeff p ij.1 = 0
    · simp [hp]
    by_cases hq : coeff q ij.2 = 0
    · simp [hq]
    exfalso
    apply hmem
    apply Finset.mem_biUnion.mpr
    refine ⟨ij.1, Finsupp.mem_support_iff.mpr hp, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨ij.2, Finsupp.mem_support_iff.mpr hq, ?_⟩
    exact Finset.mem_antidiagonal.mp hij)

def nsmul (n : Nat) (p : Polynomial R) : Polynomial R :=
  ofSupport (support p) (fun i => n • coeff p i) (by
    intro i hi
    by_contra hmem
    apply hi
    change n • coeff p i = 0
    have hp : coeff p i = 0 := by
      change p.toFinsupp i = 0
      exact Finsupp.notMem_support_iff.mp hmem
    rw [hp, smul_zero])

def zsmul (n : Int) (p : Polynomial R) : Polynomial R :=
  ofSupport (support p) (fun i => n • coeff p i) (by
    intro i hi
    by_contra hmem
    apply hi
    change n • coeff p i = 0
    have hp : coeff p i = 0 := by
      change p.toFinsupp i = 0
      exact Finsupp.notMem_support_iff.mp hmem
    rw [hp, smul_zero])

def pow (p : Polynomial R) : Nat → Polynomial R
  | 0 => const 1
  | n + 1 => mul (pow p n) p

def natCast (n : Nat) : Polynomial R := const n

def intCast (n : Int) : Polynomial R := const n

theorem zero_eq : (zero : Polynomial R) = 0 := by
  apply Polynomial.ext
  intro i
  rfl

theorem const_eq (a : R) : const a = Polynomial.C a := by
  apply Polynomial.ext
  intro i
  change (if i = 0 then a else 0) = _
  by_cases hi : i = 0 <;> simp [hi, Polynomial.coeff_C]

theorem X_eq : (X : Polynomial R) = Polynomial.X := by
  apply Polynomial.ext
  intro i
  change (if i = 1 then 1 else 0) = _
  by_cases hi : i = 1 <;> simp [hi, ne_comm, Polynomial.coeff_X]

theorem add_eq (p q : Polynomial R) : add p q = p + q := by
  apply Polynomial.ext
  intro i
  rfl

theorem neg_eq (p : Polynomial R) : neg p = -p := by
  apply Polynomial.ext
  intro i
  rfl

theorem sub_eq (p q : Polynomial R) : sub p q = p - q := by
  apply Polynomial.ext
  intro i
  exact (Polynomial.coeff_sub p q i).symm

theorem mul_eq (p q : Polynomial R) : mul p q = p * q := by
  apply Polynomial.ext
  intro i
  exact (Polynomial.coeff_mul p q i).symm

theorem nsmul_eq (n : Nat) (p : Polynomial R) : nsmul n p = n • p := by
  apply Polynomial.ext
  intro i
  rfl

theorem zsmul_eq (n : Int) (p : Polynomial R) : zsmul n p = n • p := by
  apply Polynomial.ext
  intro i
  rfl

theorem pow_eq (p : Polynomial R) (n : Nat) : pow p n = p ^ n := by
  induction n with
  | zero => simp [pow, const_eq]
  | succ n ih => simp [pow, ih, mul_eq, _root_.pow_succ]

/-- Executable monic division.  Mathlib's definition installs `Classical.decEq` internally even
when the coefficient ring already has decidable equality; this is the same recursion with the
coefficient-data operations supplied explicitly. -/
def divModByMonicAux : ∀ (_p : Polynomial R) {q : Polynomial R}, q.Monic →
    Polynomial R × Polynomial R
  | p, q, hq =>
      if h : p.degree ≥ q.degree ∧ p ≠ zero then
        let z := mul (const p.leadingCoeff) (pow X (p.natDegree - q.natDegree))
        have hwf : (sub p (mul q z)).degree < p.degree := by
          have h' : p.degree ≥ q.degree ∧ p ≠ 0 := by
            simpa only [zero_eq] using h
          dsimp only [z]
          simpa only [sub_eq, mul_eq, const_eq, pow_eq, X_eq] using
            Polynomial.div_wf_lemma h' hq
        let dm := divModByMonicAux (sub p (mul q z)) hq
        (add z dm.1, dm.2)
      else (zero, p)
  termination_by p => p

def modByMonic (p q : Polynomial R) : Polynomial R :=
  if hq : q.Monic then (divModByMonicAux p hq).2 else p

theorem divModByMonicAux_eq (p : Polynomial R) {q : Polynomial R} (hq : q.Monic) :
    divModByMonicAux p hq = Polynomial.divModByMonicAux p hq := by
  fun_induction divModByMonicAux p hq
  · rw [Polynomial.divModByMonicAux]
    simp_all +zetaDelta only [zero_eq, add_eq, sub_eq, mul_eq, const_eq, pow_eq, X_eq,
      true_and]
    split
    · rfl
    · aesop
  · rw [Polynomial.divModByMonicAux]
    simp_all +zetaDelta only [zero_eq]
    split
    · contradiction
    · rfl

theorem modByMonic_eq (p q : Polynomial R) : modByMonic p q = p %ₘ q := by
  unfold modByMonic Polynomial.modByMonic
  split <;> rename_i hq
  · exact congrArg Prod.snd (divModByMonicAux_eq p hq)
  · rfl

theorem natCast_eq (n : Nat) : natCast n = (n : Polynomial R) := by
  simp [natCast, const_eq]

theorem intCast_eq (n : Int) : intCast n = (n : Polynomial R) := by
  simp [intCast, const_eq]

/-- Executable list sum using the coefficient-data addition. -/
def sumList (ps : List (Polynomial R)) : Polynomial R :=
  ps.foldl add zero

theorem foldl_add_eq (ps : List (Polynomial R)) (acc : Polynomial R) :
    ps.foldl add acc = acc + ps.sum := by
  induction ps generalizing acc with
  | nil => simp
  | cons p ps ih =>
      rw [List.foldl_cons, ih, add_eq, List.sum_cons, add_assoc]

theorem sumList_eq (ps : List (Polynomial R)) : sumList ps = ps.sum := by
  rw [sumList, foldl_add_eq, zero_eq, zero_add]

/-- Executable list product using the coefficient-data multiplication. -/
def prodList (ps : List (Polynomial R)) : Polynomial R :=
  ps.foldl mul (const 1)

theorem foldl_mul_eq (ps : List (Polynomial R)) (acc : Polynomial R) :
    ps.foldl mul acc = acc * ps.prod := by
  induction ps generalizing acc with
  | nil => simp
  | cons p ps ih =>
      rw [List.foldl_cons, ih, mul_eq, List.prod_cons, mul_assoc]

theorem prodList_eq (ps : List (Polynomial R)) : prodList ps = ps.prod := by
  rw [prodList, foldl_mul_eq, const_eq, Polynomial.C_1, one_mul]

omit [DecidableEq R] in
private theorem standard_left_distrib (a b c : Polynomial R) :
    a * (b + c) = a * b + a * c := by
  exact left_distrib a b c

/-- The standard polynomial commutative ring with all computational fields supplied by the
coefficient-data implementations above. -/
@[reducible] def commRing : CommRing (Polynomial R) :=
  letI : Zero (Polynomial R) := ⟨zero⟩
  letI : One (Polynomial R) := ⟨const 1⟩
  letI : Add (Polynomial R) := ⟨add⟩
  letI : Mul (Polynomial R) := ⟨mul⟩
  letI : Neg (Polynomial R) := ⟨neg⟩
  CommRing.ofMinimalAxioms
    (by
      intro a b c
      change add (add a b) c = add a (add b c)
      rw [add_eq, add_eq, add_eq, add_eq]
      exact add_assoc a b c)
    (by
      intro a
      change add zero a = a
      rw [add_eq, zero_eq, zero_add])
    (by
      intro a
      change add (neg a) a = zero
      rw [add_eq, neg_eq, zero_eq, neg_add_cancel])
    (by
      intro a b c
      change mul (mul a b) c = mul a (mul b c)
      rw [mul_eq, mul_eq, mul_eq, mul_eq]
      exact mul_assoc a b c)
    (by
      intro a b
      change mul a b = mul b a
      rw [mul_eq, mul_eq, mul_comm])
    (by
      intro a
      change mul (const 1) a = a
      rw [mul_eq, const_eq, Polynomial.C_1, one_mul])
    (by
      intro a b c
      change mul a (add b c) = add (mul a b) (mul a c)
      rw [mul_eq, add_eq, mul_eq, mul_eq, add_eq]
      exact standard_left_distrib a b c)

theorem commRing_eq : (Polynomial.commRing : CommRing (Polynomial R)) = commRing := by
  apply CommRing.ext
  · funext p q
    exact (add_eq p q).symm
  · funext p q
    exact (mul_eq p q).symm

/-- Executable commutative multiset product. -/
def prodMultiset (ps : Multiset (Polynomial R)) : Polynomial R :=
  letI : CommRing (Polynomial R) := commRing
  ps.prod

theorem prodMultiset_eq (ps : Multiset (Polynomial R)) :
    prodMultiset ps = ps.prod := by
  unfold prodMultiset
  rw [← commRing_eq]

/-- Executable product of the linear factors `X + C u`. -/
def xAddProduct (s : Multiset R) : Polynomial R :=
  prodMultiset (s.map fun u => add X (const u))

theorem xAddProduct_eq (s : Multiset R) :
    xAddProduct s = (s.map fun u => Polynomial.X + Polynomial.C u).prod := by
  rw [xAddProduct, prodMultiset_eq]
  apply congrArg Multiset.prod
  apply Multiset.map_congr rfl
  intro u _
  rw [add_eq, X_eq, const_eq]

/-- Executable elementary symmetric polynomial of polynomial-valued entries. -/
def sumMultiset (ps : Multiset (Polynomial R)) : Polynomial R :=
  letI : CommRing (Polynomial R) := commRing
  ps.sum

theorem sumMultiset_eq (ps : Multiset (Polynomial R)) :
    sumMultiset ps = ps.sum := by
  unfold sumMultiset
  rw [← commRing_eq]

/-- Executable elementary symmetric polynomial of polynomial-valued entries. -/
def esymm (s : Multiset (Polynomial R)) (n : Nat) : Polynomial R :=
  sumMultiset ((s.powersetCard n).map prodMultiset)

theorem esymm_eq (s : Multiset (Polynomial R)) (n : Nat) :
    esymm s n = s.esymm n := by
  rw [esymm, sumMultiset_eq, Multiset.esymm]
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro ps _
  rw [prodMultiset_eq]

/-- Executable polynomial composition. -/
def comp (p q : Polynomial R) : Polynomial R :=
  letI : CommRing (Polynomial R) := commRing
  p.sum fun i a => mul (const a) (pow q i)

theorem comp_eq (p q : Polynomial R) : comp p q = p.comp q := by
  unfold comp
  rw [← commRing_eq]
  simp only [mul_eq, const_eq, pow_eq]
  exact Polynomial.comp_eq_sum_left.symm

/-- Coefficient comparison gives executable polynomial equality. -/
def decidableEq : DecidableEq (Polynomial R) := fun p q =>
  if h : p.toFinsupp = q.toFinsupp then
    isTrue (Polynomial.toFinsupp_injective h)
  else
    isFalse fun hpq => h (congrArg Polynomial.toFinsupp hpq)

end Zcash.Snark.ComputablePolynomial
