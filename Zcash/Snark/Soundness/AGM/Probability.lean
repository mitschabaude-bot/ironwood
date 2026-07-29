import Zcash.Snark.Soundness.AGM.Adapter
import Zcash.Snark.Soundness.Forking.Probability

/-!
# From relation probability to DL probability

`Soundness.AGM.Adapter` extracts the challenge's discrete log from a relation whose challenge
component is nonzero. This module prices that reduction: relation finding costs the textbook DL
advantage plus `1/|F|`.

## Experiment

The textbook DL game supplies the challenge `z • B` for uniform `z`. The reduction draws fresh
uniform pairs `(x i, y i)` and presents the basis whose slot `i` has log `x i + z * y i`. It
solves for the challenge unless the returned relation annihilates `y` (Lemma 3 of Jaeger–Tessaro,
<https://eprint.iacr.org/2020/1213>).

## What is proven

* `programmedRelSet_card`: the simulation is perfect — the relation event on programmed coins has
  exactly the honest relation probability.
* `missSet_card_le`: annihilation costs at most a `1/|F|` fraction of the coins.
* `relation_prob_le_of_textbookDL`: textbook DL hardness bounds relation finding by
  `bound + 1/|F|`. No multiplicative factor appears; the fixed-slot reduction this replaces
  guessed the challenge slot and paid `|ι|`.
* `relation_prob_le_of_tightDL`: an independently factored randomized-basis formulation proves
  the same additive `bound + 1/|F|` loss.

## Boundary

The relation finder `A` is a deterministic total function. These are information-theoretic counting
theorems; efficiency is modeled outside Lean. `Soundness.AGM.Capstone` supplies the deployed finder
and `.ProbabilityVesta` specializes the bounds; plain-DL hardness, the AGM, and the generator
random-oracle model remain assumptions there.
-/

open scoped ENNReal
open Classical

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

section Reduction
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype F] (B : G)

/-- The public basis whose slot `i` is `s i • B`. -/
def scalarBasis (s : ι → F) : ι → G := fun i => s i • B

/-- The slot logs the reduction presents, for programming pairs `(x, y)` and challenge log `z`. -/
def programmedLogs (z : F) (x y : ι → F) : ι → F := fun i => x i + z * y i

omit [DecidableEq ι] [Nonempty ι] [Fintype F] in
/-- The presented basis carries its programming: slot `i` is `x i • B + y i • (z • B)`. -/
def programmedEmbedding (z : F) (x y : ι → F) :
    ProgrammedBasisEmbedding (F := F) B (z • B) (scalarBasis B (programmedLogs z x y)) :=
  { x := x
    y := y
    programmed := fun i => by
      simp [scalarBasis, programmedLogs, add_smul, mul_comm z (y i), mul_smul] }

variable (A : (b : ι → G) → Option (AlgebraicRelationWitness (F := F) b))

/-- Relation-finding event: on the presented basis, `A` returns a (nontrivial) relation. -/
noncomputable def relSet : Finset (ι → F) :=
  Finset.univ.filter (fun s => (A (scalarBasis B s)).isSome)

/-! ### The programmed experiment

Reduction coins `(z, x, y)`: the challenge log and the two programming vectors. The finder runs on
the presented logs `programmedLogs z x y`. -/

/-- The coefficients of the relation returned on presented logs `s`; zero when none returns. -/
def returnedCoeffs (s : ι → F) : ι → F :=
  (A (scalarBasis B s)).elim 0 (fun r => r.coeffs)

omit [DecidableEq ι] [Nonempty ι] [Fintype F] in
/-- `returnedCoeffs` reads off the coefficients of the relation actually returned. -/
theorem returnedCoeffs_of_eq_some {s : ι → F}
    {r : AlgebraicRelationWitness (F := F) (scalarBasis B s)}
    (hr : A (scalarBasis B s) = some r) :
    returnedCoeffs B A s = r.coeffs := by
  simp [returnedCoeffs, hr]

/-- A pivot slot where the returned relation has nonzero coefficient; arbitrary when none
returns. -/
noncomputable def pivotSlot (s : ι → F) : ι :=
  (A (scalarBasis B s)).elim (Classical.arbitrary ι) (fun r => r.exists_nonzero_coeff.choose)

omit [DecidableEq ι] [Fintype F] in
/-- The pivot slot's coefficient is nonzero whenever a relation returns. -/
theorem returnedCoeffs_pivotSlot_ne_zero {s : ι → F}
    (hsome : (A (scalarBasis B s)).isSome) :
    returnedCoeffs B A s (pivotSlot B A s) ≠ 0 := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hsome
  rw [returnedCoeffs_of_eq_some B A hr]
  simp only [pivotSlot, hr, Option.elim_some]
  exact r.exists_nonzero_coeff.choose_spec

/-- Programmed coins on which `A` returns a relation. -/
noncomputable def programmedRelSet : Finset (F × (ι → F) × (ι → F)) :=
  Finset.univ.filter (fun t =>
    (A (scalarBasis B (programmedLogs t.1 t.2.1 t.2.2))).isSome)

/-- Winning coins: the returned relation's component against `y` is nonzero, so
`discreteLogOfChallenge_of_relation` computes the discrete log of `z • B`. -/
noncomputable def winSet : Finset (F × (ι → F) × (ι → F)) :=
  Finset.univ.filter (fun t =>
    (A (scalarBasis B (programmedLogs t.1 t.2.1 t.2.2))).isSome ∧
      (∑ i, returnedCoeffs B A (programmedLogs t.1 t.2.1 t.2.2) i * t.2.2 i) ≠ 0)

/-- Failing coins: the returned relation annihilates the challenge programming `y`. -/
noncomputable def missSet : Finset (F × (ι → F) × (ι → F)) :=
  Finset.univ.filter (fun t =>
    (A (scalarBasis B (programmedLogs t.1 t.2.1 t.2.2))).isSome ∧
      (∑ i, returnedCoeffs B A (programmedLogs t.1 t.2.1 t.2.2) i * t.2.2 i) = 0)

omit [Nonempty ι] in
/-- Every relation-producing programmed coin wins or lands in the annihilation hyperplane. -/
theorem programmedRelSet_subset_win_union_miss :
    programmedRelSet B A ⊆ winSet B A ∪ missSet B A := by
  intro t ht
  simp only [programmedRelSet, Finset.mem_filter, Finset.mem_univ, true_and] at ht
  rcases eq_or_ne
      (∑ i, returnedCoeffs B A (programmedLogs t.1 t.2.1 t.2.2) i * t.2.2 i) 0 with h0 | h0
  · exact Finset.mem_union_right _ (by
      simp only [missSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨ht, h0⟩)
  · exact Finset.mem_union_left _ (by
      simp only [winSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨ht, h0⟩)

omit [Nonempty ι] in
/-- Perfect simulation: for each honest log vector in the relation event, the programmed coins
hitting it are exactly the free choices of `(z, y)`. -/
theorem programmedRelSet_card :
    (programmedRelSet B A).card = (relSet B A).card * Fintype.card (F × (ι → F)) := by
  rw [← Finset.card_univ (α := F × (ι → F)), ← Finset.card_product]
  refine Finset.card_bij'
    (fun t _ => (programmedLogs t.1 t.2.1 t.2.2, (t.1, t.2.2)))
    (fun p _ => (p.2.1, fun i => p.1 i - p.2.1 * p.2.2 i, p.2.2))
    ?hi ?hj ?left ?right
  case hi =>
    rintro ⟨z, x, y⟩ ht
    simp only [programmedRelSet, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    simp only [Finset.mem_product, Finset.mem_univ, and_true]
    simp only [relSet, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ht
  case hj =>
    rintro ⟨s, z, y⟩ hp
    simp only [Finset.mem_product, Finset.mem_univ, and_true, relSet, Finset.mem_filter,
      true_and] at hp
    simp only [programmedRelSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hs : programmedLogs z (fun i => s i - z * y i) y = s := by
      funext i
      simp [programmedLogs]
    rw [hs]
    exact hp
  case left =>
    rintro ⟨z, x, y⟩ _
    simp only [Prod.mk.injEq, true_and, and_true]
    funext i
    simp [programmedLogs]
  case right =>
    rintro ⟨s, z, y⟩ _
    simp only [Prod.mk.injEq, and_true]
    funext i
    simp [programmedLogs]

/-- Annihilation costs at most a `1/|F|` slice of the coins: stash the challenge log in the
returned relation's pivot slot of `y`, which the hyperplane equation recovers, so the coins embed
into one fewer field factor. -/
theorem missSet_card_le :
    (missSet B A).card ≤ Fintype.card ((ι → F) × (ι → F)) := by
  rw [← Finset.card_univ]
  refine Finset.card_le_card_of_injOn
    (fun t => (programmedLogs t.1 t.2.1 t.2.2,
      Function.update t.2.2 (pivotSlot B A (programmedLogs t.1 t.2.1 t.2.2)) t.1))
    (fun _ _ => Finset.mem_univ _) ?_
  rintro ⟨z, x, y⟩ ht ⟨z', x', y'⟩ ht' heq
  simp only [Finset.mem_coe, missSet, Finset.mem_filter, Finset.mem_univ, true_and] at ht ht'
  obtain ⟨hsome, hmiss⟩ := ht
  obtain ⟨hsome', hmiss'⟩ := ht'
  dsimp only at heq
  rw [Prod.mk.injEq] at heq
  obtain ⟨hs', hupd⟩ := heq
  have hs : programmedLogs z' x' y' = programmedLogs z x y := hs'.symm
  rw [hs] at hsome' hmiss' hupd
  set j := pivotSlot B A (programmedLogs z x y) with hj
  have hz : z = z' := by
    have := congrFun hupd j
    simpa [Function.update_self] using this
  have hyoff : ∀ i, i ≠ j → y i = y' i := by
    intro i hi
    have := congrFun hupd i
    simpa [Function.update_of_ne hi] using this
  have hcj : returnedCoeffs B A (programmedLogs z x y) j ≠ 0 :=
    returnedCoeffs_pivotSlot_ne_zero B A hsome
  have hyj : y j = y' j := by
    have h1 : returnedCoeffs B A (programmedLogs z x y) j * y j +
        ∑ i ∈ Finset.univ.erase j, returnedCoeffs B A (programmedLogs z x y) i * y i = 0 :=
      (Finset.add_sum_erase Finset.univ
        (fun i => returnedCoeffs B A (programmedLogs z x y) i * y i)
        (Finset.mem_univ j)).trans hmiss
    have h2 : returnedCoeffs B A (programmedLogs z x y) j * y' j +
        ∑ i ∈ Finset.univ.erase j, returnedCoeffs B A (programmedLogs z x y) i * y' i = 0 :=
      (Finset.add_sum_erase Finset.univ
        (fun i => returnedCoeffs B A (programmedLogs z x y) i * y' i)
        (Finset.mem_univ j)).trans hmiss'
    have herase : (∑ i ∈ Finset.univ.erase j,
          returnedCoeffs B A (programmedLogs z x y) i * y i)
        = ∑ i ∈ Finset.univ.erase j, returnedCoeffs B A (programmedLogs z x y) i * y' i :=
      Finset.sum_congr rfl fun i hi => by
        rw [hyoff i (Finset.ne_of_mem_erase hi)]
    rw [herase] at h1
    exact mul_left_cancel₀ hcj (add_right_cancel (h1.trans h2.symm))
  have hy : y = y' := by
    funext i
    rcases eq_or_ne i j with hi | hi
    · rw [hi]; exact hyj
    · exact hyoff i hi
  have hx : x = x' := by
    funext i
    have := congrFun hs.symm i
    simp only [programmedLogs] at this
    rw [hz, hy] at this
    exact add_right_cancel this
  simp only [Prod.mk.injEq]
  exact ⟨hz, hx, hy⟩

/-! ### Reduction to textbook single-generator discrete log -/

/-- The reduction built from `A` wins the textbook single-generator DL game with probability at
most `bound`. Its winning coins are those on which `discreteLogOfChallenge_of_relation`, applied
to `programmedEmbedding`, computes the discrete log of `z • B`. -/
def TextbookDLAdvantageLE (bound : ℝ≥0∞) : Prop :=
  (PMF.uniformOfFintype (F × (ι → F) × (ι → F))).toOuterMeasure (winSet B A) ≤ bound

/-- Under textbook DL hardness, relation finding has probability at most `bound + 1/|F|` — the
tight Jaeger–Tessaro form, with no multiplicative loss. -/
theorem relation_prob_le_of_textbookDL {bound : ℝ≥0∞} (h : TextbookDLAdvantageLE B A bound) :
    (PMF.uniformOfFintype (ι → F)).toOuterMeasure (relSet B A)
      ≤ bound + 1 / Fintype.card F := by
  haveI : Nonempty (ι → F) := ⟨fun _ => 0⟩
  have hM0 : (Fintype.card ((ι → F) × (ι → F)) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hMtop : (Fintype.card ((ι → F) × (ι → F)) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hC0 : (Fintype.card (F × (ι → F)) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hCtop : (Fintype.card (F × (ι → F)) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hwin : ((winSet B A).card : ℝ≥0∞) / Fintype.card (F × (ι → F) × (ι → F)) ≤ bound := by
    rw [← uniformOfFintype_toOuterMeasure_finset]
    exact h
  have hmiss : ((missSet B A).card : ℝ≥0∞) / Fintype.card (F × (ι → F) × (ι → F))
      ≤ 1 / Fintype.card F := by
    have hcard : ((missSet B A).card : ℝ≥0∞) ≤ Fintype.card ((ι → F) × (ι → F)) := by
      exact_mod_cast missSet_card_le B A
    have hN : (Fintype.card (F × (ι → F) × (ι → F)) : ℝ≥0∞)
        = (Fintype.card ((ι → F) × (ι → F)) : ℝ≥0∞) * Fintype.card F := by
      push_cast [Fintype.card_prod]
      ring
    calc ((missSet B A).card : ℝ≥0∞) / Fintype.card (F × (ι → F) × (ι → F))
        ≤ (Fintype.card ((ι → F) × (ι → F)) : ℝ≥0∞)
            / Fintype.card (F × (ι → F) × (ι → F)) := by gcongr
      _ = 1 / Fintype.card F := by
          rw [hN]
          calc (Fintype.card ((ι → F) × (ι → F)) : ℝ≥0∞)
                / ((Fintype.card ((ι → F) × (ι → F)) : ℝ≥0∞) * Fintype.card F)
              = (Fintype.card ((ι → F) × (ι → F)) : ℝ≥0∞) * 1
                  / ((Fintype.card ((ι → F) × (ι → F)) : ℝ≥0∞) * Fintype.card F) := by
                rw [mul_one]
            _ = 1 / Fintype.card F := ENNReal.mul_div_mul_left _ _ hM0 hMtop
  have hrel : (PMF.uniformOfFintype (ι → F)).toOuterMeasure (relSet B A)
      = ((programmedRelSet B A).card : ℝ≥0∞)
          / Fintype.card (F × (ι → F) × (ι → F)) := by
    rw [uniformOfFintype_toOuterMeasure_finset, programmedRelSet_card]
    have hN : (Fintype.card (F × (ι → F) × (ι → F)) : ℝ≥0∞)
        = (Fintype.card (F × (ι → F)) : ℝ≥0∞) * Fintype.card (ι → F) := by
      push_cast [Fintype.card_prod]
      ring
    rw [hN]
    push_cast
    rw [mul_comm ((relSet B A).card : ℝ≥0∞) (Fintype.card (F × (ι → F)) : ℝ≥0∞),
      ENNReal.mul_div_mul_left _ _ hC0 hCtop]
  have hsplit : ((programmedRelSet B A).card : ℝ≥0∞)
      ≤ ((winSet B A).card : ℝ≥0∞) + ((missSet B A).card : ℝ≥0∞) := by
    exact_mod_cast le_trans
      (Finset.card_le_card (programmedRelSet_subset_win_union_miss B A))
      (Finset.card_union_le _ _)
  calc (PMF.uniformOfFintype (ι → F)).toOuterMeasure (relSet B A)
      = ((programmedRelSet B A).card : ℝ≥0∞)
          / Fintype.card (F × (ι → F) × (ι → F)) := hrel
    _ ≤ (((winSet B A).card : ℝ≥0∞) + ((missSet B A).card : ℝ≥0∞))
          / Fintype.card (F × (ι → F) × (ι → F)) := by gcongr
    _ = ((winSet B A).card : ℝ≥0∞) / Fintype.card (F × (ι → F) × (ι → F))
          + ((missSet B A).card : ℝ≥0∞) / Fintype.card (F × (ι → F) × (ι → F)) := by
        rw [← ENNReal.div_add_div_same]
    _ ≤ bound + 1 / Fintype.card F := add_le_add hwin hmiss

end Reduction

/-! ## Alternative factorization: randomized basis, additive `1/|F|` loss

Like the programmed-basis reduction above, this independently factored construction presents
`α i • B + t i • X`, planting the challenge in all slots simultaneously. A relation with
coefficients `c` yields

  `(∑ i, c i · α i) • B + (∑ i, c i · t i) • X = 0`,

so the log of `X` is recoverable whenever the *mask combination* `∑ i, c i · t i` is nonzero. The
adversary sees only `α + x · t`, which for fixed `x` is uniform and independent of `t`; a nonzero
`c` is annihilated by exactly a `1/|F|` fraction of hiding vectors.
-/

section TightReduction

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype F] (B : G)

/-- The public basis presented by the randomized reduction: slot `i` is `α i • B + t i • X`. -/
def randomizedBasis (X : G) (α t : ι → F) : ι → G := fun i => α i • B + t i • X

/-- The pairing of a relation's coefficients with the hiding vector. Extraction succeeds exactly
when it is nonzero. -/
def maskCombination (coeffs t : ι → F) : F := ∑ i, coeffs i * t i

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype F] in
/-- With `X = x • B` the randomized basis is the plain scalar basis at logs `α + x · t`: the
reduction presents exactly the distribution the honest experiment does. -/
theorem randomizedBasis_smul (x : F) (α t : ι → F) :
    randomizedBasis B (x • B) α t = scalarBasis B (fun i => α i + x * t i) := by
  funext i
  show α i • B + t i • (x • B) = (α i + x * t i) • B
  rw [smul_smul, add_smul, mul_comm (t i) x]

/-- Recover the discrete log of the challenge `X` over `B` from a relation over the randomized
basis whose mask combination is nonzero.

No slot is fixed in advance: every returned relation extracts unless it lands in the annihilator
of the hiding vector. -/
def discreteLogOfRandomizedRelation (X : G) (α t : ι → F)
    (r : AlgebraicRelationWitness (F := F) (randomizedBasis B X α t))
    (hmask : maskCombination r.coeffs t ≠ 0) :
    DiscreteLogWitness (F := F) B X := by
  refine ⟨(maskCombination r.coeffs t)⁻¹ * (-(maskCombination r.coeffs α)), ?_⟩
  have hsplit : representationEval (randomizedBasis B X α t) r.coeffs
      = maskCombination r.coeffs α • B + maskCombination r.coeffs t • X := by
    rw [representationEval, maskCombination, maskCombination, Finset.sum_smul, Finset.sum_smul,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    show r.coeffs i • (α i • B + t i • X)
      = (r.coeffs i * α i) • B + (r.coeffs i * t i) • X
    rw [smul_add, smul_smul, smul_smul]
  have hzero : maskCombination r.coeffs t • X + maskCombination r.coeffs α • B = 0 := by
    rw [add_comm, ← hsplit]
    exact r.relation
  have hmul : maskCombination r.coeffs t • X = (-(maskCombination r.coeffs α)) • B := by
    rw [neg_smul]
    exact eq_neg_of_add_eq_zero_left hzero
  have hX : X = ((maskCombination r.coeffs t)⁻¹ * (-(maskCombination r.coeffs α))) • B := by
    have h := congrArg (fun Y : G => (maskCombination r.coeffs t)⁻¹ • Y) hmul
    simp only [smul_smul, inv_mul_cancel₀ hmask, one_smul] at h
    exact h
  exact hX.symm

variable (A : (b : ι → G) → Option (AlgebraicRelationWitness (F := F) b))

/-! The randomized reduction reads the finder's output through the same `returnedCoeffs` and
`pivotSlot` the programmed reduction uses. `pivotSlot` is chosen *after* the adversary runs and
serves only to count annihilating hiding vectors; this reduction plants no slot. -/

omit [DecidableEq ι] [Nonempty ι] [Fintype F] in
/-- On a relation-producing scalar vector, the returned coefficients are nontrivial. -/
theorem returnedCoeffs_ne_zero {s : ι → F} (hs : (A (scalarBasis B s)).isSome) :
    returnedCoeffs B A s ≠ 0 := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hs
  rw [returnedCoeffs_of_eq_some B A hr]
  exact r.nontrivial

omit [DecidableEq ι] [Fintype F] in
/-- The pivot slot really carries a nonzero coefficient. -/
theorem returnedCoeffs_pivotSlot {s : ι → F} (hs : returnedCoeffs B A s ≠ 0) :
    returnedCoeffs B A s (pivotSlot B A s) ≠ 0 := by
  refine returnedCoeffs_pivotSlot_ne_zero B A ?_
  by_contra hnone
  rw [Option.not_isSome_iff_eq_none] at hnone
  exact hs (by simp [returnedCoeffs, hnone])

/-- Scalar vectors and hiding vectors on which the randomized reduction extracts. -/
noncomputable def tightSuccSet : Finset ((ι → F) × (ι → F)) :=
  Finset.univ.filter
    (fun p => (A (scalarBasis B p.1)).isSome ∧ maskCombination (returnedCoeffs B A p.1) p.2 ≠ 0)

omit [Nonempty ι] in
/-- A nonzero coefficient vector is annihilated by at most a `1/|F|` fraction of hiding vectors:
fixing the entries off a nonzero slot determines the entry at it.

This is the whole probabilistic content of the tight reduction, stated for one fixed coefficient
vector. `relProb_le_tightSuccProb_add_inv` reruns the same injection with the pivot slot varying
per scalar vector, so it does not call this lemma; the standalone form is here because it is the
claim a reader should check. -/
theorem card_maskZero_mul_card_le {c : ι → F} (hc : c ≠ 0) :
    (Finset.univ.filter (fun t : ι → F => maskCombination c t = 0)).card * Fintype.card F
      ≤ Fintype.card (ι → F) := by
  obtain ⟨j, hj⟩ : ∃ j, c j ≠ 0 := by
    by_contra h
    exact hc (funext fun i => not_not.mp (not_exists.mp h i))
  have hinj : Set.InjOn (fun q : (ι → F) × F => Function.update q.1 j q.2)
      ↑((Finset.univ.filter (fun t : ι → F => maskCombination c t = 0)) ×ˢ
        (Finset.univ : Finset F)) := by
    rintro ⟨t₁, u₁⟩ h₁ ⟨t₂, u₂⟩ h₂ heq
    simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_univ,
      true_and, and_true] at h₁ h₂
    have hupd : Function.update t₁ j u₁ = Function.update t₂ j u₂ := heq
    have hu : u₁ = u₂ := by
      have h := congrFun hupd j
      simpa using h
    have hoff : ∀ i, i ≠ j → t₁ i = t₂ i := by
      intro i hi
      have h := congrFun hupd i
      simpa [Function.update_apply, hi] using h
    have hsum : ∑ i ∈ Finset.univ.erase j, c i * t₁ i
        = ∑ i ∈ Finset.univ.erase j, c i * t₂ i :=
      Finset.sum_congr rfl fun i hi => by rw [hoff i (Finset.mem_erase.mp hi).1]
    have e₁ : ∑ i ∈ Finset.univ.erase j, c i * t₁ i + c j * t₁ j = 0 := by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ j)]
      exact h₁
    have e₂ : ∑ i ∈ Finset.univ.erase j, c i * t₂ i + c j * t₂ j = 0 := by
      rw [Finset.sum_erase_add _ _ (Finset.mem_univ j)]
      exact h₂
    have hcj : c j * t₁ j = c j * t₂ j := by
      have hchain := e₁.trans e₂.symm
      rw [hsum] at hchain
      exact add_left_cancel hchain
    have ht : t₁ = t₂ := by
      funext i
      by_cases hi : i = j
      · subst hi
        exact mul_left_cancel₀ hj hcj
      · exact hoff i hi
    simp [ht, hu]
  calc (Finset.univ.filter (fun t : ι → F => maskCombination c t = 0)).card * Fintype.card F
      = ((Finset.univ.filter (fun t : ι → F => maskCombination c t = 0)) ×ˢ
          (Finset.univ : Finset F)).card := by
        rw [Finset.card_product, Finset.card_univ]
    _ ≤ (Finset.univ : Finset (ι → F)).card :=
        Finset.card_le_card_of_injOn _ (fun q _ => Finset.mem_univ _) hinj
    _ = Fintype.card (ι → F) := Finset.card_univ

/-- The relation event exceeds the randomized reduction's success event by at most `1 / |F|`. -/
theorem relProb_le_tightSuccProb_add_inv :
    (PMF.uniformOfFintype (ι → F)).toOuterMeasure (relSet B A)
      ≤ (PMF.uniformOfFintype ((ι → F) × (ι → F))).toOuterMeasure (tightSuccSet B A)
        + 1 / Fintype.card F := by
  haveI : Nonempty (ι → F) := ⟨fun _ => 0⟩
  have hN0 : (Fintype.card (ι → F) : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hNt : (Fintype.card (ι → F) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hF0 : (Fintype.card F : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hFt : (Fintype.card F : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hNN0 : ((Fintype.card (ι → F) : ℝ≥0∞) * Fintype.card (ι → F)) ≠ 0 := mul_ne_zero hN0 hN0
  have hNNt : ((Fintype.card (ι → F) : ℝ≥0∞) * Fintype.card (ι → F)) ≠ ⊤ :=
    ENNReal.mul_ne_top hNt hNt
  -- the success set sits inside the relation-producing rectangle
  have hsub : tightSuccSet B A ⊆ relSet B A ×ˢ (Finset.univ : Finset (ι → F)) := by
    intro p hp
    simp only [tightSuccSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_product, Finset.mem_univ, and_true, relSet, Finset.mem_filter,
      true_and]
    exact hp.1
  set Miss := (relSet B A ×ˢ (Finset.univ : Finset (ι → F))) \ tightSuccSet B A with hMissdef
  have hMissmem : ∀ p ∈ Miss, (A (scalarBasis B p.1)).isSome ∧
      maskCombination (returnedCoeffs B A p.1) p.2 = 0 := by
    intro p hp
    rw [hMissdef, Finset.mem_sdiff, Finset.mem_product] at hp
    obtain ⟨⟨hrel, -⟩, hout⟩ := hp
    simp only [relSet, Finset.mem_filter, Finset.mem_univ, true_and] at hrel
    refine ⟨hrel, ?_⟩
    by_contra hne
    exact hout (by
      simp only [tightSuccSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hrel, hne⟩)
  -- the rectangle splits into successes and annihilations
  have hsum : Miss.card + (tightSuccSet B A).card
      = (relSet B A).card * Fintype.card (ι → F) := by
    rw [hMissdef, Finset.card_sdiff_add_card_eq_card hsub, Finset.card_product, Finset.card_univ]
  -- annihilations are a `1/|F|` slice of the rectangle
  have hmiss : Miss.card * Fintype.card F
      ≤ (relSet B A).card * Fintype.card (ι → F) := by
    have hmap : ∀ q ∈ Miss ×ˢ (Finset.univ : Finset F),
        ((q.1.1, Function.update q.1.2 (pivotSlot B A q.1.1) q.2) : (ι → F) × (ι → F))
          ∈ relSet B A ×ˢ (Finset.univ : Finset (ι → F)) := by
      intro q hq
      rw [Finset.mem_product] at hq
      rw [Finset.mem_product]
      refine ⟨?_, Finset.mem_univ _⟩
      simp only [relSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hMissmem q.1 hq.1).1
    have hinj : Set.InjOn
        (fun q : ((ι → F) × (ι → F)) × F =>
          ((q.1.1, Function.update q.1.2 (pivotSlot B A q.1.1) q.2) : (ι → F) × (ι → F)))
        ↑(Miss ×ˢ (Finset.univ : Finset F)) := by
      rintro ⟨⟨s₁, t₁⟩, u₁⟩ h₁ ⟨⟨s₂, t₂⟩, u₂⟩ h₂ heq
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, and_true] at h₁ h₂
      have hs : s₁ = s₂ := congrArg Prod.fst heq
      subst hs
      have hc₁ := hMissmem (s₁, t₁) h₁
      have hc₂ := hMissmem (s₁, t₂) h₂
      have hcne : returnedCoeffs B A s₁ ≠ 0 := returnedCoeffs_ne_zero B A hc₁.1
      have hj : returnedCoeffs B A s₁ (pivotSlot B A s₁) ≠ 0 :=
        returnedCoeffs_pivotSlot B A hcne
      have hupd : Function.update t₁ (pivotSlot B A s₁) u₁
          = Function.update t₂ (pivotSlot B A s₁) u₂ := congrArg Prod.snd heq
      have hu : u₁ = u₂ := by
        have h := congrFun hupd (pivotSlot B A s₁)
        simpa using h
      have hoff : ∀ i, i ≠ pivotSlot B A s₁ → t₁ i = t₂ i := by
        intro i hi
        have h := congrFun hupd i
        simpa [Function.update_apply, hi] using h
      have hsum' : ∑ i ∈ Finset.univ.erase (pivotSlot B A s₁), returnedCoeffs B A s₁ i * t₁ i
          = ∑ i ∈ Finset.univ.erase (pivotSlot B A s₁), returnedCoeffs B A s₁ i * t₂ i :=
        Finset.sum_congr rfl fun i hi => by rw [hoff i (Finset.mem_erase.mp hi).1]
      have e₁ : ∑ i ∈ Finset.univ.erase (pivotSlot B A s₁), returnedCoeffs B A s₁ i * t₁ i
          + returnedCoeffs B A s₁ (pivotSlot B A s₁) * t₁ (pivotSlot B A s₁) = 0 := by
        rw [Finset.sum_erase_add _ _ (Finset.mem_univ (pivotSlot B A s₁))]
        exact hc₁.2
      have e₂ : ∑ i ∈ Finset.univ.erase (pivotSlot B A s₁), returnedCoeffs B A s₁ i * t₂ i
          + returnedCoeffs B A s₁ (pivotSlot B A s₁) * t₂ (pivotSlot B A s₁) = 0 := by
        rw [Finset.sum_erase_add _ _ (Finset.mem_univ (pivotSlot B A s₁))]
        exact hc₂.2
      have hcj : returnedCoeffs B A s₁ (pivotSlot B A s₁) * t₁ (pivotSlot B A s₁)
          = returnedCoeffs B A s₁ (pivotSlot B A s₁) * t₂ (pivotSlot B A s₁) := by
        have hchain := e₁.trans e₂.symm
        rw [hsum'] at hchain
        exact add_left_cancel hchain
      have ht : t₁ = t₂ := by
        funext i
        by_cases hi : i = pivotSlot B A s₁
        · subst hi
          exact mul_left_cancel₀ hj hcj
        · exact hoff i hi
      simp [ht, hu]
    calc Miss.card * Fintype.card F
        = (Miss ×ˢ (Finset.univ : Finset F)).card := by
          rw [Finset.card_product, Finset.card_univ]
      _ ≤ (relSet B A ×ˢ (Finset.univ : Finset (ι → F))).card :=
          Finset.card_le_card_of_injOn _ hmap hinj
      _ = (relSet B A).card * Fintype.card (ι → F) := by
          rw [Finset.card_product, Finset.card_univ]
  -- move to `ℝ≥0∞`
  have hsumE : (Miss.card : ℝ≥0∞) + (tightSuccSet B A).card
      = ((relSet B A).card : ℝ≥0∞) * Fintype.card (ι → F) := by exact_mod_cast hsum
  have hmissE : (Miss.card : ℝ≥0∞) * Fintype.card F
      ≤ (Fintype.card (ι → F) : ℝ≥0∞) * Fintype.card (ι → F) := by
    have hR : (relSet B A).card ≤ Fintype.card (ι → F) := by
      simpa using Finset.card_le_card (Finset.subset_univ (relSet B A))
    have h1 : (Miss.card : ℝ≥0∞) * Fintype.card F
        ≤ ((relSet B A).card : ℝ≥0∞) * Fintype.card (ι → F) := by exact_mod_cast hmiss
    refine h1.trans ?_
    gcongr
  rw [uniformOfFintype_toOuterMeasure_finset, uniformOfFintype_toOuterMeasure_finset,
    Fintype.card_prod, Nat.cast_mul]
  have hstep1 : ((relSet B A).card : ℝ≥0∞) / Fintype.card (ι → F)
      = ((tightSuccSet B A).card : ℝ≥0∞)
          / ((Fintype.card (ι → F) : ℝ≥0∞) * Fintype.card (ι → F))
        + (Miss.card : ℝ≥0∞) / ((Fintype.card (ι → F) : ℝ≥0∞) * Fintype.card (ι → F)) := by
    rw [ENNReal.div_add_div_same]
    have hnum : ((tightSuccSet B A).card : ℝ≥0∞) + Miss.card
        = (Fintype.card (ι → F) : ℝ≥0∞) * (relSet B A).card := by
      rw [add_comm, hsumE, mul_comm]
    rw [hnum]
    exact (ENNReal.mul_div_mul_left _ _ hN0 hNt).symm
  have hstep2 : (Miss.card : ℝ≥0∞)
        / ((Fintype.card (ι → F) : ℝ≥0∞) * Fintype.card (ι → F))
      ≤ 1 / Fintype.card F := by
    have hle : (Miss.card : ℝ≥0∞)
        ≤ ((Fintype.card (ι → F) : ℝ≥0∞) * Fintype.card (ι → F)) / Fintype.card F := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hF0) (Or.inl hFt)]
      exact hmissE
    calc (Miss.card : ℝ≥0∞) / ((Fintype.card (ι → F) : ℝ≥0∞) * Fintype.card (ι → F))
        ≤ (((Fintype.card (ι → F) : ℝ≥0∞) * Fintype.card (ι → F)) / Fintype.card F)
            / ((Fintype.card (ι → F) : ℝ≥0∞) * Fintype.card (ι → F)) :=
          ENNReal.div_le_div_right hle _
      _ = 1 / Fintype.card F := by
          rw [div_eq_mul_inv, div_eq_mul_inv, one_div,
            mul_comm ((Fintype.card (ι → F) : ℝ≥0∞) * Fintype.card (ι → F))
              ((Fintype.card F : ℝ≥0∞)⁻¹),
            mul_assoc, ENNReal.mul_inv_cancel hNN0 hNNt, mul_one]
  rw [hstep1]
  exact add_le_add le_rfl hstep2

/-- Winning coins for the tight reduction against the textbook DL game: the secret `x`, the base
randomization `α`, and the hiding vector `t`. The presented basis is `scalarBasis B (α + x · t)`,
which is uniform and independent of `t`. -/
noncomputable def tightWinSet : Finset (F × (ι → F) × (ι → F)) :=
  Finset.univ.filter
    (fun w => ((fun i => w.2.1 i + w.1 * w.2.2 i), w.2.2) ∈ tightSuccSet B A)

omit [Nonempty ι] in
/-- The winning-coins set has `|F|` elements for each element of `tightSuccSet`: for each fixed
secret, `(α, t) ↦ (α + x · t, t)` is a bijection. -/
theorem tightWinSet_card :
    (tightWinSet B A).card = (tightSuccSet B A).card * Fintype.card F := by
  rw [← Finset.card_univ (α := F), ← Finset.card_product]
  refine Finset.card_bij'
    (fun w _ => (((fun i => w.2.1 i + w.1 * w.2.2 i), w.2.2), w.1))
    (fun p _ => (p.2, (fun i => p.1.1 i - p.2 * p.1.2 i), p.1.2))
    ?hi ?hj ?left ?right
  case hi =>
    rintro ⟨x, α, t⟩ hw
    simp only [tightWinSet, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    simp only [Finset.mem_product, Finset.mem_univ, and_true]
    exact hw
  case hj =>
    rintro ⟨⟨s, t⟩, x⟩ hp
    simp only [Finset.mem_product, Finset.mem_univ, and_true] at hp
    simp only [tightWinSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hfun : (fun i => (s i - x * t i) + x * t i) = s := by funext i; ring
    simpa only [hfun] using hp
  case left =>
    rintro ⟨x, α, t⟩ _
    have hfun : (fun i => (α i + x * t i) - x * t i) = α := by funext i; ring
    simp only [hfun]
  case right =>
    rintro ⟨⟨s, t⟩, x⟩ _
    have hfun : (fun i => (s i - x * t i) + x * t i) = s := by funext i; ring
    simp only [hfun]

omit [Nonempty ι] in
/-- The tight reduction and the randomized experiment have the same success probability. -/
theorem tight_winProb_eq_succProb :
    (PMF.uniformOfFintype (F × (ι → F) × (ι → F))).toOuterMeasure (tightWinSet B A)
      = (PMF.uniformOfFintype ((ι → F) × (ι → F))).toOuterMeasure (tightSuccSet B A) := by
  haveI : Nonempty (ι → F) := ⟨fun _ => 0⟩
  rw [uniformOfFintype_toOuterMeasure_finset, uniformOfFintype_toOuterMeasure_finset,
    tightWinSet_card]
  have hcard : Fintype.card (F × (ι → F) × (ι → F))
      = Fintype.card F * Fintype.card ((ι → F) × (ι → F)) := by
    simp only [Fintype.card_prod]
  rw [hcard]
  push_cast
  rw [mul_comm ((tightSuccSet B A).card : ℝ≥0∞) (Fintype.card F : ℝ≥0∞),
    ENNReal.mul_div_mul_left _ _
      (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)]

/-- The randomized reduction built from `A` wins the textbook single-generator DL game with
probability at most `bound`. -/
def TightDLAdvantageLE (bound : ℝ≥0∞) : Prop :=
  (PMF.uniformOfFintype (F × (ι → F) × (ι → F))).toOuterMeasure (tightWinSet B A) ≤ bound

/-- Under textbook DL hardness, relation finding has probability at most `bound + 1 / |F|`.

This is an alternative factorization of the programmed-basis result
`relation_prob_le_of_textbookDL`. -/
theorem relation_prob_le_of_tightDL {bound : ℝ≥0∞} (h : TightDLAdvantageLE B A bound) :
    (PMF.uniformOfFintype (ι → F)).toOuterMeasure (relSet B A)
      ≤ bound + 1 / Fintype.card F := by
  refine le_trans (relProb_le_tightSuccProb_add_inv B A) ?_
  gcongr
  rw [← tight_winProb_eq_succProb]
  exact h

end TightReduction

end Zcash.Snark
