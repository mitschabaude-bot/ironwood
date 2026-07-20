import Zcash.Snark.Soundness.AGM.Probability

/-!
# Relation-to-DL probability with extractor coins

Carry independent extractor coins through the fixed-slot DL reduction with a uniformly hidden slot.
-/

open scoped ENNReal
open Classical

namespace Zcash.Snark

variable {F G ρ : Type*} [Field F] [AddCommGroup G] [Module F G]

/-! ## Independent setup and extractor coins -/

/-- Draw from two PMFs independently. -/
noncomputable def independentProductPMF {A B : Type*} (p : PMF A) (q : PMF B) : PMF (A × B) :=
  p.bind fun a => q.map (Prod.mk a)

/-- Mapping the first component commutes with an independent product. -/
theorem independentProductPMF_map_left {A B C : Type*} (p : PMF A) (q : PMF B)
    (f : A → C) :
    (independentProductPMF p q).map (fun x => (f x.1, x.2)) =
      independentProductPMF (p.map f) q := by
  rw [independentProductPMF, PMF.map_bind, independentProductPMF, PMF.bind_map]
  congr 1
  funext a
  rw [PMF.map_comp]
  congr 1

/-- Independent uniform draws are the uniform draw on the product type. -/
theorem independentProductPMF_uniform {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    independentProductPMF (PMF.uniformOfFintype A) (PMF.uniformOfFintype B) =
      PMF.uniformOfFintype (A × B) := by
  classical
  apply PMF.ext
  rintro ⟨a, b⟩
  rw [independentProductPMF, PMF.bind_apply, tsum_fintype]
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  rw [Finset.sum_eq_single a]
  · rw [tsum_eq_single b]
    · rw [if_pos rfl]
      rw [ENNReal.mul_inv (Or.inl (by exact_mod_cast Fintype.card_ne_zero))
        (Or.inl (ENNReal.natCast_ne_top _))]
    · intro b' hb'
      rw [if_neg]
      exact fun h => hb' (Prod.mk.inj h).2.symm
  · intro a' _ ha'
    have hzero : (∑' b' : B, if (a, b) = (a', b') then
        ((Fintype.card B : ℝ≥0∞))⁻¹ else 0) = 0 := ENNReal.tsum_eq_zero.mpr fun b' => by
      rw [if_neg]
      exact fun h => ha' (Prod.mk.inj h).1.symm
    rw [hzero, mul_zero]
  · simp

section Reduction

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype F] [Fintype ρ] [Nonempty ρ] (B : G)

variable (A : (b : ι → G) → ρ → Option (AlgebraicRelationWitness (F := F) b))

/-- Basis scalars and extractor coins on which the computed producer returns a relation. -/
noncomputable def relSetWithCoins : Finset ((ι → F) × ρ) :=
  Finset.univ.filter (fun p => (A (scalarBasis B p.1) p.2).isSome)

/-- Relation-producing basis/coin pairs whose relation hits the sampled challenge slot. -/
noncomputable def succSetWithCoins : Finset (((ι → F) × ρ) × ι) :=
  Finset.univ.filter (fun p =>
    ∃ r, A (scalarBasis B p.1.1) p.1.2 = some r ∧ r.coeffs p.2 ≠ 0)

omit [Nonempty ι] [Nonempty ρ] in
/-- Every relation-producing basis/coin pair has a slot that solves DL. -/
theorem relSetWithCoins_card_le_succSetWithCoins_card :
    (relSetWithCoins B A).card ≤ (succSetWithCoins B A).card := by
  have hsub : relSetWithCoins B A ⊆ Finset.image Prod.fst (succSetWithCoins B A) := by
    intro p hp
    simp only [relSetWithCoins, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hp
    obtain ⟨c, hc⟩ := r.nonzeroCoeffSlots_nonempty
    rw [Finset.mem_image]
    refine ⟨(p, c), ?_, rfl⟩
    simp only [succSetWithCoins, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨r, hr, (r.mem_nonzeroCoeffSlots c).mp hc⟩
  calc
    (relSetWithCoins B A).card
        ≤ (Finset.image Prod.fst (succSetWithCoins B A)).card := Finset.card_le_card hsub
    _ ≤ (succSetWithCoins B A).card := Finset.card_image_le

/-- The randomized DL reduction succeeds at least as often as relation production divided by the
number of augmented-basis slots. -/
theorem reductionWithCoins_advantage_ge :
    (1 : ℝ≥0∞) / Fintype.card ι *
        (PMF.uniformOfFintype ((ι → F) × ρ)).toOuterMeasure (relSetWithCoins B A)
      ≤ (PMF.uniformOfFintype (((ι → F) × ρ) × ι)).toOuterMeasure
          (succSetWithCoins B A) := by
  rw [uniformOfFintype_toOuterMeasure_finset, uniformOfFintype_toOuterMeasure_finset,
    show Fintype.card (((ι → F) × ρ) × ι) =
      Fintype.card ((ι → F) × ρ) * Fintype.card ι by simp only [Fintype.card_prod]]
  have hcard : ((relSetWithCoins B A).card : ℝ≥0∞) ≤ (succSetWithCoins B A).card := by
    exact_mod_cast relSetWithCoins_card_le_succSetWithCoins_card B A
  have hn0 : (Fintype.card ((ι → F) × ρ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hnTop : (Fintype.card ((ι → F) × ρ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [one_div, div_eq_mul_inv, div_eq_mul_inv, Nat.cast_mul,
    ENNReal.mul_inv (Or.inl hn0) (Or.inl hnTop)]
  calc
    (Fintype.card ι : ℝ≥0∞)⁻¹ *
          ((relSetWithCoins B A).card * (Fintype.card ((ι → F) × ρ) : ℝ≥0∞)⁻¹)
        = (relSetWithCoins B A).card *
            ((Fintype.card ((ι → F) × ρ) : ℝ≥0∞)⁻¹ *
              (Fintype.card ι : ℝ≥0∞)⁻¹) := by ac_rfl
    _ ≤ (succSetWithCoins B A).card *
            ((Fintype.card ((ι → F) × ρ) : ℝ≥0∞)⁻¹ *
              (Fintype.card ι : ℝ≥0∞)⁻¹) := by gcongr

/-! ## Textbook single-generator DL game -/

/-- Winning coins for the textbook DL reduction, including the extractor's independent coins. -/
noncomputable def textbookWinSetWithCoins : Finset (F × ι × (ι → F) × ρ) :=
  Finset.univ.filter (fun t =>
    (((Function.update t.2.2.1 t.2.1 t.1, t.2.2.2), t.2.1) ∈ succSetWithCoins B A))

omit [Nonempty ι] [Nonempty ρ] in
/-- The textbook coin transformation preserves the extractor coins and has `|F|` preimages per
embedded-game outcome. -/
theorem textbookWinSetWithCoins_card :
    (textbookWinSetWithCoins B A).card =
      (succSetWithCoins B A).card * Fintype.card F := by
  rw [← Finset.card_univ (α := F), ← Finset.card_product]
  refine Finset.card_bij'
    (fun t _ =>
      ((((Function.update t.2.2.1 t.2.1 t.1, t.2.2.2), t.2.1)), t.2.2.1 t.2.1))
    (fun p _ =>
      (p.1.1.1 p.1.2, p.1.2, Function.update p.1.1.1 p.1.2 p.2, p.1.1.2))
    ?hi ?hj ?left ?right
  case hi =>
    rintro ⟨x, c, s, coins⟩ ht
    simp only [textbookWinSetWithCoins, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    simp only [Finset.mem_product, Finset.mem_univ, and_true]
    exact ht
  case hj =>
    rintro ⟨⟨⟨s, coins⟩, c⟩, y⟩ hp
    simp only [Finset.mem_product, Finset.mem_univ, and_true] at hp
    simp only [textbookWinSetWithCoins, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.update_idem, Function.update_eq_self]
    exact hp
  case left =>
    rintro ⟨x, c, s, coins⟩ _
    simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
  case right =>
    rintro ⟨⟨⟨s, coins⟩, c⟩, y⟩ _
    simp only [Function.update_self, Function.update_idem, Function.update_eq_self]

/-- The textbook and embedded DL experiments have equal success probability with extractor coins. -/
theorem textbookWithCoins_winProb_eq_succProb :
    (PMF.uniformOfFintype (F × ι × (ι → F) × ρ)).toOuterMeasure
        (textbookWinSetWithCoins B A)
      = (PMF.uniformOfFintype (((ι → F) × ρ) × ι)).toOuterMeasure
          (succSetWithCoins B A) := by
  rw [uniformOfFintype_toOuterMeasure_finset, uniformOfFintype_toOuterMeasure_finset,
    textbookWinSetWithCoins_card]
  have hcard : Fintype.card (F × ι × (ι → F) × ρ)
      = Fintype.card F * Fintype.card (((ι → F) × ρ) × ι) := by
    simp only [Fintype.card_prod]
    ring
  rw [hcard]
  push_cast
  rw [mul_comm ((succSetWithCoins B A).card : ℝ≥0∞) (Fintype.card F : ℝ≥0∞),
    ENNReal.mul_div_mul_left _ _
      (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)]

/-- A textbook DL bound for the actual randomized relation finder. -/
def TextbookDLWithCoinsAdvantageLE (bound : ℝ≥0∞) : Prop :=
  (PMF.uniformOfFintype (F × ι × (ι → F) × ρ)).toOuterMeasure
      (textbookWinSetWithCoins B A) ≤ bound

/-- Under textbook DL hardness, randomized relation production is bounded by the fixed-slot loss. -/
theorem relationWithCoins_prob_le_of_textbookDL {bound : ℝ≥0∞}
    (h : TextbookDLWithCoinsAdvantageLE B A bound) :
    (PMF.uniformOfFintype ((ι → F) × ρ)).toOuterMeasure (relSetWithCoins B A)
      ≤ Fintype.card ι * bound := by
  have hm0 : (Fintype.card ι : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hmTop : (Fintype.card ι : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hstep : (1 : ℝ≥0∞) / Fintype.card ι *
      (PMF.uniformOfFintype ((ι → F) × ρ)).toOuterMeasure (relSetWithCoins B A) ≤ bound :=
    le_trans (reductionWithCoins_advantage_ge B A)
      (by rw [← textbookWithCoins_winProb_eq_succProb]; exact h)
  have hmul : (Fintype.card ι : ℝ≥0∞) *
      ((1 : ℝ≥0∞) / Fintype.card ι *
        (PMF.uniformOfFintype ((ι → F) × ρ)).toOuterMeasure (relSetWithCoins B A))
      ≤ Fintype.card ι * bound := by gcongr
  rwa [one_div, ← mul_assoc, ENNReal.mul_inv_cancel hm0 hmTop, one_mul] at hmul

end Reduction

end Zcash.Snark
