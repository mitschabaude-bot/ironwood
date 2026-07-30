import Zcash.Snark.Soundness.AGM.AdaptiveIpaSurfaces

/-!
# Composed root pricing for arbitrary adaptive online-AGM adversaries

Query-local IPA quadratics are identified with the verifier's quadratics and their table bounds
are summed. Chronology comes from transcript prefixes and query annotations.
-/

namespace Zcash.Snark

open Classical CompPoly.CPolynomial
open scoped ENNReal

variable {shape : Shape}

local instance vestaInhabitedAdaptiveComposition : Inhabited VestaG := ⟨0⟩

/-- The polynomial fixed before round `j` reads only challenges strictly before `j`. -/
theorem ipaDiscrepancyPolynomialAt_eq_of_challenges_take_eq
    (initial : Fp) (rounds : List (Fp × Fp)) (challenges challenges' : List Fp) (j : Nat)
    (hlength : challenges.length = challenges'.length)
    (hchallenges : challenges.take j = challenges'.take j) :
    ipaDiscrepancyPolynomialAt initial rounds challenges j =
      ipaDiscrepancyPolynomialAt initial rounds challenges' j := by
  induction j generalizing initial rounds challenges challenges' with
  | zero =>
      cases rounds <;> cases challenges <;> cases challenges' <;>
        simp_all [ipaDiscrepancyPolynomialAt]
  | succ j ih =>
      cases rounds with
      | nil => rfl
      | cons round rounds =>
          cases challenges with
          | nil =>
              cases challenges' with
              | nil => rfl
              | cons challenge' challenges' => simp at hlength
          | cons challenge challenges =>
              cases challenges' with
              | nil => simp at hlength
              | cons challenge' challenges' =>
                  have hparts : challenge = challenge' ∧
                      challenges.take j = challenges'.take j := by
                    simpa only [List.take_succ_cons, List.cons.injEq] using hchallenges
                  rcases hparts with ⟨hhead, htail⟩
                  subst challenge'
                  exact ih (ipaDiscrepancyStep initial round challenge) rounds
                    challenges challenges' (by simpa using hlength) htail

/-- Pointwise agreement before `j` is enough to identify the round-`j` quadratic. -/
theorem adaptiveIpaRootPolynomial_eq_of_chi_before
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (coordinates : AdaptiveIpaCoordinateData basis)
    (hcover : ∀ nu : Fin 11 → Fp, ∀ pr,
      pr ∈ (multiopenMsm vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).other →
        ∃ ap ∈ coordinates.multiopenSource, ap.point = pr.2)
    (nu : Fin 11 → Fp) (chi chi' : Fin shape.k → Fp) (j : Fin shape.k)
    (hchi : ∀ i : Fin shape.k, i.val < j.val → chi i = chi' i) :
    adaptiveIpaRootPolynomial vk instanceCommitment ps coordinates hcover nu chi j =
      adaptiveIpaRootPolynomial vk instanceCommitment ps coordinates hcover nu chi' j := by
  unfold adaptiveIpaRootPolynomial
  apply ipaDiscrepancyPolynomialAt_eq_of_challenges_take_eq
  · simp
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_take, List.getElem_ofFn]
    have hij : i < j.val := by simpa using hi'
    exact hchi ⟨i, lt_trans hij j.isLt⟩ (by simpa using hi)

set_option maxHeartbeats 3200000 in
/-- Canonicalizing the unused IPA suffix does not change the initial straight-line data. -/
theorem OnlineMemberProofData.adaptiveIpaCanonicalRootPolynomial_eq
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed)
    (nu : Fin 11 → Fp) (chi : Fin shape.k → Fp) (j : Fin shape.k) :
    adaptiveIpaRootPolynomial vk instanceCommitment
        (adaptiveIpaCanonicalProof data.algebraicProof.erase)
        data.adaptiveIpaCoordinates (by
          intro rho pr hpr
          exact data.assemblyCovered rho pr hpr) nu chi j =
      data.toAlgebraicWfProof.straightLineIpaRootPolynomial nu chi j := by
  unfold adaptiveIpaRootPolynomial AlgebraicWfProof.straightLineIpaRootPolynomial
  rw [data.toAlgebraicWfProof.straightLineInitialDiscrepancy_eq nu]
  rfl

set_option maxHeartbeats 800000 in
/-- The shorter pre-IPA views of an actual IPA prefix are its actual verifier prefixes. -/
theorem adaptiveIpaPreRecord_fullPrefixes
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    (init : List (TranscriptElt Fp VestaG))
    (p : AlgebraicWfProof basis vk instanceCommitment) (j : Fin shape.k)
    (O : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k) → Fp) :
    adaptiveIpaPreRecord (shape := shape) init (algebraicFullPrefixes init p j) O =
      fun n => O (algebraicFullPrefixesPre init p n) := by
  funext n
  unfold adaptiveIpaPreRecord adaptiveEarlierPrefix
  congr 1
  exact (fullDecodeDeployed shape init).chainPre_prefixes p.proof j n

set_option maxHeartbeats 800000 in
/-- The shorter IPA-round views of an actual round prefix are its actual earlier round prefixes. -/
theorem adaptiveIpaRoundRecord_fullPrefixes_before
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    (init : List (TranscriptElt Fp VestaG))
    (p : AlgebraicWfProof basis vk instanceCommitment) (j i : Fin shape.k)
    (hij : i.val < j.val)
    (O : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k) → Fp) :
    adaptiveIpaRoundRecord (shape := shape) init j (algebraicFullPrefixes init p j) O i =
      O (algebraicFullPrefixes init p i) := by
  change (if h : i.val < j.val then
      O (adaptiveEarlierRoundPrefix (shape := shape) init
        (algebraicFullPrefixes init p j) i) else 0) = _
  rw [dif_pos hij]
  change O ((fullDecodeDeployed shape init).chainAt
      (algebraicFullPrefixes init p j) i) = _
  change O ((fullDecodeDeployed shape init).chainAt
      (fullPrefixes init p.proof j) i) = O (fullPrefixes init p.proof i)
  rw [(fullDecodeDeployed shape init).chainAt_prefixes p.proof j i (Nat.le_of_lt hij)]

set_option maxHeartbeats 1600000 in
/-- At the verifier's actual round point, the fallback surface is exactly its straight-line
quadratic root set. -/
theorem ComputedAdaptiveOnlineAGMFSFamily.adaptiveIpaFallbackBad_actual
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (j : Fin shape.k) :
    let data := (family.adversary basis).run O
    let p := data.toAlgebraicWfProof
    let nu : Fin 11 → Fp := fun n => O (algebraicFullPrefixesPre family.init p n)
    let chi : Fin shape.k → Fp := fun i => O (algebraicFullPrefixes family.init p i)
    adaptiveIpaFallbackBad family basis j data (algebraicFullPrefixes family.init p j) O =
      szBadSet (p.straightLineIpaRootPolynomial nu chi j) := by
  dsimp only
  let data := (family.adversary basis).run O
  let p := data.toAlgebraicWfProof
  let nu : Fin 11 → Fp := fun n => O (algebraicFullPrefixesPre family.init p n)
  let chi : Fin shape.k → Fp := fun i => O (algebraicFullPrefixes family.init p i)
  have hlen := algebraicFullPrefixes_length_eq_adaptiveIpaRoundLen family.init p j
  have hcover := data.adaptiveIpaCanonicalCovered j
  unfold adaptiveIpaFallbackBad adaptiveFallbackIpaSurface adaptiveFallbackIpaSurfaceCore
  rw [if_pos hlen, dif_pos hcover]
  have hnu : adaptiveIpaPreRecord (shape := shape) family.init
      (algebraicFullPrefixes family.init p j) O = nu := by
    exact adaptiveIpaPreRecord_fullPrefixes family.init p j O
  rw [hnu]
  apply congrArg (fun polynomial : CPoly => (szBadSet polynomial : Set Fp))
  calc
    adaptiveIpaRootPolynomial (family.vk basis) (family.instanceCommitment basis)
        (adaptiveIpaCanonicalProof data.algebraicProof.erase)
        (data.adaptiveIpaCoordinates.prefix basis j) hcover nu
        (adaptiveIpaRoundRecord (shape := shape) family.init j
          (algebraicFullPrefixes family.init p j) O) j =
      adaptiveIpaRootPolynomial (family.vk basis) (family.instanceCommitment basis)
        (adaptiveIpaCanonicalProof data.algebraicProof.erase)
        data.adaptiveIpaCoordinates (by
          intro rho pr hpr
          exact data.assemblyCovered rho pr hpr) nu
        (adaptiveIpaRoundRecord (shape := shape) family.init j
          (algebraicFullPrefixes family.init p j) O) j :=
        adaptiveIpaRootPolynomial_prefix _ _ _ _ _ _ _ j
    _ = adaptiveIpaRootPolynomial (family.vk basis) (family.instanceCommitment basis)
        (adaptiveIpaCanonicalProof data.algebraicProof.erase)
        data.adaptiveIpaCoordinates (by
          intro rho pr hpr
          exact data.assemblyCovered rho pr hpr) nu chi j := by
        apply adaptiveIpaRootPolynomial_eq_of_chi_before
        intro i hij
        exact adaptiveIpaRoundRecord_fullPrefixes_before family.init p j i hij O
    _ = p.straightLineIpaRootPolynomial nu chi j :=
        data.adaptiveIpaCanonicalRootPolynomial_eq nu chi j

/-- The actual verifier IPA-root event with no provenance relation. -/
def ComputedAdaptiveOnlineAGMFSFamily.adaptiveIpaBadWithoutRelation
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k) :
    Set (BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :=
  {O | let data := (family.adversary basis).run O
    let p := data.toAlgebraicWfProof
    let nu : Fin 11 → Fp := fun n => O (algebraicFullPrefixesPre family.init p n)
    let chi : Fin shape.k → Fp := fun i => O (algebraicFullPrefixes family.init p i)
    chi j ∈ szBadSet (p.straightLineIpaRootPolynomial nu chi j) ∧
      family.adaptiveIpaRepresentationRelationFinder basis O = none}

/-- Each actual IPA round has the annotation-aware adaptive squeeze price. -/
theorem ComputedAdaptiveOnlineAGMFSFamily.adaptiveIpaBadWithoutRelation_measure_le
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k) :
    (PMF.uniformOfFintype (BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)).toOuterMeasure
      (family.adaptiveIpaBadWithoutRelation basis j) ≤
        (family.Q + 1 : Nat) * (2 / (Fintype.card Fp : ENNReal)) := by
  have heq : family.adaptiveIpaBadWithoutRelation basis j =
      {O | let data := (family.adversary basis).run O
        let t := algebraicFullPrefixes family.init data.toAlgebraicWfProof j
        O t ∈ adaptiveIpaFallbackBad family basis j data t O ∧
          family.adaptiveIpaRepresentationRelationFinder basis O = none} := by
    ext O
    simp only [ComputedAdaptiveOnlineAGMFSFamily.adaptiveIpaBadWithoutRelation,
      Set.mem_setOf_eq]
    rw [family.adaptiveIpaFallbackBad_actual basis O j]
    rfl
  rw [heq]
  exact family.adaptiveFinalIpaBadWithoutRelation_table_le basis j

/-- The union of all actual IPA-round roots is additive. -/
theorem ComputedAdaptiveOnlineAGMFSFamily.adaptiveIpaBadWithoutRelation_all_measure_le
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) :
    (PMF.uniformOfFintype (BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)).toOuterMeasure
      {O | ∃ j : Fin shape.k, O ∈ family.adaptiveIpaBadWithoutRelation basis j} ≤
        shape.k * ((family.Q + 1 : Nat) *
          (2 / (Fintype.card Fp : ENNReal))) := by
  have hsub : {O | ∃ j : Fin shape.k,
      O ∈ family.adaptiveIpaBadWithoutRelation basis j} ⊆
      ⋃ j : Fin shape.k, family.adaptiveIpaBadWithoutRelation basis j := by
    rintro O ⟨j, hj⟩
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  rw [tsum_fintype]
  calc
    ∑ j : Fin shape.k,
        (PMF.uniformOfFintype (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)).toOuterMeasure
          (family.adaptiveIpaBadWithoutRelation basis j) ≤
      ∑ _j : Fin shape.k,
        ((family.Q + 1 : Nat) * (2 / (Fintype.card Fp : ENNReal))) := by
          gcongr with j
          exact family.adaptiveIpaBadWithoutRelation_measure_le basis j
    _ = shape.k * ((family.Q + 1 : Nat) *
        (2 / (Fintype.card Fp : ENNReal))) := by simp

/-- The adaptive index translation is inverse to the deployed six-root ordering. -/
@[simp] theorem adaptiveRootEventIndex_deployedRootChallengeIndex (i : Fin 6) :
    adaptiveRootEventIndex (deployedRootChallengeIndex i) = i := by
  fin_cases i <;> rfl

/-- One actual deployed-root event, excluding the executable pre-IPA provenance relation. -/
def ComputedAdaptiveOnlineAGMFSFamily.adaptiveRootBadWithoutRelation
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (i : Fin 6) :
    Set (BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :=
  {O | let data := (family.adversary basis).run O
    let n := deployedRootChallengeIndex i
    let t := algebraicFullPrefixesPre family.init data.toAlgebraicWfProof n
    O t ∈ adaptiveFinalRootBad family basis n data t O ∧
      family.adaptivePreIpaRepresentationRelationFinder basis O = none}

/-- Each actual deployed root has its direct-route adaptive squeeze price. -/
theorem ComputedAdaptiveOnlineAGMFSFamily.adaptiveRootBadWithoutRelation_measure_le
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (i : Fin 6) :
    (PMF.uniformOfFintype (BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)).toOuterMeasure
      (family.adaptiveRootBadWithoutRelation basis i) ≤
        (family.Q + 1 : Nat) * deployedRootEventBudget shape i := by
  let n := deployedRootChallengeIndex i
  have h5n : 5 ≤ (n : Nat) := by
    fin_cases i <;> norm_num [n, deployedRootChallengeIndex]
  have hbound := family.adaptiveFinalRootBadWithoutRelation_table_le basis n h5n
  simpa only [ComputedAdaptiveOnlineAGMFSFamily.adaptiveRootBadWithoutRelation,
    n, adaptiveRootEventIndex_deployedRootChallengeIndex] using hbound

/-- The six actual deployed roots sum to the existing conservative shape budget. -/
theorem ComputedAdaptiveOnlineAGMFSFamily.adaptiveRootBadWithoutRelation_all_measure_le
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) :
    (PMF.uniformOfFintype (BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)).toOuterMeasure
      {O | ∃ i : Fin 6, O ∈ family.adaptiveRootBadWithoutRelation basis i} ≤
        (family.Q + 1 : Nat) * algebraicRootBudget shape shape.k := by
  have hsub : {O | ∃ i : Fin 6, O ∈ family.adaptiveRootBadWithoutRelation basis i} ⊆
      ⋃ i : Fin 6, family.adaptiveRootBadWithoutRelation basis i := by
    rintro O ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  rw [tsum_fintype]
  calc
    ∑ i : Fin 6,
        (PMF.uniformOfFintype (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)).toOuterMeasure
          (family.adaptiveRootBadWithoutRelation basis i) ≤
      ∑ i : Fin 6, (family.Q + 1 : Nat) * deployedRootEventBudget shape i := by
        gcongr with i
        exact family.adaptiveRootBadWithoutRelation_measure_le basis i
    _ = (family.Q + 1 : Nat) *
        ∑ i : Fin 6, deployedRootEventBudget shape i := by rw [Finset.mul_sum]
    _ ≤ (family.Q + 1 : Nat) * algebraicRootBudget shape shape.k := by
      gcongr
      exact deployedRootEventBudget_sum_le shape

/-- A binding attack with no executable combined relation lands in one of the actual adaptive
IPA events.  This is the deterministic bridge from the verifier equation to the table pricing
above. -/
lemma ComputedAdaptiveOnlineAGMFSFamily.adaptiveBindingAttack_ipaBad
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (hattack : let data := (family.adversary basis).run O
      fullAlgebraicBindingAttackZ basis (family.vk basis)
        (family.instanceCommitment basis) data.toAlgebraicWfProof
        (fun n => O (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof n))
        (fun j => O (algebraicFullPrefixes family.init data.toAlgebraicWfProof j)))
    (hnone : family.adaptiveStraightLineDeployedRelationFinder basis O = none) :
    ∃ j : Fin shape.k, O ∈ family.adaptiveIpaBadWithoutRelation basis j := by
  let data := (family.adversary basis).run O
  let p := data.toAlgebraicWfProof
  let nu : Fin 11 → Fp := fun n => O (algebraicFullPrefixesPre family.init p n)
  let chi : Fin shape.k → Fp := fun j => O (algebraicFullPrefixes family.init p j)
  have hipaNone := family.adaptiveStraightLineDeployedRelationFinder_none_ipa basis O hnone
  have hprovenance :=
    family.adaptiveStraightLineDeployedRelationFinder_none_provenance basis O hnone
  cases hsplit : p.straightLineBindingAttackZIndexedRootOrRelation nu chi hattack with
  | inl root =>
      obtain ⟨j, hj⟩ := root
      refine ⟨j, ?_⟩
      exact ⟨hj, hprovenance.2⟩
  | inr relation =>
      exfalso
      simp only [adaptiveStraightLineIpaRelationFinder] at hipaNone
      rw [dif_pos hattack, hsplit] at hipaNone
      simp at hipaNone

end Zcash.Snark
