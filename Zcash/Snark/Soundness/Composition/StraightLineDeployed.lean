import Zcash.Snark.Soundness.AGM.DirectX4Columns
import Zcash.Snark.Soundness.AGM.StraightLinePinnedRoots
import Zcash.Snark.Soundness.Composition.DeployedRootContainment
import Zcash.Snark.Soundness.Composition.DeployedConstraintContainment

/-!
# Straight-line AGM composition through deployed multiopen decoding

This module combines the one-run IPA extractor with the deployed batch/root decoder to form the
deployed AGM composition.
-/

namespace Zcash.Snark

open Classical
open scoped ENNReal

local instance vestaInhabitedStraightLineDeployed : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

/-- A deployed online-AGM family carrying the existing six-root multiopen chronology, the staged
constraint-`x` chronology, and the new per-IPA-round chronology.  Carrying the constraint-`x` trace
here is what lets the captured endpoints derive exact `x` pinning instead of assuming it. -/
structure ComputedStraightLineDeployedFSFamily (shape : Shape)
    extends ComputedDeployedRootFSFamily shape where
  ipaTrace : StraightLineIpaOnlineTrace toComputedAlgebraicFSFamily
  constraintXTrace : DeployedConstraintXOnlineTrace toComputedDeployedRootFSFamily

namespace ComputedStraightLineDeployedFSFamily

/-- **Adapter constructor from the online representation-carrying prover model.**  The online
family already supplies canonical aggregate coordinates and deployed-member coverage; the three
staged traces add the six deployed root computations, the IPA-round computations, and the
constraint-`x` computation.  Callers supply those executable stages with their freshness proofs.

The captured Orchard key profile is applied to the result by the fixture endpoint, not here. -/
def ofCovered
    (online : ComputedOnlineMemberFSFamily shape)
    (rootTrace : DeployedRootOnlineTrace online.toFamily
      (deployedRootOutcomeOfCovered online))
    (ipaTrace : StraightLineIpaOnlineTrace online.toFamily)
    (xTrace : DeployedConstraintXOnlineTrace
      (ComputedDeployedRootFSFamily.ofCovered online rootTrace)) :
    ComputedStraightLineDeployedFSFamily shape where
  toComputedDeployedRootFSFamily :=
    ComputedDeployedRootFSFamily.ofCovered online rootTrace
  ipaTrace := ipaTrace
  constraintXTrace := xTrace

/-- Forget the IPA chronology while retaining the deployed multiopen root family. -/
abbrev toRootFamily (family : ComputedStraightLineDeployedFSFamily shape) :
    ComputedDeployedRootFSFamily shape := family.toComputedDeployedRootFSFamily

/-- Forget the IPA chronology while retaining both deployed chronology refinements. -/
abbrev toConstraintFamily (family : ComputedStraightLineDeployedFSFamily shape) :
    ComputedDeployedConstraintFSFamily shape :=
  .ofRoot family.toRootFamily family.constraintXTrace

/-- Exact constraint-`x` pinning derived from the family's own staged trace. -/
theorem pinnedX (family : ComputedStraightLineDeployedFSFamily shape) :
    DeployedConstraintXPinning family.toRootFamily :=
  family.constraintXTrace.toPinning

/-- Forget both chronology refinements. -/
abbrev toFamily (family : ComputedStraightLineDeployedFSFamily shape) :
    ComputedAlgebraicFSFamily shape := family.toComputedAlgebraicFSFamily

/-- View the same adversary through the straight-line IPA interface. -/
def toIpaFamily (family : ComputedStraightLineDeployedFSFamily shape) :
    ComputedStraightLineIpaFSFamily shape where
  toComputedAlgebraicFSFamily := family.toFamily
  ipaTrace := family.ipaTrace

/-- The direct deployed relation finder: first the one-run IPA branch, then the existing online
multiopen outcome.  It reads the run's own oracle table and rewinds nothing. -/
def straightLineDeployedRelationFinder
    (family : ComputedStraightLineDeployedFSFamily shape) :
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) ->
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    match family.toIpaFamily.straightLineIpaRelationFinder basis O with
    | some relation => some relation
    | none =>
        match family.outcome basis O with
        | PSum.inl _ => none
        | PSum.inr relation =>
            some (ComputedStraightLineIpaFSFamily.straightLineCanonicalRelation relation)

/-- The existing deployed root decode, indexed by the one-run oracle table. -/
def straightLineRootDecoded (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) : Prop :=
  deployedRootDecoded family.toRootFamily basis O

/-- The direct root-layer output is either an explicit relation or the complete deployed decode. -/
def straightLineRootExtracted (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) : Prop :=
  (family.straightLineDeployedRelationFinder basis O).isSome ∨
    family.straightLineRootDecoded basis O

/-- The exact shifted aggregate-value equality needed by the deployed root decoder. -/
def StraightLineShiftedValue (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) : Prop :=
  let pnu := (wrappedAdversary family.toFamily basis).run O
  let nu := wrappedPreIpaReads pnu
  let ch := wrappedPreIpaRecord pnu
  ch.z ≠ 0 ∧
    commitGen (evalVector shape.k ch.x3) (pnu.1.aMulti nu) =
      multiopenValue (family.vk basis) (family.instanceCommitment basis)
        pnu.1.proof.1 ch +
        ch.z⁻¹ * (pnu.1.multiU nu + ch.xi * pnu.1.sU) -
          ch.xi * commitGen (evalVector shape.k ch.x3) pnu.1.s

/-- On an accepted nonzero-`z` run, absence of the binding attack is exactly the shifted aggregate
value equality used by the root decoder. -/
theorem straightLineShiftedValue_of_accept_not_attack
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (haccept : fullAlgebraicAccept basis (family.vk basis)
      (family.instanceCommitment basis) (runProof family.toFamily basis O)
      (runReads family.toFamily basis O) (runRounds family.toFamily basis O))
    (hz : runReads family.toFamily basis O 10 ≠ 0)
    (hnot : ¬fullAlgebraicBindingAttackZ basis (family.vk basis)
      (family.instanceCommitment basis) (runProof family.toFamily basis O)
      (runReads family.toFamily basis O) (runRounds family.toFamily basis O)) :
    family.StraightLineShiftedValue basis O := by
  have heq : innerProduct
      ((runProof family.toFamily basis O).aMulti (runReads family.toFamily basis O))
      (evalVector shape.k (runReads family.toFamily basis O 7)) =
    multiopenValue (family.vk basis) (family.instanceCommitment basis)
      (runProof family.toFamily basis O).proof.1
      (chRecord (runReads family.toFamily basis O) (fun _ => 0)) +
      (runReads family.toFamily basis O 10)⁻¹ *
        ((runProof family.toFamily basis O).multiU (runReads family.toFamily basis O) +
          runReads family.toFamily basis O 9 *
            (runProof family.toFamily basis O).sU) -
      runReads family.toFamily basis O 9 *
        innerProduct (runProof family.toFamily basis O).s
          (evalVector shape.k (runReads family.toFamily basis O 7)) := by
    by_contra hmismatch
    exact hnot ⟨⟨haccept, hmismatch⟩, hz⟩
  constructor
  · simpa [StraightLineShiftedValue, wrappedPreIpaRecord, wrappedAdversary_run_fst,
      wrappedPreIpaReads_run, chRecord] using hz
  · simpa [StraightLineShiftedValue, wrappedPreIpaRecord, wrappedAdversary_run_fst,
      wrappedPreIpaReads_run, commitGen, innerProduct] using heq

/-- Avoiding the existing six multiopen root sets turns the straight-line shifted value into the
complete deployed member decode. -/
theorem straightLineRootDecoded_of_shiftedValue
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (witness : DeployedBatchWitness family.toFamily basis
      ((wrappedAdversary family.toFamily basis).run O))
    (hout : family.outcome basis O = PSum.inl witness)
    (hroots : ¬(family.toRootFamily.pinnedRoots basis).Landing O)
    (hshifted : family.StraightLineShiftedValue basis O) :
    family.straightLineRootDecoded basis O := by
  let pnu := (wrappedAdversary family.toFamily basis).run O
  let nu := wrappedPreIpaReads pnu
  let ch := wrappedPreIpaRecord pnu
  have hgood := family.toRootFamily.goodRoots_of_not_landing basis O witness hout hroots
  have hz : ch.z ≠ 0 := hshifted.1
  have hshifted' : commitGen (evalVector shape.k ch.x3) (pnu.1.aMulti nu) =
      multiopenValue (family.vk basis) (family.instanceCommitment basis)
        pnu.1.proof.1 ch +
        ch.z⁻¹ * (pnu.1.multiU nu + ch.xi * pnu.1.sU) -
          ch.xi * commitGen (evalVector shape.k ch.x3) pnu.1.s := hshifted.2
  have hgoodXi : ch.xi ∉ szBadSet
      (ipaShiftXiPolynomial
        (commitGen (evalVector shape.k ch.x3) (pnu.1.aMulti nu) -
          multiopenValue (family.vk basis) (family.instanceCommitment basis)
            pnu.1.proof.1 ch)
        (commitGen (evalVector shape.k ch.x3) pnu.1.s)) := by
    simpa [deployedRootBad, hout, pnu, nu, ch, wrappedPreIpaRecord] using hgood.xi
  have hgoodZ : ch.z ∉ szBadSet
      (ipaShiftZPolynomial
        (commitGen (evalVector shape.k ch.x3) (pnu.1.aMulti nu) -
          multiopenValue (family.vk basis) (family.instanceCommitment basis)
            pnu.1.proof.1 ch)
        (pnu.1.multiU nu) pnu.1.sU
        (commitGen (evalVector shape.k ch.x3) pnu.1.s) ch.xi) := by
    simpa [deployedRootBad, hout, pnu, nu, ch, wrappedPreIpaRecord] using hgood.z
  have hvalue : commitGen (evalVector shape.k ch.x3) (pnu.1.aMulti nu) =
      multiopenValue (family.vk basis) (family.instanceCommitment basis)
        pnu.1.proof.1 ch :=
    rawValue_of_shiftedValue_of_good _ _ _ _ _ _ _ hz hshifted' hgoodXi hgoodZ
  have hgood4 : ch.x4 ∉ deployedX4RootSet
      (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
        (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches := by
    simpa [deployedRootBad, hout, pnu, nu, ch, wrappedPreIpaRecord] using hgood.x4
  have hgood3 : ch.x3 ∉ deployedX3RootSet
      (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
        (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches := by
    simpa [deployedRootBad, hout, pnu, nu, ch, wrappedPreIpaRecord] using hgood.x3
  have hgood2 : ch.x2 ∉ deployedX2RootSet
      (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
        (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches := by
    simpa [deployedRootBad, hout, pnu, nu, ch, wrappedPreIpaRecord] using hgood.x2
  have hgood1All : ch.x1 ∉ deployedX1AllRootSet
      (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
        (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches := by
    simpa [deployedRootBad, hout, pnu, nu, ch, wrappedPreIpaRecord] using hgood.x1
  have hgood1 := not_mem_deployedX1RootSet_of_not_mem_all
    (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches hgood1All
  let decoded := deployedAlgebraicDecode_of_good_roots
    (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches
      hvalue hgood4 hgood3 hgood2 hgood1
  exact ⟨{
    batchWitness := witness
    outcome_eq := hout
    decoded := decoded
    batches_eq := rfl }⟩

/-- Pointwise straight-line root containment.  An accepted run missing both the direct relation
and deployed decode must lie in the `z = 0` slice, an IPA-round quadratic, or one of the existing
six multiopen root events. -/
theorem straightLineRootFailure
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (haccept : fullAlgebraicAccept basis (family.vk basis)
      (family.instanceCommitment basis) (runProof family.toFamily basis O)
      (runReads family.toFamily basis O) (runRounds family.toFamily basis O))
    (hfailure : ¬family.straightLineRootExtracted basis O) :
    runReads family.toFamily basis O 10 = 0 ∨
      (family.toIpaFamily.pinnedIpaRoots basis).Landing O ∨
      (family.toRootFamily.pinnedRoots basis).Landing O := by
  by_cases hz : runReads family.toFamily basis O 10 = 0
  · exact Or.inl hz
  · apply Or.inr
    by_cases hattack : fullAlgebraicBindingAttackZ basis (family.vk basis)
        (family.instanceCommitment basis) (runProof family.toFamily basis O)
        (runReads family.toFamily basis O) (runRounds family.toFamily basis O)
    · rcases family.toIpaFamily.pinnedIpaRoots_landing_or_relation basis O hattack with
        hroot | hrelation
      · exact Or.inl hroot
      · exfalso
        apply hfailure
        apply Or.inl
        unfold straightLineDeployedRelationFinder
        cases hipa : family.toIpaFamily.straightLineIpaRelationFinder basis O with
        | none => simp [hipa] at hrelation
        | some relation => simp
    · have hshifted := family.straightLineShiftedValue_of_accept_not_attack
        basis O haccept hz hattack
      cases hout : family.outcome basis O with
      | inr relation =>
          exfalso
          apply hfailure
          apply Or.inl
          unfold straightLineDeployedRelationFinder
          cases hipa : family.toIpaFamily.straightLineIpaRelationFinder basis O <;>
            simp [hout]
      | inl witness =>
          by_cases hroots : (family.toRootFamily.pinnedRoots basis).Landing O
          · exact Or.inr hroots
          · exfalso
            apply hfailure
            apply Or.inr
            exact family.straightLineRootDecoded_of_shiftedValue
              basis O witness hout hroots hshifted

/-- The direct deployed finder reduces to textbook DLOG with the programmed-slot loss. -/
theorem straightLineDeployedRelation_prob_le_of_textbookDL
    (B : VestaG) (family : ComputedStraightLineDeployedFSFamily shape) {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      family.straightLineDeployedRelationFinder bound) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        (relSetWithCoins B family.straightLineDeployedRelationFinder) <=
      bound + 1 / Fintype.card Fp :=
  relationWithCoins_prob_le_of_textbookDL B family.straightLineDeployedRelationFinder hDL

/-! ## Root-layer probability capstone -/

/-- Scalar-basis/oracle pairs on which deployed acceptance holds but the complete root decode is
missing.  Unlike `straightLineRootExtracted`, this event treats a returned relation as a security
failure to be charged to DLOG. -/
def straightLineRootDecodeFailureSet (B : VestaG)
    (family : ComputedStraightLineDeployedFSFamily shape) :
    Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
  {q |
    let basis := scalarBasis B q.1
    fsWinsFull (family.adversary basis)
      (fullAlgebraicAccept basis (family.vk basis) (family.instanceCommitment basis))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) q.2 ∧
    ¬family.straightLineRootDecoded basis q.2}

/-- The adaptive `z = 0` slice of root-decode failure. -/
def straightLineRootZeroSet (B : VestaG)
    (family : ComputedStraightLineDeployedFSFamily shape) :
    Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
  {q |
    let basis := scalarBasis B q.1
    fsWinsFull (family.adversary basis)
      (fullAlgebraicAccept basis (family.vk basis) (family.instanceCommitment basis))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) q.2 ∧
    q.2 (algebraicFullPrefixesPre family.init
      ((family.adversary basis).run q.2) 10) = 0}

/-- A missing deployed root decode is covered by the zero slice, the straight-line IPA roots,
the existing six deployed roots, or the single combined relation event. -/
theorem straightLineRootDecodeFailureSet_subset
    (B : VestaG) (family : ComputedStraightLineDeployedFSFamily shape) :
    family.straightLineRootDecodeFailureSet B <=
      family.straightLineRootZeroSet B ∪
        ({q | (family.toIpaFamily.pinnedIpaRoots (scalarBasis B q.1)).Landing q.2} ∪
          ({q | (family.toRootFamily.pinnedRoots (scalarBasis B q.1)).Landing q.2} ∪
            (relSetWithCoins B family.straightLineDeployedRelationFinder :
              Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
                (BTranscript Fp VestaG
                  (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))))) := by
  intro q hfailure
  let basis := scalarBasis B q.1
  by_cases hrelation :
      (family.straightLineDeployedRelationFinder basis q.2).isSome
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    simpa [relSetWithCoins, basis] using hrelation
  · have hnotExtracted : ¬family.straightLineRootExtracted basis q.2 := by
      rintro (hfound | hdecoded)
      · exact hrelation hfound
      · exact hfailure.2 hdecoded
    have hsplit := family.straightLineRootFailure basis q.2 hfailure.1 hnotExtracted
    rcases hsplit with hzero | hipa | hroot
    · apply Or.inl
      exact ⟨hfailure.1, hzero⟩
    · exact Or.inr (Or.inl hipa)
    · exact Or.inr (Or.inr (Or.inl hroot))

/-- The root-layer zero slice has the standard `(Q+1)/|Fp|` adaptive-query cost. -/
theorem straightLineRootZero_prob_le
    (B : VestaG) (family : ComputedStraightLineDeployedFSFamily shape) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        (family.straightLineRootZeroSet B) <=
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) := by
  apply uniformOfFintype_prod_fiber_bound_right
    (fun logs =>
      let basis := scalarBasis B logs
      {O | fsWinsFull (family.adversary basis)
          (fullAlgebraicAccept basis (family.vk basis)
            (family.instanceCommitment basis))
          (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) O ∧
        O (algebraicFullPrefixesPre family.init
          ((family.adversary basis).run O) 10) = 0})
  intro logs
  let basis := scalarBasis B logs
  exact fsAdvantageFull_zero_slice_le (family.adversary basis)
    (fullAlgebraicAccept basis (family.vk basis) (family.instanceCommitment basis))
    (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) 10
    (family.queryBound basis)

/-- The existing six deployed roots retain their wrapped-query cost. -/
theorem straightLineDeployedRoots_prob_le
    (B : VestaG) (family : ComputedStraightLineDeployedFSFamily shape) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        {q | (family.toRootFamily.pinnedRoots (scalarBasis B q.1)).Landing q.2} <=
      (family.Q + (11 + shape.k) + 1 : Nat) *
        algebraicRootBudget shape shape.k := by
  apply uniformOfFintype_prod_fiber_bound_right
    (fun logs =>
      {O | (family.toRootFamily.pinnedRoots (scalarBasis B logs)).Landing O})
  intro logs
  let basis := scalarBasis B logs
  refine le_trans ((family.toRootFamily.pinnedRoots basis).landing_measure_le
    (queryBound_wrappedAdversary family.toFamily basis)) ?_
  exact mul_le_mul_right (family.toRootFamily.pinnedRoots_budget_le basis) _

/-- Straight-line deployed root capstone.  It charges the relation finder once and contains no
expectation, truncation budget, or Markov tail. -/
theorem straightLineRootDecodeFailure_prob_le_of_textbookDL
    (B : VestaG) (family : ComputedStraightLineDeployedFSFamily shape) {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      family.straightLineDeployedRelationFinder bound) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        (family.straightLineRootDecodeFailureSet B) <=
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          (shape.k * (2 / (Fintype.card Fp : ENNReal))) +
        (family.Q + (11 + shape.k) + 1 : Nat) *
          algebraicRootBudget shape shape.k +
        (bound + 1 / Fintype.card Fp) := by
  let zeroSet := family.straightLineRootZeroSet B
  let ipaSet : Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
    {q | (family.toIpaFamily.pinnedIpaRoots (scalarBasis B q.1)).Landing q.2}
  let rootSet : Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
    {q | (family.toRootFamily.pinnedRoots (scalarBasis B q.1)).Landing q.2}
  let relationSet : Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
    relSetWithCoins B family.straightLineDeployedRelationFinder
  have hzero := family.straightLineRootZero_prob_le B
  have hipa : (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ipaSet <=
      (family.Q + 1 : Nat) *
        (shape.k * (2 / (Fintype.card Fp : ENNReal))) := by
    apply uniformOfFintype_prod_fiber_bound_right
      (fun logs =>
        {O | (family.toIpaFamily.pinnedIpaRoots (scalarBasis B logs)).Landing O})
    intro logs
    exact family.toIpaFamily.pinnedIpaRoots_landing_measure_le (scalarBasis B logs)
  have hroot := family.straightLineDeployedRoots_prob_le B
  have hrelation := family.straightLineDeployedRelation_prob_le_of_textbookDL B hDL
  refine le_trans (MeasureTheory.measure_mono
    (family.straightLineRootDecodeFailureSet_subset B)) ?_
  refine le_trans (MeasureTheory.measure_union_le zeroSet
    (ipaSet ∪ (rootSet ∪ relationSet))) ?_
  refine le_trans (add_le_add hzero
    (MeasureTheory.measure_union_le ipaSet (rootSet ∪ relationSet))) ?_
  refine le_trans (add_le_add le_rfl (add_le_add hipa
    (MeasureTheory.measure_union_le rootSet relationSet))) ?_
  calc
    _ <= (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          ((family.Q + 1 : Nat) *
              (shape.k * (2 / (Fintype.card Fp : ENNReal))) +
            ((family.Q + (11 + shape.k) + 1 : Nat) *
                algebraicRootBudget shape shape.k +
              (bound + 1 / Fintype.card Fp))) :=
      add_le_add le_rfl (add_le_add le_rfl (add_le_add hroot hrelation))
    _ = _ := by ring

end ComputedStraightLineDeployedFSFamily

end Zcash.Snark
