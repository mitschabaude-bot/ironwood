import Zcash.Snark.Soundness.Composition.StraightLineDeployed
import Zcash.Snark.Soundness.Composition.DeployedConstraintContainment

/-!
# Straight-line AGM composition through the deployed constraint relation

This module lifts the one-table straight-line IPA/root extractor through the existing online
constraint adapter.  It is additive to the recursive/reprogramming AGM capstone.  The fixed dummy
tape below is only an index used to reuse proof-only decode provenance; the new relation finder
never invokes the recursive extractor.
-/

namespace Zcash.Snark

open Classical
open scoped ENNReal

local instance vestaInhabitedStraightLineConstraint : Inhabited VestaG := ⟨0⟩

attribute [local irreducible] deployedConstraintDifferencePreX

variable {shape : Shape}

namespace ComputedStraightLineDeployedFSFamily

/-- Relation-only projection of the existing online quotient comparison on the one-run table. -/
def straightLineConstraintQuotientFinder
    (family : ComputedStraightLineDeployedFSFamily shape) :
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) ->
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    let pnu := (wrappedAdversary family.toFamily basis).run O
    match family.outcome basis O with
    | PSum.inr _ => none
    | PSum.inl _ =>
        match deployedConstraintQuotientAgreementOrRelation
            family.toRootFamily basis pnu with
        | PSum.inl _ => none
        | PSum.inr relation =>
            some (augmentedBasis_ursOfAugmentedBasis shape.k basis ▸
              relation.toAlgebraicRelationWitness)

/-- Complete straight-line relation finder: IPA, deployed unbatching, then quotient collision.
Every branch returns explicit relation coefficients and no branch calls the recursive extractor. -/
def straightLineConstraintRelationFinder
    (family : ComputedStraightLineDeployedFSFamily shape) :
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) ->
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    match family.straightLineDeployedRelationFinder basis O with
    | some relation => some relation
    | none => family.straightLineConstraintQuotientFinder basis O

/-- Modeled black-box invocations of the straight-line combined finder.  The IPA branch costs one
run.  If it returns no relation, the direct-coordinate outcome costs one more; on its witness
branch the quotient comparison repeats the wrapped output and outcome, for a worst case of four.
Algebraic postprocessing and group work are accounted for separately by the finite-security
profile. -/
def straightLineConstraintRelationFinderCalls
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) : Nat :=
  match family.toIpaFamily.straightLineIpaRelationFinder basis O with
  | some _ => 1
  | none =>
      match family.outcome basis O with
      | PSum.inr _ => 2
      | PSum.inl _ => 4

/-- The new combined finder has a pointwise four-invocation bound — independent of the field, `k`,
and the adversary's success distribution. -/
theorem straightLineConstraintRelationFinderCalls_le_four
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) :
    family.straightLineConstraintRelationFinderCalls basis O <= 4 := by
  unfold straightLineConstraintRelationFinderCalls
  cases hipa : family.toIpaFamily.straightLineIpaRelationFinder basis O
  · cases hout : family.outcome basis O <;> simp
  · simp

/-- Fixed-call hardness for the straight-line finder is exactly ordinary hardness plus the proved
pointwise call budget; no truncation or expected-time conversion is needed. -/
theorem straightLineConstraint_fixedCalls_iff
    (B : VestaG) (family : ComputedStraightLineDeployedFSFamily shape) {bound : ENNReal} :
    TextbookDLWithCoinsFixedCallsAdvantageLE B
        family.straightLineConstraintRelationFinder
        family.straightLineConstraintRelationFinderCalls 4 bound <->
      TextbookDLWithCoinsAdvantageLE B
        family.straightLineConstraintRelationFinder bound := by
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨family.straightLineConstraintRelationFinderCalls_le_four, h⟩

/-- The existing root-backed constraint decode, restricted to the one-run oracle table.  Like its
recursive counterpart this is proposition-only: it asserts that the root decode yields a concrete
constraint witness, and hands out no relation data. -/
def straightLineConstraintDecoded
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) : Prop :=
  deployedConstraintDecodedOfRoot family.toRootFamily static basis (O, straightLineDummyTape)

/-- Basis/oracle pairs on which the one-run endpoint accepts but does not return the concrete
constraint witness. -/
def straightLineConstraintFailureEvent
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily) :
    Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
  {q | fsWinsFull (family.adversary q.1)
      (fullAlgebraicAcceptDeployed q.1 (family.vk q.1)
        (family.instanceCommitment q.1))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) q.2 ∧
    ¬family.straightLineConstraintDecoded static q.1 q.2}

/-- Scalar-basis form used by the textbook-DLOG reduction. -/
def straightLineConstraintFailureSet (B : VestaG)
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily) :
    Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
  (fun q => (scalarBasis B q.1, q.2)) ⁻¹'
    family.straightLineConstraintFailureEvent static

/-- Transfer the complete straight-line failure event across a uniform-URS identification. -/
theorem straightLineConstraintFailure_prob_eq_of_uniformURS
    {Omega : Type*} (setup : PMF Omega) (B : VestaG)
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basisOf : Omega -> AugmentedIndex (2 ^ shape.k) -> VestaG)
    (hURS : OrchardUniformURSIdentification setup shape.k B basisOf) :
    (independentProductPMF setup
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (basisOf p.1, p.2)) ⁻¹'
          family.straightLineConstraintFailureEvent static) =
      (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
          (BTranscript Fp VestaG
            (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        (family.straightLineConstraintFailureSet B static) := by
  let oraclePMF := PMF.uniformOfFintype
    (BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
  have hprod :
      (independentProductPMF setup oraclePMF).map (fun p => (basisOf p.1, p.2)) =
        (independentProductPMF
          (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) oraclePMF).map
            (fun p => (scalarBasis B p.1, p.2)) := by
    calc
      _ = independentProductPMF (setup.map basisOf) oraclePMF :=
        independentProductPMF_map_left setup oraclePMF basisOf
      _ = independentProductPMF
          ((PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)).map (scalarBasis B))
          oraclePMF := congrArg (fun p => independentProductPMF p oraclePMF) hURS
      _ = _ := (independentProductPMF_map_left
        (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) oraclePMF
        (scalarBasis B)).symm
  have hmeasure := congrArg
    (fun p : PMF ((AugmentedIndex (2 ^ shape.k) -> VestaG) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) =>
      p.toOuterMeasure (family.straightLineConstraintFailureEvent static)) hprod
  change ((independentProductPMF setup oraclePMF).map
      (fun p => (basisOf p.1, p.2))).toOuterMeasure
        (family.straightLineConstraintFailureEvent static) =
    ((independentProductPMF
      (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) oraclePMF).map
        (fun p => (scalarBasis B p.1, p.2))).toOuterMeasure
          (family.straightLineConstraintFailureEvent static) at hmeasure
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply] at hmeasure
  calc
    _ = (independentProductPMF
          (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) oraclePMF).toOuterMeasure
          ((fun p => (scalarBasis B p.1, p.2)) ⁻¹'
            family.straightLineConstraintFailureEvent static) := hmeasure
    _ = _ := by
      rw [independentProductPMF_uniform]
      rfl

/-- The exact pre-`x` bad event, restricted to the fixed proof-only tape used by the straight-line
decode. -/
def straightLineConstraintBadXSet (B : VestaG)
    (family : ComputedStraightLineDeployedFSFamily shape) :
    Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
  {q | (scalarBasis B q.1, (q.2, straightLineDummyTape)) ∈
    deployedConstraintBadXEvent family.toRootFamily}

/-- Deterministic straight-line constraint containment.  Failure is covered by the root-layer
zero and pinned-root events, the one combined relation finder, or the single constraint-`x` root.
-/
theorem straightLineConstraintFailureSet_subset
    (B : VestaG) (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily) :
    family.straightLineConstraintFailureSet B static <=
      family.straightLineRootZeroSet B ∪
        ({q | (family.toIpaFamily.pinnedIpaRoots (scalarBasis B q.1)).Landing q.2} ∪
          ({q | (family.toRootFamily.pinnedRoots (scalarBasis B q.1)).Landing q.2} ∪
            ((relSetWithCoins B family.straightLineConstraintRelationFinder :
                Set ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
                  (BTranscript Fp VestaG
                    (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))) ∪
              family.straightLineConstraintBadXSet B))) := by
  intro q hfailure
  let basis := scalarBasis B q.1
  let coins : family.toFamily.Coins := (q.2, straightLineDummyTape)
  by_cases hroot : family.straightLineRootDecoded basis q.2
  · let root := Classical.choice hroot
    by_cases hxgood : (wrappedPreIpaRecord
        (deployedRootRunOutput family.toRootFamily basis coins)).x ∉
        szBadSet (deployedConstraintDifferencePreX family.toRootFamily basis coins)
    · cases hout : deployedConstraintOutcomeOfRoot family.toRootFamily static basis coins
          hfailure.1 root hxgood with
      | inl witness =>
          exfalso
          apply hfailure.2
          exact ⟨hfailure.1, root, hxgood, witness, hout⟩
      | inr relation =>
          apply Or.inr
          apply Or.inr
          apply Or.inr
          apply Or.inl
          simp only [relSetWithCoins, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
            true_and]
          unfold straightLineConstraintRelationFinder
          cases hbase : family.straightLineDeployedRelationFinder basis q.2 with
          | some baseRelation => simp
          | none =>
              have hrelation := deployedConstraintOutcomeOfRoot_relation_eq_online
                family.toRootFamily static basis coins hfailure.1 root hxgood relation hout
              -- Restate both equations with the `let`s expanded so `simp` can use them.
              have houtcome : family.outcome (scalarBasis B q.1) q.2 =
                PSum.inl root.batchWitness := root.outcome_eq
              have hrel : deployedConstraintQuotientAgreementOrRelation family.toRootFamily
                  (scalarBasis B q.1)
                  ((wrappedAdversary family.toFamily (scalarBasis B q.1)).run q.2) =
                  PSum.inr relation := hrelation
              simp [straightLineConstraintQuotientFinder, houtcome, hrel]
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      change (wrappedPreIpaRecord
          (deployedRootRunOutput family.toRootFamily basis coins)).x ∈
        szBadSet (deployedConstraintDifferencePreX family.toRootFamily basis coins)
      exact Classical.not_not.mp hxgood
  · by_cases hrelation :
        (family.straightLineDeployedRelationFinder basis q.2).isSome
    · apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inl
      simp only [relSetWithCoins, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      unfold straightLineConstraintRelationFinder
      cases hbase : family.straightLineDeployedRelationFinder basis q.2 with
      | none => simp [hbase] at hrelation
      | some relation => simp
    · have hnotExtracted : ¬family.straightLineRootExtracted basis q.2 := by
        rintro (hfound | hdecoded)
        · exact hrelation hfound
        · exact hroot hdecoded
      have hplain : fsWinsFull (family.adversary basis)
          (fullAlgebraicAccept basis (family.vk basis) (family.instanceCommitment basis))
          (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) q.2 := by
        exact fullAlgebraicAccept_of_deployed basis (family.vk basis)
          (family.instanceCommitment basis) ((family.adversary basis).run q.2) _ _ hfailure.1
      rcases family.straightLineRootFailure basis q.2 hplain hnotExtracted with
        hzero | hipa | hdeployed
      · exact Or.inl ⟨hplain, hzero⟩
      · exact Or.inr (Or.inl hipa)
      · exact Or.inr (Or.inr (Or.inl hdeployed))

/-- The constraint-`x` slice retains the direct `(Q+1) * epsilonX` pinned-squeeze price. -/
theorem straightLineConstraintBadX_prob_le
    (B : VestaG) (family : ComputedStraightLineDeployedFSFamily shape)
    {epsilonX : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family.toRootFamily epsilonX) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        (family.straightLineConstraintBadXSet B) <=
      (family.Q + 1 : Nat) * epsilonX := by
  apply uniformOfFintype_prod_fiber_bound_right
    (fun logs =>
      {O | (scalarBasis B logs, (O, straightLineDummyTape)) ∈
        deployedConstraintBadXEvent family.toRootFamily})
  intro logs
  refine le_trans (MeasureTheory.measure_mono
    (show {O | (scalarBasis B logs, (O, straightLineDummyTape)) ∈
          deployedConstraintBadXEvent family.toRootFamily} <=
        {O | (deployedConstraintXPinnedEvent family.toRootFamily schedule
          (scalarBasis B logs)).Landing O}
      from fun O hbad => deployedConstraintBadX_subset_landing family.toRootFamily schedule
        (scalarBasis B logs) hbad)) ?_
  exact (deployedConstraintXPinnedEvent family.toRootFamily schedule
    (scalarBasis B logs)).landing_measure_le (family.queryBound (scalarBasis B logs))

/-- The complete straight-line constraint relation event reduces to textbook DLOG with only the
programmed-slot loss. -/
theorem straightLineConstraintRelation_prob_le_of_textbookDL
    (B : VestaG) (family : ComputedStraightLineDeployedFSFamily shape) {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      family.straightLineConstraintRelationFinder bound) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        (relSetWithCoins B family.straightLineConstraintRelationFinder) <=
      bound + 1 / Fintype.card Fp :=
  relationWithCoins_prob_le_of_textbookDL B family.straightLineConstraintRelationFinder hDL

/-- Straight-line AGM deployed-constraint capstone.  The bound is linear in `Q`, uses a fixed
finite relation finder, and contains no recursive AFK or Markov term. -/
theorem straightLineConstraintFailure_prob_le_of_textbookDL
    (B : VestaG) (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    {epsilonX bound : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family.toRootFamily epsilonX)
    (hDL : TextbookDLWithCoinsAdvantageLE B
      family.straightLineConstraintRelationFinder bound) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        (family.straightLineConstraintFailureSet B static) <=
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          (shape.k * (2 / (Fintype.card Fp : ENNReal))) +
        (family.Q + (11 + shape.k) + 1 : Nat) *
          algebraicRootBudget shape shape.k +
        (bound + 1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) * epsilonX := by
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
    relSetWithCoins B family.straightLineConstraintRelationFinder
  let badXSet := family.straightLineConstraintBadXSet B
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
  have hrelation := family.straightLineConstraintRelation_prob_le_of_textbookDL B hDL
  have hbadX := family.straightLineConstraintBadX_prob_le B schedule
  refine le_trans (MeasureTheory.measure_mono
    (family.straightLineConstraintFailureSet_subset B static)) ?_
  refine le_trans (MeasureTheory.measure_union_le zeroSet
    (ipaSet ∪ (rootSet ∪ (relationSet ∪ badXSet)))) ?_
  refine le_trans (add_le_add hzero
    (MeasureTheory.measure_union_le ipaSet (rootSet ∪ (relationSet ∪ badXSet)))) ?_
  refine le_trans (add_le_add le_rfl (add_le_add hipa
    (MeasureTheory.measure_union_le rootSet (relationSet ∪ badXSet)))) ?_
  refine le_trans (add_le_add le_rfl (add_le_add le_rfl
    (add_le_add hroot (MeasureTheory.measure_union_le relationSet badXSet)))) ?_
  calc
    _ <= (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          ((family.Q + 1 : Nat) *
              (shape.k * (2 / (Fintype.card Fp : ENNReal))) +
            ((family.Q + (11 + shape.k) + 1 : Nat) *
                algebraicRootBudget shape shape.k +
              ((bound + 1 / Fintype.card Fp) +
                (family.Q + 1 : Nat) * epsilonX))) :=
      add_le_add le_rfl (add_le_add le_rfl
        (add_le_add le_rfl (add_le_add hrelation hbadX)))
    _ = _ := by ring

/-- Runtime-aware spelling of the capstone using the proved fixed four-call budget. -/
theorem straightLineConstraintFailure_prob_le_of_fixedCallsTextbookDL
    (B : VestaG) (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    {epsilonX bound : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family.toRootFamily epsilonX)
    (hDL : TextbookDLWithCoinsFixedCallsAdvantageLE B
      family.straightLineConstraintRelationFinder
      family.straightLineConstraintRelationFinderCalls 4 bound) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        (family.straightLineConstraintFailureSet B static) <=
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          (shape.k * (2 / (Fintype.card Fp : ENNReal))) +
        (family.Q + (11 + shape.k) + 1 : Nat) *
          algebraicRootBudget shape shape.k +
        (bound + 1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) * epsilonX :=
  family.straightLineConstraintFailure_prob_le_of_textbookDL B static schedule hDL.2

/-! ## Promotion from the compressed identity to circuit semantics

The one-run decode proves the verifier's compressed constraint identity, exactly as on the
recursive side.  Row-level semantics additionally price collisions at the four earlier squeezes:
the caller supplies the semantic predicate, the four failure events, and a proof that a compressed
witness outside them has the intended semantics.
-/

/-- Outside the four challenge-failure events, the one-run compressed constraint decode upgrades
to the caller's row-level semantic predicate. -/
def StraightLineConstraintSemanticUpgradeContained
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (semanticDecoded : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) -> Prop)
    (badY badBeta badGamma badTheta :
      Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))) : Prop :=
  {q | family.straightLineConstraintDecoded static q.1 q.2 ∧ ¬ semanticDecoded q.1 q.2} <=
    badY ∪ (badBeta ∪ (badGamma ∪ badTheta))

/-- Basis/oracle pairs on which the one-run endpoint accepts but the caller's semantic predicate
fails. -/
def straightLineConstraintSemanticFailureEvent
    (family : ComputedStraightLineDeployedFSFamily shape)
    (semanticDecoded : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) -> Prop) :
    Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
  {q | fsWinsFull (family.adversary q.1)
      (fullAlgebraicAcceptDeployed q.1 (family.vk q.1)
        (family.instanceCommitment q.1))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) q.2 ∧
    ¬ semanticDecoded q.1 q.2}

/-- One-run semantic failure is compressed-identity failure or one of the four explicitly priced
challenge surfaces. -/
theorem straightLineConstraintSemanticFailure_subset_union
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (semanticDecoded : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) -> Prop)
    (badY badBeta badGamma badTheta :
      Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)))
    (hsemantic : family.StraightLineConstraintSemanticUpgradeContained static
      semanticDecoded badY badBeta badGamma badTheta) :
    family.straightLineConstraintSemanticFailureEvent semanticDecoded <=
      family.straightLineConstraintFailureEvent static ∪
        (badY ∪ (badBeta ∪ (badGamma ∪ badTheta))) := by
  rintro q ⟨haccept, hnotSemantic⟩
  by_cases hcompressed : family.straightLineConstraintDecoded static q.1 q.2
  · exact Or.inr (hsemantic ⟨hcompressed, hnotSemantic⟩)
  · exact Or.inl ⟨haccept, hcompressed⟩

/-- The four-budget straight-line semantic promotion, factored over an arbitrary bound for the
compressed-identity failure event in the generator-random-oracle model. -/
theorem straightLineConstraintSemanticFailure_prob_le_of_compressed_bound
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ shape.k) -> T)
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (semanticDecoded : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) -> Prop)
    (badY badBeta badGamma badTheta :
      Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)))
    {compressedBound yBound betaBound gammaBound thetaBound : ENNReal}
    (hsemantic : family.StraightLineConstraintSemanticUpgradeContained static
      semanticDecoded badY badBeta badGamma badTheta)
    (hcompressed : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintFailureEvent static) <= compressedBound)
    (hY : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badY) <= yBound)
    (hBeta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badBeta) <= betaBound)
    (hGamma : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badGamma) <= gammaBound)
    (hTheta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badTheta) <= thetaBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintSemanticFailureEvent semanticDecoded)
      <= compressedBound + (yBound + (betaBound + (gammaBound + thetaBound))) := by
  let mu := (independentProductPMF (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
  let basisOracle : ((↥(Set.range query) -> VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) ->
      ((AugmentedIndex (2 ^ shape.k) -> VestaG) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
    fun p => (orchardGeneratorROBasis query p.1, p.2)
  change mu (basisOracle ⁻¹'
      family.straightLineConstraintSemanticFailureEvent semanticDecoded) <= _
  have hsubset : basisOracle ⁻¹'
        family.straightLineConstraintSemanticFailureEvent semanticDecoded <=
      basisOracle ⁻¹'
        (family.straightLineConstraintFailureEvent static ∪
          (badY ∪ (badBeta ∪ (badGamma ∪ badTheta)))) :=
    Set.preimage_mono
      (family.straightLineConstraintSemanticFailure_subset_union static semanticDecoded
        badY badBeta badGamma badTheta hsemantic)
  calc
    mu (basisOracle ⁻¹'
        family.straightLineConstraintSemanticFailureEvent semanticDecoded)
        <= mu (basisOracle ⁻¹'
          (family.straightLineConstraintFailureEvent static ∪
            (badY ∪ (badBeta ∪ (badGamma ∪ badTheta))))) :=
      MeasureTheory.measure_mono hsubset
    _ = mu ((basisOracle ⁻¹' family.straightLineConstraintFailureEvent static) ∪
        ((basisOracle ⁻¹' badY) ∪
          ((basisOracle ⁻¹' badBeta) ∪
            ((basisOracle ⁻¹' badGamma) ∪ (basisOracle ⁻¹' badTheta))))) := by
      simp only [Set.preimage_union]
    _ <= mu (basisOracle ⁻¹' family.straightLineConstraintFailureEvent static) +
        (mu (basisOracle ⁻¹' badY) +
          (mu (basisOracle ⁻¹' badBeta) +
            (mu (basisOracle ⁻¹' badGamma) + mu (basisOracle ⁻¹' badTheta)))) := by
      exact (MeasureTheory.measure_union_le _ _).trans
        (add_le_add le_rfl ((MeasureTheory.measure_union_le _ _).trans
          (add_le_add le_rfl ((MeasureTheory.measure_union_le _ _).trans
            (add_le_add le_rfl (MeasureTheory.measure_union_le _ _))))))
    _ <= compressedBound + (yBound + (betaBound + (gammaBound + thetaBound))) :=
      add_le_add hcompressed (add_le_add hY (add_le_add hBeta (add_le_add hGamma hTheta)))

end ComputedStraightLineDeployedFSFamily

end Zcash.Snark
