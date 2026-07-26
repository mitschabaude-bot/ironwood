import Zcash.Snark.Soundness.Action.AdaptiveSurfaces
import Zcash.Snark.Soundness.AGM.AdaptiveComposition

/-!
# Action soundness and knowledge soundness for adaptive online-AGM adversaries

One cached terminal returns private Action witnesses or relation data. The endpoints bound
accepting false statements and accepting runs whose witness projection fails, without sequential
traces or propositionally closed relations.
-/

namespace Zcash.Snark

namespace ActionTerminal

open Halo2 CompPoly.CPolynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder)
open scoped ENNReal

local instance vestaInhabitedAdaptiveActionEvent : Inhabited VestaG := ⟨0⟩

variable (pp : ProofParams)
  (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
  (inputs : Fin pp.numProofs → PublicInputs Fp)
  (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey
    (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
  (hI : ∀ basis, family.instanceCommitment basis =
    actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
  (hchar : ∀ basis O, deployedX4PairCount
    (actionCircuit.toVerifierKey
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (adaptiveActionRunOutput family basis O).1.proof.1
    (adaptiveActionRunRecord family basis O) < scalarFieldOrder)

/-- The exact Action soundness event for the bare adaptive online-AGM family. -/
def adaptiveActionAcceptFalseStatementEvent :
    Set ((AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)) :=
  {q | adaptiveActionAccepts family q.1 q.2 ∧ ¬BundleStatement inputs}

include inputs hvk hI hchar in
/-- The zero-pre-`x` identity branch of the adaptive Action terminal.  When the fixed pre-`x`
difference is identically zero, canonical circuit satisfaction is already available and the
terminal must not re-test the `x`-dependent reassembled quotient polynomial. -/
def adaptiveActionPreXIdentityWitnessOrRelationFinder
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (hprovenance : family.adaptiveActionRepresentationRelationFinder basis O = none)
    (witness : DeployedBatchWitness family.toFamily basis
      (adaptiveActionRunOutput family basis O))
    (hsrc : witness.fixedRepresentations = family.fixedRepresentations basis)
    (hroots : family.AdaptiveDeployedGoodRoots basis O witness)
    (hshifted : family.AdaptiveShiftedValue basis O)
    (haccepts : adaptiveActionAccepts family basis O) :
    Option (ActionBundleWitness inputs ⊕
      AlgebraicRelationWitness (F := Fp) basis) := by
  let pnu := adaptiveActionRunOutput family basis O
  let ch := adaptiveActionRunRecord family basis O
  let data := (family.adversary basis).run O
  let source := data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis)
  let pointPoly := onlinePointPolynomial source
  let piecePoly := fun i => onlinePointPolynomial source (data.algebraicProof.erase.hPieces i)
  have hblinding : (family.vk basis).blindingFactors < (family.vk basis).n := by
    rw [hvk basis]
    exact actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
  let difference := adaptiveActionPreXDifferenceOf (family.vk basis)
    (family.instanceCommitment basis) data.algebraicProof.erase source ch hblinding
  if hsupport : difference = 0 then
    let rawDecode := family.adaptiveAlgebraicDecode_of_deployedGoodRoots
      basis O witness hroots hshifted
    let fullDecode := rawDecode.reRound (runRounds family.toFamily basis O)
    let decode := hI basis ▸ hvk basis ▸
      fullDecode
    let hacceptsAction := adaptiveActionRunAccepts pp family basis O inputs hvk hI haccepts
    let preXPoly := committedPreXQuotient (family.vk basis) piecePoly
    have hcharRaw : deployedX4PairCount (family.vk basis)
        (family.instanceCommitment basis) pnu.1.proof.1 ch < scalarFieldOrder := by
      rw [hvk basis, hI basis]
      simpa only [pnu, ch, adaptiveActionRunRecord] using
        (show deployedX4PairCount
          (actionCircuit.toVerifierKey
            (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
          (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
          (adaptiveActionRunOutput family basis O).1.proof.1
          (adaptiveActionRunRecord family basis O) < scalarFieldOrder from hchar basis O)
    have hbatches : rawDecode.batches = witness.batches := by
      rfl
    let rawModel := CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := fun i hi => fullDecode.toMemberDecode hcharRaw i hi)
      (hblinding := hblinding) haccepts
    let rawPoly := CanonicalMemberConstraintRelation.acceptedPolynomial
      (memberDecode := fun i hi => fullDecode.toMemberDecode hcharRaw i hi) haccepts
    have hpolyStage : ∀ id, id ≠ .vanishingH → id ≠ .randomPoly →
        rawPoly id = adaptiveActionCommitmentPolynomialOf (family.vk basis)
          (family.instanceCommitment basis) data.algebraicProof.erase
          (data.algebraicProof.actionRepresentationsBefore (4 : Fin 5) ++
            family.fixedRepresentations basis) ch id := by
      intro id hvanishing hrandom
      have havailable : adaptiveActionCommitmentActive
          (actionCircuit.shape.withProofParams pp) (ActionTerminal.vkAt basis) id →
          adaptiveActionCommitmentAvailable (4 : Fin 5) id := by
        intro hactive
        cases id <;> simp_all [adaptiveActionCommitmentAvailable]
      have hraw := family.adaptiveAcceptedPolynomial_eq_actionStage_nonterminal pp basis O
        inputs hvk hI hprovenance (4 : Fin 5) id havailable ⟨hvanishing, hrandom⟩
        pnu rfl witness hsrc rawDecode hbatches haccepts hcharRaw
      rw [adaptiveActionCommitmentPolynomialOf_action pp basis inputs
        (family.vk basis) (family.instanceCommitment basis) data.algebraicProof.erase
        (data.algebraicProof.actionRepresentationsBefore (4 : Fin 5) ++
          family.fixedRepresentations basis) ch (hvk basis) (hI basis)]
      simpa only [rawPoly, fullDecode, pnu, ch, data, adaptiveActionRunRecord] using hraw
    have hmodel : rawModel = adaptiveActionCommittedModelOf (family.vk basis)
        (family.instanceCommitment basis) data.algebraicProof.erase
        (data.algebraicProof.actionRepresentationsBefore (4 : Fin 5) ++
          family.fixedRepresentations basis) ch hblinding := by
      unfold rawModel adaptiveActionCommittedModelOf
      exact VerifyingKey.constraintModel_congr_nonterminal
        pp.numProofs (family.vk basis) ch _ _ _ hpolyStage
    have hzero : difference = 0 := hsupport
    have hdiff := adaptiveActionPreXDifferenceOf_eq (family.vk basis)
      (family.instanceCommitment basis) data.algebraicProof.erase
      (data.algebraicProof.actionRepresentationsBefore (4 : Fin 5) ++
        family.fixedRepresentations basis) ch hblinding
    have hsource4 :
        data.algebraicProof.actionRepresentationsBefore (4 : Fin 5) ++
            family.fixedRepresentations basis = source :=
      data.algebraicProof.actionRepresentationsBefore_four_append
        (family.fixedRepresentations basis)
    rw [hsource4] at hdiff
    have hidentity :
        let model := adaptiveActionCommittedModelOf (family.vk basis)
          (family.instanceCommitment basis) data.algebraicProof.erase
          (data.algebraicProof.actionRepresentationsBefore (4 : Fin 5) ++
            family.fixedRepresentations basis) ch hblinding
        combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
            model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
            ch.y model.chunkLen model.l0 model.lLast model.lBlind =
          preXPoly * (X ^ (family.vk basis).n - 1) := by
      dsimp only [preXPoly, piecePoly]
      rw [hsource4]
      apply sub_eq_zero.mp
      rw [← hdiff]
      exact hzero
    have hsatisfiedRaw : rawModel.CircuitSat ch.y preXPoly
        (family.vk basis).n
        (pnu.1.aMulti (wrappedPreIpaReads pnu)) := by
      rw [hmodel]
      exact hidentity
    let hn : (family.vk basis).n ≠ 0 := by
      rw [hvk basis]
      change 2 ^ actionCircuit.domainExponent ≠ 0
      positivity
    exact match hgoodY : foldSplitAvoidance? rawModel.constraints
        (family.vk basis).n hn ch.y with
    | none => none
    | some hgoodYProof =>
      match hpermutation : resolverPermutationChallengeExclusions?
          pp.numProofs (family.vk basis) ch rawPoly actionActiveRows with
      | none => none
      | some hpermutationProof =>
        match hlookup : TopLevelLookup.topLevelLookupChallengeExclusions?
            actionCircuit pp
            (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) ch rawPoly with
        | none => none
        | some hlookupProof =>
          let actionModel := CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi)
            (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
              (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)) hacceptsAction
          let actionPoly := CanonicalMemberConstraintRelation.acceptedPolynomial
            (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi)
            hacceptsAction
          have hmodelTransport := ComputedAdaptiveOnlineAGMFSFamily.acceptedModel_transport
            (hI basis) (hvk basis) fullDecode hcharRaw haccepts hblinding
          have hpolyTransport := ComputedAdaptiveOnlineAGMFSFamily.acceptedPolynomial_transport
            (hI basis) (hvk basis) fullDecode hcharRaw haccepts
          have hvkAt : family.vk basis = ActionTerminal.vkAt basis := by
            simpa only [ActionTerminal.vkAt, CircuitShape.withProofParams_k] using hvk basis
          have hnTransport : (family.vk basis).n = actionCircuit.n := by
            rw [hvk basis]
            exact actionCircuit.toVerifierKey_n
              (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
          have hsatisfied : actionModel.CircuitSat ch.y preXPoly
              actionCircuit.n
              (pnu.1.aMulti (wrappedPreIpaReads pnu)) := by
            simpa only [actionModel, decode, hacceptsAction, pnu, ch,
              adaptiveActionRunRecord, adaptiveActionRunAccepts, ← hmodelTransport,
              ← hnTransport] using hsatisfiedRaw
          have hgoodYAction : ∀ j, ch.y ∉ szBadSet
              (foldSplitWitness actionModel.constraints
                actionCircuit.n j) := by
            intro j
            simpa only [actionModel, decode, hacceptsAction, pnu, ch,
              adaptiveActionRunRecord, adaptiveActionRunAccepts, ← hmodelTransport,
              ← hnTransport] using hgoodYProof.down j
          have hpermutationAction : ResolverPermutationChallengeExclusions
              pp.numProofs (ActionTerminal.vkAt basis) ch actionPoly actionActiveRows := by
            simpa only [actionPoly, decode, hacceptsAction, pnu, ch,
              adaptiveActionRunRecord, adaptiveActionRunAccepts, ← hpolyTransport,
              ← hvkAt] using hpermutationProof.down
          have hlookupAction :
              TopLevelLookup.ChallengeExclusions actionCircuit pp
                (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) ch actionPoly := by
            simpa only [actionPoly, decode, hacceptsAction, pnu, ch,
              adaptiveActionRunRecord, adaptiveActionRunAccepts,
              ← hpolyTransport] using hlookupProof.down
          match action_bundleWitness_or_relation_of_decode_circuitSat pp
              (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) rfl inputs
              pnu.1.proof.1 ch
              (pnu.1.multiU (wrappedPreIpaReads pnu))
              (pnu.1.multiBlind (wrappedPreIpaReads pnu))
              (pnu.1.aMulti (wrappedPreIpaReads pnu)) decode (hchar basis O)
              hacceptsAction preXPoly hsatisfied hgoodYAction
              hpermutationAction hlookupAction with
          | PSum.inl extracted => some (Sum.inl extracted)
          | PSum.inr relation => some (Sum.inr
              (augmentedBasis_ursOfAugmentedBasis
                (actionCircuit.shape.withProofParams pp).k basis ▸
                  AugmentedRelationWitness.toAlgebraicRelationWitness relation))
  else
    exact none

/-- Relation-only projection used by the existing ordinary-soundness finder. -/
def adaptiveActionPreXIdentityRelationFinder
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (hprovenance : family.adaptiveActionRepresentationRelationFinder basis O = none)
    (witness : DeployedBatchWitness family.toFamily basis
      (adaptiveActionRunOutput family basis O))
    (hsrc : witness.fixedRepresentations = family.fixedRepresentations basis)
    (hroots : family.AdaptiveDeployedGoodRoots basis O witness)
    (hshifted : family.AdaptiveShiftedValue basis O)
    (haccepts : adaptiveActionAccepts family basis O) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  match adaptiveActionPreXIdentityWitnessOrRelationFinder pp family inputs hvk hI hchar
      basis O hprovenance witness hsrc hroots hshifted haccepts with
  | some (Sum.inr relation) => some relation
  | _ => none

theorem adaptiveActionPreXIdentityRelationFinder_isSome_of_witnessOrRelation
    (basis) (O) (hprovenance) (witness) (hsrc) (hroots) (hshifted) (haccepts)
    (hcomplete : (adaptiveActionPreXIdentityWitnessOrRelationFinder pp family inputs hvk hI
      hchar basis O hprovenance witness hsrc hroots hshifted haccepts).isSome)
    (hfalse : ¬BundleStatement inputs) :
    (adaptiveActionPreXIdentityRelationFinder pp family inputs hvk hI hchar basis O
      hprovenance witness hsrc hroots hshifted haccepts).isSome := by
  obtain ⟨outcome, houtcome⟩ := Option.isSome_iff_exists.mp hcomplete
  cases outcome with
  | inl extracted => exact False.elim (hfalse extracted.statement)
  | inr relation =>
      unfold adaptiveActionPreXIdentityRelationFinder
      rw [houtcome]
      rfl

/-- On the identically-zero pre-`x` branch, successful semantic exclusions and a false literal
statement force the executable identity terminal to return relation data. -/
theorem adaptiveActionPreXIdentityWitnessOrRelationFinder_isSome_of
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (hprovenance : family.adaptiveActionRepresentationRelationFinder basis O = none)
    (witness : DeployedBatchWitness family.toFamily basis
      (adaptiveActionRunOutput family basis O))
    (hsrc : witness.fixedRepresentations = family.fixedRepresentations basis)
    (hroots : family.AdaptiveDeployedGoodRoots basis O witness)
    (hshifted : family.AdaptiveShiftedValue basis O)
    (haccepts : adaptiveActionAccepts family basis O)
    (hsupport : let data := (family.adversary basis).run O
      let source := data.algebraicProof.preX1AssemblySource
        (family.fixedRepresentations basis)
      let hblinding : (family.vk basis).blindingFactors < (family.vk basis).n := by
        rw [hvk basis]
        exact actionCircuit.toVerifierKey_blindingFactors_lt_n
          (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
      let difference := adaptiveActionPreXDifferenceOf (family.vk basis)
        (family.instanceCommitment basis) data.algebraicProof.erase source
        (adaptiveActionRunRecord family basis O) hblinding
      difference = 0)
    (hgoodY : let _pnu := adaptiveActionRunOutput family basis O
      let decode := hI basis ▸ hvk basis ▸
        (family.adaptiveAlgebraicDecode_of_deployedGoodRoots
          basis O witness hroots hshifted).reRound (runRounds family.toFamily basis O)
      let hacceptsAction := adaptiveActionRunAccepts pp family basis O inputs hvk hI haccepts
      let model := CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi)
        (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
          (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)) hacceptsAction
      ∀ j, (adaptiveActionRunRecord family basis O).y ∉
        szBadSet (foldSplitWitness model.constraints actionCircuit.n j))
    (hpermutation : let decode := hI basis ▸ hvk basis ▸
        (family.adaptiveAlgebraicDecode_of_deployedGoodRoots
          basis O witness hroots hshifted).reRound (runRounds family.toFamily basis O)
      let hacceptsAction := adaptiveActionRunAccepts pp family basis O inputs hvk hI haccepts
      ResolverPermutationChallengeExclusions pp.numProofs (ActionTerminal.vkAt basis)
        (adaptiveActionRunRecord family basis O)
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi)
          hacceptsAction) actionActiveRows)
    (hlookup : let decode := hI basis ▸ hvk basis ▸
        (family.adaptiveAlgebraicDecode_of_deployedGoodRoots
          basis O witness hroots hshifted).reRound (runRounds family.toFamily basis O)
      let hacceptsAction := adaptiveActionRunAccepts pp family basis O inputs hvk hI haccepts
      TopLevelLookup.ChallengeExclusions actionCircuit pp
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
        (adaptiveActionRunRecord family basis O)
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi)
          hacceptsAction)) :
    (adaptiveActionPreXIdentityWitnessOrRelationFinder pp family inputs hvk hI hchar basis O
      hprovenance witness hsrc hroots hshifted haccepts).isSome := by
  let pnu := adaptiveActionRunOutput family basis O
  let rawDecode := family.adaptiveAlgebraicDecode_of_deployedGoodRoots
    basis O witness hroots hshifted
  let fullDecode := rawDecode.reRound (runRounds family.toFamily basis O)
  let decode := hI basis ▸ hvk basis ▸
    fullDecode
  let hacceptsAction := adaptiveActionRunAccepts pp family basis O inputs hvk hI haccepts
  let model := CanonicalMemberConstraintRelation.acceptedModel
    (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi)
    (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)) hacceptsAction
  let polynomial := CanonicalMemberConstraintRelation.acceptedPolynomial
    (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi) hacceptsAction
  dsimp only at hsupport hgoodY hpermutation hlookup
  have hcharRaw : deployedX4PairCount (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1
      (adaptiveActionRunRecord family basis O) < scalarFieldOrder := by
    rw [hvk basis, hI basis]
    exact hchar basis O
  have hblinding : (family.vk basis).blindingFactors < (family.vk basis).n := by
    rw [hvk basis]
    exact actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
  let rawModel := CanonicalMemberConstraintRelation.acceptedModel
    (memberDecode := fun i hi => fullDecode.toMemberDecode hcharRaw i hi)
    (hblinding := hblinding) haccepts
  let rawPolynomial := CanonicalMemberConstraintRelation.acceptedPolynomial
    (memberDecode := fun i hi => fullDecode.toMemberDecode hcharRaw i hi) haccepts
  have hmodelTransport := ComputedAdaptiveOnlineAGMFSFamily.acceptedModel_transport
    (hI basis) (hvk basis) fullDecode hcharRaw haccepts hblinding
  have hpolyTransport := ComputedAdaptiveOnlineAGMFSFamily.acceptedPolynomial_transport
    (hI basis) (hvk basis) fullDecode hcharRaw haccepts
  have hmodelEq : rawModel = model := by
    simpa only [rawModel, model, decode, fullDecode, pnu, hacceptsAction,
      adaptiveActionRunAccepts] using hmodelTransport
  have hpolynomialEq : rawPolynomial = polynomial := by
    simpa only [rawPolynomial, polynomial, decode, fullDecode, pnu, hacceptsAction,
      adaptiveActionRunAccepts] using hpolyTransport
  have hnTransport : (family.vk basis).n = actionCircuit.n := by
    rw [hvk basis]
    exact actionCircuit.toVerifierKey_n
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
  have hgoodYRaw : ∀ j, (adaptiveActionRunRecord family basis O).y ∉
      szBadSet (foldSplitWitness rawModel.constraints (family.vk basis).n j) := by
    intro j
    rw [hmodelEq, hnTransport]
    exact hgoodY j
  have hpermutationRaw : ResolverPermutationChallengeExclusions
      pp.numProofs (family.vk basis) (adaptiveActionRunRecord family basis O)
      rawPolynomial actionActiveRows := by
    rw [hvk basis, hpolynomialEq]
    exact hpermutation
  have hlookupRaw : TopLevelLookup.ChallengeExclusions
      actionCircuit pp (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
      (adaptiveActionRunRecord family basis O) rawPolynomial := by
    rw [hpolynomialEq]
    exact hlookup
  have hn : (family.vk basis).n ≠ 0 := by
    rw [hvk basis]
    change 2 ^ actionCircuit.domainExponent ≠ 0
    positivity
  have hySome := foldSplitAvoidance?_isSome_of rawModel.constraints _ hn _ hgoodYRaw
  have hpSome := resolverPermutationChallengeExclusions?_isSome_of
    pp.numProofs _ _ _ _ hpermutationRaw
  have hlSome := TopLevelLookup.topLevelLookupChallengeExclusions?_isSome_of
    actionCircuit pp (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
      _ _ hlookupRaw
  obtain ⟨hgoodYProof, hgoodYEq⟩ := Option.isSome_iff_exists.mp hySome
  obtain ⟨hpermutationProof, hpermutationEq⟩ := Option.isSome_iff_exists.mp hpSome
  obtain ⟨hlookupProof, hlookupEq⟩ := Option.isSome_iff_exists.mp hlSome
  unfold adaptiveActionPreXIdentityWitnessOrRelationFinder
  rw [dif_pos hsupport]
  dsimp only
  rw [hgoodYEq, hpermutationEq, hlookupEq]
  dsimp only
  split <;> rfl

/-- On the identically-zero pre-`x` branch, a false statement projects the complete outcome to
explicit relation data. -/
theorem adaptiveActionPreXIdentityRelationFinder_isSome_of
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (hprovenance : family.adaptiveActionRepresentationRelationFinder basis O = none)
    (witness : DeployedBatchWitness family.toFamily basis
      (adaptiveActionRunOutput family basis O))
    (hsrc : witness.fixedRepresentations = family.fixedRepresentations basis)
    (hroots : family.AdaptiveDeployedGoodRoots basis O witness)
    (hshifted : family.AdaptiveShiftedValue basis O)
    (haccepts : adaptiveActionAccepts family basis O)
    (hsupport : let data := (family.adversary basis).run O
      let source := data.algebraicProof.preX1AssemblySource
        (family.fixedRepresentations basis)
      let hblinding : (family.vk basis).blindingFactors < (family.vk basis).n := by
        rw [hvk basis]
        exact actionCircuit.toVerifierKey_blindingFactors_lt_n
          (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
      let difference := adaptiveActionPreXDifferenceOf (family.vk basis)
        (family.instanceCommitment basis) data.algebraicProof.erase source
        (adaptiveActionRunRecord family basis O) hblinding
      difference = 0)
    (hgoodY : let _pnu := adaptiveActionRunOutput family basis O
      let decode := hI basis ▸ hvk basis ▸
        (family.adaptiveAlgebraicDecode_of_deployedGoodRoots
          basis O witness hroots hshifted).reRound (runRounds family.toFamily basis O)
      let hacceptsAction := adaptiveActionRunAccepts pp family basis O inputs hvk hI haccepts
      let model := CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi)
        (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
          (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)) hacceptsAction
      ∀ j, (adaptiveActionRunRecord family basis O).y ∉
        szBadSet (foldSplitWitness model.constraints actionCircuit.n j))
    (hpermutation : let decode := hI basis ▸ hvk basis ▸
        (family.adaptiveAlgebraicDecode_of_deployedGoodRoots
          basis O witness hroots hshifted).reRound (runRounds family.toFamily basis O)
      let hacceptsAction := adaptiveActionRunAccepts pp family basis O inputs hvk hI haccepts
      ResolverPermutationChallengeExclusions pp.numProofs (ActionTerminal.vkAt basis)
        (adaptiveActionRunRecord family basis O)
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi)
          hacceptsAction) actionActiveRows)
    (hlookup : let decode := hI basis ▸ hvk basis ▸
        (family.adaptiveAlgebraicDecode_of_deployedGoodRoots
          basis O witness hroots hshifted).reRound (runRounds family.toFamily basis O)
      let hacceptsAction := adaptiveActionRunAccepts pp family basis O inputs hvk hI haccepts
      TopLevelLookup.ChallengeExclusions actionCircuit pp
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
        (adaptiveActionRunRecord family basis O)
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi)
          hacceptsAction))
    (hfalse : ¬BundleStatement inputs) :
    (adaptiveActionPreXIdentityRelationFinder pp family inputs hvk hI hchar basis O
      hprovenance witness hsrc hroots hshifted haccepts).isSome :=
  adaptiveActionPreXIdentityRelationFinder_isSome_of_witnessOrRelation
    pp family inputs hvk hI hchar basis O hprovenance witness hsrc hroots hshifted
      haccepts
      (adaptiveActionPreXIdentityWitnessOrRelationFinder_isSome_of pp family inputs
        hvk hI hchar basis O hprovenance witness hsrc hroots hshifted haccepts
        hsupport hgoodY hpermutation hlookup)
      hfalse

/-- One executable adaptive Action terminal covering both the zero pre-`x` identity branch and
the existing nonzero reassembled-quotient branch. -/
def adaptiveActionRootOutcomeWithSource
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp) :
    PSum
      { witness : DeployedBatchWitness family.toFamily basis
          (adaptiveActionRunOutput family basis O) //
        witness.fixedRepresentations = family.fixedRepresentations basis }
      (AugmentedRelationWitness (F := Fp)
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis).g
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis).u
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis).w) :=
  match hout : deployedRootOutcomeOfCovered family.toOnlineMemberFamily basis O with
  | PSum.inr relation => PSum.inr relation
  | PSum.inl witness => PSum.inl ⟨witness,
      deployedRootOutcomeOfCovered_fixedRepresentations family.toOnlineMemberFamily
        basis O witness hout⟩

/-- A successful deployed-root outcome is retained together with its executable source
identification. -/
theorem adaptiveActionRootOutcomeWithSource_eq_inl
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (witness : DeployedBatchWitness family.toFamily basis
      (adaptiveActionRunOutput family basis O))
    (hout : deployedRootOutcomeOfCovered family.toOnlineMemberFamily basis O =
      PSum.inl witness) :
    adaptiveActionRootOutcomeWithSource pp family basis O =
      PSum.inl ⟨witness,
        deployedRootOutcomeOfCovered_fixedRepresentations family.toOnlineMemberFamily
          basis O witness hout⟩ := by
  unfold adaptiveActionRootOutcomeWithSource
  split
  · rename_i relation hrelation
    rw [hrelation] at hout
    contradiction
  · rename_i witness' hwitness
    have hw : witness' = witness := PSum.inl.inj (hwitness.symm.trans hout)
    subst witness'
    congr

def adaptiveActionCompleteTerminalWitnessOrRelationFinder
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (hprovenance : family.adaptiveActionRepresentationRelationFinder basis O = none) :
    Option (ActionBundleWitness inputs ⊕
      AlgebraicRelationWitness (F := Fp) basis) :=
  let pnu := adaptiveActionRunOutput family basis O
  let nu := wrappedPreIpaReads pnu
  let rounds := runRounds family.toFamily basis O
  match adaptiveActionAccepts? family basis O with
  | some hacceptsProof =>
    let haccepts : adaptiveActionAccepts family basis O := by
      simpa only [adaptiveActionAccepts, adaptiveActionRunRecord, pnu, nu, rounds] using
        hacceptsProof.down
    if hz : nu 10 ≠ 0 then
      if hattack : fullAlgebraicBindingAttackZ basis (family.vk basis)
          (family.instanceCommitment basis) pnu.1 nu rounds then
        none
      else
        match adaptiveActionRootOutcomeWithSource pp family basis O with
        | PSum.inr relation =>
            some (Sum.inr
              (ComputedStraightLineIpaFSFamily.straightLineCanonicalRelation relation))
        | PSum.inl sourcedWitness =>
            let witness := sourcedWitness.1
            let hsrc := sourcedWitness.2
            match family.adaptiveDeployedGoodRoots? basis O witness with
            | none => none
            | some hroots =>
                let hshifted := adaptiveShiftedValue_of_accept_not_attack
                  family basis O haccepts hz hattack
                match adaptiveActionPreXIdentityWitnessOrRelationFinder pp family inputs
                    hvk hI hchar
                    basis O hprovenance witness hsrc hroots.down hshifted haccepts with
                | some outcome => some outcome
                | none =>
                    let decode : DeployedAlgebraicDecode
                        (actionCircuit.shape.withProofParams pp)
                        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) rfl
                        (actionCircuit.toVerifierKey
                          (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
                        (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
                        pnu.1.proof.1 (chRecord nu rounds)
                        (pnu.1.aMulti nu) (pnu.1.multiU nu) (pnu.1.multiBlind nu) :=
                      hI basis ▸ hvk basis ▸
                        (family.adaptiveAlgebraicDecode_of_deployedGoodRoots
                          basis O witness hroots.down hshifted).reRound rounds
                    let hacceptsAction : DeployedAccepts
                        (actionCircuit.shape.withProofParams pp)
                        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) rfl
                        (actionCircuit.toVerifierKey
                          (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
                        (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
                        pnu.1.proof.1 (chRecord nu rounds) :=
                      adaptiveActionRunAccepts pp family basis O inputs hvk hI haccepts
                    adaptiveActionWitnessOrRelationOfDecode? pp family basis O inputs
                      (hchar basis O) decode hacceptsAction
    else none
  | none => none

/-- Relation-only projection used by the ordinary-soundness reduction. -/
def adaptiveActionCompleteTerminalRelationFinder
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (hprovenance : family.adaptiveActionRepresentationRelationFinder basis O = none) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  match adaptiveActionCompleteTerminalWitnessOrRelationFinder pp family inputs hvk hI hchar
      basis O hprovenance with
  | some (Sum.inr relation) => some relation
  | _ => none

theorem adaptiveActionCompleteTerminalRelationFinder_isSome_of_witnessOrRelation
    (basis) (O) (hprovenance)
    (hcomplete : (adaptiveActionCompleteTerminalWitnessOrRelationFinder pp family inputs
      hvk hI hchar basis O hprovenance).isSome)
    (hfalse : ¬BundleStatement inputs) :
    (adaptiveActionCompleteTerminalRelationFinder pp family inputs hvk hI hchar
      basis O hprovenance).isSome := by
  obtain ⟨outcome, houtcome⟩ := Option.isSome_iff_exists.mp hcomplete
  cases outcome with
  | inl extracted => exact False.elim (hfalse extracted.statement)
  | inr relation =>
      unfold adaptiveActionCompleteTerminalRelationFinder
      rw [houtcome]
      rfl

/-- Once the algebraic/root branches and five Action semantic surfaces are good, the complete
terminal returns either extracted witnesses or explicit relation data. -/
theorem adaptiveActionCompleteTerminalWitnessOrRelationFinder_isSome_of
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (hprovenance : family.adaptiveActionRepresentationRelationFinder basis O = none)
    (witness : DeployedBatchWitness family.toFamily basis
      (adaptiveActionRunOutput family basis O))
    (hout : deployedRootOutcomeOfCovered family.toOnlineMemberFamily basis O =
      PSum.inl witness)
    (hroots : family.AdaptiveDeployedGoodRoots basis O witness)
    (haccepts : adaptiveActionAccepts family basis O)
    (hz : wrappedPreIpaReads (adaptiveActionRunOutput family basis O) 10 ≠ 0)
    (hattack : ¬fullAlgebraicBindingAttackZ basis (family.vk basis)
      (family.instanceCommitment basis) (adaptiveActionRunOutput family basis O).1
      (wrappedPreIpaReads (adaptiveActionRunOutput family basis O))
      (runRounds family.toFamily basis O))
    (hshifted : family.AdaptiveShiftedValue basis O)
    (hx : let data := (family.adversary basis).run O
      let source := data.algebraicProof.preX1AssemblySource
        (family.fixedRepresentations basis)
      let hblinding : (family.vk basis).blindingFactors < (family.vk basis).n := by
        rw [hvk basis]
        exact actionCircuit.toVerifierKey_blindingFactors_lt_n
          (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
      (adaptiveActionRunRecord family basis O).x ∉ szBadSet
        (adaptiveActionPreXDifferenceOf (family.vk basis)
          (family.instanceCommitment basis) data.algebraicProof.erase source
          (adaptiveActionRunRecord family basis O) hblinding))
    (hgoodY : let decode := hI basis ▸ hvk basis ▸
        (family.adaptiveAlgebraicDecode_of_deployedGoodRoots
          basis O witness hroots hshifted).reRound (runRounds family.toFamily basis O)
      let hacceptsAction := adaptiveActionRunAccepts pp family basis O inputs hvk hI haccepts
      let model := CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi)
        (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
          (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)) hacceptsAction
      ∀ j, (adaptiveActionRunRecord family basis O).y ∉
        szBadSet (foldSplitWitness model.constraints actionCircuit.n j))
    (hpermutation : let decode := hI basis ▸ hvk basis ▸
        (family.adaptiveAlgebraicDecode_of_deployedGoodRoots
          basis O witness hroots hshifted).reRound (runRounds family.toFamily basis O)
      let hacceptsAction := adaptiveActionRunAccepts pp family basis O inputs hvk hI haccepts
      ResolverPermutationChallengeExclusions pp.numProofs (ActionTerminal.vkAt basis)
        (adaptiveActionRunRecord family basis O)
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi)
          hacceptsAction) actionActiveRows)
    (hlookup : let decode := hI basis ▸ hvk basis ▸
        (family.adaptiveAlgebraicDecode_of_deployedGoodRoots
          basis O witness hroots hshifted).reRound (runRounds family.toFamily basis O)
      let hacceptsAction := adaptiveActionRunAccepts pp family basis O inputs hvk hI haccepts
      TopLevelLookup.ChallengeExclusions actionCircuit pp
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
        (adaptiveActionRunRecord family basis O)
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi)
          hacceptsAction)) :
    (adaptiveActionCompleteTerminalWitnessOrRelationFinder pp family inputs hvk hI hchar
      basis O hprovenance).isSome := by
  let pnu := adaptiveActionRunOutput family basis O
  let rawDecode := family.adaptiveAlgebraicDecode_of_deployedGoodRoots
    basis O witness hroots hshifted
  let decode := hI basis ▸ hvk basis ▸
    rawDecode.reRound (runRounds family.toFamily basis O)
  let hacceptsAction := adaptiveActionRunAccepts pp family basis O inputs hvk hI haccepts
  let model := CanonicalMemberConstraintRelation.acceptedModel
    (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi)
    (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)) hacceptsAction
  let polynomial := CanonicalMemberConstraintRelation.acceptedPolynomial
    (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi) hacceptsAction
  let data := (family.adversary basis).run O
  let source := data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis)
  let pointPoly := onlinePointPolynomial source
  let piecePoly := fun i => onlinePointPolynomial source (data.algebraicProof.hPieces i).point
  have hblinding : (family.vk basis).blindingFactors < (family.vk basis).n := by
    rw [hvk basis]
    exact actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
  let difference := adaptiveActionPreXDifferenceOf (family.vk basis)
    (family.instanceCommitment basis) data.algebraicProof.erase source
    (adaptiveActionRunRecord family basis O) hblinding
  dsimp only at hx hgoodY hpermutation hlookup
  have hacceptsSome := adaptiveActionAccepts?_isSome_of family basis O haccepts
  obtain ⟨hacceptsProof, hacceptsEq⟩ := Option.isSome_iff_exists.mp hacceptsSome
  have hrootsSome := family.adaptiveDeployedGoodRoots?_isSome_of basis O witness hroots
  obtain ⟨hrootsProof, hrootsEq⟩ := Option.isSome_iff_exists.mp hrootsSome
  have hsrc : witness.fixedRepresentations = family.fixedRepresentations basis :=
    deployedRootOutcomeOfCovered_fixedRepresentations family.toOnlineMemberFamily
      basis O witness hout
  have hrootSourceEq : adaptiveActionRootOutcomeWithSource pp family basis O =
      PSum.inl ⟨witness, hsrc⟩ := by
    simpa only [hsrc] using
      adaptiveActionRootOutcomeWithSource_eq_inl pp family basis O witness hout
  by_cases hsupport : difference = 0
  · have hidentityDataSome :=
      adaptiveActionPreXIdentityWitnessOrRelationFinder_isSome_of
      pp family inputs hvk hI hchar basis O hprovenance witness hsrc hroots hshifted
      haccepts (by simpa only [difference, source, data] using hsupport)
      hgoodY hpermutation hlookup
    obtain ⟨outcome, hidentityEq⟩ := Option.isSome_iff_exists.mp hidentityDataSome
    unfold adaptiveActionCompleteTerminalWitnessOrRelationFinder
    rw [hacceptsEq]
    dsimp only
    rw [dif_pos hz, dif_neg hattack]
    rw [hrootSourceEq]
    dsimp only
    rw (occs := .pos [1]) [hrootsEq]
    dsimp only
    rw [hidentityEq]
    rfl
  · have hbatches : rawDecode.batches = witness.batches := by rfl
    have heval := family.adaptiveActionAcceptedDifference_eval_eq_preX pp basis O inputs
      hvk hI hprovenance witness hsrc rawDecode hbatches haccepts (hchar basis O)
    dsimp only at heval
    have hdiffData := adaptiveActionPreXDifferenceOf_action pp basis inputs
      (family.vk basis) (family.instanceCommitment basis) data.algebraicProof.erase source
      (adaptiveActionRunRecord family basis O) hblinding (hvk basis) (hI basis)
    rw [← hdiffData] at heval
    have hdifferenceNe : difference ≠ 0 := hsupport
    have hpreEval : difference.eval (adaptiveActionRunRecord family basis O).x ≠ 0 :=
      (not_mem_szBadSet.mp hx) hdifferenceNe
    have heval' :
        (combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
          model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
          (adaptiveActionRunRecord family basis O).y model.chunkLen model.l0 model.lLast
          model.lBlind - polynomial .vanishingH *
            (X ^ actionCircuit.n - 1)).eval
              (adaptiveActionRunRecord family basis O).x =
          difference.eval (adaptiveActionRunRecord family basis O).x := by
      simpa only [model, polynomial, difference] using heval
    have hactionGood : (adaptiveActionRunRecord family basis O).x ∉ szBadSet
        (combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
          model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
          (adaptiveActionRunRecord family basis O).y model.chunkLen model.l0 model.lLast
          model.lBlind - polynomial .vanishingH *
            (X ^ actionCircuit.n - 1)) := by
      apply not_mem_szBadSet.mpr
      intro _
      rw [heval']
      exact hpreEval
    have holdDataSome := adaptiveActionWitnessOrRelationOfDecode?_isSome_of
      pp family basis O inputs (hchar basis O) decode hacceptsAction hactionGood hgoodY
      hpermutation hlookup
    have hidentityNone : adaptiveActionPreXIdentityWitnessOrRelationFinder pp family inputs
        hvk hI hchar
        basis O hprovenance witness hsrc hroots hshifted haccepts = none := by
      unfold adaptiveActionPreXIdentityWitnessOrRelationFinder
      rw [dif_neg (by simpa only [difference, source, data] using hsupport)]
    unfold adaptiveActionCompleteTerminalWitnessOrRelationFinder
    rw [hacceptsEq]
    dsimp only
    rw [dif_pos hz, dif_neg hattack]
    rw [hrootSourceEq]
    dsimp only
    rw (occs := .pos [1]) [hrootsEq]
    dsimp only
    rw [hidentityNone]
    simpa only [decode, rawDecode, hacceptsAction, pnu] using holdDataSome

/-- A false statement rules out the extracted-witness branch of the complete outcome. -/
theorem adaptiveActionCompleteTerminalRelationFinder_isSome_of
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (hprovenance : family.adaptiveActionRepresentationRelationFinder basis O = none)
    (witness : DeployedBatchWitness family.toFamily basis
      (adaptiveActionRunOutput family basis O))
    (hout : deployedRootOutcomeOfCovered family.toOnlineMemberFamily basis O =
      PSum.inl witness)
    (hroots : family.AdaptiveDeployedGoodRoots basis O witness)
    (haccepts : adaptiveActionAccepts family basis O)
    (hz : wrappedPreIpaReads (adaptiveActionRunOutput family basis O) 10 ≠ 0)
    (hattack : ¬fullAlgebraicBindingAttackZ basis (family.vk basis)
      (family.instanceCommitment basis) (adaptiveActionRunOutput family basis O).1
      (wrappedPreIpaReads (adaptiveActionRunOutput family basis O))
      (runRounds family.toFamily basis O))
    (hshifted : family.AdaptiveShiftedValue basis O)
    (hfalse : ¬BundleStatement inputs)
    (hx : let data := (family.adversary basis).run O
      let source := data.algebraicProof.preX1AssemblySource
        (family.fixedRepresentations basis)
      let hblinding : (family.vk basis).blindingFactors < (family.vk basis).n := by
        rw [hvk basis]
        exact actionCircuit.toVerifierKey_blindingFactors_lt_n
          (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
      (adaptiveActionRunRecord family basis O).x ∉ szBadSet
        (adaptiveActionPreXDifferenceOf (family.vk basis)
          (family.instanceCommitment basis) data.algebraicProof.erase source
          (adaptiveActionRunRecord family basis O) hblinding))
    (hgoodY : let decode := hI basis ▸ hvk basis ▸
        (family.adaptiveAlgebraicDecode_of_deployedGoodRoots
          basis O witness hroots hshifted).reRound (runRounds family.toFamily basis O)
      let hacceptsAction := adaptiveActionRunAccepts pp family basis O inputs hvk hI haccepts
      let model := CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi)
        (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
          (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)) hacceptsAction
      ∀ j, (adaptiveActionRunRecord family basis O).y ∉
        szBadSet (foldSplitWitness model.constraints actionCircuit.n j))
    (hpermutation : let decode := hI basis ▸ hvk basis ▸
        (family.adaptiveAlgebraicDecode_of_deployedGoodRoots
          basis O witness hroots hshifted).reRound (runRounds family.toFamily basis O)
      let hacceptsAction := adaptiveActionRunAccepts pp family basis O inputs hvk hI haccepts
      ResolverPermutationChallengeExclusions pp.numProofs (ActionTerminal.vkAt basis)
        (adaptiveActionRunRecord family basis O)
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi)
          hacceptsAction) actionActiveRows)
    (hlookup : let decode := hI basis ▸ hvk basis ▸
        (family.adaptiveAlgebraicDecode_of_deployedGoodRoots
          basis O witness hroots hshifted).reRound (runRounds family.toFamily basis O)
      let hacceptsAction := adaptiveActionRunAccepts pp family basis O inputs hvk hI haccepts
      TopLevelLookup.ChallengeExclusions actionCircuit pp
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
        (adaptiveActionRunRecord family basis O)
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode (hchar basis O) i hi)
          hacceptsAction)) :
    (adaptiveActionCompleteTerminalRelationFinder pp family inputs hvk hI hchar
      basis O hprovenance).isSome :=
  adaptiveActionCompleteTerminalRelationFinder_isSome_of_witnessOrRelation
    pp family inputs hvk hI hchar basis O hprovenance
      (adaptiveActionCompleteTerminalWitnessOrRelationFinder_isSome_of
        pp family inputs hvk hI hchar basis O hprovenance witness hout hroots haccepts
        hz hattack hshifted hx hgoodY hpermutation hlookup)
      hfalse

/-- One cached adaptive execution returning either extracted Action witnesses or relation data. -/
def adaptiveActionKnowledgeOutcome :
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp) →
    Option (ActionBundleWitness inputs ⊕
      AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    match hprovenance : family.adaptiveActionRepresentationRelationFinder basis O with
    | some relation => some (Sum.inr relation)
    | none =>
        match family.adaptiveStraightLineDeployedRelationFinder basis O with
        | some relation => some (Sum.inr relation)
        | none => adaptiveActionCompleteTerminalWitnessOrRelationFinder pp family inputs
            hvk hI hchar basis O hprovenance

theorem adaptiveActionKnowledgeOutcome_eq_complete_of_none
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (hprovenance : family.adaptiveActionRepresentationRelationFinder basis O = none)
    (hstraight : family.adaptiveStraightLineDeployedRelationFinder basis O = none) :
    adaptiveActionKnowledgeOutcome pp family inputs hvk hI hchar basis O =
      adaptiveActionCompleteTerminalWitnessOrRelationFinder pp family inputs hvk hI hchar
        basis O hprovenance := by
  unfold adaptiveActionKnowledgeOutcome
  split
  · rename_i relation heq
    rw [heq] at hprovenance
    contradiction
  · split
    · rename_i relation heq
      rw [heq] at hstraight
      contradiction
    · congr

/-- Executable knowledge extractor for every private Action witness in the accepted bundle. -/
def adaptiveActionKnowledgeExtractor :
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp) →
    Option (ActionBundleWitness inputs) := fun basis O =>
  match adaptiveActionKnowledgeOutcome pp family inputs hvk hI hchar basis O with
  | some (Sum.inl witness) => some witness
  | _ => none

/-- The complete adaptive relation projection, charged by one DLOG reduction. -/
def adaptiveActionRelationFinder :
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp) →
    Option (AlgebraicRelationWitness (F := Fp) basis) := fun basis O =>
  match adaptiveActionKnowledgeOutcome pp family inputs hvk hI hchar basis O with
  | some (Sum.inr relation) => some relation
  | _ => none

/-- Modeled adversary traversals of the shared executable knowledge outcome.  Action provenance performs
one output/annotation traversal and one quotient traversal.  The deployed straight-line list adds
four traversals, and its terminal fallback adds two more. -/
def adaptiveActionRelationFinderCalls
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp) : Nat :=
  match family.adaptiveActionRepresentationRelationFinder basis O with
  | some _ => 2
  | none =>
      match family.adaptiveStraightLineDeployedRelationFinder basis O with
      | some _ => 6
      | none => 8

/-- Independently charged adversary-traversal slots in the adaptive combined finder: one cached
output/annotation traversal plus the quotient traversal for Action provenance, four traversals for
cached pre-IPA provenance, cached IPA provenance, IPA binding, and deployed roots, and two for the
terminal fallback. -/
def adaptiveActionDlogTraversalSlots : Nat := 2 + 4 + 2

@[simp] theorem adaptiveActionDlogTraversalSlots_eq_eight :
    adaptiveActionDlogTraversalSlots = 8 := rfl

/-- The executable combined finder has a pointwise eight-traversal bound. -/
theorem adaptiveActionRelationFinderCalls_le_traversalSlots
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp) :
    adaptiveActionRelationFinderCalls pp family basis O ≤ adaptiveActionDlogTraversalSlots := by
  unfold adaptiveActionRelationFinderCalls adaptiveActionDlogTraversalSlots
  split
  · omega
  · split <;> omega

/-- The witness extractor and relation projection share this pointwise traversal bound; neither
projection reruns the adversary or re-scans a provenance log. -/
theorem adaptiveActionKnowledgeExtractorCalls_le_traversalSlots
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp) :
    adaptiveActionRelationFinderCalls pp family basis O ≤ adaptiveActionDlogTraversalSlots :=
  adaptiveActionRelationFinderCalls_le_traversalSlots pp family basis O

/-- Each of the three provenance aggregates retains one output/annotation log of length at most
`Q`; its five, six, or `k` lookups scan that retained data and make no further oracle calls. -/
theorem adaptiveActionCachedProvenanceLog_length_le
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp) :
    ((family.adversary basis).runWithAnnotations O).2.length ≤ family.Q :=
  family.runWithAnnotations_log_length_le basis O

/-- Conservative random-oracle work for the adaptive combined finder after provenance caching.
Every independently charged traversal slot includes its own `Q`-query run allowance and its own
designated `11 + k` transcript reads. -/
def adaptiveActionDlogRandomOracleQueries : Nat :=
  adaptiveActionDlogTraversalSlots * family.Q +
    adaptiveActionDlogTraversalSlots * (11 + actionCircuit.domainExponent)

/-- The knowledge extractor is the other projection of the same cached outcome, so it has the
same random-oracle envelope and does not add a ninth adversary traversal. -/
def adaptiveActionKnowledgeExtractorRandomOracleQueries : Nat :=
  adaptiveActionDlogRandomOracleQueries pp family

@[simp] theorem adaptiveActionKnowledgeExtractorRandomOracleQueries_eq :
    adaptiveActionKnowledgeExtractorRandomOracleQueries pp family =
      adaptiveActionDlogRandomOracleQueries pp family := rfl

/-- Group-work envelope of the adaptive combined finder. -/
def adaptiveActionDlogGroupWork (proverGroupWork reductionGroupWork : Nat) : Nat :=
  8 * proverGroupWork + reductionGroupWork

/-- Direct-coordinate work of one adaptive deployed-root decode on the actual run. -/
def adaptiveActionDirectDecodeOps
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp) : Nat :=
  let pnu := adaptiveActionRunOutput family basis O
  deployedDirectDecodeOps (family.vk basis) (family.instanceCommitment basis)
    pnu.1.proof.1 (adaptiveActionRunRecord family basis O)
    (pnu.1.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis)).length

/-- Finite-security premise for the complete adaptive Action finder. -/
structure AdaptiveActionDlogProfile (B : VestaG) where
  proverGroupWork : Nat
  reductionGroupWork : Nat
  advantage : Nat → Nat → ENNReal
  advantage_mono : ∀ {q q' g g'}, q ≤ q' → g ≤ g' →
    advantage q g ≤ advantage q' g'
  hardness : TextbookDLWithCoinsAdvantageLE B
    (adaptiveActionRelationFinder pp family inputs hvk hI hchar)
    (advantage (adaptiveActionDlogRandomOracleQueries pp family)
      (adaptiveActionDlogGroupWork proverGroupWork reductionGroupWork))

/-- Concrete resource profile for the bare adaptive route.  Unlike the sequential six-call
profile, this charges all eight independently traversed adaptive slots after provenance caching. -/
structure AdaptiveActionDirectDlogProfile (B : VestaG) (T : Nat)
    extends AdaptiveActionDlogProfile pp family inputs hvk hI hchar B where
  scheduleOverheadBound : 11 + actionCircuit.domainExponent ≤ T
  queryBound : family.Q ≤ T
  proverWorkBound : toAdaptiveActionDlogProfile.proverGroupWork ≤ T
  reductionWorkBound : toAdaptiveActionDlogProfile.reductionGroupWork ≤ T
  directDecodeWorkBound : ∀ basis O,
    2 * adaptiveActionDirectDecodeOps pp family basis O ≤ T

/-- The concrete adaptive profile fits a conservative four-bit solver envelope. -/
theorem AdaptiveActionDirectDlogProfile.solverCost_le
    {B : VestaG} {T : Nat}
    (profile : AdaptiveActionDirectDlogProfile pp family inputs hvk hI hchar B T) :
    adaptiveActionDlogRandomOracleQueries pp family ≤ 16 * T ∧
      adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
        16 * T ∧
      ∀ basis O, 2 * adaptiveActionDirectDecodeOps pp family basis O ≤ T := by
  constructor
  · unfold adaptiveActionDlogRandomOracleQueries
    rw [adaptiveActionDlogTraversalSlots_eq_eight]
    have hT := profile.scheduleOverheadBound
    calc
      8 * family.Q + 8 * (11 + actionCircuit.domainExponent) ≤
          8 * T + 8 * (11 + actionCircuit.domainExponent) := by
        gcongr
        exact profile.queryBound
      _ ≤ 16 * T := by omega
  constructor
  · unfold adaptiveActionDlogGroupWork
    calc
      8 * profile.proverGroupWork + profile.reductionGroupWork ≤ 8 * T + T := by
        gcongr
        · exact profile.proverWorkBound
        · exact profile.reductionWorkBound
      _ ≤ 16 * T := by omega
  · exact profile.directDecodeWorkBound

/-- Concrete runtime accounting for the knowledge extractor projection: cached oracle
traversals, represented group work, and direct deployed-root decoding. -/
theorem AdaptiveActionDirectDlogProfile.knowledgeExtractorCost_le
    {B : VestaG} {T : Nat}
    (profile : AdaptiveActionDirectDlogProfile pp family inputs hvk hI hchar B T) :
    adaptiveActionKnowledgeExtractorRandomOracleQueries pp family ≤ 16 * T ∧
      adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
        16 * T ∧
      ∀ basis O, 2 * adaptiveActionDirectDecodeOps pp family basis O ≤ T := by
  simpa only [adaptiveActionKnowledgeExtractorRandomOracleQueries_eq] using profile.solverCost_le

/-- An empty combined finder excludes every stage-local Action provenance mismatch. -/
theorem adaptiveActionRelationFinder_none_actionProvenance
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (hnone : adaptiveActionRelationFinder pp family inputs hvk hI hchar basis O = none) :
    family.adaptiveActionRepresentationRelationFinder basis O = none := by
  generalize hprovenance : family.adaptiveActionRepresentationRelationFinder basis O = outcome
  cases outcome with
  | none => rfl
  | some relation =>
      have houtcome : adaptiveActionKnowledgeOutcome pp family inputs hvk hI hchar basis O =
          some (Sum.inr relation) := by
        unfold adaptiveActionKnowledgeOutcome
        split
        · rename_i relation' heq
          have hr : relation' = relation := Option.some.inj (heq.symm.trans hprovenance)
          subst relation'
          rfl
        · rename_i hnone'
          rw [hnone'] at hprovenance
          contradiction
      unfold adaptiveActionRelationFinder at hnone
      rw [houtcome] at hnone
      contradiction

/-- An empty combined finder also excludes every pre-IPA/IPA/deployed-root relation branch. -/
theorem adaptiveActionRelationFinder_none_straightLine
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (hnone : adaptiveActionRelationFinder pp family inputs hvk hI hchar basis O = none) :
    family.adaptiveStraightLineDeployedRelationFinder basis O = none := by
  have hprovenance := adaptiveActionRelationFinder_none_actionProvenance
    pp family inputs hvk hI hchar basis O hnone
  generalize hstraight : family.adaptiveStraightLineDeployedRelationFinder basis O = outcome
  cases outcome with
  | none => rfl
  | some relation =>
      have houtcome : adaptiveActionKnowledgeOutcome pp family inputs hvk hI hchar basis O =
          some (Sum.inr relation) := by
        unfold adaptiveActionKnowledgeOutcome
        split
        · rename_i relation' heq
          rw [heq] at hprovenance
          contradiction
        · split
          · rename_i relation' heq
            have hr : relation' = relation := Option.some.inj (heq.symm.trans hstraight)
            subst relation'
            rfl
          · rename_i hnone'
            rw [hnone'] at hstraight
            contradiction
      unfold adaptiveActionRelationFinder at hnone
      rw [houtcome] at hnone
      contradiction

/-- Explicit relation-producing runs of the combined adaptive Action finder. -/
def adaptiveActionRelationEvent :
    Set ((AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)) :=
  {q | (adaptiveActionRelationFinder pp family inputs hvk hI hchar q.1 q.2).isSome}

/-- The separately priced adaptive `z = 0` slice. -/
def adaptiveActionZeroEvent :
    Set ((AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)) :=
  {q | wrappedPreIpaReads (adaptiveActionRunOutput family q.1 q.2) 10 = 0}

/-- The union of the annotation-aware adaptive IPA surfaces. -/
def adaptiveActionIpaEvent :
    Set ((AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)) :=
  {q | ∃ j : Fin (actionCircuit.shape.withProofParams pp).k,
    q.2 ∈ family.adaptiveIpaBadWithoutRelation q.1 j}

/-- The union of the six annotation-aware deployed-root surfaces. -/
def adaptiveActionRootEvent :
    Set ((AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)) :=
  {q | ∃ i : Fin 6, q.2 ∈ family.adaptiveRootBadWithoutRelation q.1 i}

/-- The semantic-squeeze obligation outside the executable algebraic branches. Subsequent Action
surface lemmas refine this residual into the `x/y/β/γ/θ` finite bad sets; importantly, it is stated
directly on the bare adaptive family. -/
def adaptiveActionSemanticResidualEvent :
    Set ((AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)) :=
  adaptiveActionAcceptFalseStatementEvent pp family inputs \
    (adaptiveActionZeroEvent pp family ∪
      (adaptiveActionIpaEvent pp family ∪
        (adaptiveActionRootEvent pp family ∪
          adaptiveActionRelationEvent pp family inputs hvk hI hchar)))

/-- Literal false-statement acceptance is exhausted by the zero slice, adaptive IPA/root
surfaces, the single computed relation event, and the remaining five semantic squeezes. -/
theorem adaptiveActionAcceptFalseStatementEvent_subset :
    adaptiveActionAcceptFalseStatementEvent pp family inputs ⊆
      adaptiveActionZeroEvent pp family ∪
        (adaptiveActionIpaEvent pp family ∪
          (adaptiveActionRootEvent pp family ∪
            (adaptiveActionRelationEvent pp family inputs hvk hI hchar ∪
              adaptiveActionSemanticResidualEvent pp family inputs hvk hI hchar))) := by
  intro q hq
  by_cases hz : q ∈ adaptiveActionZeroEvent pp family
  · exact Or.inl hz
  by_cases hipa : q ∈ adaptiveActionIpaEvent pp family
  · exact Or.inr (Or.inl hipa)
  by_cases hroot : q ∈ adaptiveActionRootEvent pp family
  · exact Or.inr (Or.inr (Or.inl hroot))
  by_cases hrelation : q ∈ adaptiveActionRelationEvent pp family inputs hvk hI hchar
  · exact Or.inr (Or.inr (Or.inr (Or.inl hrelation)))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hq, ?_⟩)))
    simp only [Set.mem_union, not_or]
    exact ⟨hz, hipa, hroot, hrelation⟩

/-- Outside every priced algebraic/statistical event, an accepting run produces executable
private witnesses for every Action in the bundle. -/
theorem adaptiveActionKnowledgeExtractor_isSome_of_no_events
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (haccepts : adaptiveActionAccepts family basis O)
    (hzeroEvent : (basis, O) ∉ adaptiveActionZeroEvent pp family)
    (hipaEvent : (basis, O) ∉ adaptiveActionIpaEvent pp family)
    (hrootEvent : (basis, O) ∉ adaptiveActionRootEvent pp family)
    (hrelationEvent : (basis, O) ∉
      adaptiveActionRelationEvent pp family inputs hvk hI hchar)
    (hnosurface : ∀ n : Fin 5,
      O ∉ family.adaptiveActionBadWithoutRelation pp inputs basis n) :
    (adaptiveActionKnowledgeExtractor pp family inputs hvk hI hchar basis O).isSome := by
  change ¬(adaptiveActionRelationFinder pp family inputs hvk hI hchar basis O).isSome
    at hrelationEvent
  have hfinderNone := Option.not_isSome_iff_eq_none.mp hrelationEvent
  have hprovenance := adaptiveActionRelationFinder_none_actionProvenance pp family inputs
    hvk hI hchar basis O hfinderNone
  have hstraight := adaptiveActionRelationFinder_none_straightLine pp family inputs
    hvk hI hchar basis O hfinderNone
  let data := (family.adversary basis).run O
  let pnu := adaptiveActionRunOutput family basis O
  let nu : Fin 11 → Fp := fun i =>
    O (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof i)
  have hnu : wrappedPreIpaReads pnu = nu := by
    exact (wrappedPreIpaReads_run family.toFamily basis O).trans (by
      simpa only [nu, data] using family.toFamily_runReads basis O)
  have hsurface : ∀ n : Fin 5,
      let n11 : Fin 11 := Fin.castLE (by omega) n
      nu n11 ∉ adaptiveActionSurfaceAt pp basis inputs n data.algebraicProof.erase
        (data.algebraicProof.actionRepresentationsBefore n ++
          family.fixedRepresentations basis)
        (fun i => nu (i.castLE (le_of_lt n11.isLt))) := by
    intro n
    exact fun hbad => hnosurface n
      ((family.mem_adaptiveActionBadWithoutRelation_iff pp inputs basis O n
        hprovenance).2 hbad)
  have hz : wrappedPreIpaReads pnu 10 ≠ 0 := by
    intro hz
    apply hzeroEvent
    exact hz
  have hpreIpaNone : family.adaptivePreIpaRepresentationRelationFinder basis O = none :=
    (family.adaptiveStraightLineDeployedRelationFinder_none_provenance
      basis O hstraight).1
  have hrootGood : family.AdaptiveAllRootGood basis O := by
    unfold ComputedAdaptiveOnlineAGMFSFamily.AdaptiveAllRootGood
    dsimp only
    intro i hbad
    apply hrootEvent
    refine ⟨i, ?_⟩
    exact ⟨hbad, hpreIpaNone⟩
  obtain ⟨witness, hwitness⟩ :=
    family.adaptiveDeployedRootOutcome_eq_inl_of_finder_none basis O hstraight
  have hdeployedRoots := family.adaptiveDeployedGoodRoots_of_goodRoots
    basis O witness hwitness hrootGood
  have hattack : ¬fullAlgebraicBindingAttackZ basis (family.vk basis)
      (family.instanceCommitment basis) pnu.1
      (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O) := by
    intro hattack
    have hpnu : pnu.1 = data.toAlgebraicWfProof :=
      (wrappedAdversary_run_fst family.toFamily basis O).trans
        (family.toFamily_runProof basis O)
    have hrounds : runRounds family.toFamily basis O =
        fun j => O (algebraicFullPrefixes family.init data.toAlgebraicWfProof j) := by
      funext j
      unfold runRounds
      change O (algebraicFullPrefixes family.init
        (runProof family.toFamily basis O) j) = _
      rw [family.toFamily_runProof]
      rfl
    have hattack' := hattack
    rw [hpnu, hnu, hrounds] at hattack'
    obtain ⟨j, hj⟩ := family.adaptiveBindingAttack_ipaBad basis O hattack' hstraight
    exact hipaEvent ⟨j, hj⟩
  let hshifted := adaptiveShiftedValue_of_accept_not_attack
    family basis O haccepts hz hattack
  let rawDecode := family.adaptiveAlgebraicDecode_of_deployedGoodRoots
    basis O witness hdeployedRoots hshifted
  have hsrc : witness.fixedRepresentations = family.fixedRepresentations basis :=
    deployedRootOutcomeOfCovered_fixedRepresentations family.toOnlineMemberFamily
      basis O witness hwitness
  have hbatches : rawDecode.batches = witness.batches := by rfl
  have hexclusions := family.adaptiveActionExclusions_of_no_surface pp basis O inputs
    hvk hI hprovenance witness hsrc rawDecode hbatches haccepts (hchar basis O) hsurface
  let source := data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis)
  have hblinding : (family.vk basis).blindingFactors < (family.vk basis).n := by
    rw [hvk basis]
    exact actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
  have hdiffData := adaptiveActionPreXDifferenceOf_action pp basis inputs
    (family.vk basis) (family.instanceCommitment basis) data.algebraicProof.erase source
    (adaptiveActionRunRecord family basis O) hblinding (hvk basis) (hI basis)
  have hx : (adaptiveActionRunRecord family basis O).x ∉ szBadSet
      (adaptiveActionPreXDifferenceOf (family.vk basis)
        (family.instanceCommitment basis) data.algebraicProof.erase source
        (adaptiveActionRunRecord family basis O) hblinding) := by
    rw [hdiffData]
    exact hexclusions.1
  have hterminalSome := adaptiveActionCompleteTerminalWitnessOrRelationFinder_isSome_of
    pp family inputs hvk hI hchar basis O hprovenance witness hwitness hdeployedRoots
    haccepts hz hattack hshifted (by simpa only [data, source] using hx)
    hexclusions.2.1 hexclusions.2.2.1
    hexclusions.2.2.2
  have houtcomeEq := adaptiveActionKnowledgeOutcome_eq_complete_of_none pp family inputs
    hvk hI hchar basis O hprovenance hstraight
  have houtcomeSome :
      (adaptiveActionKnowledgeOutcome pp family inputs hvk hI hchar basis O).isSome := by
    rw [houtcomeEq]
    exact hterminalSome
  obtain ⟨outcome, houtcome⟩ := Option.isSome_iff_exists.mp houtcomeSome
  cases outcome with
  | inl extracted =>
      unfold adaptiveActionKnowledgeExtractor
      rw [houtcome]
      rfl
  | inr relation =>
      unfold adaptiveActionRelationFinder at hfinderNone
      rw [houtcome] at hfinderNone
      contradiction

/-- The ordinary semantic residual is contained in the same five surfaces, now as a corollary
of the executable knowledge extractor. -/
theorem adaptiveActionSemanticResidualEvent_subset_surfaces :
    adaptiveActionSemanticResidualEvent pp family inputs hvk hI hchar ⊆
      {q | ∃ n : Fin 5, q.2 ∈ family.adaptiveActionBadWithoutRelation pp inputs q.1 n} := by
  rintro ⟨basis, O⟩ hresidual
  rcases hresidual with ⟨⟨haccepts, hfalse⟩, houtside⟩
  simp only [Set.mem_union, not_or] at houtside
  rcases houtside with ⟨hzeroEvent, hipaEvent, hrootEvent, hrelationEvent⟩
  by_contra hnosurface
  have hnosurface' : ∀ n : Fin 5,
      O ∉ family.adaptiveActionBadWithoutRelation pp inputs basis n := by
    intro n hbad
    exact hnosurface ⟨n, hbad⟩
  have hextracted := adaptiveActionKnowledgeExtractor_isSome_of_no_events
    pp family inputs hvk hI hchar basis O haccepts hzeroEvent hipaEvent hrootEvent
      hrelationEvent hnosurface'
  obtain ⟨extracted, hextractedEq⟩ := Option.isSome_iff_exists.mp hextracted
  exact hfalse extracted.statement

/-- Knowledge-soundness failure: the deployed verifier accepts but the executable extractor
does not return private witnesses for the whole Action bundle. -/
def adaptiveActionKnowledgeFailureEvent :
    Set ((AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)) :=
  {q | adaptiveActionAccepts family q.1 q.2 ∧
    adaptiveActionKnowledgeExtractor pp family inputs hvk hI hchar q.1 q.2 = none}

def adaptiveActionKnowledgeResidualEvent :
    Set ((AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)) :=
  adaptiveActionKnowledgeFailureEvent pp family inputs hvk hI hchar \
    (adaptiveActionZeroEvent pp family ∪
      (adaptiveActionIpaEvent pp family ∪
        (adaptiveActionRootEvent pp family ∪
          adaptiveActionRelationEvent pp family inputs hvk hI hchar)))

theorem adaptiveActionKnowledgeFailureEvent_subset :
    adaptiveActionKnowledgeFailureEvent pp family inputs hvk hI hchar ⊆
      adaptiveActionZeroEvent pp family ∪
        (adaptiveActionIpaEvent pp family ∪
          (adaptiveActionRootEvent pp family ∪
            (adaptiveActionRelationEvent pp family inputs hvk hI hchar ∪
              adaptiveActionKnowledgeResidualEvent pp family inputs hvk hI hchar))) := by
  intro q hq
  by_cases hz : q ∈ adaptiveActionZeroEvent pp family
  · exact Or.inl hz
  by_cases hipa : q ∈ adaptiveActionIpaEvent pp family
  · exact Or.inr (Or.inl hipa)
  by_cases hroot : q ∈ adaptiveActionRootEvent pp family
  · exact Or.inr (Or.inr (Or.inl hroot))
  by_cases hrelation : q ∈ adaptiveActionRelationEvent pp family inputs hvk hI hchar
  · exact Or.inr (Or.inr (Or.inr (Or.inl hrelation)))
  · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hq, ?_⟩)))
    simp only [Set.mem_union, not_or]
    exact ⟨hz, hipa, hroot, hrelation⟩

theorem adaptiveActionKnowledgeResidualEvent_subset_surfaces :
    adaptiveActionKnowledgeResidualEvent pp family inputs hvk hI hchar ⊆
      {q | ∃ n : Fin 5, q.2 ∈ family.adaptiveActionBadWithoutRelation pp inputs q.1 n} := by
  rintro ⟨basis, O⟩ hresidual
  rcases hresidual with ⟨⟨haccepts, hextractorNone⟩, houtside⟩
  simp only [Set.mem_union, not_or] at houtside
  rcases houtside with ⟨hzeroEvent, hipaEvent, hrootEvent, hrelationEvent⟩
  by_contra hnosurface
  have hnosurface' : ∀ n : Fin 5,
      O ∉ family.adaptiveActionBadWithoutRelation pp inputs basis n := by
    intro n hbad
    exact hnosurface ⟨n, hbad⟩
  have hextracted := adaptiveActionKnowledgeExtractor_isSome_of_no_events
    pp family inputs hvk hI hchar basis O haccepts hzeroEvent hipaEvent hrootEvent
      hrelationEvent hnosurface'
  rw [hextractorNone] at hextracted
  contradiction

/-- Transfer any adaptive Action event across a uniform-URS basis identification. -/
theorem adaptiveActionEvent_prob_eq_of_uniformURS
    {Omega : Type*} (setup : PMF Omega) (B : VestaG)
    (basisOf : Omega → AugmentedIndex actionCircuit.n → VestaG)
    (hURS : OrchardUniformURSIdentification setup
      actionCircuit.domainExponent B basisOf)
    (event : Set ((AugmentedIndex actionCircuit.n → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * actionCircuit.domainExponent) → Fp))) :
    (independentProductPMF setup
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
      ((fun p => (basisOf p.1, p.2)) ⁻¹' event) =
    (PMF.uniformOfFintype
      ((AugmentedIndex actionCircuit.n → Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
      ((fun p => (scalarBasis B p.1, p.2)) ⁻¹' event) := by
  let oraclePMF := PMF.uniformOfFintype
    (BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * actionCircuit.domainExponent) → Fp)
  have hprod :
      (independentProductPMF setup oraclePMF).map (fun p => (basisOf p.1, p.2)) =
        (independentProductPMF
          (PMF.uniformOfFintype
            (AugmentedIndex actionCircuit.n → Fp))
          oraclePMF).map (fun p => (scalarBasis B p.1, p.2)) := by
    calc
      _ = independentProductPMF (setup.map basisOf) oraclePMF :=
        independentProductPMF_map_left setup oraclePMF basisOf
      _ = independentProductPMF
          ((PMF.uniformOfFintype
            (AugmentedIndex actionCircuit.n → Fp)).map
              (scalarBasis B)) oraclePMF :=
        congrArg (fun p => independentProductPMF p oraclePMF) hURS
      _ = _ := (independentProductPMF_map_left
        (PMF.uniformOfFintype
          (AugmentedIndex actionCircuit.n → Fp))
        oraclePMF (scalarBasis B)).symm
  have hmeasure := congrArg
    (fun p : PMF ((AugmentedIndex actionCircuit.n → VestaG) ×
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * actionCircuit.domainExponent) → Fp)) =>
      p.toOuterMeasure event) hprod
  change ((independentProductPMF setup oraclePMF).map
      (fun p => (basisOf p.1, p.2))).toOuterMeasure event =
    ((independentProductPMF
      (PMF.uniformOfFintype
        (AugmentedIndex actionCircuit.n → Fp))
      oraclePMF).map (fun p => (scalarBasis B p.1, p.2))).toOuterMeasure event at hmeasure
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply] at hmeasure
  calc
    _ = (independentProductPMF
        (PMF.uniformOfFintype
          (AugmentedIndex actionCircuit.n → Fp))
        oraclePMF).toOuterMeasure
      ((fun p => (scalarBasis B p.1, p.2)) ⁻¹' event) := hmeasure
    _ = _ := by rw [independentProductPMF_uniform]

/-- The combined executable adaptive Action finder has the standard textbook-DLOG reduction. -/
theorem adaptiveActionRelation_prob_le_of_textbookDL
    (B : VestaG) {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      (adaptiveActionRelationFinder pp family inputs hvk hI hchar) bound) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp))).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹'
        adaptiveActionRelationEvent pp family inputs hvk hI hchar) ≤
      bound + 1 / Fintype.card Fp := by
  simpa [adaptiveActionRelationEvent, relSetWithCoins] using
    (relationWithCoins_prob_le_of_textbookDL B
      (adaptiveActionRelationFinder pp family inputs hvk hI hchar) hDL)

/-- The adaptive Action zero slice has the ordinary one-field query-loss price. -/
theorem adaptiveActionZero_prob_le (B : VestaG) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp))).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' adaptiveActionZeroEvent pp family) ≤
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) := by
  apply uniformOfFintype_prod_fiber_bound_right
    (fun logs => {O | (scalarBasis B logs, O) ∈ adaptiveActionZeroEvent pp family})
  intro logs
  let basis := scalarBasis B logs
  have hzero := fsAdvantageFull_zero_slice_le (family.toFamily.adversary basis)
    (fun _ _ _ => True) (algebraicFullPrefixesPre family.init)
    (algebraicFullPrefixes family.init) 10 (family.toFamily.queryBound basis)
  simpa only [adaptiveActionZeroEvent, Set.mem_setOf_eq, basis, fsWinsFull, true_and,
    adaptiveActionRunOutput, wrappedPreIpaReads_run, runReads] using hzero

/-- All adaptive IPA surfaces, averaged over the sampled basis, retain their direct squeeze
price. -/
theorem adaptiveActionIpa_prob_le (B : VestaG) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp))).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' adaptiveActionIpaEvent pp family) ≤
      (actionCircuit.shape.withProofParams pp).k *
        ((family.Q + 1 : Nat) * (2 / (Fintype.card Fp : ENNReal))) := by
  apply uniformOfFintype_prod_fiber_bound_right
    (fun logs => {O | ∃ j : Fin (actionCircuit.shape.withProofParams pp).k,
      O ∈ family.adaptiveIpaBadWithoutRelation (scalarBasis B logs) j})
  intro logs
  exact family.adaptiveIpaBadWithoutRelation_all_measure_le (scalarBasis B logs)

/-- All six deployed-root surfaces, averaged over the sampled basis, retain their direct adaptive
squeeze price. -/
theorem adaptiveActionRoot_prob_le (B : VestaG) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp))).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹' adaptiveActionRootEvent pp family) ≤
      (family.Q + 1 : Nat) *
        algebraicRootBudget (actionCircuit.shape.withProofParams pp)
          (actionCircuit.shape.withProofParams pp).k := by
  apply uniformOfFintype_prod_fiber_bound_right
    (fun logs => {O | ∃ i : Fin 6,
      O ∈ family.adaptiveRootBadWithoutRelation (scalarBasis B logs) i})
  intro logs
  exact family.adaptiveRootBadWithoutRelation_all_measure_le (scalarBasis B logs)

/-- The adaptive semantic residual is priced directly by the five annotation-aware Action
surfaces, averaged over the sampled AGM basis. -/
theorem adaptiveActionSemanticResidual_prob_le
    (B : VestaG) (epsilon : Fin 5 → ENNReal)
    (hsurface : ∀
      (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
      (n : Fin 5)
      (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
      (_hwf : PsWellFormed ps)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (n : Nat) → Fp),
      uniformChallenge.toOuterMeasure
          (adaptiveActionSurfaceAt pp basis inputs n ps source earlier) ≤ epsilon n) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp))).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹'
        adaptiveActionSemanticResidualEvent pp family inputs hvk hI hchar) ≤
      (family.Q + 1 : Nat) * ∑ n : Fin 5, epsilon n := by
  refine le_trans (MeasureTheory.measure_mono (Set.preimage_mono
    (adaptiveActionSemanticResidualEvent_subset_surfaces pp family inputs hvk hI hchar))) ?_
  apply uniformOfFintype_prod_fiber_bound_right
    (fun logs => {O | ∃ n : Fin 5,
      O ∈ family.adaptiveActionBadWithoutRelation pp inputs (scalarBasis B logs) n})
  intro logs
  exact family.adaptiveActionBadWithoutRelation_all_measure_le pp inputs
    (scalarBasis B logs) epsilon (hsurface (scalarBasis B logs))

theorem adaptiveActionKnowledgeResidual_prob_le
    (B : VestaG) (epsilon : Fin 5 → ENNReal)
    (hsurface : ∀
      (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
      (n : Fin 5)
      (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
      (_hwf : PsWellFormed ps)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (n : Nat) → Fp),
      uniformChallenge.toOuterMeasure
          (adaptiveActionSurfaceAt pp basis inputs n ps source earlier) ≤ epsilon n) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp))).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹'
        adaptiveActionKnowledgeResidualEvent pp family inputs hvk hI hchar) ≤
      (family.Q + 1 : Nat) * ∑ n : Fin 5, epsilon n := by
  refine le_trans (MeasureTheory.measure_mono (Set.preimage_mono
    (adaptiveActionKnowledgeResidualEvent_subset_surfaces
      pp family inputs hvk hI hchar))) ?_
  apply uniformOfFintype_prod_fiber_bound_right
    (fun logs => {O | ∃ n : Fin 5,
      O ∈ family.adaptiveActionBadWithoutRelation pp inputs (scalarBasis B logs) n})
  intro logs
  exact family.adaptiveActionBadWithoutRelation_all_measure_le pp inputs
    (scalarBasis B logs) epsilon (hsurface (scalarBasis B logs))

/-- End-to-end adaptive Action knowledge soundness.  Failure of the executable private-witness
extractor is charged to the same cached relation reduction and five statistical surfaces. -/
theorem adaptiveActionKnowledgeFailure_prob_le
    (B : VestaG) (epsilon : Fin 5 → ENNReal)
    (profile : AdaptiveActionDlogProfile pp family inputs hvk hI hchar B)
    (hsurface : ∀
      (basis : AugmentedIndex actionCircuit.n → VestaG)
      (n : Fin 5)
      (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
      (_hwf : PsWellFormed ps)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (n : Nat) → Fp),
      uniformChallenge.toOuterMeasure
          (adaptiveActionSurfaceAt pp basis inputs n ps source earlier) ≤ epsilon n) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp))).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹'
        adaptiveActionKnowledgeFailureEvent pp family inputs hvk hI hchar) ≤
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        ((actionCircuit.shape.withProofParams pp).k *
          ((family.Q + 1 : Nat) * (2 / (Fintype.card Fp : ENNReal))) +
        ((family.Q + 1 : Nat) *
          algebraicRootBudget (actionCircuit.shape.withProofParams pp)
            (actionCircuit.shape.withProofParams pp).k +
        ((profile.advantage (adaptiveActionDlogRandomOracleQueries pp family)
            (adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
            1 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * ∑ n : Fin 5, epsilon n))) := by
  refine le_trans (MeasureTheory.measure_mono
    (Set.preimage_mono
      (adaptiveActionKnowledgeFailureEvent_subset pp family inputs hvk hI hchar))) ?_
  simp only [Set.preimage_union]
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add (adaptiveActionZero_prob_le pp family B) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add (adaptiveActionIpa_prob_le pp family B) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add (adaptiveActionRoot_prob_le pp family B) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add
    (adaptiveActionRelation_prob_le_of_textbookDL pp family inputs hvk hI hchar B
      profile.hardness)
    (adaptiveActionKnowledgeResidual_prob_le pp family inputs hvk hI hchar B epsilon hsurface)

/-- Probability composition for the bare adaptive family.  Every algebraic branch is closed by
the executable combined finder and the remaining semantic term is derived from the five explicit
Action squeeze surfaces. -/
theorem adaptiveActionAcceptFalseStatement_prob_le
    (B : VestaG) (epsilon : Fin 5 → ENNReal)
    (profile : AdaptiveActionDlogProfile pp family inputs hvk hI hchar B)
    (hsurface : ∀
      (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
      (n : Fin 5)
      (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
      (_hwf : PsWellFormed ps)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (n : Nat) → Fp),
      uniformChallenge.toOuterMeasure
          (adaptiveActionSurfaceAt pp basis inputs n ps source earlier) ≤ epsilon n) :
    (PMF.uniformOfFintype
      ((AugmentedIndex actionCircuit.n → Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
      ((fun q => (scalarBasis B q.1, q.2)) ⁻¹'
        adaptiveActionAcceptFalseStatementEvent pp family inputs) ≤
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        (actionCircuit.domainExponent *
          ((family.Q + 1 : Nat) * (2 / (Fintype.card Fp : ENNReal))) +
        ((family.Q + 1 : Nat) *
          algebraicRootBudget (actionCircuit.shape.withProofParams pp)
            actionCircuit.domainExponent +
        ((profile.advantage (adaptiveActionDlogRandomOracleQueries pp family)
            (adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
            1 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * ∑ n : Fin 5, epsilon n))) := by
  refine le_trans (MeasureTheory.measure_mono
    (Set.preimage_mono
      (adaptiveActionAcceptFalseStatementEvent_subset pp family inputs hvk hI hchar))) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add (adaptiveActionZero_prob_le pp family B) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add (adaptiveActionIpa_prob_le pp family B) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add (adaptiveActionRoot_prob_le pp family B) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add
    (adaptiveActionRelation_prob_le_of_textbookDL pp family inputs hvk hI hchar B
      profile.hardness)
    (adaptiveActionSemanticResidual_prob_le pp family inputs hvk hI hchar B epsilon hsurface)

end ActionTerminal

end Zcash.Snark
