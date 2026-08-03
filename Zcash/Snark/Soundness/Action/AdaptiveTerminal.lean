import Zcash.Snark.Soundness.Action.StraightLineTerminal
import Zcash.Snark.Soundness.AGM.ExecutableDeployedRoots

/-!
# The Action terminal for arbitrary adaptive online-AGM adversaries

This bridge feeds one represented adaptive run into the Action terminal, with no phased execution
or caller-supplied trace.
-/

namespace Zcash.Snark

namespace ActionTerminal

open Halo2 CompPoly.CPolynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder)

local instance vestaInhabitedAdaptiveActionTerminal : Inhabited VestaG := ⟨0⟩

/-- Package a URS relation as the relation branch over the augmented basis. -/
private def relationResultAtBasis
    {A : Type} {k : ℕ}
    (basis : AugmentedIndex (2 ^ k) → VestaG)
    (relation : AugmentedRelationWitness (F := Fp)
      (ursOfAugmentedBasis k basis).g
      (ursOfAugmentedBasis k basis).u
      (ursOfAugmentedBasis k basis).w) :
    Option (A ⊕ AlgebraicRelationWitness (F := Fp) basis) :=
  some (Sum.inr (AugmentedRelationWitness.toBasisRelation basis relation))

/-- Package a relation without changing its URS presentation. -/
private def ursRelationResult
    {A : Type} {G : Type} [AddCommGroup G] [Module Fp G] {urs : URS G}
    (relation : NontrivialRelation (F := Fp) urs.g urs.u urs.w) :
    Option (A ⊕ NontrivialRelation (F := Fp) urs.g urs.u urs.w) :=
  some (Sum.inr relation)

/-- Continue a circuit-satisfaction-or-relation result without exposing its relation branch to a
concrete circuit expression. -/
private def continueCircuitSatOrRelation
    {A : Prop} {B : Type} {G : Type} [AddCommGroup G] [Module Fp G]
    {urs : URS G}
    (result : A ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (onSat : A → Option (B ⊕ NontrivialRelation (F := Fp) urs.g urs.u urs.w)) :
    Option (B ⊕ NontrivialRelation (F := Fp) urs.g urs.u urs.w) :=
  match result with
  | .inl hsatisfied => onSat hsatisfied
  | .inr relation => ursRelationResult relation

attribute [local irreducible] actionCircuit TopLevelCircuit.toVerifierKey
  TopLevelCircuit.instanceCommitment

variable {shape : Shape}

/-- The Action proof shape and its basis-derived URS have the same domain exponent. -/
private theorem actionUrsOfAugmentedBasis_k
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) :
    (actionCircuit.shape.withProofParams pp).k =
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis).k :=
  (ursOfAugmentedBasis_k (actionCircuit.shape.withProofParams pp).k basis).symm

/-- The adaptive adversary's one wrapped run. -/
abbrev adaptiveActionRunOutput
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :=
  (wrappedAdversary family.toFamily basis).run O

/-- The complete challenge record of the one adaptive run. -/
abbrev adaptiveActionRunRecord
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    Challenges shape.k Fp :=
  chRecord (wrappedPreIpaReads (adaptiveActionRunOutput family basis O))
    (runRounds family.toFamily basis O)

/-- The decode type attached to one adaptive Action run. -/
abbrev AdaptiveActionDecode
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp) :=
  DeployedAlgebraicDecode
    (actionCircuit.shape.withProofParams pp)
    (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
    (actionUrsOfAugmentedBasis_k pp basis)
    (actionCircuit.toVerifierKey (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (actionCircuit.instanceCommitment
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (adaptiveActionRunOutput family basis O).1.proof.1
    (adaptiveActionRunRecord family basis O)
    ((adaptiveActionRunOutput family basis O).1.aMulti
      (wrappedPreIpaReads (adaptiveActionRunOutput family basis O)))
    ((adaptiveActionRunOutput family basis O).1.multiU
      (wrappedPreIpaReads (adaptiveActionRunOutput family basis O)))
    ((adaptiveActionRunOutput family basis O).1.multiBlind
      (wrappedPreIpaReads (adaptiveActionRunOutput family basis O)))

/-- The acceptance proposition attached to one adaptive Action run. -/
abbrev AdaptiveActionAccepts
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp) :=
  DeployedAccepts
    (actionCircuit.shape.withProofParams pp)
    (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
    (actionUrsOfAugmentedBasis_k pp basis)
    (actionCircuit.toVerifierKey (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (actionCircuit.instanceCommitment
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (adaptiveActionRunOutput family basis O).1.proof.1
    (adaptiveActionRunRecord family basis O)

/-- The decoder's scalar-characteristic side condition for one adaptive Action run. -/
abbrev AdaptiveActionX4CountLt
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp) : Prop :=
  deployedX4PairCount
    (actionCircuit.toVerifierKey (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (actionCircuit.instanceCommitment
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (adaptiveActionRunOutput family basis O).1.proof.1
    (adaptiveActionRunRecord family basis O) < scalarFieldOrder

/-- Deployed acceptance of the adaptive adversary's actual proof and challenge record. -/
def adaptiveActionAccepts
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) : Prop :=
  let pnu := adaptiveActionRunOutput family basis O
  DeployedAccepts shape (ursOfAugmentedBasis shape.k basis) rfl
    (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
    (adaptiveActionRunRecord family basis O)

/-- Executable deployed-acceptance certificate for the adaptive adversary's actual run. -/
def adaptiveActionAccepts?
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    let pnu := adaptiveActionRunOutput family basis O
    Option (PLift (DeployedAccepts shape (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (adaptiveActionRunRecord family basis O))) := by
  let pnu := adaptiveActionRunOutput family basis O
  let fullCh := adaptiveActionRunRecord family basis O
  match hassemble : assemble? (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 fullCh with
  | none => exact none
  | some msm =>
      if hzero : msm.eval (ursOfAugmentedBasis shape.k basis) = 0 then
        exact some ⟨by
          unfold DeployedAccepts
          rw [hassemble]
          exact hzero⟩
      else exact none

theorem adaptiveActionAccepts?_isSome_of
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (haccepts : adaptiveActionAccepts family basis O) :
    (adaptiveActionAccepts? family basis O).isSome := by
  let pnu := adaptiveActionRunOutput family basis O
  let fullCh := adaptiveActionRunRecord family basis O
  change DeployedAccepts shape (ursOfAugmentedBasis shape.k basis) rfl
    (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1 fullCh at haccepts
  unfold DeployedAccepts at haccepts
  unfold adaptiveActionAccepts?
  dsimp only
  split
  · rename_i hassemble
    rw [hassemble] at haccepts
    exact False.elim haccepts
  · rename_i msm hassemble
    rw [hassemble] at haccepts
    simp [haccepts]

/-- Transport an adaptive run's decode to identified verifier artifacts before specializing the
circuit that supplied those artifacts. -/
def adaptiveRunDecodeAt
    {shape : Shape}
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (hvk : family.vk basis = vk)
    (hI : family.instanceCommitment basis = instanceCommitment)
    (witness : DeployedBatchWitness family.toFamily basis
      (adaptiveActionRunOutput family basis O))
    (hout : deployedRootOutcomeOfCovered family.toOnlineMemberFamily basis O =
      PSum.inl witness)
    (hroots : family.AdaptiveAllRootGood basis O)
    (hshifted : family.AdaptiveShiftedValue basis O) :
    DeployedAlgebraicDecode shape (ursOfAugmentedBasis shape.k basis) rfl
      vk instanceCommitment
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O)
      ((adaptiveActionRunOutput family basis O).1.aMulti
        (wrappedPreIpaReads (adaptiveActionRunOutput family basis O)))
      ((adaptiveActionRunOutput family basis O).1.multiU
        (wrappedPreIpaReads (adaptiveActionRunOutput family basis O)))
      ((adaptiveActionRunOutput family basis O).1.multiBlind
        (wrappedPreIpaReads (adaptiveActionRunOutput family basis O))) :=
  hI ▸ hvk ▸
    (family.adaptiveAlgebraicDecode_of_goodRoots basis O witness hout hroots hshifted).reRound
      (runRounds family.toFamily basis O)

/-- Transport an adaptive run's acceptance to identified verifier artifacts. -/
def adaptiveRunAcceptsAt
    {shape : Shape}
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (hvk : family.vk basis = vk)
    (hI : family.instanceCommitment basis = instanceCommitment)
    (haccepts : adaptiveActionAccepts family basis O) :
    DeployedAccepts shape (ursOfAugmentedBasis shape.k basis) rfl
      vk instanceCommitment
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O) :=
  hI ▸ hvk ▸ haccepts

/-- The adaptive root decoder, re-rounded and transported to the Action circuit artifacts. -/
def adaptiveActionRunDecode
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (witness : DeployedBatchWitness family.toFamily basis
      (adaptiveActionRunOutput family basis O))
    (hout : deployedRootOutcomeOfCovered family.toOnlineMemberFamily basis O =
      PSum.inl witness)
    (hroots : family.AdaptiveAllRootGood basis O)
    (hshifted : family.AdaptiveShiftedValue basis O) :
    DeployedAlgebraicDecode
      (actionCircuit.shape.withProofParams pp)
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
      (actionUrsOfAugmentedBasis_k pp basis)
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O)
      ((adaptiveActionRunOutput family basis O).1.aMulti
        (wrappedPreIpaReads (adaptiveActionRunOutput family basis O)))
      ((adaptiveActionRunOutput family basis O).1.multiU
        (wrappedPreIpaReads (adaptiveActionRunOutput family basis O)))
      ((adaptiveActionRunOutput family basis O).1.multiBlind
        (wrappedPreIpaReads (adaptiveActionRunOutput family basis O))) :=
  adaptiveRunDecodeAt (shape := actionCircuit.shape.withProofParams pp)
    family basis O
    (actionCircuit.toVerifierKey (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (actionCircuit.instanceCommitment
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (hvk basis) (hI basis) witness hout hroots hshifted

/-- Transport the run's deployed acceptance to the Action key and instance commitment. -/
theorem adaptiveActionRunAccepts
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (haccepts : adaptiveActionAccepts family basis O) :
    DeployedAccepts (actionCircuit.shape.withProofParams pp)
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
      (actionUrsOfAugmentedBasis_k pp basis)
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O) :=
  adaptiveRunAcceptsAt (shape := actionCircuit.shape.withProofParams pp)
    family basis O
    (actionCircuit.toVerifierKey (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (actionCircuit.instanceCommitment
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (hvk basis) (hI basis) haccepts

/-- On an accepted nonzero-`z` adaptive run, absence of the IPA binding attack gives the exact
shifted aggregate equality consumed by the executable deployed decoder. -/
theorem adaptiveShiftedValue_of_accept_not_attack
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (haccept : adaptiveActionAccepts family basis O)
    (hz : wrappedPreIpaReads (adaptiveActionRunOutput family basis O) 10 ≠ 0)
    (hnot : ¬fullAlgebraicBindingAttackZ basis (family.vk basis)
      (family.instanceCommitment basis) (adaptiveActionRunOutput family basis O).1
      (wrappedPreIpaReads (adaptiveActionRunOutput family basis O))
      (runRounds family.toFamily basis O)) :
    family.AdaptiveShiftedValue basis O := by
  let pnu := adaptiveActionRunOutput family basis O
  let nu := wrappedPreIpaReads pnu
  let rounds := runRounds family.toFamily basis O
  have hdeployed : DeployedAccepts shape (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (chRecord nu rounds) := by
    simpa only [adaptiveActionAccepts, adaptiveActionRunRecord, pnu, nu, rounds] using haccept
  have hacceptFull : fullAlgebraicAccept basis (family.vk basis)
      (family.instanceCommitment basis) pnu.1 nu rounds :=
    fullAlgebraicAccept_of_deployed basis (family.vk basis)
      (family.instanceCommitment basis) pnu.1 nu rounds hdeployed
  have heq : innerProduct (pnu.1.aMulti nu) (evalVector shape.k (nu 7)) =
      multiopenValue (family.vk basis) (family.instanceCommitment basis)
        pnu.1.proof.1 (chRecord nu (fun _ => 0)) +
      (nu 10)⁻¹ * (pnu.1.multiU nu + nu 9 * pnu.1.sU) -
        nu 9 * innerProduct pnu.1.s (evalVector shape.k (nu 7)) := by
    by_contra hmismatch
    exact hnot ⟨⟨hacceptFull, hmismatch⟩, hz⟩
  constructor
  · simpa only [ComputedAdaptiveOnlineAGMFSFamily.AdaptiveShiftedValue, pnu, nu,
      wrappedPreIpaRecord] using hz
  · simpa only [ComputedAdaptiveOnlineAGMFSFamily.AdaptiveShiftedValue, pnu, nu,
      wrappedPreIpaRecord, commitGen, innerProduct] using heq

/-- Explicit-shape spelling of `adaptiveShiftedValue_of_accept_not_attack`, used when a concrete
circuit supplies the shape. -/
private def adaptiveShiftedValueAt
    (shape : Shape)
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (haccept : adaptiveActionAccepts family basis O)
    (hz : wrappedPreIpaReads (adaptiveActionRunOutput family basis O) 10 ≠ 0)
    (hnot : ¬fullAlgebraicBindingAttackZ basis (family.vk basis)
      (family.instanceCommitment basis) (adaptiveActionRunOutput family basis O).1
      (wrappedPreIpaReads (adaptiveActionRunOutput family basis O))
      (runRounds family.toFamily basis O)) :
    family.AdaptiveShiftedValue basis O :=
  adaptiveShiftedValue_of_accept_not_attack family basis O haccept hz hnot

set_option maxRecDepth 10000 in
/-- Execute the Action terminal checks while retaining either the extracted private witnesses or
the explicit relation data.  The successful branch is data, not an existential `Prop`. -/
private def adaptiveActionWitnessOrUrsRelationOfDecode?
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hchar : AdaptiveActionX4CountLt pp family basis O inputs)
    (decode : AdaptiveActionDecode pp family basis O inputs)
    (haccepts : AdaptiveActionAccepts pp family basis O inputs) :
    Option (ActionBundleWitness inputs ⊕
      NontrivialRelation (F := Fp)
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis).g
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis).u
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis).w) :=
  let pnu := adaptiveActionRunOutput family basis O
  let urs := ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis
  let ch := adaptiveActionRunRecord family basis O
  let model := CanonicalMemberConstraintRelation.acceptedModel
    (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
    (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n urs) haccepts
  let polynomial := CanonicalMemberConstraintRelation.acceptedPolynomial
    (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts
  match hxgood : szBadSetAvoidance?
      ((combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
          model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
          ch.y model.chunkLen model.l0 model.lLast model.lBlind)
        - polynomial CommitmentId.vanishingH
          * (X ^ actionCircuit.n - 1)) ch.x with
  | none => none
  | some hxgoodProof =>
      let hn : actionCircuit.n ≠ 0 := actionCircuit.n_ne_zero
      match hgoodY : foldSplitAvoidance? model.constraints
          actionCircuit.n hn ch.y with
      | none => none
      | some hgoodYProof =>
          match hpermutation : resolverPermutationChallengeExclusions?
              pp.numProofs (actionCircuit.toVerifierKey urs) ch polynomial actionActiveRows with
          | none => none
          | some hpermutationProof =>
              match hlookup : TopLevelLookup.topLevelLookupChallengeExclusions?
                  actionCircuit pp urs ch polynomial with
              | none => none
              | some hlookupProof =>
                  continueCircuitSatOrRelation
                    (topLevelCircuitSat_or_relation_of_decodedMemberPolynomial_eq
                      actionCircuit pp urs (actionUrsOfAugmentedBasis_k pp basis)
                      inputs pnu.1.proof.1 ch
                      (fun i hi => decode.toMemberDecode hchar i hi) haccepts
                      (polynomial .vanishingH) rfl
                      (fun slot point hpoint =>
                        PSum.inl (decode.memberBinding hchar slot point hpoint))
                      ActionPermutationDomain.domainExponent_lt
                      (ActionPermutationDomain.routingCoherent_of_derived urs)
                      (by exact hxgoodProof.down)) fun hsatisfied =>
                      match action_bundleWitness_or_relation_of_decode_circuitSat pp urs
                          (actionUrsOfAugmentedBasis_k pp basis)
                          inputs pnu.1.proof.1 ch
                          (pnu.1.multiU (wrappedPreIpaReads pnu))
                          (pnu.1.multiBlind (wrappedPreIpaReads pnu))
                          (pnu.1.aMulti (wrappedPreIpaReads pnu)) decode hchar haccepts
                          (polynomial .vanishingH) hsatisfied hgoodYProof.down
                          hpermutationProof.down
                          hlookupProof.down with
                      | PSum.inl witness => some (Sum.inl witness)
                      | PSum.inr relation =>
                          ursRelationResult relation

/-- Execute the adaptive terminal and present any URS relation over the original augmented basis. -/
def adaptiveActionWitnessOrRelationOfDecode?
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hchar : AdaptiveActionX4CountLt pp family basis O inputs)
    (decode : AdaptiveActionDecode pp family basis O inputs)
    (haccepts : AdaptiveActionAccepts pp family basis O inputs) :
    Option (ActionBundleWitness inputs ⊕
      AlgebraicRelationWitness (F := Fp) basis) :=
  match adaptiveActionWitnessOrUrsRelationOfDecode?
      pp family basis O inputs hchar decode haccepts with
  | some (Sum.inl witness) => some (Sum.inl witness)
  | some (Sum.inr relation) => relationResultAtBasis basis relation
  | none => none

/-- Relation-only projection retained for the ordinary-soundness reduction. -/
def adaptiveActionRelationOfDecode?
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hchar : AdaptiveActionX4CountLt pp family basis O inputs)
    (decode : AdaptiveActionDecode pp family basis O inputs)
    (haccepts : AdaptiveActionAccepts pp family basis O inputs) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  match adaptiveActionWitnessOrRelationOfDecode?
      pp family basis O inputs hchar decode haccepts with
  | some (Sum.inr relation) => some relation
  | _ => none

/-- A complete data-bearing terminal outcome projects to relation data whenever the extracted
witness branch would contradict the claimed false statement. -/
theorem adaptiveActionRelationOfDecode?_isSome_of_witnessOrRelation
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hchar) (decode) (haccepts)
    (hcomplete : (adaptiveActionWitnessOrRelationOfDecode?
      pp family basis O inputs hchar decode haccepts).isSome)
    (hfalse : ¬BundleStatement inputs) :
    (adaptiveActionRelationOfDecode?
      pp family basis O inputs hchar decode haccepts).isSome := by
  obtain ⟨outcome, houtcome⟩ := Option.isSome_iff_exists.mp hcomplete
  cases outcome with
  | inl witness => exact False.elim (hfalse witness.statement)
  | inr relation =>
      unfold adaptiveActionRelationOfDecode?
      rw [houtcome]
      rfl

set_option maxRecDepth 10000 in
/-- If every Action semantic exclusion succeeds and the literal bundle statement is false, the
executable decoded terminal returns explicit relation data. -/
theorem adaptiveActionWitnessOrRelationOfDecode?_isSome_of
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hchar : deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O) < scalarFieldOrder)
    (decode : DeployedAlgebraicDecode
      (actionCircuit.shape.withProofParams pp)
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) rfl
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O)
      ((adaptiveActionRunOutput family basis O).1.aMulti
        (wrappedPreIpaReads (adaptiveActionRunOutput family basis O)))
      ((adaptiveActionRunOutput family basis O).1.multiU
        (wrappedPreIpaReads (adaptiveActionRunOutput family basis O)))
      ((adaptiveActionRunOutput family basis O).1.multiBlind
        (wrappedPreIpaReads (adaptiveActionRunOutput family basis O))))
    (haccepts : DeployedAccepts
      (actionCircuit.shape.withProofParams pp)
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) rfl
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O))
    (hxgood :
      let model := CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
          (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
            (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)) haccepts
      let polynomial := CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts
      (adaptiveActionRunRecord family basis O).x ∉ szBadSet
        (combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
          model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
          (adaptiveActionRunRecord family basis O).y model.chunkLen model.l0 model.lLast
          model.lBlind - polynomial .vanishingH *
            (X ^ actionCircuit.n - 1)))
    (hgoodY :
      let model := CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
          (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
            (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)) haccepts
      ∀ j, (adaptiveActionRunRecord family basis O).y ∉
        szBadSet (foldSplitWitness model.constraints
          actionCircuit.n j))
    (hpermutation : ResolverPermutationChallengeExclusions
      pp.numProofs (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (adaptiveActionRunRecord family basis O)
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)
      actionActiveRows)
    (hlookup : TopLevelLookup.ChallengeExclusions actionCircuit pp
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
      (adaptiveActionRunRecord family basis O)
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)) :
    (adaptiveActionWitnessOrRelationOfDecode?
      pp family basis O inputs hchar decode haccepts).isSome := by
  let model := CanonicalMemberConstraintRelation.acceptedModel
    (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
    (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)) haccepts
  dsimp only at hxgood hgoodY
  have hxSome := (szBadSetAvoidance?_isSome_iff _ _).2 hxgood
  have hn : actionCircuit.n ≠ 0 := actionCircuit.n_ne_zero
  have hySome := foldSplitAvoidance?_isSome_of model.constraints _ hn _ hgoodY
  have hpSome := resolverPermutationChallengeExclusions?_isSome_of
    pp.numProofs _ _ _ _ hpermutation
  have hlSome := TopLevelLookup.topLevelLookupChallengeExclusions?_isSome_of
    actionCircuit pp (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
      _ _ hlookup
  obtain ⟨hxProof, hxEq⟩ := Option.isSome_iff_exists.mp hxSome
  obtain ⟨hyProof, hyEq⟩ := Option.isSome_iff_exists.mp hySome
  obtain ⟨hpProof, hpEq⟩ := Option.isSome_iff_exists.mp hpSome
  obtain ⟨hlProof, hlEq⟩ := Option.isSome_iff_exists.mp hlSome
  have hraw : (adaptiveActionWitnessOrUrsRelationOfDecode?
      pp family basis O inputs hchar decode haccepts).isSome := by
    unfold adaptiveActionWitnessOrUrsRelationOfDecode?
    simp only
    rw [hxEq, hyEq, hpEq, hlEq]
    dsimp only
    unfold continueCircuitSatOrRelation
    split
    · dsimp only
      split <;> rfl
    · rfl
  obtain ⟨outcome, houtcome⟩ := Option.isSome_iff_exists.mp hraw
  unfold adaptiveActionWitnessOrRelationOfDecode?
  rw [houtcome]
  cases outcome <;> simp [relationResultAtBasis]

set_option maxRecDepth 10000 in
theorem adaptiveActionRelationOfDecode?_isSome_of
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hchar : deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O) < scalarFieldOrder)
    (decode : DeployedAlgebraicDecode
      (actionCircuit.shape.withProofParams pp)
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) rfl
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O)
      ((adaptiveActionRunOutput family basis O).1.aMulti
        (wrappedPreIpaReads (adaptiveActionRunOutput family basis O)))
      ((adaptiveActionRunOutput family basis O).1.multiU
        (wrappedPreIpaReads (adaptiveActionRunOutput family basis O)))
      ((adaptiveActionRunOutput family basis O).1.multiBlind
        (wrappedPreIpaReads (adaptiveActionRunOutput family basis O))))
    (haccepts : DeployedAccepts
      (actionCircuit.shape.withProofParams pp)
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) rfl
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O))
    (hxgood :
      let model := CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
          (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
            (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)) haccepts
      let polynomial := CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts
      (adaptiveActionRunRecord family basis O).x ∉ szBadSet
        (combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
          model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
          (adaptiveActionRunRecord family basis O).y model.chunkLen model.l0 model.lLast
          model.lBlind - polynomial .vanishingH *
            (X ^ actionCircuit.n - 1)))
    (hgoodY :
      let model := CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
          (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
            (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)) haccepts
      ∀ j, (adaptiveActionRunRecord family basis O).y ∉
        szBadSet (foldSplitWitness model.constraints
          actionCircuit.n j))
    (hpermutation : ResolverPermutationChallengeExclusions
      pp.numProofs (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (adaptiveActionRunRecord family basis O)
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)
      actionActiveRows)
    (hlookup : TopLevelLookup.ChallengeExclusions actionCircuit pp
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
      (adaptiveActionRunRecord family basis O)
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts))
    (hfalse : ¬BundleStatement inputs) :
    (adaptiveActionRelationOfDecode? pp family basis O inputs hchar decode haccepts).isSome := by
  refine adaptiveActionRelationOfDecode?_isSome_of_witnessOrRelation
    pp family basis O inputs hchar decode haccepts
      (adaptiveActionWitnessOrRelationOfDecode?_isSome_of pp family basis O inputs
        hchar decode haccepts hxgood hgoodY hpermutation hlookup) hfalse

set_option maxRecDepth 10000 in
/-- The executable adaptive Action-terminal finder.  Root checks and the decode are computed from
the adversary's one actual run; the only relation result is explicit coefficient data. -/
def adaptiveActionTerminalRelationFinder
    (pp : ProofParams)
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
      (adaptiveActionRunRecord family basis O) < scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp) →
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
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
          match deployedRootOutcomeOfCovered family.toOnlineMemberFamily basis O with
          | PSum.inr relation =>
              some (ComputedStraightLineIpaFSFamily.straightLineCanonicalRelation relation)
          | PSum.inl witness =>
              match family.adaptiveDeployedGoodRoots? basis O witness with
              | none => none
              | some hroots =>
                  let hshifted : family.AdaptiveShiftedValue basis O :=
                    adaptiveShiftedValueAt (actionCircuit.shape.withProofParams pp)
                      family basis O haccepts hz hattack
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
                  adaptiveActionRelationOfDecode? pp family basis O inputs
                    (hchar basis O) decode hacceptsAction
      else none
    | none => none

/-- The existing Action terminal reached from one arbitrary adaptive online-AGM run.  The result
is the literal bundle statement or explicit augmented-basis relation data. -/
def action_bundleStatement_or_relation_of_adaptiveDecode
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (witness : DeployedBatchWitness family.toFamily basis
      (adaptiveActionRunOutput family basis O))
    (hout : deployedRootOutcomeOfCovered family.toOnlineMemberFamily basis O =
      PSum.inl witness)
    (hroots : family.AdaptiveAllRootGood basis O)
    (hshifted : family.AdaptiveShiftedValue basis O)
    (haccepts : adaptiveActionAccepts family basis O)
    (hchar : deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O) < scalarFieldOrder) :=
  action_bundleStatement_or_relation_of_decode pp
    (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) rfl inputs
    (adaptiveActionRunOutput family basis O).1.proof.1
    (adaptiveActionRunRecord family basis O)
    ((adaptiveActionRunOutput family basis O).1.multiU
      (wrappedPreIpaReads (adaptiveActionRunOutput family basis O)))
    ((adaptiveActionRunOutput family basis O).1.multiBlind
      (wrappedPreIpaReads (adaptiveActionRunOutput family basis O)))
    ((adaptiveActionRunOutput family basis O).1.aMulti
      (wrappedPreIpaReads (adaptiveActionRunOutput family basis O)))
    (adaptiveActionRunDecode pp family basis O inputs hvk hI witness hout hroots hshifted)
    hchar (adaptiveActionRunAccepts pp family basis O inputs hvk hI haccepts)

end ActionTerminal

end Zcash.Snark
