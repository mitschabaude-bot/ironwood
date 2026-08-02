import Zcash.Snark.Soundness.AGM.DecodeToOpened
import Zcash.Snark.Soundness.Composition.StraightLineDecodeSupply
import Zcash.Snark.Soundness.TopLevelTerminal

/-!
# Straight-line terminal for any top-level circuit

This module transports the verifier artifacts produced by a straight-line AGM
run to the derived key and public-input commitment of an arbitrary
`TopLevelCircuit`. Circuit-specific gate, fixed, copy, and lookup work remains in
the constructor of `TopLevelCircuitCorrectness`.
-/

namespace Zcash.Snark

universe u v

open Halo2 CompPoly.CPolynomial Keygen
open Zcash.Arithmetic (scalarFieldOrder)

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

local instance topLevelStraightLineInhabitedVesta : Inhabited VestaG := ⟨0⟩

/-- Transport a deployed decode when only the verifying key and instance commitment change. -/
def DeployedAlgebraicDecode.transportArtifacts
    {shape : Shape} {urs : URS G} {hk : shape.k = urs.k}
    {vk vk' : VerifyingKey shape Fp G}
    {instanceCommitment instanceCommitment' : Fin shape.numProofs → ℕ → G}
    {ps : ProofString shape Fp G} {ch : Challenges shape.k Fp}
    {a : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (decode : DeployedAlgebraicDecode shape urs hk vk instanceCommitment ps ch a pU pW)
    (hvk : vk = vk') (hI : instanceCommitment = instanceCommitment') :
    DeployedAlgebraicDecode shape urs hk vk' instanceCommitment' ps ch a pU pW := by
  subst vk'
  subst instanceCommitment'
  exact decode

/-- Transport deployed acceptance when only the verifying key and instance commitment change. -/
theorem deployedAccepts_transportArtifacts
    {shape : Shape} {urs : URS G} {hk : shape.k = urs.k}
    {vk vk' : VerifyingKey shape Fp G}
    {instanceCommitment instanceCommitment' : Fin shape.numProofs → ℕ → G}
    {ps : ProofString shape Fp G} {ch : Challenges shape.k Fp}
    (haccepts : DeployedAccepts shape urs hk vk instanceCommitment ps ch)
    (hvk : vk = vk') (hI : instanceCommitment = instanceCommitment') :
    DeployedAccepts shape urs hk vk' instanceCommitment' ps ch := by
  subst vk'
  subst instanceCommitment'
  exact haccepts

/-- Present the successful straight-line decode at identified verifier artifacts. -/
def ComputedStraightLineDeployedFSFamily.StraightLineConstraintSuccess.decodeAt
    {shape : Shape}
    {family : ComputedStraightLineDeployedFSFamily shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp}
    (success : ComputedStraightLineDeployedFSFamily.StraightLineConstraintSuccess family basis O)
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (hvk : family.vk basis = vk)
    (hI : family.instanceCommitment basis = instanceCommitment) :
    let pnu := (wrappedAdversary family.toFamily basis).run O
    DeployedAlgebraicDecode shape (ursOfAugmentedBasis shape.k basis)
      (ursOfAugmentedBasis_k shape.k basis).symm
      vk instanceCommitment pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O))
      (pnu.1.aMulti (wrappedPreIpaReads pnu))
      (pnu.1.multiU (wrappedPreIpaReads pnu))
      (pnu.1.multiBlind (wrappedPreIpaReads pnu)) :=
  (success.witness.decode.reRound
    (runRounds family.toFamily basis O)).transportArtifacts hvk hI

/-- Present the successful straight-line acceptance at identified verifier artifacts. -/
theorem ComputedStraightLineDeployedFSFamily.StraightLineConstraintSuccess.acceptsAt
    {shape : Shape}
    {family : ComputedStraightLineDeployedFSFamily shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp}
    (success : ComputedStraightLineDeployedFSFamily.StraightLineConstraintSuccess family basis O)
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (hvk : family.vk basis = vk)
    (hI : family.instanceCommitment basis = instanceCommitment) :
    let pnu := (wrappedAdversary family.toFamily basis).run O
    DeployedAccepts shape (ursOfAugmentedBasis shape.k basis)
      (ursOfAugmentedBasis_k shape.k basis).symm
      vk instanceCommitment pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O)) :=
  deployedAccepts_transportArtifacts success.accepts hvk hI

/-- The decode and acceptance retained by one successful run, presented at named artifacts. -/
structure StraightLineAcceptedView
    {shape : Shape}
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) where
  decode : let pnu := (wrappedAdversary family.toFamily basis).run O
    DeployedAlgebraicDecode shape (ursOfAugmentedBasis shape.k basis)
      (ursOfAugmentedBasis_k shape.k basis).symm
      vk instanceCommitment pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O))
      (pnu.1.aMulti (wrappedPreIpaReads pnu))
      (pnu.1.multiU (wrappedPreIpaReads pnu))
      (pnu.1.multiBlind (wrappedPreIpaReads pnu))
  accepts : let pnu := (wrappedAdversary family.toFamily basis).run O
    DeployedAccepts shape (ursOfAugmentedBasis shape.k basis)
      (ursOfAugmentedBasis_k shape.k basis).symm
      vk instanceCommitment pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O))

@[ext] theorem StraightLineAcceptedView.ext
    {shape : Shape}
    {family : ComputedStraightLineDeployedFSFamily shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → ℕ → VestaG}
    {left right : StraightLineAcceptedView family basis O vk instanceCommitment}
    (hdecode : left.decode = right.decode) : left = right := by
  cases left
  cases right
  simpa only [StraightLineAcceptedView.mk.injEq] using hdecode

/-- Package a successful run at identified verifier artifacts. -/
def ComputedStraightLineDeployedFSFamily.StraightLineConstraintSuccess.acceptedViewAt
    {shape : Shape}
    {family : ComputedStraightLineDeployedFSFamily shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp}
    (success : ComputedStraightLineDeployedFSFamily.StraightLineConstraintSuccess family basis O)
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (hvk : family.vk basis = vk)
    (hI : family.instanceCommitment basis = instanceCommitment) :
    StraightLineAcceptedView family basis O vk instanceCommitment where
  decode := success.decodeAt vk instanceCommitment hvk hI
  accepts := success.acceptsAt vk instanceCommitment hvk hI

/-- The member decode selected by a successful straight-line view. -/
def StraightLineAcceptedView.memberDecode
    {shape : Shape}
    {family : ComputedStraightLineDeployedFSFamily shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → ℕ → VestaG}
    (view : StraightLineAcceptedView family basis O vk instanceCommitment)
    (hchar : let pnu := (wrappedAdversary family.toFamily basis).run O
      deployedX4PairCount vk instanceCommitment pnu.1.proof.1
        (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O)) <
        scalarFieldOrder)
    (i : ℕ)
    (hi : let pnu := (wrappedAdversary family.toFamily basis).run O
      i < deployedX4PairCount vk instanceCommitment pnu.1.proof.1
        (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O))) :=
  view.decode.toMemberDecode hchar i hi

/-- A successful view's decoded member is bound to every verifier claim point. -/
def StraightLineAcceptedView.memberBinding
    {shape : Shape}
    {family : ComputedStraightLineDeployedFSFamily shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → ℕ → VestaG}
    (view : StraightLineAcceptedView family basis O vk instanceCommitment)
    (hchar : deployedX4PairCount vk instanceCommitment
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder)
    (slot : DeployedMemberSlot (instanceCommitment := instanceCommitment) vk
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O))
    (point : Fp)
    (hpoint : point ∈ deployedSetPts (instanceCommitment := instanceCommitment) vk
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) slot.setIndex) :=
  view.decode.memberBinding hchar slot point hpoint

/-- The canonical constraint model exposed by a successful straight-line view. -/
def StraightLineAcceptedView.model
    {shape : Shape}
    {family : ComputedStraightLineDeployedFSFamily shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → ℕ → VestaG}
    (view : StraightLineAcceptedView family basis O vk instanceCommitment)
    (hchar : let pnu := (wrappedAdversary family.toFamily basis).run O
      deployedX4PairCount vk instanceCommitment pnu.1.proof.1
        (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O)) <
        scalarFieldOrder)
    (hblinding : vk.blindingFactors < vk.n) :
    ConstraintPolyModel shape.numProofs :=
  CanonicalMemberConstraintRelation.acceptedModel
    (memberDecode := view.memberDecode hchar)
    (hblinding := hblinding) view.accepts

/-- The canonical member polynomial exposed by a successful straight-line view. -/
def StraightLineAcceptedView.polynomial
    {shape : Shape}
    {family : ComputedStraightLineDeployedFSFamily shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → ℕ → VestaG}
    (view : StraightLineAcceptedView family basis O vk instanceCommitment)
    (hchar : let pnu := (wrappedAdversary family.toFamily basis).run O
      deployedX4PairCount vk instanceCommitment pnu.1.proof.1
        (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O)) <
        scalarFieldOrder) : CommitmentId → CPoly :=
  CanonicalMemberConstraintRelation.acceptedPolynomial
    (memberDecode := view.memberDecode hchar)
    view.accepts

/-- Apply the canonical quotient terminal directly to a successful straight-line view. -/
def StraightLineAcceptedView.circuitSatOrRelation
    {shape : Shape}
    {family : ComputedStraightLineDeployedFSFamily shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → ℕ → VestaG}
    (view : StraightLineAcceptedView family basis O vk instanceCommitment)
    (hchar : deployedX4PairCount vk instanceCommitment
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder)
    (hblinding : vk.blindingFactors < vk.n)
    (hfixedLayout : vk.fixedQueryLayout.length = shape.numFixedQueries)
    (hadviceLayout : vk.adviceQueryLayout.length = shape.numAdviceQueries)
    (hinstanceLayout : vk.instanceQueryLayout.length = shape.numInstanceQueries)
    (hbind : ∀
      (slot : DeployedMemberSlot
        (instanceCommitment := instanceCommitment) vk
        (straightLineRunOutput family basis O).1.proof.1
        (straightLineRunRecord family basis O))
      (point : Fp),
      point ∈ deployedSetPts (instanceCommitment := instanceCommitment) vk
          (straightLineRunOutput family basis O).1.proof.1
          (straightLineRunRecord family basis O) slot.setIndex →
      (decodedMemberPolynomial
        (instanceCommitment := instanceCommitment)
        (ursOfAugmentedBasis shape.k basis)
        (ursOfAugmentedBasis_k shape.k basis).symm vk
        (straightLineRunOutput family basis O).1.proof.1
        (straightLineRunRecord family basis O)
        (view.memberDecode hchar) slot).eval point =
          deployedMemberClaim (instanceCommitment := instanceCommitment) vk
            (straightLineRunOutput family basis O).1.proof.1
            (straightLineRunRecord family basis O) slot point ⊕'
        NontrivialRelation (F := Fp)
          (ursOfAugmentedBasis shape.k basis).g
          (ursOfAugmentedBasis shape.k basis).u
          (ursOfAugmentedBasis shape.k basis).w)
    (hpermutationRouting : PermutationChunkRoutingCoherent vk)
    (hrows : Function.Injective (fun row : Fin vk.n => vk.omega ^ (row : ℕ)))
    (hroot : vk.omega ^ vk.n = 1)
    (hnFp : (vk.n : Fp) ≠ 0)
    (hxgood :
      (straightLineRunRecord family basis O).x ∉ szBadSet
        (combineConstraints
          (view.model hchar hblinding).fixedCols
          (view.model hchar hblinding).adviceCols
          (view.model hchar hblinding).instanceCols
          (view.model hchar hblinding).gates
          (view.model hchar hblinding).sets
          (view.model hchar hblinding).chunks
          (view.model hchar hblinding).lookups
          (view.model hchar hblinding).beta
          (view.model hchar hblinding).gamma
          (view.model hchar hblinding).delta
          (view.model hchar hblinding).theta
          (straightLineRunRecord family basis O).y
          (view.model hchar hblinding).chunkLen
          (view.model hchar hblinding).l0
          (view.model hchar hblinding).lLast
          (view.model hchar hblinding).lBlind -
        view.polynomial hchar .vanishingH * (X ^ vk.n - 1))) :
    (view.model hchar hblinding).CircuitSat
        (straightLineRunRecord family basis O).y
        (view.polynomial hchar .vanishingH) vk.n
        ((straightLineRunOutput family basis O).1.aMulti
          (wrappedPreIpaReads (straightLineRunOutput family basis O))) ⊕'
      NontrivialRelation (F := Fp)
        (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u
        (ursOfAugmentedBasis shape.k basis).w :=
  acceptedModel_circuitSat_or_relation_of_decodedMemberPolynomial_eq
    (ursOfAugmentedBasis shape.k basis)
    (ursOfAugmentedBasis_k shape.k basis).symm vk instanceCommitment
    (straightLineRunOutput family basis O).1.proof.1
    (straightLineRunRecord family basis O)
    (view.memberDecode hchar) view.accepts hblinding
    (view.polynomial hchar .vanishingH) rfl
    hfixedLayout hadviceLayout hinstanceLayout hbind hpermutationRouting
    hrows hroot hnFp hxgood

/-- Retain top-level witnesses directly from the canonical model of a successful run view. -/
def StraightLineAcceptedView.topLevelWitnessesOrRelationOfCircuitSat
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams)
    {family : ComputedStraightLineDeployedFSFamily (top.shape.withProofParams pp)}
    {basis : AugmentedIndex (2 ^ (top.shape.withProofParams pp).k) → VestaG}
    {O : BTranscript Fp VestaG
      (preIpaLen (top.shape.withProofParams pp) family.init.length 10 +
        3 * (top.shape.withProofParams pp).k) → Fp}
    (inputs : Fin pp.numProofs → PublicInput Fp)
    (view : StraightLineAcceptedView family basis O
      (top.toVerifierKey
        (ursOfAugmentedBasis (top.shape.withProofParams pp).k basis))
      (top.instanceCommitment
        (ursOfAugmentedBasis (top.shape.withProofParams pp).k basis) inputs))
    (hchar : deployedX4PairCount
      (top.toVerifierKey
        (ursOfAugmentedBasis (top.shape.withProofParams pp).k basis))
      (top.instanceCommitment
        (ursOfAugmentedBasis (top.shape.withProofParams pp).k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder)
    (hsatisfied :
      (view.model hchar
        (top.toVerifierKey_blindingFactors_lt_n
          (ursOfAugmentedBasis (top.shape.withProofParams pp).k basis))).CircuitSat
        (straightLineRunRecord family basis O).y
        (view.polynomial hchar .vanishingH) top.n
        ((straightLineRunOutput family basis O).1.aMulti
          (wrappedPreIpaReads (straightLineRunOutput family basis O))))
    (hgoodY : ∀ j,
      (straightLineRunRecord family basis O).y ∉ szBadSet
        (foldSplitWitness
          (view.model hchar
            (top.toVerifierKey_blindingFactors_lt_n
              (ursOfAugmentedBasis (top.shape.withProofParams pp).k basis))).constraints
          top.n j))
    {cell : Type} [DecidableEq cell] [Fintype cell]
    (correctness : TopLevelCircuitCorrectness top pp
      (ursOfAugmentedBasis (top.shape.withProofParams pp).k basis)
      (straightLineRunRecord family basis O)
      (view.polynomial hchar) cell
      (NontrivialRelation (F := Fp)
        (ursOfAugmentedBasis (top.shape.withProofParams pp).k basis).g
        (ursOfAugmentedBasis (top.shape.withProofParams pp).k basis).u
        (ursOfAugmentedBasis (top.shape.withProofParams pp).k basis).w)) :
    TopLevelExternalBundleWitness top inputs ⊕'
      NontrivialRelation (F := Fp)
        (ursOfAugmentedBasis (top.shape.withProofParams pp).k basis).g
        (ursOfAugmentedBasis (top.shape.withProofParams pp).k basis).u
        (ursOfAugmentedBasis (top.shape.withProofParams pp).k basis).w :=
  topLevelWitnesses_or_relation_of_circuitSat top pp
    (ursOfAugmentedBasis (top.shape.withProofParams pp).k basis)
    (ursOfAugmentedBasis_k (top.shape.withProofParams pp).k basis).symm
    inputs (straightLineRunOutput family basis O).1.proof.1
    (straightLineRunRecord family basis O)
    ((straightLineRunOutput family basis O).1.multiU
      (wrappedPreIpaReads (straightLineRunOutput family basis O)))
    ((straightLineRunOutput family basis O).1.multiBlind
      (wrappedPreIpaReads (straightLineRunOutput family basis O)))
    ((straightLineRunOutput family basis O).1.aMulti
      (wrappedPreIpaReads (straightLineRunOutput family basis O)))
    (view.decode.toOpenedBatch hchar) (view.memberDecode hchar) view.accepts
    (view.polynomial hchar .vanishingH) hsatisfied hgoodY correctness

/-- Apply the quotient terminal and retain the witnesses of an arbitrary top-level circuit. -/
def StraightLineAcceptedView.topLevelWitnessesOrRelation
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams)
    {family : ComputedStraightLineDeployedFSFamily (top.shape.withProofParams pp)}
    {basis : AugmentedIndex (2 ^ (top.shape.withProofParams pp).k) → VestaG}
    {O : BTranscript Fp VestaG
      (preIpaLen (top.shape.withProofParams pp) family.init.length 10 +
        3 * (top.shape.withProofParams pp).k) → Fp}
    (inputs : Fin pp.numProofs → PublicInput Fp)
    (view : StraightLineAcceptedView family basis O
      (top.toVerifierKey
        (ursOfAugmentedBasis (top.shape.withProofParams pp).k basis))
      (top.instanceCommitment
        (ursOfAugmentedBasis (top.shape.withProofParams pp).k basis) inputs))
    (hchar : deployedX4PairCount
      (top.toVerifierKey
        (ursOfAugmentedBasis (top.shape.withProofParams pp).k basis))
      (top.instanceCommitment
        (ursOfAugmentedBasis (top.shape.withProofParams pp).k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder)
    (domainExponent_lt : top.domainExponent < 33)
    (hxgood :
      let urs := ursOfAugmentedBasis (top.shape.withProofParams pp).k basis
      let model := view.model hchar (top.toVerifierKey_blindingFactors_lt_n urs)
      (straightLineRunRecord family basis O).x ∉ szBadSet
        (combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
          model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
          (straightLineRunRecord family basis O).y model.chunkLen model.l0 model.lLast
          model.lBlind - view.polynomial hchar .vanishingH * (X ^ top.n - 1)))
    (hgoodY :
      let urs := ursOfAugmentedBasis (top.shape.withProofParams pp).k basis
      let model := view.model hchar (top.toVerifierKey_blindingFactors_lt_n urs)
      ∀ j, (straightLineRunRecord family basis O).y ∉
        szBadSet (foldSplitWitness model.constraints top.n j))
    {cell : Type} [DecidableEq cell] [Fintype cell]
    (correctness :
      let urs := ursOfAugmentedBasis (top.shape.withProofParams pp).k basis
      let model := view.model hchar (top.toVerifierKey_blindingFactors_lt_n urs)
      model.CircuitSat (straightLineRunRecord family basis O).y
          (view.polynomial hchar .vanishingH) top.n
          ((straightLineRunOutput family basis O).1.aMulti
            (wrappedPreIpaReads (straightLineRunOutput family basis O))) →
        TopLevelCircuitCorrectness top pp urs
          (straightLineRunRecord family basis O) (view.polynomial hchar) cell
          (NontrivialRelation (F := Fp) urs.g urs.u urs.w)) :
    TopLevelExternalBundleWitness top inputs ⊕'
      NontrivialRelation (F := Fp)
        (ursOfAugmentedBasis (top.shape.withProofParams pp).k basis).g
        (ursOfAugmentedBasis (top.shape.withProofParams pp).k basis).u
        (ursOfAugmentedBasis (top.shape.withProofParams pp).k basis).w := by
  let urs := ursOfAugmentedBasis (top.shape.withProofParams pp).k basis
  have hfixedLayout := ((top.toVerifierKey_fixedQueryCount urs).trans
    top.shape_numFixedQueries.symm).trans
    (CircuitShape.withProofParams_numFixedQueries top.shape pp).symm
  have hadviceLayout := ((top.toVerifierKey_adviceQueryCount urs).trans
    top.shape_numAdviceQueries.symm).trans
    (CircuitShape.withProofParams_numAdviceQueries top.shape pp).symm
  have hinstanceLayout := ((top.toVerifierKey_instanceQueryCount urs).trans
    top.shape_numInstanceQueries.symm).trans
    (CircuitShape.withProofParams_numInstanceQueries top.shape pp).symm
  have hnFp : ((top.toVerifierKey urs).n : Fp) ≠ 0 := by
    rw [top.toVerifierKey_n]
    exact TopLevelAssignment.domainSizeCastNeZero domainExponent_lt
  match view.circuitSatOrRelation hchar
      (top.toVerifierKey_blindingFactors_lt_n urs)
      hfixedLayout hadviceLayout hinstanceLayout
      (fun slot point hpoint => PSum.inl (view.memberBinding hchar slot point hpoint))
      (top.permutationChunkRoutingCoherent urs)
      (TopLevelAssignment.toVerifierKey_domainRowsInjective urs domainExponent_lt)
      (TopLevelAssignment.toVerifierKey_domainRoot urs domainExponent_lt)
      hnFp (by simpa only [top.toVerifierKey_n] using hxgood) with
  | PSum.inr relation => exact PSum.inr relation
  | PSum.inl hsatisfied =>
      have hsatisfiedTop := by
        simpa only [top.toVerifierKey_n] using hsatisfied
      exact StraightLineAcceptedView.topLevelWitnessesOrRelationOfCircuitSat
        top pp inputs view hchar hsatisfiedTop hgoodY (correctness hsatisfiedTop)

/-- Forget the augmented generators in a straight-line relation witness. -/
def straightLineRelationWitness
    (k : ℕ)
    {basis : AugmentedIndex (2 ^ k) → VestaG}
    (relation : AugmentedRelationWitness (F := Fp)
      (ursOfAugmentedBasis k basis).g
      (ursOfAugmentedBasis k basis).u
      (ursOfAugmentedBasis k basis).w) :
    AlgebraicRelationWitness (F := Fp) basis := by
  simpa only [augmentedBasis_ursOfAugmentedBasis] using
    relation.toAlgebraicRelationWitness

/-- Check every potentially nonzero fold-split witness by direct evaluation. -/
def foldSplitAvoidance?
    (cs : List CPoly) (n : Nat) (hn : n ≠ 0) (y : Fp) :
    Option (PLift (∀ j, y ∉ szBadSet (foldSplitWitness cs n j))) :=
  match finForallOption (fun j : Fin n =>
      szBadSetAvoidance? (foldSplitWitness cs n j.1) y) with
  | none => none
  | some hgood => some ⟨fun j =>
      if hj : j < n then (hgood ⟨j, hj⟩).down
      else not_mem_szBadSet.mpr fun hne =>
        False.elim (hne (foldSplitWitness_zero_of_le hn (Nat.le_of_not_gt hj)))⟩

theorem foldSplitAvoidance?_isSome_of
    (cs : List CPoly) (n : Nat) (hn : n ≠ 0) (y : Fp)
    (hgood : ∀ j, y ∉ szBadSet (foldSplitWitness cs n j)) :
    (foldSplitAvoidance? cs n hn y).isSome := by
  have hfinite : ∀ j : Fin n,
      (szBadSetAvoidance? (foldSplitWitness cs n j.1) y).isSome :=
    fun j => (szBadSetAvoidance?_isSome_iff _ _).2 (hgood j.1)
  obtain ⟨found, hfound⟩ := Option.isSome_iff_exists.mp
    (finForallOption_isSome_of _ hfinite)
  simp [foldSplitAvoidance?, hfound]

/-- Present a deployed algebraic decode directly to any top-level circuit. -/
def topLevelStatements_or_relation_of_decode
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (hk : (top.shape.withProofParams pp).k = urs.k)
    (inputs : Fin pp.numProofs → PublicInput Fp)
    (ps : ProofString (top.shape.withProofParams pp) Fp G)
    (ch : Challenges (top.shape.withProofParams pp).k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (decode : DeployedAlgebraicDecode (top.shape.withProofParams pp) urs hk
      (top.toVerifierKey urs)
      (top.instanceCommitment urs inputs) ps ch a pU pW)
    (hchar : deployedX4PairCount
      (shape := top.shape.withProofParams pp)
      (top.toVerifierKey urs)
      (top.instanceCommitment urs inputs) ps ch < scalarFieldOrder)
    (haccepts :
      DeployedAccepts (top.shape.withProofParams pp) urs hk
        (top.toVerifierKey urs)
        (top.instanceCommitment urs inputs) ps ch)
    (domainExponent_lt : top.domainExponent < 33)
    (hxgood :
      let memberDecode := fun i hi => decode.toMemberDecode hchar i hi
      let model :=
        CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := memberDecode)
          (hblinding :=
            top.toVerifierKey_blindingFactors_lt_n urs)
          haccepts
      ch.x ∉ szBadSet
        (combineConstraints
          model.fixedCols model.adviceCols model.instanceCols model.gates
          model.sets model.chunks model.lookups
          model.beta model.gamma model.delta model.theta ch.y
          model.chunkLen model.l0 model.lLast model.lBlind -
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts) .vanishingH *
          (X ^ top.n - 1)))
    (hgoodY :
      let memberDecode := fun i hi => decode.toMemberDecode hchar i hi
      ∀ j, ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              top.toVerifierKey_blindingFactors_lt_n urs)
            haccepts).constraints
          top.n j))
    {cell : Type} [DecidableEq cell] [Fintype cell]
    (correctness :
      let memberDecode := fun i hi => decode.toMemberDecode hchar i hi
      (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := memberDecode)
        (hblinding :=
          top.toVerifierKey_blindingFactors_lt_n urs)
        haccepts).CircuitSat
          ch.y
          (CanonicalMemberConstraintRelation.acceptedPolynomial
            (memberDecode := memberDecode) haccepts .vanishingH)
          top.n a →
      TopLevelCircuitCorrectness top pp urs ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)
        cell
        (NontrivialRelation (F := Fp) urs.g urs.u urs.w)) :
    (∀ proofIndex, top.Statement (inputs proofIndex)) ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  let memberDecode := fun i hi => decode.toMemberDecode hchar i hi
  exact topLevelStatements_or_relation_of_decodedMemberPolynomial_eq
    top pp urs hk inputs ps ch pU pW a
    (decode.toOpenedBatch hchar) memberDecode haccepts
    (CanonicalMemberConstraintRelation.acceptedPolynomial
      (memberDecode := memberDecode) haccepts .vanishingH)
    rfl
    (fun slot point hpoint =>
      PSum.inl (decode.memberBinding hchar slot point hpoint))
    domainExponent_lt hxgood hgoodY correctness

/-- The decode type at a straight-line run, with its URS and transcript data derived from the
run itself. -/
abbrev StraightLineRunDecode
    {shape : Shape}
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) :=
  let pnu := straightLineRunOutput family basis O
  DeployedAlgebraicDecode shape (ursOfAugmentedBasis shape.k basis) rfl
    vk instanceCommitment pnu.1.proof.1
    (straightLineRunRecord family basis O)
    (pnu.1.aMulti (wrappedPreIpaReads pnu))
    (pnu.1.multiU (wrappedPreIpaReads pnu))
    (pnu.1.multiBlind (wrappedPreIpaReads pnu))

/-- The acceptance proposition at a straight-line run. -/
abbrev StraightLineRunAccepts
    {shape : Shape}
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) :=
  let pnu := straightLineRunOutput family basis O
  DeployedAccepts shape (ursOfAugmentedBasis shape.k basis) rfl
    vk instanceCommitment pnu.1.proof.1
    (straightLineRunRecord family basis O)

/-- Transport the run's decode to any identified verifier artifacts. -/
def straightLineRunDecodeAt
    {shape : Shape}
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (hvk : family.vk basis = vk)
    (hI : family.instanceCommitment basis = instanceCommitment)
    (hdecoded : family.straightLineConstraintDecoded static basis O) :
    let pnu := straightLineRunOutput family basis O
    DeployedAlgebraicDecode shape (ursOfAugmentedBasis shape.k basis)
      (ursOfAugmentedBasis_k shape.k basis).symm
      vk instanceCommitment
      pnu.1.proof.1
      (straightLineRunRecord family basis O)
      (pnu.1.aMulti (wrappedPreIpaReads pnu))
      (pnu.1.multiU (wrappedPreIpaReads pnu))
      (pnu.1.multiBlind (wrappedPreIpaReads pnu)) :=
  ((straightLineDecode family static basis O hdecoded).reRound
    (runRounds family.toFamily basis O)).transportArtifacts hvk hI

/-- Transport the run's verifier acceptance to any identified verifier artifacts. -/
theorem straightLineRunAcceptsAt
    {shape : Shape}
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (hvk : family.vk basis = vk)
    (hI : family.instanceCommitment basis = instanceCommitment)
    (hdecoded : family.straightLineConstraintDecoded static basis O) :
    let pnu := straightLineRunOutput family basis O
    DeployedAccepts shape (ursOfAugmentedBasis shape.k basis)
      (ursOfAugmentedBasis_k shape.k basis).symm
      vk instanceCommitment
      pnu.1.proof.1
      (straightLineRunRecord family basis O) :=
  deployedAccepts_transportArtifacts
    (straightLineAccepts_of_decoded family static basis O hdecoded) hvk hI

end Zcash.Snark
