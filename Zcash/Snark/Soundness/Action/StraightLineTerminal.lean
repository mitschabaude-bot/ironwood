import Zcash.Circuits.Integration.ActionCorrectness
import Zcash.Circuits.Integration.ActionPermutationDomain
import Zcash.Snark.Soundness.AGM.DecodeToOpened
import Zcash.Snark.Soundness.Composition.StraightLineDecodeSupply
import Zcash.Snark.Soundness.StraightLine.TopLevelTerminal

/-!
# The rewind-free decode at the Action terminal

This bridge feeds one straight-line decode into `ActionTerminal`. The shared executable outcome
retains either all private witnesses or relation coefficients; `StraightLineActionEvent` prices
the remaining challenge exclusions.
-/

namespace Zcash.Snark

namespace ActionTerminal

open Halo2 CompPoly.CPolynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder)

variable {G : Type} [AddCommGroup G] [Module Fp G] [DecidableEq G] [Inhabited G]

local instance vestaInhabitedStraightLineActionTerminal : Inhabited VestaG := ⟨0⟩

/-- Type-valued private witnesses for every Action in the accepted bundle. -/
abbrev ActionBundleWitness {numProofs : ℕ}
    (inputs : Fin numProofs → PublicInputs Fp) : Type :=
  TopLevelExternalBundleWitness actionCircuit inputs

namespace ActionBundleWitness

/-- An extracted Action witness bundle entails the ordinary existential statement. -/
theorem statement
    {numProofs : ℕ} {inputs : Fin numProofs → PublicInputs Fp}
    (witness : ActionBundleWitness inputs) : BundleStatement inputs :=
  fun proofIndex => (witness proofIndex).statement

end ActionBundleWitness

/-- Check every potentially nonzero fold-split witness by direct evaluation.  Witnesses at
indices `j ≥ n` are zero by degree, so this finite traversal returns the full specification-level
avoidance certificate without computing any root set. -/
def foldSplitAvoidance?
    (cs : List (CPoly)) (n : Nat) (hn : n ≠ 0) (y : Fp) :
    Option (PLift (∀ j, y ∉ szBadSet (foldSplitWitness cs n j))) :=
  match finForallOption (fun j : Fin n =>
      szBadSetAvoidance? (foldSplitWitness cs n j.1) y) with
  | none => none
  | some hgood => some ⟨fun j =>
      if hj : j < n then (hgood ⟨j, hj⟩).down
      else not_mem_szBadSet.mpr fun hne =>
        False.elim (hne (foldSplitWitness_zero_of_le hn (Nat.le_of_not_gt hj)))⟩

theorem foldSplitAvoidance?_isSome_of
    (cs : List (CPoly)) (n : Nat) (hn : n ≠ 0) (y : Fp)
    (hgood : ∀ j, y ∉ szBadSet (foldSplitWitness cs n j)) :
    (foldSplitAvoidance? cs n hn y).isSome := by
  have hfinite : ∀ j : Fin n,
      (szBadSetAvoidance? (foldSplitWitness cs n j.1) y).isSome :=
    fun j => (szBadSetAvoidance?_isSome_iff _ _).2 (hgood j.1)
  obtain ⟨found, hfound⟩ := Option.isSome_iff_exists.mp
    (finForallOption_isSome_of _ hfinite)
  simp [foldSplitAvoidance?, hfound]

/-- **The Action bundle statement from a rewind-free decode.**  The decode supplies the batch
openings, the member decodes, the `x₄` designation and the member-binding premise; the caller
supplies acceptance and the challenge exclusions.

The member-binding premise never takes its relation branch here: a decode already carries the
value equations, so `memberBinding` lands on the left for every slot and point. -/
def action_bundleStatement_or_relation_of_decode
    (pp : ProofParams) (urs : URS G)
    (hk : (actionCircuit.shape.withProofParams pp).k = urs.k)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp G)
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (decode : DeployedAlgebraicDecode (actionCircuit.shape.withProofParams pp) urs hk
      (actionCircuit.toVerifierKey urs)
      (actionCircuit.instanceCommitment urs inputs) ps ch a pU pW)
    (hchar : deployedX4PairCount
      (shape := actionCircuit.shape.withProofParams pp)
      (actionCircuit.toVerifierKey urs)
      (actionCircuit.instanceCommitment urs inputs) ps ch < scalarFieldOrder)
    (haccepts :
      DeployedAccepts (actionCircuit.shape.withProofParams pp) urs hk
        (actionCircuit.toVerifierKey urs)
        (actionCircuit.instanceCommitment urs inputs) ps ch)
    (hxgood :
      let memberDecode := fun i hi => decode.toMemberDecode hchar i hi
      let model :=
        CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := memberDecode)
          (hblinding :=
            actionCircuit.toVerifierKey_blindingFactors_lt_n urs)
          haccepts
      ch.x ∉ szBadSet
        (combineConstraints
          model.fixedCols model.adviceCols model.instanceCols model.gates
          model.sets model.chunks model.lookups
          model.beta model.gamma model.delta model.theta ch.y
          model.chunkLen model.l0 model.lLast model.lBlind -
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts) .vanishingH *
          (X ^ actionCircuit.n - 1)))
    (hgoodY :
      let memberDecode := fun i hi => decode.toMemberDecode hchar i hi
      ∀ j, ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              actionCircuit.toVerifierKey_blindingFactors_lt_n urs)
            haccepts).constraints
          actionCircuit.n j))
    (permutationExclusions :
      ResolverPermutationChallengeExclusions
        pp.numProofs (actionCircuit.toVerifierKey urs) ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)
        actionActiveRows)
    (lookupExclusions :
      TopLevelLookup.ChallengeExclusions
        actionCircuit pp urs ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)) :
    BundleStatement inputs ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  let memberDecode := fun i hi => decode.toMemberDecode hchar i hi
  let polynomial :=
    CanonicalMemberConstraintRelation.acceptedPolynomial
      (memberDecode := memberDecode) haccepts
  exact topLevelStatements_or_relation_of_decode
    actionCircuit pp urs hk inputs ps ch pU pW a decode hchar haccepts
    ActionConstraintBounds.domainExponent_lt
    hxgood hgoodY
    (fun hsatisfied =>
      ActionCorrectness.ofAcceptedCircuitSat
        pp urs hk inputs ps ch pU pW a
        (decode.toOpenedBatch hchar) memberDecode haccepts
        (polynomial .vanishingH)
        (by
          simpa only [actionCircuit.toVerifierKey_n] using hsatisfied)
        (by
          simpa only [actionCircuit.toVerifierKey_n] using hgoodY)
        permutationExclusions lookupExclusions)

/-- The Action endpoint when a pre-`x` constraint identity has already supplied canonical circuit
satisfaction.  This avoids re-testing the `x`-dependent reassembled quotient polynomial. -/
def action_bundleStatement_or_relation_of_decode_circuitSat
    (pp : ProofParams) (urs : URS G)
    (hk : (actionCircuit.shape.withProofParams pp).k = urs.k)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp G)
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (decode : DeployedAlgebraicDecode (actionCircuit.shape.withProofParams pp) urs hk
      (actionCircuit.toVerifierKey urs)
      (actionCircuit.instanceCommitment urs inputs) ps ch a pU pW)
    (hchar : deployedX4PairCount
      (shape := actionCircuit.shape.withProofParams pp)
      (actionCircuit.toVerifierKey urs)
      (actionCircuit.instanceCommitment urs inputs) ps ch < scalarFieldOrder)
    (haccepts : DeployedAccepts (actionCircuit.shape.withProofParams pp) urs hk
      (actionCircuit.toVerifierKey urs)
      (actionCircuit.instanceCommitment urs inputs) ps ch)
    (hpoly : CPoly)
    (hsatisfied :
      (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
        (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n urs)
        haccepts).CircuitSat ch.y hpoly
          actionCircuit.n a)
    (hgoodY : ∀ j, ch.y ∉ szBadSet
      (foldSplitWitness
        (CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
          (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n urs)
          haccepts).constraints
        actionCircuit.n j))
    (permutationExclusions : ResolverPermutationChallengeExclusions
      pp.numProofs (actionCircuit.toVerifierKey urs) ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)
      actionActiveRows)
    (lookupExclusions : TopLevelLookup.ChallengeExclusions
      actionCircuit pp urs ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)) :
    BundleStatement inputs ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  exact topLevelStatements_or_relation_of_circuitSat
    actionCircuit pp urs hk inputs ps ch pU pW a
    (decode.toOpenedBatch hchar)
    (fun i hi => decode.toMemberDecode hchar i hi) haccepts
    hpoly
    (by simpa only [actionCircuit.toVerifierKey_n] using hsatisfied)
    (by simpa only [actionCircuit.toVerifierKey_n] using hgoodY)
    (ActionCorrectness.ofAcceptedCircuitSat pp urs hk inputs ps ch
      pU pW a
      (decode.toOpenedBatch hchar)
      (fun i hi => decode.toMemberDecode hchar i hi) haccepts hpoly hsatisfied hgoodY
      permutationExclusions lookupExclusions)

section OpaqueActionArtifacts

attribute [local irreducible] actionCircuit TopLevelCircuit.toVerifierKey
  TopLevelCircuit.instanceCommitment

/-- The run's decode at the Action circuit's artifacts: extracted from the event, re-rounded to
the run's complete challenge record, and transported along the key and instance identifications. -/
def actionRunDecode
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : family.instanceCommitment basis =
      actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.shape.k basis) inputs)
    (hdecoded : family.straightLineConstraintDecoded static basis O) :
    DeployedAlgebraicDecode
      (actionCircuit.shape.withProofParams pp)
      (ursOfAugmentedBasis actionCircuit.shape.k basis)
      (ursOfAugmentedBasis_k actionCircuit.shape.k basis).symm
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis actionCircuit.shape.k basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.shape.k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O)
      ((straightLineRunOutput family basis O).1.aMulti
        (wrappedPreIpaReads (straightLineRunOutput family basis O)))
      ((straightLineRunOutput family basis O).1.multiU
        (wrappedPreIpaReads (straightLineRunOutput family basis O)))
      ((straightLineRunOutput family basis O).1.multiBlind
        (wrappedPreIpaReads (straightLineRunOutput family basis O))) :=
  (straightLineDecode family static basis O hdecoded).reRound
      (runRounds family.toFamily basis O)
    |>.transportArtifacts hvk hI

/-- The Action spelling of a transported run decode is the generic spelling. -/
theorem actionRunDecode_eq_straightLineRunDecodeAt
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * actionCircuit.shape.k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : family.vk basis = actionCircuit.toVerifierKey
      (ursOfAugmentedBasis actionCircuit.shape.k basis))
    (hI : family.instanceCommitment basis = actionCircuit.instanceCommitment
      (ursOfAugmentedBasis actionCircuit.shape.k basis) inputs)
    (hdecoded : family.straightLineConstraintDecoded static basis O) :
    actionRunDecode pp family static basis O inputs hvk hI hdecoded =
      straightLineRunDecodeAt family static basis O
        (actionCircuit.toVerifierKey
          (ursOfAugmentedBasis actionCircuit.shape.k basis))
        (actionCircuit.instanceCommitment
          (ursOfAugmentedBasis actionCircuit.shape.k basis) inputs)
        hvk hI hdecoded := by
  rfl

/-- The run's acceptance at the Action circuit's artifacts. -/
def actionRunAccepts
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : family.instanceCommitment basis =
      actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.shape.k basis) inputs)
    (hdecoded : family.straightLineConstraintDecoded static basis O) :
    DeployedAccepts (actionCircuit.shape.withProofParams pp)
      (ursOfAugmentedBasis actionCircuit.shape.k basis)
      (ursOfAugmentedBasis_k actionCircuit.shape.k basis).symm
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis actionCircuit.shape.k basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.shape.k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) :=
  deployedAccepts_transportArtifacts
    (straightLineAccepts_of_decoded family static basis O hdecoded) hvk hI

/-- The pre-`x` Action endpoint retaining the extracted private witnesses as data. -/
def action_bundleWitness_or_relation_of_decode_circuitSat
    (pp : ProofParams) (urs : URS G)
    (hk : actionCircuit.shape.k = urs.k)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp G)
    (ch : Challenges actionCircuit.shape.k Fp)
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    (decode : DeployedAlgebraicDecode (actionCircuit.shape.withProofParams pp) urs hk
      (actionCircuit.toVerifierKey urs)
      (actionCircuit.instanceCommitment urs inputs) ps ch a pU pW)
    (hchar : deployedX4PairCount
      (shape := actionCircuit.shape.withProofParams pp)
      (actionCircuit.toVerifierKey urs)
      (actionCircuit.instanceCommitment urs inputs) ps ch < scalarFieldOrder)
    (haccepts : DeployedAccepts (actionCircuit.shape.withProofParams pp) urs hk
      (actionCircuit.toVerifierKey urs)
      (actionCircuit.instanceCommitment urs inputs) ps ch)
    (hpoly : CPoly)
    (hsatisfied :
      (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
        (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n urs)
        haccepts).CircuitSat ch.y hpoly
          actionCircuit.n a)
    (hgoodY : ∀ j, ch.y ∉ szBadSet
      (foldSplitWitness
        (CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
          (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n urs)
          haccepts).constraints
        actionCircuit.n j))
    (permutationExclusions : ResolverPermutationChallengeExclusions
      pp.numProofs (actionCircuit.toVerifierKey urs) ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)
      actionActiveRows)
    (lookupExclusions : TopLevelLookup.ChallengeExclusions
      actionCircuit pp urs ch
      (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts)) :
    ActionBundleWitness inputs ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  exact topLevelWitnesses_or_relation_of_circuitSat
    actionCircuit pp urs hk inputs ps ch pU pW a
    (decode.toOpenedBatch hchar)
    (fun i hi => decode.toMemberDecode hchar i hi) haccepts
    hpoly
    (by simpa only [actionCircuit.toVerifierKey_n] using hsatisfied)
    (by simpa only [actionCircuit.toVerifierKey_n] using hgoodY)
    (ActionCorrectness.ofAcceptedCircuitSat pp urs hk inputs ps ch
      pU pW a
      (decode.toOpenedBatch hchar)
      (fun i hi => decode.toMemberDecode hchar i hi) haccepts hpoly hsatisfied hgoodY
      permutationExclusions lookupExclusions)

/-- **The Action terminal reached from the straight-line constraint event.**  A family at the
Action shape supplies the decode and the acceptance from its own accepting run, so the terminal
is reached without a rewind.

`hvk` and `hI` identify the family's verifying key and instance commitment with the Action
circuit's, and the run data is transported along them.  Everything is stated at the run's
complete challenge record — acceptance reads the IPA rounds, so the root layer's zero-round
record cannot carry it.  The challenge exclusions are still open, exactly as in
`action_bundleStatement_or_relation_of_decode`. -/
def action_bundleStatement_or_relation_of_straightLineDecoded
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * actionCircuit.shape.k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis actionCircuit.shape.k basis))
    (hI : family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis actionCircuit.shape.k basis) inputs)
    (hdecoded : family.straightLineConstraintDecoded static basis O)
    (hchar : deployedX4PairCount
      (shape := actionCircuit.shape.withProofParams pp)
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis actionCircuit.shape.k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis actionCircuit.shape.k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder) :=
  action_bundleStatement_or_relation_of_decode pp
    (ursOfAugmentedBasis actionCircuit.shape.k basis)
    (ursOfAugmentedBasis_k actionCircuit.shape.k basis).symm inputs
    (straightLineRunOutput family basis O).1.proof.1
    (straightLineRunRecord family basis O)
    ((straightLineRunOutput family basis O).1.multiU
      (wrappedPreIpaReads (straightLineRunOutput family basis O)))
    ((straightLineRunOutput family basis O).1.multiBlind
      (wrappedPreIpaReads (straightLineRunOutput family basis O)))
    ((straightLineRunOutput family basis O).1.aMulti
      (wrappedPreIpaReads (straightLineRunOutput family basis O)))
    (actionRunDecode pp family static basis O inputs hvk hI hdecoded)
    hchar
    (actionRunAccepts pp family static basis O inputs hvk hI hdecoded)

end OpaqueActionArtifacts

section OpaqueActionCorrectness

attribute [local irreducible] actionCircuit TopLevelCircuit.toVerifierKey
  TopLevelCircuit.instanceCommitment

/-- Supply the Action-owned correctness argument from an abstract successful run view. -/
def StraightLineAcceptedView.actionCorrectness
    (pp : ProofParams)
    {family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp)}
    {basis : AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG}
    {O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10 +
        3 * actionCircuit.shape.k) → Fp}
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (view : StraightLineAcceptedView family basis O
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis actionCircuit.shape.k basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.shape.k basis) inputs))
    (hchar : deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis actionCircuit.shape.k basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.shape.k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder)
    (hsatisfied :
      (view.model hchar
        (actionCircuit.toVerifierKey_blindingFactors_lt_n
          (ursOfAugmentedBasis
            actionCircuit.shape.k basis))).CircuitSat
        (straightLineRunRecord family basis O).y
        (view.polynomial hchar .vanishingH) actionCircuit.n
        ((straightLineRunOutput family basis O).1.aMulti
          (wrappedPreIpaReads (straightLineRunOutput family basis O))))
    (hgoodY : ∀ j,
      (straightLineRunRecord family basis O).y ∉ szBadSet
        (foldSplitWitness
          (view.model hchar
            (actionCircuit.toVerifierKey_blindingFactors_lt_n
              (ursOfAugmentedBasis
                actionCircuit.shape.k basis))).constraints
          actionCircuit.n j))
    (permutationExclusions : ResolverPermutationChallengeExclusions
      pp.numProofs
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis actionCircuit.shape.k basis))
      (straightLineRunRecord family basis O) (view.polynomial hchar) actionActiveRows)
    (lookupExclusions : TopLevelLookup.ChallengeExclusions actionCircuit pp
      (ursOfAugmentedBasis actionCircuit.shape.k basis)
      (straightLineRunRecord family basis O) (view.polynomial hchar)) :
    TopLevelCircuitCorrectness actionCircuit pp
      (ursOfAugmentedBasis actionCircuit.shape.k basis)
      (straightLineRunRecord family basis O) (view.polynomial hchar)
      (FlatCell actionNumPermCols actionDomainSize)
      (NontrivialRelation (F := Fp)
        (ursOfAugmentedBasis actionCircuit.shape.k basis).g
        (ursOfAugmentedBasis actionCircuit.shape.k basis).u
        (ursOfAugmentedBasis actionCircuit.shape.k basis).w) :=
  ActionCorrectness.ofAcceptedCircuitSat pp
    (ursOfAugmentedBasis actionCircuit.shape.k basis)
    (ursOfAugmentedBasis_k actionCircuit.shape.k basis).symm
    inputs (straightLineRunOutput family basis O).1.proof.1
    (straightLineRunRecord family basis O)
    ((straightLineRunOutput family basis O).1.multiU
      (wrappedPreIpaReads (straightLineRunOutput family basis O)))
    ((straightLineRunOutput family basis O).1.multiBlind
      (wrappedPreIpaReads (straightLineRunOutput family basis O)))
    ((straightLineRunOutput family basis O).1.aMulti
      (wrappedPreIpaReads (straightLineRunOutput family basis O)))
    (view.decode.toOpenedBatch hchar) (view.memberDecode hchar) view.accepts
    (view.polynomial hchar .vanishingH) hsatisfied hgoodY
    permutationExclusions lookupExclusions

/-- Run the remaining algebraic checks for an accepted Action view. -/
def StraightLineAcceptedView.actionTerminalOutcome?
    (pp : ProofParams)
    {family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp)}
    {basis : AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG}
    {O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10 +
        3 * actionCircuit.shape.k) → Fp}
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (view : StraightLineAcceptedView family basis O
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis actionCircuit.shape.k basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.shape.k basis) inputs))
    (hchar : deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis actionCircuit.shape.k basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.shape.k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder) :
    Option (ActionBundleWitness inputs ⊕
      AlgebraicRelationWitness (F := Fp) basis) :=
  let pnu := straightLineRunOutput family basis O
  let urs := ursOfAugmentedBasis actionCircuit.shape.k basis
  let ch := straightLineRunRecord family basis O
  let model := view.model hchar
    (actionCircuit.toVerifierKey_blindingFactors_lt_n urs)
  let polynomial := view.polynomial hchar
  match szBadSetAvoidance?
      (combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
          model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
          ch.y model.chunkLen model.l0 model.lLast model.lBlind
        - polynomial CommitmentId.vanishingH
            * (X ^ (actionCircuit.toVerifierKey urs).n - 1)) ch.x with
  | some hxgoodProof =>
    let hn : actionCircuit.n ≠ 0 := actionCircuit.n_ne_zero
    match foldSplitAvoidance? model.constraints actionCircuit.n hn ch.y with
    | some hgoodYProof =>
      match resolverPermutationChallengeExclusions?
          pp.numProofs (actionCircuit.toVerifierKey urs) ch polynomial actionActiveRows with
      | some hpermutationProof =>
        match TopLevelLookup.topLevelLookupChallengeExclusions?
            actionCircuit pp urs ch polynomial with
        | some hlookupProof =>
          let hxgoodTop : ch.x ∉ szBadSet
              (combineConstraints model.fixedCols model.adviceCols model.instanceCols
                  model.gates model.sets model.chunks model.lookups model.beta model.gamma
                  model.delta model.theta ch.y model.chunkLen model.l0 model.lLast model.lBlind -
                polynomial .vanishingH * (X ^ actionCircuit.n - 1)) := by
            simpa only [actionCircuit.toVerifierKey_n] using hxgoodProof.down
          match StraightLineAcceptedView.topLevelWitnessesOrRelation
              actionCircuit pp inputs view hchar
              ActionConstraintBounds.domainExponent_lt hxgoodTop hgoodYProof.down
              (fun hsatisfied => StraightLineAcceptedView.actionCorrectness
                pp inputs view hchar hsatisfied hgoodYProof.down
                hpermutationProof.down hlookupProof.down) with
          | PSum.inl witness => some (Sum.inl witness)
          | PSum.inr relation => some (Sum.inr (straightLineRelationWitness
              actionCircuit.shape.k (basis := basis) relation))
        | none => none
      | none => none
    | none => none
  | none => none

/-- Successful semantic exclusions make the accepted Action terminal return data. -/
theorem StraightLineAcceptedView.actionTerminalOutcome?_isSome_of
    (pp : ProofParams)
    {family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp)}
    {basis : AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG}
    {O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * actionCircuit.shape.k) → Fp}
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (view : StraightLineAcceptedView family basis O
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis actionCircuit.shape.k basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.shape.k basis) inputs))
    (hchar : deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis actionCircuit.shape.k basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.shape.k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder)
    (hxgood :
      let urs := ursOfAugmentedBasis actionCircuit.shape.k basis
      let model := view.model hchar (actionCircuit.toVerifierKey_blindingFactors_lt_n urs)
      let polynomial := view.polynomial hchar
      (straightLineRunRecord family basis O).x ∉ szBadSet
        (combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
          model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
          (straightLineRunRecord family basis O).y model.chunkLen model.l0 model.lLast
          model.lBlind - polynomial .vanishingH * (X ^ actionCircuit.n - 1)))
    (hgoodY :
      let urs := ursOfAugmentedBasis actionCircuit.shape.k basis
      let model := view.model hchar (actionCircuit.toVerifierKey_blindingFactors_lt_n urs)
      ∀ j, (straightLineRunRecord family basis O).y ∉
        szBadSet (foldSplitWitness model.constraints actionCircuit.n j))
    (hpermutation : ResolverPermutationChallengeExclusions pp.numProofs
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis actionCircuit.shape.k basis))
      (straightLineRunRecord family basis O) (view.polynomial hchar) actionActiveRows)
    (hlookup : TopLevelLookup.ChallengeExclusions actionCircuit pp
      (ursOfAugmentedBasis actionCircuit.shape.k basis)
      (straightLineRunRecord family basis O) (view.polynomial hchar)) :
    (StraightLineAcceptedView.actionTerminalOutcome? pp inputs view hchar).isSome := by
  let urs := ursOfAugmentedBasis actionCircuit.shape.k basis
  let model := view.model hchar (actionCircuit.toVerifierKey_blindingFactors_lt_n urs)
  let polynomial := view.polynomial hchar
  dsimp only at hxgood hgoodY
  have hxgoodVk : (straightLineRunRecord family basis O).x ∉ szBadSet
      (combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
        model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
        (straightLineRunRecord family basis O).y model.chunkLen model.l0 model.lLast
        model.lBlind - polynomial .vanishingH *
          (X ^ (actionCircuit.toVerifierKey urs).n - 1)) := by
    simpa only [actionCircuit.toVerifierKey_n] using hxgood
  have hxSome := (szBadSetAvoidance?_isSome_iff _ _).2 hxgoodVk
  have hn : actionCircuit.n ≠ 0 := actionCircuit.n_ne_zero
  have hySome := foldSplitAvoidance?_isSome_of model.constraints _ hn _ hgoodY
  have hpSome := resolverPermutationChallengeExclusions?_isSome_of
    pp.numProofs _ _ _ _ hpermutation
  have hlSome := TopLevelLookup.topLevelLookupChallengeExclusions?_isSome_of
    actionCircuit pp urs _ _ hlookup
  obtain ⟨hxProof, hxEq⟩ := Option.isSome_iff_exists.mp hxSome
  obtain ⟨hyProof, hyEq⟩ := Option.isSome_iff_exists.mp hySome
  obtain ⟨hpProof, hpEq⟩ := Option.isSome_iff_exists.mp hpSome
  obtain ⟨hlProof, hlEq⟩ := Option.isSome_iff_exists.mp hlSome
  unfold StraightLineAcceptedView.actionTerminalOutcome?
  simp only
  rw [hxEq, hyEq, hpEq, hlEq]
  dsimp only
  have hxgoodTop : (straightLineRunRecord family basis O).x ∉ szBadSet
      (combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
        model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
        (straightLineRunRecord family basis O).y model.chunkLen model.l0 model.lLast
        model.lBlind - polynomial .vanishingH * (X ^ actionCircuit.n - 1)) := by
    simpa only [actionCircuit.toVerifierKey_n] using hxProof.down
  cases StraightLineAcceptedView.topLevelWitnessesOrRelation
      actionCircuit pp inputs view hchar ActionConstraintBounds.domainExponent_lt
      hxgoodTop hyProof.down (cell := FlatCell actionNumPermCols actionDomainSize)
      (fun hsatisfied => StraightLineAcceptedView.actionCorrectness
        pp inputs view hchar hsatisfied hyProof.down hpProof.down hlProof.down) <;> rfl

end OpaqueActionCorrectness

attribute [local irreducible] actionCircuit TopLevelCircuit.toVerifierKey
  TopLevelCircuit.instanceCommitment

/-- Checks terminal exclusions and returns private witnesses or explicit relation coefficients
from the reconstructed run. -/
def actionTerminalWitnessOrRelationFinder
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.shape.k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (shape := actionCircuit.shape.withProofParams pp)
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis actionCircuit.shape.k basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.shape.k basis) inputs)
      ((wrappedAdversary family.toFamily basis).run O).1.proof.1
      (chRecord
        (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O))
        (runRounds family.toFamily basis O)) < scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp) →
    Option (ActionBundleWitness inputs ⊕
      AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    match family.straightLineConstraintOutcome? static basis O with
    | none => none
    | some (PSum.inr relation) =>
        some (Sum.inr (straightLineRelationWitness
          actionCircuit.shape.k (basis := basis) relation))
    | some (PSum.inl success) =>
        let view : StraightLineAcceptedView family basis O
            (actionCircuit.toVerifierKey
              (ursOfAugmentedBasis actionCircuit.shape.k basis))
            (actionCircuit.instanceCommitment
              (ursOfAugmentedBasis actionCircuit.shape.k basis) inputs) :=
          success.acceptedViewAt
              (actionCircuit.toVerifierKey
                (ursOfAugmentedBasis actionCircuit.shape.k basis))
              (actionCircuit.instanceCommitment
                (ursOfAugmentedBasis actionCircuit.shape.k basis) inputs)
              (hvk basis) (hI basis)
        StraightLineAcceptedView.actionTerminalOutcome?
          pp (family := family) (basis := basis) (O := O)
          inputs view (hchar basis O)

/-- Relation-only projection retained for the ordinary-soundness reduction. -/
def actionTerminalRelationFinder
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (shape := actionCircuit.shape.withProofParams pp)
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      ((wrappedAdversary family.toFamily basis).run O).1.proof.1
      (chRecord
        (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O))
        (runRounds family.toFamily basis O)) < scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp) →
    Option (AlgebraicRelationWitness (F := Fp) basis) := fun basis O =>
  match actionTerminalWitnessOrRelationFinder pp family static inputs hvk hI hchar basis O with
  | some (Sum.inr relation) => some relation
  | _ => none

/-- One executable straight-line outcome shared by the witness extractor and DLOG projection. -/
def actionKnowledgeOutcome
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (shape := actionCircuit.shape.withProofParams pp)
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      ((wrappedAdversary family.toFamily basis).run O).1.proof.1
      (chRecord
        (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O))
        (runRounds family.toFamily basis O)) < scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp) →
    Option (ActionBundleWitness inputs ⊕
      AlgebraicRelationWitness (F := Fp) basis) := fun basis O =>
  match family.straightLineConstraintRelationFinder basis O with
  | some relation => some (Sum.inr relation)
  | none => actionTerminalWitnessOrRelationFinder pp family static inputs hvk hI hchar basis O

/-- Executable private-witness extractor for the straight-line/sequential presentation. -/
def actionKnowledgeExtractor
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (shape := actionCircuit.shape.withProofParams pp)
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      ((wrappedAdversary family.toFamily basis).run O).1.proof.1
      (chRecord
        (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O))
        (runRounds family.toFamily basis O)) < scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp) →
    Option (ActionBundleWitness inputs) := fun basis O =>
  match actionKnowledgeOutcome pp family static inputs hvk hI hchar basis O with
  | some (Sum.inl witness) => some witness
  | _ => none

/-- The single relation finder priced by the final Action capstone: the existing IPA/unbatching/
quotient finder first, followed by the executable Action-terminal finder. -/
def actionRelationFinder
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (shape := actionCircuit.shape.withProofParams pp)
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      ((wrappedAdversary family.toFamily basis).run O).1.proof.1
      (chRecord
        (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O))
        (runRounds family.toFamily basis O)) < scalarFieldOrder) :
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * (actionCircuit.shape.withProofParams pp).k) → Fp) →
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    match actionKnowledgeOutcome pp family static inputs hvk hI hchar basis O with
    | some (Sum.inr relation) => some relation
    | _ => none

/-- The witness projection preserves the left branch of the shared outcome exactly. -/
theorem actionKnowledgeExtractor_eq_some_of_outcome_eq_inl
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (shape := actionCircuit.shape.withProofParams pp)
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      ((wrappedAdversary family.toFamily basis).run O).1.proof.1
      (chRecord
        (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O))
        (runRounds family.toFamily basis O)) < scalarFieldOrder)
    (basis) (O) (witness : ActionBundleWitness inputs)
    (houtcome : actionKnowledgeOutcome pp family static inputs hvk hI hchar basis O =
      some (Sum.inl witness)) :
    actionKnowledgeExtractor pp family static inputs hvk hI hchar basis O = some witness := by
  unfold actionKnowledgeExtractor
  rw [houtcome]

/-- The relation projection preserves the right branch of the shared outcome exactly. -/
theorem actionRelationFinder_eq_some_of_outcome_eq_inr
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (shape := actionCircuit.shape.withProofParams pp)
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      ((wrappedAdversary family.toFamily basis).run O).1.proof.1
      (chRecord
        (wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O))
        (runRounds family.toFamily basis O)) < scalarFieldOrder)
    (basis) (O) (relation : AlgebraicRelationWitness (F := Fp) basis)
    (houtcome : actionKnowledgeOutcome pp family static inputs hvk hI hchar basis O =
      some (Sum.inr relation)) :
    actionRelationFinder pp family static inputs hvk hI hchar basis O = some relation := by
  unfold actionRelationFinder
  rw [houtcome]

end ActionTerminal

end Zcash.Snark
