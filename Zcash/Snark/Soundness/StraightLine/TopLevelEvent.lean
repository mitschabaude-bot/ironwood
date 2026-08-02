import Zcash.Snark.Soundness.Composition.StraightLineConstraint
import Zcash.Snark.Soundness.StraightLine.TopLevelTerminal

/-!
# Straight-line semantic events for any top-level circuit

These predicates connect the circuit-independent straight-line constraint event
to the `Statement` owned by an arbitrary `TopLevelCircuit`. They contain no
circuit-specific correctness argument or numerical budget.
-/

namespace Zcash.Snark

open Halo2 CompPoly.CPolynomial Keygen
open Zcash.Arithmetic (scalarFieldOrder)

local instance topLevelStraightLineEventInhabitedVesta : Inhabited VestaG := ⟨0⟩

/-- The accepted run presented at a top-level circuit's derived verifier artifacts. -/
def topLevelRunView
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (top.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInput Fp)
    (hvk : ∀ basis, family.vk basis =
      top.toVerifierKey (ursOfAugmentedBasis top.shape.k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      top.instanceCommitment (ursOfAugmentedBasis top.shape.k basis) inputs)
    (basis : AugmentedIndex (2 ^ top.shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (top.shape.withProofParams pp) family.init.length 10
        + 3 * top.shape.k) → Fp)
    (h : family.straightLineConstraintDecoded static basis O) :
    StraightLineAcceptedView family basis O
      (top.toVerifierKey (ursOfAugmentedBasis top.shape.k basis))
      (top.instanceCommitment (ursOfAugmentedBasis top.shape.k basis) inputs) where
  decode := straightLineRunDecodeAt family static basis O
    (top.toVerifierKey (ursOfAugmentedBasis top.shape.k basis))
    (top.instanceCommitment (ursOfAugmentedBasis top.shape.k basis) inputs)
    (hvk basis) (hI basis) h
  accepts := straightLineRunAcceptsAt family static basis O
    (top.toVerifierKey (ursOfAugmentedBasis top.shape.k basis))
    (top.instanceCommitment (ursOfAugmentedBasis top.shape.k basis) inputs)
    (hvk basis) (hI basis) h

@[simp] theorem topLevelRunView_decode
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (top.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInput Fp)
    (hvk : ∀ basis, family.vk basis =
      top.toVerifierKey (ursOfAugmentedBasis top.shape.k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      top.instanceCommitment (ursOfAugmentedBasis top.shape.k basis) inputs)
    (basis : AugmentedIndex (2 ^ top.shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (top.shape.withProofParams pp) family.init.length 10
        + 3 * top.shape.k) → Fp)
    (h : family.straightLineConstraintDecoded static basis O) :
    (topLevelRunView top pp family static inputs hvk hI basis O h).decode =
      straightLineRunDecodeAt family static basis O
        (top.toVerifierKey (ursOfAugmentedBasis top.shape.k basis))
        (top.instanceCommitment (ursOfAugmentedBasis top.shape.k basis) inputs)
        (hvk basis) (hI basis) h := by
  rfl

/-- The canonical constraint model accepted at a straight-line run's own decode. -/
abbrev topLevelRunModel
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (top.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInput Fp)
    (hvk : ∀ basis, family.vk basis =
      top.toVerifierKey
        (ursOfAugmentedBasis top.shape.k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      top.instanceCommitment (ursOfAugmentedBasis top.shape.k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (shape := top.shape.withProofParams pp)
      (top.toVerifierKey
        (ursOfAugmentedBasis top.shape.k basis))
      (top.instanceCommitment (ursOfAugmentedBasis top.shape.k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ top.shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (top.shape.withProofParams pp) family.init.length 10
        + 3 * top.shape.k) → Fp)
    (h : family.straightLineConstraintDecoded static basis O) :=
  (topLevelRunView top pp family static inputs hvk hI basis O h).model
    (hchar basis O)
    (top.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis top.shape.k basis))

/-- The canonical accepted member polynomial at a straight-line run's own decode. -/
abbrev topLevelRunPolynomial
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (top.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInput Fp)
    (hvk : ∀ basis, family.vk basis =
      top.toVerifierKey
        (ursOfAugmentedBasis top.shape.k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      top.instanceCommitment (ursOfAugmentedBasis top.shape.k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (shape := top.shape.withProofParams pp)
      (top.toVerifierKey
        (ursOfAugmentedBasis top.shape.k basis))
      (top.instanceCommitment (ursOfAugmentedBasis top.shape.k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder)
    (basis : AugmentedIndex (2 ^ top.shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (top.shape.withProofParams pp) family.init.length 10
        + 3 * top.shape.k) → Fp)
    (h : family.straightLineConstraintDecoded static basis O) :=
  (topLevelRunView top pp family static inputs hvk hI basis O h).polynomial
    (hchar basis O)

section ChallengeFailureEvents

variable
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (top.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInput Fp)
    (hvk : ∀ basis, family.vk basis =
      top.toVerifierKey
        (ursOfAugmentedBasis top.shape.k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      top.instanceCommitment (ursOfAugmentedBasis top.shape.k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (shape := top.shape.withProofParams pp)
      (top.toVerifierKey
        (ursOfAugmentedBasis top.shape.k basis))
      (top.instanceCommitment (ursOfAugmentedBasis top.shape.k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder)

/-- The `x` and `y` exclusions needed by the top-level terminal at one decoded run. -/
def TopLevelXYExclusions
    (basis : AugmentedIndex (2 ^ top.shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (top.shape.withProofParams pp) family.init.length 10
        + 3 * top.shape.k) → Fp)
    (h : family.straightLineConstraintDecoded static basis O) : Prop :=
  ((straightLineRunRecord family basis O).x ∉ szBadSet
        (let model :=
            topLevelRunModel top pp family static inputs hvk hI hchar basis O h;
          combineConstraints
            model.fixedCols model.adviceCols model.instanceCols model.gates
            model.sets model.chunks model.lookups
            model.beta model.gamma model.delta model.theta
            (straightLineRunRecord family basis O).y
            model.chunkLen model.l0 model.lLast model.lBlind -
          topLevelRunPolynomial top pp family static inputs hvk hI hchar basis O h
              CommitmentId.vanishingH *
            (X ^ (top.toVerifierKey
              (ursOfAugmentedBasis top.shape.k basis)).n - 1))) ∧
      ∀ j, (straightLineRunRecord family basis O).y ∉ szBadSet
        (foldSplitWitness
          (topLevelRunModel top pp family static inputs hvk hI hchar
            basis O h).constraints
          (top.toVerifierKey
            (ursOfAugmentedBasis top.shape.k basis)).n j)

/-- Runs whose `x` or `y` challenge lands in a top-level terminal exclusion set. -/
def topLevelXYFailureEvent :
    Set ((AugmentedIndex (2 ^ top.shape.k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (top.shape.withProofParams pp) family.init.length 10
          + 3 * top.shape.k) → Fp)) :=
  {q | ∃ h : family.straightLineConstraintDecoded static q.1 q.2,
    ¬TopLevelXYExclusions top pp family static inputs hvk hI hchar q.1 q.2 h}

/-- The permutation and lookup exclusions needed for `β` at one decoded run. -/
def TopLevelBetaExclusions
    (basis : AugmentedIndex (2 ^ top.shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (top.shape.withProofParams pp) family.init.length 10
        + 3 * top.shape.k) → Fp)
    (h : family.straightLineConstraintDecoded static basis O) : Prop :=
  ((straightLineRunRecord family basis O).beta ∉
        allResolverPermutationBetaBadSet
          pp.numProofs (top.toVerifierKey
            (ursOfAugmentedBasis top.shape.k basis))
          (topLevelRunPolynomial top pp family static inputs hvk hI hchar
            basis O h)
          (top.usableRowsAt top.domainExponent)) ∧
      (straightLineRunRecord family basis O).beta ∉
        allResolverLookupBetaBadSet
          pp.numProofs
          (top.toVerifierKey
            (ursOfAugmentedBasis top.shape.k basis))
          (straightLineRunRecord family basis O)
          (topLevelRunPolynomial top pp family static inputs hvk hI hchar
            basis O h)
          ((top.toVerifierKey
              (ursOfAugmentedBasis top.shape.k basis)).n -
            (top.toVerifierKey
              (ursOfAugmentedBasis top.shape.k basis)).blindingFactors - 2)

/-- Runs whose `β` challenge lands in a permutation or lookup exclusion set. -/
def topLevelBetaFailureEvent :
    Set ((AugmentedIndex (2 ^ top.shape.k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (top.shape.withProofParams pp) family.init.length 10
          + 3 * top.shape.k) → Fp)) :=
  {q | ∃ h : family.straightLineConstraintDecoded static q.1 q.2,
    ¬TopLevelBetaExclusions top pp family static inputs hvk hI hchar q.1 q.2 h}

/-- The permutation and lookup exclusions needed for `γ` at one decoded run. -/
def TopLevelGammaExclusions
    (basis : AugmentedIndex (2 ^ top.shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (top.shape.withProofParams pp) family.init.length 10
        + 3 * top.shape.k) → Fp)
    (h : family.straightLineConstraintDecoded static basis O) : Prop :=
  ((straightLineRunRecord family basis O).gamma ∉
        allResolverPermutationGammaBadSet
          pp.numProofs (top.toVerifierKey
            (ursOfAugmentedBasis top.shape.k basis))
          (straightLineRunRecord family basis O)
          (topLevelRunPolynomial top pp family static inputs hvk hI hchar
            basis O h)
          (top.usableRowsAt top.domainExponent)) ∧
      (straightLineRunRecord family basis O).gamma ∉
        allResolverLookupGammaBadSet
          pp.numProofs
          (top.toVerifierKey
            (ursOfAugmentedBasis top.shape.k basis))
          (straightLineRunRecord family basis O)
          (topLevelRunPolynomial top pp family static inputs hvk hI hchar
            basis O h)
          ((top.toVerifierKey
              (ursOfAugmentedBasis top.shape.k basis)).n -
            (top.toVerifierKey
              (ursOfAugmentedBasis top.shape.k basis)).blindingFactors - 2)

/-- Runs whose `γ` challenge lands in a permutation or lookup exclusion set. -/
def topLevelGammaFailureEvent :
    Set ((AugmentedIndex (2 ^ top.shape.k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (top.shape.withProofParams pp) family.init.length 10
          + 3 * top.shape.k) → Fp)) :=
  {q | ∃ h : family.straightLineConstraintDecoded static q.1 q.2,
    ¬TopLevelGammaExclusions top pp family static inputs hvk hI hchar q.1 q.2 h}

/-- The lookup exclusion needed for `θ` at one decoded run. -/
def TopLevelThetaExclusions
    (basis : AugmentedIndex (2 ^ top.shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (top.shape.withProofParams pp) family.init.length 10
        + 3 * top.shape.k) → Fp)
    (h : family.straightLineConstraintDecoded static basis O) : Prop :=
  (straightLineRunRecord family basis O).theta ∉
      TopLevelLookup.thetaBadSet top pp
        (ursOfAugmentedBasis top.shape.k basis)
        (topLevelRunPolynomial top pp family static inputs hvk hI hchar
          basis O h)

/-- Runs whose `θ` challenge lands in a top-level lookup exclusion set. -/
def topLevelThetaFailureEvent :
    Set ((AugmentedIndex (2 ^ top.shape.k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (top.shape.withProofParams pp) family.init.length 10
          + 3 * top.shape.k) → Fp)) :=
  {q | ∃ h : family.straightLineConstraintDecoded static q.1 q.2,
    ¬TopLevelThetaExclusions top pp family static inputs hvk hI hchar q.1 q.2 h}

theorem topLevelXYExclusions_of_not_mem
    {basis O} (hdecoded : family.straightLineConstraintDecoded static basis O)
    (hgood : (basis, O) ∉ topLevelXYFailureEvent top pp family static inputs hvk hI hchar) :
    TopLevelXYExclusions top pp family static inputs hvk hI hchar basis O hdecoded := by
  unfold topLevelXYFailureEvent at hgood
  exact Classical.not_not.mp (not_exists.mp hgood hdecoded)

theorem topLevelBetaExclusions_of_not_mem
    {basis O} (hdecoded : family.straightLineConstraintDecoded static basis O)
    (hgood : (basis, O) ∉ topLevelBetaFailureEvent top pp family static inputs hvk hI hchar) :
    TopLevelBetaExclusions top pp family static inputs hvk hI hchar basis O hdecoded := by
  unfold topLevelBetaFailureEvent at hgood
  exact Classical.not_not.mp (not_exists.mp hgood hdecoded)

theorem topLevelGammaExclusions_of_not_mem
    {basis O} (hdecoded : family.straightLineConstraintDecoded static basis O)
    (hgood : (basis, O) ∉ topLevelGammaFailureEvent top pp family static inputs hvk hI hchar) :
    TopLevelGammaExclusions top pp family static inputs hvk hI hchar basis O hdecoded := by
  unfold topLevelGammaFailureEvent at hgood
  exact Classical.not_not.mp (not_exists.mp hgood hdecoded)

theorem topLevelThetaExclusions_of_not_mem
    {basis O} (hdecoded : family.straightLineConstraintDecoded static basis O)
    (hgood : (basis, O) ∉ topLevelThetaFailureEvent top pp family static inputs hvk hI hchar) :
    TopLevelThetaExclusions top pp family static inputs hvk hI hchar basis O hdecoded := by
  unfold topLevelThetaFailureEvent at hgood
  exact Classical.not_not.mp (not_exists.mp hgood hdecoded)

end ChallengeFailureEvents

/--
A computed finder covers the top-level terminal when it returns explicit
relation coefficients on every decoded run outside the challenge-failure
events whose circuit statement is false.
-/
def topLevelTerminalRelationFinderCovers
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (top.shape.withProofParams pp))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (inputs : Fin pp.numProofs → PublicInput Fp)
    (hvk : ∀ basis, family.vk basis =
      top.toVerifierKey
        (ursOfAugmentedBasis top.shape.k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      top.instanceCommitment (ursOfAugmentedBasis top.shape.k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (shape := top.shape.withProofParams pp)
      (top.toVerifierKey
        (ursOfAugmentedBasis top.shape.k basis))
      (top.instanceCommitment (ursOfAugmentedBasis top.shape.k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder)
    (finder :
      (basis : AugmentedIndex (2 ^ top.shape.k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen (top.shape.withProofParams pp) family.init.length 10
          + 3 * top.shape.k) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis)) : Prop :=
  ∀ basis O,
    family.straightLineConstraintDecoded static basis O →
    (basis, O) ∉
      topLevelXYFailureEvent top pp family static inputs hvk hI hchar →
    (basis, O) ∉
      topLevelBetaFailureEvent top pp family static inputs hvk hI hchar →
    (basis, O) ∉
      topLevelGammaFailureEvent top pp family static inputs hvk hI hchar →
    (basis, O) ∉
      topLevelThetaFailureEvent top pp family static inputs hvk hI hchar →
    (¬∀ proofIndex, top.Statement (inputs proofIndex)) →
    (finder basis O).isSome

/-- The circuit statement or an explicit relation over the run's basis. -/
def topLevelStatementOrRelationDecoded
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (top.shape.withProofParams pp))
    (inputs : Fin pp.numProofs → PublicInput Fp) :
    (AugmentedIndex (2 ^ top.shape.k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (top.shape.withProofParams pp) family.init.length 10
        + 3 * top.shape.k) → Fp) → Prop :=
  fun basis _ =>
    Nonempty ((∀ proofIndex, top.Statement (inputs proofIndex)) ⊕'
      NontrivialRelation (F := Fp)
        (ursOfAugmentedBasis top.shape.k basis).g
        (ursOfAugmentedBasis top.shape.k basis).u
        (ursOfAugmentedBasis top.shape.k basis).w)

/-- The exact semantic target: the circuit statement holds for every bundled proof. -/
def topLevelBundleStatementDecoded
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (top.shape.withProofParams pp))
    (inputs : Fin pp.numProofs → PublicInput Fp) :
    (AugmentedIndex (2 ^ top.shape.k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (top.shape.withProofParams pp) family.init.length 10
        + 3 * top.shape.k) → Fp) → Prop :=
  fun _ _ => ∀ proofIndex, top.Statement (inputs proofIndex)

/-- Runs on which an executable terminal finder returns relation coefficients. -/
def straightLineTerminalRelationEvent
    {shape : Shape}
    (family : ComputedStraightLineDeployedFSFamily shape)
    (finder :
      (basis : AugmentedIndex (2 ^ shape.k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis)) :
    Set ((AugmentedIndex (2 ^ shape.k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)) :=
  {q | (finder q.1 q.2).isSome}

end Zcash.Snark
