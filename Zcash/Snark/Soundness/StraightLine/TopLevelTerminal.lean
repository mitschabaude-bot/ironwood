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

open Halo2 CompPoly.CPolynomial Keygen
open Zcash.Arithmetic (scalarFieldOrder)

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

local instance topLevelStraightLineInhabitedVesta : Inhabited VestaG := ⟨0⟩

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
    (hk : top.shape.k = urs.k)
    (inputs : Fin pp.numProofs → PublicInput Fp)
    (ps : ProofString (top.shape.withProofParams pp) Fp G)
    (ch : Challenges top.shape.k Fp)
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
    (permutationRouting :
      PermutationChunkRoutingCoherent (top.toVerifierKey urs))
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
    domainExponent_lt permutationRouting hxgood hgoodY correctness

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
    StraightLineRunDecode family basis O vk instanceCommitment :=
  hI ▸ hvk ▸ (straightLineDecode family static basis O hdecoded).reRound
    (runRounds family.toFamily basis O)

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
    StraightLineRunAccepts family basis O vk instanceCommitment :=
  hI ▸ hvk ▸ straightLineAccepts_of_decoded
    family static basis O hdecoded

/-- Transport a successful constraint outcome's decode to identified verifier artifacts. -/
def ComputedStraightLineDeployedFSFamily.StraightLineConstraintSuccess.decodeAt
    {shape : Shape}
    {family : ComputedStraightLineDeployedFSFamily shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp}
    (success : ComputedStraightLineDeployedFSFamily.StraightLineConstraintSuccess
      family basis O)
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (hvk : family.vk basis = vk)
    (hI : family.instanceCommitment basis = instanceCommitment) :
    StraightLineRunDecode family basis O vk instanceCommitment :=
  hI ▸ hvk ▸ success.witness.decode.reRound
    (runRounds family.toFamily basis O)

/-- Transport a successful constraint outcome's acceptance proof to identified verifier
artifacts. -/
def ComputedStraightLineDeployedFSFamily.StraightLineConstraintSuccess.acceptsAt
    {shape : Shape}
    {family : ComputedStraightLineDeployedFSFamily shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp}
    (success : ComputedStraightLineDeployedFSFamily.StraightLineConstraintSuccess
      family basis O)
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (hvk : family.vk basis = vk)
    (hI : family.instanceCommitment basis = instanceCommitment) :
    StraightLineRunAccepts family basis O vk instanceCommitment :=
  hI ▸ hvk ▸ success.accepts

/-- The dependent artifacts of one straight-line run. -/
structure StraightLineRunArtifacts
    {shape : Shape}
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → ℕ → VestaG) where
  urs : URS VestaG
  hk : shape.k = urs.k
  ps : ProofString shape Fp VestaG
  ch : Challenges shape.k Fp
  pU : Fp
  pW : Fp
  a : Fin (2 ^ urs.k) → Fp
  decode : DeployedAlgebraicDecode shape urs hk vk instanceCommitment ps ch a pU pW
  accepts : DeployedAccepts shape urs hk vk instanceCommitment ps ch

/-- Assemble the dependent artifacts carried by a successful straight-line constraint outcome. -/
def ComputedStraightLineDeployedFSFamily.StraightLineConstraintSuccess.artifactsAt
    {shape : Shape}
    {family : ComputedStraightLineDeployedFSFamily shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp}
    (success : ComputedStraightLineDeployedFSFamily.StraightLineConstraintSuccess
      family basis O)
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → ℕ → VestaG)
    (hvk : family.vk basis = vk)
    (hI : family.instanceCommitment basis = instanceCommitment) :
    StraightLineRunArtifacts family basis O vk instanceCommitment :=
  { urs := ursOfAugmentedBasis shape.k basis
    hk := rfl
    ps := (straightLineRunOutput family basis O).1.proof.1
    ch := straightLineRunRecord family basis O
    pU := (straightLineRunOutput family basis O).1.multiU
      (wrappedPreIpaReads (straightLineRunOutput family basis O))
    pW := (straightLineRunOutput family basis O).1.multiBlind
      (wrappedPreIpaReads (straightLineRunOutput family basis O))
    a := (straightLineRunOutput family basis O).1.aMulti
      (wrappedPreIpaReads (straightLineRunOutput family basis O))
    decode := success.decodeAt vk instanceCommitment hvk hI
    accepts := success.acceptsAt vk instanceCommitment hvk hI }

/-- A decoded run and the successful outcome selected by that same run transport to the same
decode at any identified verifier artifacts. -/
theorem straightLineRunDecodeAt_eq_successDecodeAt
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
    (hdecoded : family.straightLineConstraintDecoded static basis O)
    (success : ComputedStraightLineDeployedFSFamily.StraightLineConstraintSuccess
      family basis O)
    (hout : family.straightLineConstraintOutcome? static basis O = some (PSum.inl success)) :
    straightLineRunDecodeAt family static basis O vk instanceCommitment hvk hI hdecoded =
      success.decodeAt vk instanceCommitment hvk hI := by
  have hsuccess := family.straightLineConstraintSuccess_eq_of_outcome
    static basis O hdecoded success hout
  simp only [straightLineRunDecodeAt,
    ComputedStraightLineDeployedFSFamily.StraightLineConstraintSuccess.decodeAt,
    straightLineDecode, straightLineConstraintWitness, hsuccess]

end Zcash.Snark
