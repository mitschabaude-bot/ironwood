import Zcash.Circuits.Integration.TopLevelCorrectness
import Zcash.Circuits.Integration.TopLevelInstanceCommitment
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.TopLevelAssignment
import Zcash.Snark.Soundness.Canonical.Terminal
import Zcash.Snark.Soundness.Multiopen.CanonicalRelation
import Mathlib.Util.AssertNoSorry

set_option maxHeartbeats 20000

/-!
# Generic top-level circuit soundness terminal

This module is the core soundness endpoint for a Clean `TopLevelCircuit`. It
turns satisfaction of the verifier-native canonical constraint model into the
circuit's own statement for every proof in the bundle, and binds that statement
to the public inputs supplied to an accepting verifier.

The Clean/Ironwood representation work remains exposed as named component
conditions.  In particular, `TopLevelCircuitCorrectness` does not contain the
desired statement or an opaque encoding implication.
-/

namespace Zcash.Snark

open Halo2 CompPoly.CPolynomial

universe u v w

def TopLevelTerminalOutcome
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams)
    (poly : CommitmentId → CPoly)
    (Bad : Type) : Type :=
  TopLevelBundleStatement top pp poly ⊕' Bad

/-- The data-preserving terminal outcome used by knowledge extraction. -/
def TopLevelWitnessTerminalOutcome
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams)
    (poly : CommitmentId → CPoly)
    (Bad : Type) : Type :=
  TopLevelBundleWitness top pp poly ⊕' Bad

private def bindOutcome {A : Sort u} {B : Sort v} {R : Sort w}
    (outcome : A ⊕' R) (next : A → B ⊕' R) : B ⊕' R :=
  match outcome with
  | .inl value => next value
  | .inr bad => .inr bad

def topLevelBundleStatement_or_bad_of_components
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : Keygen.ProofParams} {urs : URS G}
    {k : ℕ} {ch : Challenges k Fp}
    {poly : CommitmentId → CPoly}
    {cell : Type} [DecidableEq cell] [Fintype cell]
    {Bad : Type}
    (satisfaction :
      ConstraintSatisfaction
        (top.constraintModel pp urs ch poly)
        top.n)
    (gates : TopLevelGateCoherence top)
    (fixedEncoding : ∀ proofIndex,
      TopLevelFixedEncoding top pp poly proofIndex)
    (fixed : ∀ proofIndex,
      TopLevelFixed top pp urs poly proofIndex)
    (copies : ∀ proofIndex,
      TopLevelCopies top pp urs poly cell Bad proofIndex)
    (lookups : ∀ proofIndex,
      TopLevelLookups top pp urs ch poly proofIndex) :
    TopLevelTerminalOutcome top pp poly Bad := by
  exact
    finForallOrRelationWitness
      (A := fun proofIndex =>
        let assignment :
            TopLevelAssignment top
              pp.numProofs proofIndex :=
          { polynomial := poly }
        top.Statement
          (top.extractPublicInput
            (top.environment assignment.proofAssignment)))
      fun proofIndex =>
        (TopLevelAssignment.bridgeWitness_of_components
            proofIndex satisfaction gates
            (fixedEncoding proofIndex)
            (fixed proofIndex).1 (fixed proofIndex).2
            (copies proofIndex) (lookups proofIndex)).statement_or_bad

/-- The component terminal retaining each extracted private witness as data. -/
def topLevelBundleWitness_or_bad_of_components
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : Keygen.ProofParams} {urs : URS G}
    {k : ℕ} {ch : Challenges k Fp}
    {poly : CommitmentId → CPoly}
    {cell : Type} [DecidableEq cell] [Fintype cell]
    {Bad : Type}
    (satisfaction :
      ConstraintSatisfaction
        (top.constraintModel pp urs ch poly)
        top.n)
    (gates : TopLevelGateCoherence top)
    (fixedEncoding : ∀ proofIndex,
      TopLevelFixedEncoding top pp poly proofIndex)
    (fixed : ∀ proofIndex,
      TopLevelFixed top pp urs poly proofIndex)
    (copies : ∀ proofIndex,
      TopLevelCopies top pp urs poly cell Bad proofIndex)
    (lookups : ∀ proofIndex,
      TopLevelLookups top pp urs ch poly proofIndex) :
    TopLevelWitnessTerminalOutcome top pp poly Bad := by
  exact finForallOrRelationWitness fun proofIndex =>
    (TopLevelAssignment.bridgeWitness_of_components
      proofIndex satisfaction gates
      (fixedEncoding proofIndex)
      (fixed proofIndex).1 (fixed proofIndex).2
      (copies proofIndex) (lookups proofIndex)).semanticWitness_or_bad

/--
Canonical constraint satisfaction plus the component-level circuit correctness
package implies the circuit-owned statement for every proof, preserving the one
shared exceptional event.
-/
def topLevelBundleStatement_or_bad_of_constraintSatisfaction
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : Keygen.ProofParams} {urs : URS G}
    {k : ℕ} {ch : Challenges k Fp}
    {poly : CommitmentId → CPoly}
    {cell : Type} [DecidableEq cell] [Fintype cell]
    {Bad : Type}
    (satisfaction :
      ConstraintSatisfaction
        (top.constraintModel pp urs ch poly)
        top.n)
    (correctness :
      TopLevelCircuitCorrectness top pp urs ch poly cell Bad) :
    TopLevelTerminalOutcome top pp poly Bad := by
  classical
  let fixedEncodingOutcome :=
    finForallOrRelationWitness
      (A := fun proofIndex =>
        TopLevelFixedEncoding top pp poly proofIndex)
      correctness.fixedEncoding
  let fixedOutcome :=
    finForallOrRelationWitness
      (A := fun proofIndex =>
        TopLevelFixed top pp urs poly proofIndex)
      correctness.fixed
  let copiesOutcome :=
    finForallOrRelationWitness
      (A := fun proofIndex =>
        TopLevelCopies top pp urs poly cell Bad proofIndex)
      correctness.copies
  let lookupsOutcome :=
    finForallOrRelationWitness
      (A := fun proofIndex =>
        TopLevelLookups top pp urs ch poly proofIndex)
      correctness.lookups
  exact bindOutcome fixedEncodingOutcome fun hfixedEncoding =>
    bindOutcome fixedOutcome fun hfixed =>
      bindOutcome copiesOutcome fun hcopies =>
        bindOutcome lookupsOutcome fun hlookups =>
          topLevelBundleStatement_or_bad_of_components
            satisfaction correctness.gates
            hfixedEncoding hfixed hcopies hlookups

/-- The correctness-package terminal retaining executable private witnesses. -/
def topLevelBundleWitness_or_bad_of_constraintSatisfaction
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : Keygen.ProofParams} {urs : URS G}
    {k : ℕ} {ch : Challenges k Fp}
    {poly : CommitmentId → CPoly}
    {cell : Type} [DecidableEq cell] [Fintype cell]
    {Bad : Type}
    (satisfaction :
      ConstraintSatisfaction
        (top.constraintModel pp urs ch poly)
        top.n)
    (correctness :
      TopLevelCircuitCorrectness top pp urs ch poly cell Bad) :
    TopLevelWitnessTerminalOutcome top pp poly Bad := by
  classical
  let fixedEncodingOutcome :=
    finForallOrRelationWitness
      (A := fun proofIndex =>
        TopLevelFixedEncoding top pp poly proofIndex)
      correctness.fixedEncoding
  let fixedOutcome :=
    finForallOrRelationWitness
      (A := fun proofIndex =>
        TopLevelFixed top pp urs poly proofIndex)
      correctness.fixed
  let copiesOutcome :=
    finForallOrRelationWitness
      (A := fun proofIndex =>
        TopLevelCopies top pp urs poly cell Bad proofIndex)
      correctness.copies
  let lookupsOutcome :=
    finForallOrRelationWitness
      (A := fun proofIndex =>
        TopLevelLookups top pp urs ch poly proofIndex)
      correctness.lookups
  exact bindOutcome fixedEncodingOutcome fun hfixedEncoding =>
    bindOutcome fixedOutcome fun hfixed =>
      bindOutcome copiesOutcome fun hcopies =>
        bindOutcome lookupsOutcome fun hlookups =>
          topLevelBundleWitness_or_bad_of_components
            satisfaction correctness.gates
            hfixedEncoding hfixed hcopies hlookups

assert_no_sorry topLevelBundleStatement_or_bad_of_constraintSatisfaction
assert_no_sorry topLevelBundleWitness_or_bad_of_constraintSatisfaction

variable
    {G : Type} [AddCommGroup G] [Module Fp G]
    [DecidableEq G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (hk : (pp.mergeDerived top).k = urs.k)
    (inputs : Fin pp.numProofs → PublicInput Fp)
    (ps : ProofString (pp.mergeDerived top) Fp G)
    (ch : Challenges (pp.mergeDerived top).k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := top.instanceCommitment pp urs inputs)
          urs hk (top.toVerifierKey pp urs) ps ch)
        (x4BatchEvals
          (instanceCommitment := top.instanceCommitment pp urs inputs)
          (top.toVerifierKey pp urs) ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := top.instanceCommitment pp urs inputs)
          (top.toVerifierKey pp urs) ps ch),
      OpenedMemberDecode
        (instanceCommitment := top.instanceCommitment pp urs inputs)
        urs hk (top.toVerifierKey pp urs)
        ps ch batchOpenings i hi)
    (haccepts :
      DeployedAccepts urs hk
        (top.toVerifierKey pp urs)
        (top.instanceCommitment pp urs inputs) ps ch)

/--
Satisfaction of the canonical model selected by an accepting verifier run,
together with the circuit's named correctness package, retains private witnesses
at the public inputs supplied to the verifier.
-/
def topLevelWitnesses_or_relation_of_circuitSat
    (hpoly : CPoly)
    (hsatisfied :
      (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := memberDecode)
        (hblinding :=
          top.toVerifierKey_blindingFactors_lt_n pp urs) haccepts).CircuitSat
          ch.y hpoly top.n a)
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              top.toVerifierKey_blindingFactors_lt_n pp urs)
            haccepts).constraints
          top.n j))
    {cell : Type} [DecidableEq cell] [Fintype cell]
    (correctness :
      TopLevelCircuitCorrectness top pp urs ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)
        cell
        (NontrivialRelation (F := Fp) urs.g urs.u urs.w)) :
    TopLevelExternalBundleWitness top inputs ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  let relation :=
    CanonicalMemberConstraintRelation.ofAcceptedCircuitSat
      haccepts hsatisfied
  have hpolynomial :
      relation.polynomial =
        CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts := by
    rfl
  have hn :
      top.n ≠ 0 := by
    exact top.n_ne_zero
  have hsatisfaction :=
    relation.constraintSatisfaction hn
      (by
        simpa only [
          CanonicalMemberConstraintRelation.model,
          hpolynomial] using hgoodY)
  have hwitness :=
    topLevelBundleWitness_or_bad_of_constraintSatisfaction
      (top := top) (pp := pp) (urs := urs) (ch := ch)
      (cell := cell)
      (by simpa only [hpolynomial] using hsatisfaction)
      correctness
  rcases hwitness with hwitness | hrelation
  · exact
      TopLevelInstanceCommitment.witnesses_or_relation_of_accepted_topLevelBundleWitness
        top pp urs hk inputs ps ch pU pW a batchOpenings memberDecode
        haccepts correctness.gates.domainExponent_lt hwitness
  · exact PSum.inr hrelation

assert_no_sorry topLevelWitnesses_or_relation_of_circuitSat

/-- Forget the retained private witnesses to obtain the statement-only terminal. -/
def topLevelStatements_or_relation_of_circuitSat
    (hpoly : CPoly)
    (hsatisfied :
      (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := memberDecode)
        (hblinding :=
          top.toVerifierKey_blindingFactors_lt_n pp urs) haccepts).CircuitSat
          ch.y hpoly top.n a)
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              top.toVerifierKey_blindingFactors_lt_n pp urs)
            haccepts).constraints
          top.n j))
    {cell : Type} [DecidableEq cell] [Fintype cell]
    (correctness :
      TopLevelCircuitCorrectness top pp urs ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)
        cell
        (NontrivialRelation (F := Fp) urs.g urs.u urs.w)) :
    (∀ proofIndex, top.Statement (inputs proofIndex)) ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w :=
  match topLevelWitnesses_or_relation_of_circuitSat
      top pp urs hk inputs ps ch pU pW a batchOpenings memberDecode
      haccepts hpoly hsatisfied hgoodY correctness with
  | .inl witnesses => .inl fun proofIndex =>
      (witnesses proofIndex).statement
  | .inr relation => .inr relation

assert_no_sorry topLevelStatements_or_relation_of_circuitSat

/--
Accepted decoded-member binding reaches the statement of any top-level circuit.

The verifier-native quotient terminal is circuit-independent. The circuit enters
only through its derived key, public-input commitment, permutation routing, and
the constructor for its `TopLevelCircuitCorrectness` package.
-/
def topLevelStatements_or_relation_of_decodedMemberPolynomial_eq
    {G : Type} [AddCommGroup G] [Module Fp G]
    [DecidableEq G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (hk : (pp.mergeDerived top).k = urs.k)
    (inputs : Fin pp.numProofs → PublicInput Fp)
    (ps : ProofString (pp.mergeDerived top) Fp G)
    (ch : Challenges (pp.mergeDerived top).k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := top.instanceCommitment pp urs inputs)
          urs hk (top.toVerifierKey pp urs) ps ch)
        (x4BatchEvals
          (instanceCommitment := top.instanceCommitment pp urs inputs)
          (top.toVerifierKey pp urs) ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := top.instanceCommitment pp urs inputs)
          (top.toVerifierKey pp urs) ps ch),
      OpenedMemberDecode
        (instanceCommitment := top.instanceCommitment pp urs inputs)
        urs hk (top.toVerifierKey pp urs)
        ps ch batchOpenings i hi)
    (haccepts :
      DeployedAccepts urs hk
        (top.toVerifierKey pp urs)
        (top.instanceCommitment pp urs inputs) ps ch)
    (hpoly : CPoly)
    (hquot :
      hpoly =
        CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts .vanishingH)
    (hbind : ∀
      (slot : DeployedMemberSlot
        (instanceCommitment := top.instanceCommitment pp urs inputs)
        (top.toVerifierKey pp urs) ps ch)
      (point : Fp),
      point ∈ deployedSetPts
          (instanceCommitment := top.instanceCommitment pp urs inputs)
          (top.toVerifierKey pp urs) ps ch slot.setIndex →
      (decodedMemberPolynomial
        (instanceCommitment := top.instanceCommitment pp urs inputs)
        urs hk (top.toVerifierKey pp urs)
        ps ch memberDecode slot).eval point =
          deployedMemberClaim
            (instanceCommitment := top.instanceCommitment pp urs inputs)
            (top.toVerifierKey pp urs) ps ch slot point ⊕'
        NontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (domainExponent_lt : top.domainExponent < 33)
    (permutationRouting :
      PermutationChunkRoutingCoherent (top.toVerifierKey pp urs))
    (hxgood :
      let model :=
        CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := memberDecode)
          (hblinding :=
            top.toVerifierKey_blindingFactors_lt_n pp urs)
          haccepts
      ch.x ∉ szBadSet
        (combineConstraints
          model.fixedCols model.adviceCols model.instanceCols model.gates
          model.sets model.chunks model.lookups
          model.beta model.gamma model.delta model.theta ch.y
          model.chunkLen model.l0 model.lLast model.lBlind -
        hpoly * (X ^ top.n - 1)))
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding :=
              top.toVerifierKey_blindingFactors_lt_n pp urs)
            haccepts).constraints
          top.n j))
    {cell : Type} [DecidableEq cell] [Fintype cell]
    (correctness :
        (CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode := memberDecode)
          (hblinding :=
            top.toVerifierKey_blindingFactors_lt_n pp urs)
          haccepts).CircuitSat
            ch.y hpoly top.n a →
      TopLevelCircuitCorrectness top pp urs ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)
        cell
        (NontrivialRelation (F := Fp) urs.g urs.u urs.w)) :
    (∀ proofIndex, top.Statement (inputs proofIndex)) ⊕'
      NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  have hrows :
      Function.Injective
        (fun row : Fin top.n =>
          top.omega ^ (row : ℕ)) := by
    simpa only [top.toVerifierKey_n, top.toVerifierKey_omega] using
      (TopLevelAssignment.domainRowsInjective
        (top := top) domainExponent_lt)
  have hroot :
      top.omega ^
        top.n = 1 := by
    simpa only [top.toVerifierKey_n, top.toVerifierKey_omega] using
      (TopLevelAssignment.domainRoot
        (top := top) domainExponent_lt)
  have hnFp : (top.n : Fp) ≠ 0 := by
    simpa only [top.toVerifierKey_n] using
      (TopLevelAssignment.domainSizeCastNeZero
        (top := top) domainExponent_lt)
  rcases
      acceptedModel_circuitSat_or_relation_of_decodedMemberPolynomial_eq
        urs hk (top.toVerifierKey pp urs)
        (top.instanceCommitment pp urs inputs) ps ch memberDecode
        haccepts (top.toVerifierKey_blindingFactors_lt_n pp urs)
        hpoly hquot
        (top.toVerifierKey_fixedQueryCount pp urs)
        (top.toVerifierKey_adviceQueryCount pp urs)
        (top.toVerifierKey_instanceQueryCount pp urs)
        hbind permutationRouting hrows hroot hnFp hxgood with
    hsatisfied | relation
  · exact topLevelStatements_or_relation_of_circuitSat
      top pp urs hk inputs ps ch pU pW a
      batchOpenings memberDecode haccepts hpoly
      hsatisfied hgoodY (correctness hsatisfied)
  · exact PSum.inr relation

assert_no_sorry
  topLevelStatements_or_relation_of_decodedMemberPolynomial_eq

end Zcash.Snark
