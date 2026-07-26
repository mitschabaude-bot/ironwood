import Zcash.Circuits.Integration.ActionEncoding
import Zcash.Circuits.Integration.ActionGateCoherence
import Zcash.Circuits.Integration.ActionInstanceCommitmentCompute
import Mathlib.Util.AssertNoSorry

/-!
# Action public-instance commitment provenance

The verifier's public-instance commitment is determined by the supplied Action rows
and the monomial URS. This module constructs the compatible Lagrange key directly
from that URS, defines the verifier commitment, and specializes the Action semantic
endpoint so neither the key nor its commitment equation is an external premise.
-/

namespace Zcash.Snark

open Halo2 Polynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action

namespace ActionInstanceCommitment

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

/-- The canonical Lagrange commitment key derived from a monomial URS and domain
generator. Each row generator is, by construction, the monomial commitment to the
corresponding interpolating basis polynomial. -/
noncomputable def instanceKey
    (pp : ProofParams) (urs : URS G) :
    LagrangeCommitmentKey urs
      (orchardActionTopLevelCircuit.toVerifierKey pp urs).omega where
  generators := fun i =>
    commit urs
      (polynomialCoefficients (2 ^ urs.k)
        (rowPolynomial
          (orchardActionTopLevelCircuit.toVerifierKey pp urs).omega
          (Pi.single i (1 : Fp))))
  generator_eq := fun _ => rfl

/-- The verifier-derived commitment family for Action public inputs. The Action
circuit has one public instance column; unused column indices are mapped to zero. -/
noncomputable def commitment
    (pp : ProofParams) (urs : URS G)
    (inputs :
      Fin (pp.mergeDerived orchardActionTopLevelCircuit).numProofs →
        PublicInputs) :
    Fin (pp.mergeDerived orchardActionTopLevelCircuit).numProofs →
      ℕ → G :=
  fun proofIndex column =>
    if column =
        (Action.Circuit.configure
          Specs.Sinsemilla.orchardGenerators {}).1.primary.index then
      (instanceKey pp urs).commitInstance (inputs proofIndex).rows 1
    else 0

omit [DecidableEq G] in
@[simp] theorem commitment_primary
    (pp : ProofParams) (urs : URS G)
    (inputs :
      Fin (pp.mergeDerived orchardActionTopLevelCircuit).numProofs →
        PublicInputs)
    (proofIndex :
      Fin (pp.mergeDerived orchardActionTopLevelCircuit).numProofs) :
    commitment pp urs inputs proofIndex
        (Action.Circuit.configure
          Specs.Sinsemilla.orchardGenerators {}).1.primary.index =
      (instanceKey pp urs).commitInstance (inputs proofIndex).rows 1 := by
  simp [commitment]

assert_no_sorry commitment_primary

omit [DecidableEq G] in
/-- On the primary column, the verifier commitment is the monomial-URS commitment
to the zero-padded public-row polynomial, with Halo 2's default blind. -/
theorem commitment_primary_eq_commit
    (pp : ProofParams) (urs : URS G)
    (inputs :
      Fin (pp.mergeDerived orchardActionTopLevelCircuit).numProofs →
        PublicInputs)
    (proofIndex :
      Fin (pp.mergeDerived orchardActionTopLevelCircuit).numProofs) :
    commitment pp urs inputs proofIndex
        (Action.Circuit.configure
          Specs.Sinsemilla.orchardGenerators {}).1.primary.index =
      commit urs
          (instanceCoefficients (2 ^ urs.k)
            (orchardActionTopLevelCircuit.toVerifierKey pp urs).omega
            (inputs proofIndex).rows) +
        urs.w := by
  rw [commitment_primary, LagrangeCommitmentKey.commitInstance_eq, one_smul]

assert_no_sorry commitment_primary_eq_commit

set_option maxRecDepth 100000 in
/--
The Action endpoint with public-instance provenance closed.

The instance commitment is computed from `inputs`; its compatible key, commitment
equation, primary-query registration, Action domain bound, row capacity, and static
gate package are all constructed here rather than supplied by the caller.
-/
theorem actionBundleStatement_or_relation_of_canonicalRelation
    (pp : ProofParams) (urs : URS G)
    (hk :
      (pp.mergeDerived orchardActionTopLevelCircuit).k = urs.k)
    (inputs :
      Fin (pp.mergeDerived orchardActionTopLevelCircuit).numProofs →
        PublicInputs)
    (ps : ProofString
      (pp.mergeDerived orchardActionTopLevelCircuit) Fp G)
    (ch : Challenges
      (pp.mergeDerived orchardActionTopLevelCircuit).k Fp)
    (vk : VerifyingKey
      (pp.mergeDerived orchardActionTopLevelCircuit) Fp G)
    (hvk :
      vk = orchardActionTopLevelCircuit.toVerifierKey pp urs)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := commitment pp urs inputs)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := commitment pp urs inputs)
          vk ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := commitment pp urs inputs)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := commitment pp urs inputs)
        urs hk vk ps ch batchOpenings i hi)
    (hblinding :
      vk.blindingFactors < vk.n)
    (hpoly : Polynomial Fp)
    (relation :
      CanonicalMemberConstraintRelation
        urs hk vk
        (commitment pp urs inputs) ps ch pU pW a
        batchOpenings memberDecode hblinding ch.y hpoly vk.n)
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness relation.model.constraints
          vk.n j))
    (permutationExclusions :
      ResolverPermutationChallengeExclusions
        (orchardActionTopLevelCircuit.toVerifierKey pp urs)
        ch relation.polynomial actionActiveRows)
    (lookupExclusions :
      TopLevelLookupCoherence.TopLevelLookupChallengeExclusions
        orchardActionTopLevelCircuit pp urs ch relation.polynomial) :
    BundleStatement Specs.Sinsemilla.orchardGenerators orchardBases inputs ∨
      HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  have hsize :
      10 ≤ 2 ^ orchardActionTopLevelCircuit.domainExponent := by
    have hload :=
      Zcash.Circuits.Action.initialGeneratorTableIdx_mem
        Specs.Sinsemilla.orchardGenerators orchardBases
        orchardActionTopLevelCircuit.config 0
    have hload' :
        Operation.loadTable
            orchardActionTopLevelCircuit.config.sinsemilla1.generatorTable.tableIdx
            ((List.range (2 ^ Specs.K)).map
              (Nat.cast : ℕ → Fp)) ∈
          orchardActionTopLevelCircuit.operations 0 := by
      simpa [TopLevelCircuit.operations,
        Zcash.Circuits.Action.orchardActionTopLevelCircuit,
        Zcash.Circuits.Action.topLevelCircuit,
        TopLevelCircuit.config] using hload
    have htable :
        ((List.range (2 ^ Specs.K)).map
          (Nat.cast : ℕ → Fp)).length ≤
          orchardActionTopLevelCircuit.usedRows :=
      TopLevelAssignment.loadTable_length_le_usedRows
        (orchardActionTopLevelCircuit.operations 0) _ _ hload'
    have hused : 10 ≤ orchardActionTopLevelCircuit.usedRows := by
      have hten :
          10 ≤
            ((List.range (2 ^ Specs.K)).map
              (Nat.cast : ℕ → Fp)).length := by
        norm_num [Specs.K]
      exact hten.trans htable
    have hfit :=
      orchardActionTopLevelCircuit.fitsAt_domainExponent
        ActionPermutationDomain.domainExponent_lt
    unfold TopLevelCircuit.FitsAt at hfit
    omega
  exact
    Zcash.Snark.actionBundleStatement_or_relation_of_canonicalRelation
      pp urs hk (commitment pp urs inputs) ps ch vk hvk pU pW a
      batchOpenings memberDecode ActionPermutationDomain.domainExponent_lt
      hblinding hpoly relation hgoodY inputs hsize (instanceKey pp urs)
      (commitment_primary pp urs inputs) primaryRegistered
      (ActionGateCoherence.topLevelGateCoherence pp urs)
      permutationExclusions
      lookupExclusions

assert_no_sorry actionBundleStatement_or_relation_of_canonicalRelation

/--
The deterministic `hencodes` handoff for an accepting verifier run.

The caller supplies satisfaction of the constraint model canonically routed from
that same accepting run. This theorem constructs
`CanonicalMemberConstraintRelation` internally and applies the closed Action
endpoint; no free relation, constraint family, or statement proposition remains.
-/
theorem actionBundleStatement_or_relation_of_acceptedCircuitSat
    (pp : ProofParams) (urs : URS G)
    (hk :
      (pp.mergeDerived orchardActionTopLevelCircuit).k = urs.k)
    (inputs :
      Fin (pp.mergeDerived orchardActionTopLevelCircuit).numProofs →
        PublicInputs)
    (ps : ProofString
      (pp.mergeDerived orchardActionTopLevelCircuit) Fp G)
    (ch : Challenges
      (pp.mergeDerived orchardActionTopLevelCircuit).k Fp)
    (vk : VerifyingKey
      (pp.mergeDerived orchardActionTopLevelCircuit) Fp G)
    (hvk :
      vk = orchardActionTopLevelCircuit.toVerifierKey pp urs)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := commitment pp urs inputs)
          urs hk vk ps ch)
        (x4BatchEvals
          (instanceCommitment := commitment pp urs inputs)
          vk ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := commitment pp urs inputs)
          vk ps ch),
      OpenedMemberDecode
        (instanceCommitment := commitment pp urs inputs)
        urs hk vk ps ch batchOpenings i hi)
    (haccepts :
      DeployedAccepts urs hk vk
        (commitment pp urs inputs) ps ch)
    (hblinding :
      vk.blindingFactors < vk.n)
    (hpoly : Polynomial Fp)
    (hsatisfied :
      (CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := memberDecode)
        (hblinding := hblinding) haccepts).CircuitSat
          ch.y hpoly vk.n a)
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode := memberDecode)
            (hblinding := hblinding) haccepts).constraints
          vk.n j))
    (permutationExclusions :
      ResolverPermutationChallengeExclusions
        (orchardActionTopLevelCircuit.toVerifierKey pp urs)
        ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)
        actionActiveRows)
    (lookupExclusions :
      TopLevelLookupCoherence.TopLevelLookupChallengeExclusions
        orchardActionTopLevelCircuit pp urs ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts)) :
    BundleStatement Specs.Sinsemilla.orchardGenerators orchardBases inputs ∨
      HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  let relation :=
    CanonicalMemberConstraintRelation.ofAcceptedCircuitSat
      haccepts hsatisfied
  have hpolynomial :
      relation.polynomial =
        CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode := memberDecode) haccepts := by
    rfl
  apply actionBundleStatement_or_relation_of_canonicalRelation
    pp urs hk inputs ps ch vk hvk pU pW a batchOpenings memberDecode
    hblinding hpoly relation
  · simpa only [
      CanonicalMemberConstraintRelation.model,
      hpolynomial] using hgoodY
  · simpa only [hpolynomial] using permutationExclusions
  · simpa only [hpolynomial] using lookupExclusions

assert_no_sorry actionBundleStatement_or_relation_of_acceptedCircuitSat

end ActionInstanceCommitment

end Zcash.Snark
