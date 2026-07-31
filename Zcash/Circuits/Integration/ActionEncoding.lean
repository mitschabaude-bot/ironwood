import Zcash.Circuits.Action.TopLevel
import Zcash.Circuits.Integration.FixedColumns
import Zcash.Common.RelationWitness
import Zcash.Circuits.Integration.InstanceColumns
import Zcash.Circuits.Integration.TopLevelLookups
import Zcash.Snark.Soundness.Multiopen.CanonicalRelation
import Zcash.Circuits.Integration.TopLevelCircuit
import Zcash.Circuits.Integration.TopLevelGates
import Zcash.Circuits.Integration.TopLevelCorrectness
import Zcash.Circuits.Integration.ActionCopyReplay
import Zcash.Circuits.Integration.ActionFixedCoherenceCompute
import Zcash.Circuits.Integration.ActionGateCoherence
import Zcash.Circuits.Integration.ActionLookupSelectorRows
import Zcash.Snark.Keygen.Pipeline
import Mathlib.Util.AssertNoSorry

/-!
# Action correctness instantiation

This module packages the representation laws needed to instantiate generic
top-level-circuit correctness for the Orchard Action circuit. Public-input encoding
is handled by the generic assignment layer. The generic terminal theorem remains in
`Zcash.Snark.Soundness.TopLevelTerminal`.
-/

namespace Zcash.Snark

open Halo2 CompPoly.CPolynomial
open Zcash.Circuits
open Zcash.Circuits.Action
open Keygen

set_option maxHeartbeats 20000

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

/--
Package the Action circuit's gate, fixed, copy, and lookup representation laws for
one canonical decoded relation.

This is the Action-specific constructor for the generic top-level soundness
interface.  It does not mention the Action statement or its public-input
presentation.
-/
def actionTopLevelCircuitCorrectness
    (pp : Keygen.ProofParams) (urs : URS G)
    (hk :
      (pp.mergeDerived actionCircuit).k = urs.k)
    (instanceCommitment :
      Fin pp.numProofs →
        ℕ → G)
    (ps : ProofString
      (pp.mergeDerived actionCircuit) Fp G)
    (ch : Challenges
      (pp.mergeDerived actionCircuit).k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (batchOpenings :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk (actionCircuit.toVerifierKey pp urs) ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          (actionCircuit.toVerifierKey pp urs) ps ch)
        a pU pW)
    (memberDecode : ∀ i (hi : i <
        deployedX4PairCount
          (instanceCommitment := instanceCommitment)
          (actionCircuit.toVerifierKey pp urs) ps ch),
      OpenedMemberDecode
        (instanceCommitment := instanceCommitment)
        urs hk (actionCircuit.toVerifierKey pp urs)
        ps ch batchOpenings i hi)
    (hpoly : CPoly)
    (relation :
      CanonicalMemberConstraintRelation
        urs hk (actionCircuit.toVerifierKey pp urs)
        instanceCommitment ps ch pU pW a batchOpenings memberDecode
        (actionCircuit.toVerifierKey_blindingFactors_lt_n pp urs)
        ch.y hpoly
        actionCircuit.n)
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness relation.model.constraints
          actionCircuit.n j))
    (permutationExclusions :
      ResolverPermutationChallengeExclusions
        (actionCircuit.toVerifierKey pp urs)
        ch relation.polynomial actionActiveRows)
    (lookupExclusions :
      TopLevelLookup.ChallengeExclusions
        actionCircuit pp urs ch relation.polynomial) :
    TopLevelCircuitCorrectness
      actionCircuit pp urs ch relation.polynomial
      (FlatCell actionNumPermCols actionDomainSize)
      (NontrivialRelation (F := Fp) urs.g urs.u urs.w) := by
  classical
  let fixedCoherence :
      TopLevelFixedCoherence actionCircuit urs :=
    ActionFixedCoherence.ofDerived urs hk
  have hdomainSize :
      actionCircuit.n = 2 ^ urs.k := by
    rw [actionCircuit.n_eq_two_pow_domainExponent]
    exact congrArg (2 ^ ·)
      ((pp.mergeDerived_k actionCircuit).symm.trans hk)
  have hfixedRows : Function.Injective
      fun i : Fin (2 ^ urs.k) =>
        actionCircuit.omega ^
          (i : ℕ) :=
    TopLevelAssignment.domainRowsInjective_of_domainExponent_eq
      ActionPermutationDomain.domainExponent_lt hk
  refine
    { gates := ActionGateCoherence.topLevel
      fixedEncoding := ?_
      fixed := ?_
      copies := ?_
      lookups := ?_ }
  · intro proofIndex
    refine bindOrRelationWitness
      (relation.fixedColumns_eq_rowPolynomials_or_relation
        actionCircuit.pinnedCS.numFixedColumns
        actionCircuit.fixedRows
        actionCircuit.fixedRows_length
        fixedCoherence.key fixedCoherence.commitment
        (actionCircuit.toVerifierKey_fixedQueryCount pp urs)
        fixedCoherence.queryLayout
        fixedCoherence.queryLayoutBounded hfixedRows)
      fun hbinding => ?_
    let assignment :
        TopLevelAssignment actionCircuit
          pp.numProofs
          proofIndex :=
      { polynomial := relation.polynomial }
    apply topLevelFixedColumnEncoding_of_binding
      assignment
      (TopLevelAssignment.domainRowsInjective
        (top := actionCircuit)
        ActionPermutationDomain.domainExponent_lt)
      (TopLevelAssignment.domainRoot
        (top := actionCircuit)
        ActionPermutationDomain.domainExponent_lt)
    intro column
    have hkTop :
        actionCircuit.domainExponent = urs.k :=
      hk
    simpa only [assignment,
      actionCircuit.n_eq_two_pow_domainExponent, hkTop,
      actionCircuit.toVerifierKey_omega] using hbinding column
  · intro proofIndex
    exact relation.topLevelFixedConstraints_or_relation
      rfl fixedCoherence hfixedRows hdomainSize proofIndex
  · intro proofIndex
    simpa only [actionActiveRows] using
      actionCopyReplayWitness_or_relation
        pp urs hk relation hgoodY fixedCoherence
        permutationExclusions proofIndex
  · intro proofIndex
    · have hrows : Function.Injective
          fun i : Fin
              actionCircuit.n =>
            actionCircuit.omega ^
              (i : ℕ) := by
        rw [hdomainSize]
        exact hfixedRows
      have hroot :
          actionCircuit.omega ^
            actionCircuit.n = 1 :=
        TopLevelAssignment.domainRoot
          ActionPermutationDomain.domainExponent_lt
      have hn : actionCircuit.n ≠ 0 := by
        exact actionCircuit.n_ne_zero
      have hsatisfaction :=
        relation.constraintSatisfaction hn hgoodY
      refine bindOrRelationWitness
        (listForallOrRelationWitness
          (operationEnabledLookups (actionCircuit.operations) 0)
          fun lookup henabled => ?_)
        fun lookupSelectorValues =>
          TopLevelLookup.WitnessConditions.ofChallengeExclusions
            ch relation.polynomial proofIndex
            lookupSelectorValues lookupExclusions
      · have hrow :
            actionCircuit.placement lookup.region + lookup.row <
              actionCircuit.n :=
          by
            exact
              (lookup.activationRow_lt_usableRows henabled).trans_le
                (by
                  unfold TopLevelCircuit.usableRowsAt
                  exact (Nat.sub_le _ _).trans (Nat.sub_le _ _))
        have hexact :=
          actionLookupInputSelectorLeafRowsExact
            fixedCoherence lookup henabled
        have hvalues :=
          lookup.inputSelectorValuesRealized_or_bad
            relation.polynomial
            (fun column =>
              actionCircuit.fixedRows.getD column [])
            hfixedRows hdomainSize
            (Bad :=
              NontrivialRelation (F := Fp) urs.g urs.u urs.w)
            (fun column hcolumn =>
              relation.fixedColumn_eq_rowPolynomial_or_relation
                column fixedCoherence.key
                (actionCircuit.fixedRows.getD column [])
                (fixedCoherence.commitment column hcolumn)
                hfixedRows
                (by
                  obtain ⟨rotation, hlayout⟩ :=
                    fixedCoherence.queryLayout column hcolumn
                  exact fixedQuery_of_layout
                    (actionCircuit.toVerifierKey pp urs)
                    instanceCommitment ps ch column rotation
                    (actionCircuit.toVerifierKey_fixedQueryCount pp urs) hlayout))
            proofIndex hrow hexact
        exact hvalues

assert_no_sorry actionTopLevelCircuitCorrectness
