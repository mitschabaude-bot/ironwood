import Zcash.Snark.Fixtures.SingleAction.StaticChecks
import Zcash.Snark.Soundness.Composition.ScheduleBudget
import Zcash.Snark.Soundness.AGM.StraightLineFiniteSecurity
import Zcash.Snark.Fixtures.StraightLineMaxShapeBounds
import Zcash.Snark.Keygen.Certificate
import Zcash.Snark.Soundness.Action.StraightLineEvent
import Zcash.Snark.Soundness.Action.StraightLineBudgets
import Zcash.Snark.Soundness.Action.AdaptiveEvent

/-!
# Exact Action soundness and knowledge-soundness capstones

Captured checks and executable terminals yield ordinary- and knowledge-soundness bounds for every
consensus-valid Action bundle size.
-/

namespace Zcash.Snark.Fixture

open Zcash.Snark CompPoly.CPolynomial
open Zcash.Snark.ActionTerminal
open Zcash.Snark.Keygen (actionProofParams actionProofParamsFor
  actionCircuitShape_eq_fixtureCircuitShape actionShapeFor_eq_fixtureShape
  actionShape_eq_fixtureShape vk_eq_toVerifierKey)
open Zcash.Circuits Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder URS)
open scoped ENNReal

private theorem actionProofShape_eq_maxShape (numProofs : ℕ) :
    actionCircuit.shape.withProofParams (actionProofParamsFor numProofs) =
      Zcash.Snark.FixtureMax.shape numProofs := by
  rw [actionShapeFor_eq_fixtureShape]
  rfl

/-! ## Exact false-statement events -/

/-- **The exact public Action-soundness event.**  The deployed verifier accepts while the Orchard
Action bundle statement at its supplied public inputs is false. -/
def actionAcceptFalseStatementEvent
    (family : ComputedStraightLineDeployedFSFamily
      (actionCircuit.shape.withProofParams actionProofParams))
    (inputs : Fin actionProofParams.numProofs →
      PublicInputs Fp) :
    Set ((AugmentedIndex actionCircuit.n → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams actionProofParams) family.init.length 10
          + 3 * actionCircuit.domainExponent) → Fp)) :=
  family.straightLineConstraintSemanticFailureEvent
    (topLevelBundleStatementDecoded actionCircuit actionProofParams family inputs)

/-- Literal accepting-false-`BundleStatement` event at an arbitrary Action bundle size. -/
def actionAcceptFalseStatementEventFor (numProofs : ℕ)
    (family : ComputedStraightLineDeployedFSFamily
      (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)))
    (inputs : Fin (actionProofParamsFor numProofs).numProofs →
      PublicInputs Fp) :
    Set ((AugmentedIndex
      actionCircuit.n → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
          family.init.length 10 +
          3 * actionCircuit.domainExponent) → Fp)) :=
  family.straightLineConstraintSemanticFailureEvent
    (topLevelBundleStatementDecoded actionCircuit (actionProofParamsFor numProofs) family inputs)

/-! ## The derived key's captured scalars -/

/-- Field projections commute with the shape cast when the field's type does not mention the
shape. -/
private theorem castVk_field {s₁ s₂ : CircuitShape} (h : s₁ = s₂)
    (K : VerifyingKey s₁ Fp VestaG) :
    K.omega = (h ▸ K : VerifyingKey s₂ Fp VestaG).omega ∧
    K.n = (h ▸ K : VerifyingKey s₂ Fp VestaG).n ∧
    K.gates = (h ▸ K : VerifyingKey s₂ Fp VestaG).gates ∧
    K.instanceQueryLayout = (h ▸ K : VerifyingKey s₂ Fp VestaG).instanceQueryLayout ∧
    K.adviceQueryLayout = (h ▸ K : VerifyingKey s₂ Fp VestaG).adviceQueryLayout ∧
    K.fixedQueryLayout = (h ▸ K : VerifyingKey s₂ Fp VestaG).fixedQueryLayout ∧
    K.permutationChunks = (h ▸ K : VerifyingKey s₂ Fp VestaG).permutationChunks := by
  cases h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Lookup-expression projections commute with the shape cast, up to the index cast. -/
private theorem castVk_lookup {s₁ s₂ : CircuitShape} (h : s₁ = s₂)
    (K : VerifyingKey s₁ Fp VestaG) (l : Fin s₁.numLookups) :
    K.lookupInputExprs l =
      (h ▸ K : VerifyingKey s₂ Fp VestaG).lookupInputExprs
        (Fin.cast (congrArg CircuitShape.numLookups h) l) ∧
    K.lookupTableExprs l =
      (h ▸ K : VerifyingKey s₂ Fp VestaG).lookupTableExprs
        (Fin.cast (congrArg CircuitShape.numLookups h) l) := by
  cases h
  exact ⟨rfl, rfl⟩

/-- **The Action circuit carries the captured scalar data.** The scalar fields do not depend on
the proof parameters or URS; the keygen certificate pins their circuit-owned values to the
capture. -/
theorem derived_scalars :
    actionCircuit.omega = vk.omega ∧
    actionCircuit.n = vk.n ∧
    actionCircuit.verifierCS.gates = vk.gates ∧
    actionCircuit.instanceQueryLayout =
      vk.instanceQueryLayout ∧
    actionCircuit.adviceQueryLayout =
      vk.adviceQueryLayout ∧
    actionCircuit.fixedQueryLayout =
      vk.fixedQueryLayout ∧
    actionCircuit.verifierCS.permutationChunks =
      vk.permutationChunks := by
  have hcast := castVk_field actionCircuitShape_eq_fixtureCircuitShape
    (actionCircuit.toVerifierKey capturedURS)
  simp only [actionCircuit.toVerifierKey_omega, actionCircuit.toVerifierKey_n,
    actionCircuit.toVerifierKey_gates, actionCircuit.toVerifierKey_instanceQueryLayout,
    actionCircuit.toVerifierKey_adviceQueryLayout, actionCircuit.toVerifierKey_fixedQueryLayout,
    actionCircuit.toVerifierKey_permutationChunks] at hcast
  have hvk : (actionCircuitShape_eq_fixtureCircuitShape ▸
      actionCircuit.toVerifierKey capturedURS :
      VerifyingKey shape Fp VestaG) = vk := vk_eq_toVerifierKey.symm
  exact ⟨hcast.1.trans (congrArg VerifyingKey.omega hvk),
    hcast.2.1.trans (congrArg VerifyingKey.n hvk),
    hcast.2.2.1.trans (congrArg VerifyingKey.gates hvk),
    hcast.2.2.2.1.trans (congrArg VerifyingKey.instanceQueryLayout hvk),
    hcast.2.2.2.2.1.trans (congrArg VerifyingKey.adviceQueryLayout hvk),
    hcast.2.2.2.2.2.1.trans (congrArg VerifyingKey.fixedQueryLayout hvk),
    hcast.2.2.2.2.2.2.trans (congrArg VerifyingKey.permutationChunks hvk)⟩

private theorem action_numLookups_eq :
    actionCircuit.lookupCount =
      shape.numLookups := by
  simpa only [actionCircuit.shape_numLookups] using
    congrArg CircuitShape.numLookups actionCircuitShape_eq_fixtureCircuitShape

/-- The circuit-owned lookup expressions are the captured ones, up to the index cast. -/
theorem derived_lookups
    (l : Fin actionCircuit.lookupCount) :
    actionCircuit.verifierCS.lookupInputExprs l =
      vk.lookupInputExprs (Fin.cast action_numLookups_eq l) ∧
    actionCircuit.verifierCS.lookupTableExprs l =
      vk.lookupTableExprs (Fin.cast action_numLookups_eq l) := by
  have hcast := castVk_lookup actionCircuitShape_eq_fixtureCircuitShape
    (actionCircuit.toVerifierKey capturedURS) l
  simp only [actionCircuit.toVerifierKey_lookupInputExprs,
    actionCircuit.toVerifierKey_lookupTableExprs] at hcast
  have hvk : (actionCircuitShape_eq_fixtureCircuitShape ▸
      actionCircuit.toVerifierKey capturedURS :
      VerifyingKey shape Fp VestaG) = vk := vk_eq_toVerifierKey.symm
  constructor
  · exact hcast.1.trans (by
      rw [hvk]
      exact congrArg vk.lookupInputExprs (Fin.ext (by simp)))
  · exact hcast.2.trans (by
      rw [hvk]
      exact congrArg vk.lookupTableExprs (Fin.ext (by simp)))

/-! ## The captured checks and schedule at the derived shape -/

/-- The derived shape's count fields are the captured ones. -/
private theorem md_counts :
    actionCircuit.domainExponent = shape.k ∧
    actionCircuit.adviceQueryCount =
      shape.numAdviceQueries ∧
    actionCircuit.instanceQueryCount =
      shape.numInstanceQueries ∧
    actionCircuit.fixedQueryCount =
      shape.numFixedQueries ∧
    actionCircuit.quotientPieceCount =
      shape.numQuotientPieces :=
  ⟨by simpa only [CircuitShape.withProofParams_k, actionCircuit.shape_k] using
      congrArg (fun proofShape : Shape => proofShape.k) actionShape_eq_fixtureShape,
    by simpa only [CircuitShape.withProofParams_numAdviceQueries,
        actionCircuit.shape_numAdviceQueries] using
      congrArg (fun proofShape : Shape => proofShape.numAdviceQueries)
        actionShape_eq_fixtureShape,
    by simpa only [CircuitShape.withProofParams_numInstanceQueries,
        actionCircuit.shape_numInstanceQueries] using
      congrArg (fun proofShape : Shape => proofShape.numInstanceQueries)
        actionShape_eq_fixtureShape,
    by simpa only [CircuitShape.withProofParams_numFixedQueries,
        actionCircuit.shape_numFixedQueries] using
      congrArg (fun proofShape : Shape => proofShape.numFixedQueries)
        actionShape_eq_fixtureShape,
    by simpa only [CircuitShape.withProofParams_numQuotientPieces,
        actionCircuit.shape_numQuotientPieces] using
      congrArg (fun proofShape : Shape => proofShape.numQuotientPieces)
        actionShape_eq_fixtureShape⟩

private theorem action_domainExponent_eq :
    actionCircuit.domainExponent = 11 := by
  simpa [shape] using md_counts.1

/-- **The captured static checks at the derived key** (issue #128 F3): the five decided facts,
transferred through the derived key's scalar equalities. -/
theorem staticChecks_of_derived
    (family : ComputedStraightLineDeployedFSFamily
      (actionCircuit.shape.withProofParams actionProofParams))
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey
      (ursOfAugmentedBasis actionCircuit.domainExponent basis)) :
    DeployedConstraintStaticChecks family.toRootFamily where
  adviceLength := fun basis => by
    rw [hvk basis, actionCircuit.toVerifierKey_adviceQueryLayout,
      CircuitShape.withProofParams_numAdviceQueries]
    exact Nat.le_refl _
  instanceLength := fun basis => by
    rw [hvk basis, actionCircuit.toVerifierKey_instanceQueryLayout,
      CircuitShape.withProofParams_numInstanceQueries]
    exact Nat.le_refl _
  fixedLength := fun basis => by
    rw [hvk basis, actionCircuit.toVerifierKey_fixedQueryLayout,
      CircuitShape.withProofParams_numFixedQueries]
    exact Nat.le_refl _
  omegaOrder := fun basis => by
    rw [hvk basis, actionCircuit.toVerifierKey_omega,
      actionCircuit.toVerifierKey_n]
    exact TopLevelAssignment.domainRoot
      ActionPermutationDomain.domainExponent_lt
  characteristic := fun basis => by
    rw [hvk basis, actionCircuit.toVerifierKey_n]
    exact TopLevelAssignment.domainSizeCastNeZero
      ActionPermutationDomain.domainExponent_lt

/-- **The captured `x`-squeeze schedule at the derived key** (issue #128 F3): the degree caps
transfer through the scalar equalities, and pinning is the family's own derived projection. -/
def schedule_of_derived
    (family : ComputedStraightLineDeployedFSFamily
      (actionCircuit.shape.withProofParams actionProofParams))
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey
      (ursOfAugmentedBasis actionCircuit.domainExponent basis)) :
    DeployedConstraintXSqueezeSchedule family.toRootFamily
      ((20470 : ℕ) / (Fintype.card Fp : ℝ≥0∞)) := by
  have hk : actionCircuit.n - 1 = 2047 := by
    rw [actionCircuit.n_eq_two_pow_domainExponent, md_counts.1]
    norm_num [shape]
  have h := deployedConstraintXSqueezeSchedule_of_pinned family.toRootFamily
    (B := 2047) (W := 7) (Dc := 8188) (D := 20470) (Dq := 20470)
    (by norm_num) (le_of_eq hk)
    (fun basis => by
      rw [hvk basis, actionCircuit.toVerifierKey_n, hk])
    (fun basis => by
      rw [hvk basis, actionCircuit.toVerifierKey_gates,
        derived_scalars.2.2.1]
      exact vk_gates_degree_le)
    (fun basis => by
      rw [hvk basis, actionCircuit.toVerifierKey_permutationChunks,
        derived_scalars.2.2.2.2.2.2]
      exact vk_chunk_width_le)
    (fun basis l => by
      rw [hvk basis, actionCircuit.toVerifierKey_lookupInputExprs,
        (derived_lookups l).1]
      exact vk_lookup_input_degree_le _)
    (fun basis l => by
      rw [hvk basis, actionCircuit.toVerifierKey_lookupTableExprs,
        (derived_lookups l).2]
      exact vk_lookup_table_degree_le _)
    (fun basis => by
      rw [hvk basis, actionCircuit.toVerifierKey_n,
        CircuitShape.withProofParams_numQuotientPieces,
        actionCircuit.shape_numQuotientPieces,
        md_counts.2.2.2.2, ← hk,
        actionCircuit.n_eq_two_pow_domainExponent, md_counts.1]
      exact vk_quotient_tail_le)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    family.constraintXTrace.toPinning
  simpa using h

private theorem md_counts_for (numProofs : ℕ) :
    actionCircuit.domainExponent = shape.k ∧
    actionCircuit.adviceQueryCount =
      shape.numAdviceQueries ∧
    actionCircuit.instanceQueryCount =
      shape.numInstanceQueries ∧
    actionCircuit.fixedQueryCount =
      shape.numFixedQueries ∧
    actionCircuit.quotientPieceCount =
      shape.numQuotientPieces := by
  have h := actionShapeFor_eq_fixtureShape numProofs
  exact
    ⟨by simpa only [CircuitShape.withProofParams_k, actionCircuit.shape_k] using
        congrArg (fun proofShape : Shape => proofShape.k) h,
      by simpa only [CircuitShape.withProofParams_numAdviceQueries,
          actionCircuit.shape_numAdviceQueries] using
        congrArg (fun proofShape : Shape => proofShape.numAdviceQueries) h,
      by simpa only [CircuitShape.withProofParams_numInstanceQueries,
          actionCircuit.shape_numInstanceQueries] using
        congrArg (fun proofShape : Shape => proofShape.numInstanceQueries) h,
      by simpa only [CircuitShape.withProofParams_numFixedQueries,
          actionCircuit.shape_numFixedQueries] using
        congrArg (fun proofShape : Shape => proofShape.numFixedQueries) h,
      by simpa only [CircuitShape.withProofParams_numQuotientPieces,
          actionCircuit.shape_numQuotientPieces] using
        congrArg (fun proofShape : Shape => proofShape.numQuotientPieces) h⟩

/-- The captured static checks transported to an arbitrary Action bundle size. -/
theorem staticChecks_of_derived_for (numProofs : ℕ)
    (family : ComputedStraightLineDeployedFSFamily
      (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)))
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis)) :
    DeployedConstraintStaticChecks family.toRootFamily where
  adviceLength := fun basis => by
    rw [hvk basis, actionCircuit.toVerifierKey_adviceQueryLayout,
      CircuitShape.withProofParams_numAdviceQueries]
    exact Nat.le_refl _
  instanceLength := fun basis => by
    rw [hvk basis, actionCircuit.toVerifierKey_instanceQueryLayout,
      CircuitShape.withProofParams_numInstanceQueries]
    exact Nat.le_refl _
  fixedLength := fun basis => by
    rw [hvk basis, actionCircuit.toVerifierKey_fixedQueryLayout,
      CircuitShape.withProofParams_numFixedQueries]
    exact Nat.le_refl _
  omegaOrder := fun basis => by
    rw [hvk basis, actionCircuit.toVerifierKey_omega,
      actionCircuit.toVerifierKey_n]
    exact TopLevelAssignment.domainRoot
      ActionPermutationDomain.domainExponent_lt
  characteristic := fun basis => by
    rw [hvk basis, actionCircuit.toVerifierKey_n]
    exact TopLevelAssignment.domainSizeCastNeZero
      ActionPermutationDomain.domainExponent_lt

/-- The captured `x`-squeeze schedule transported to an arbitrary Action bundle size. -/
def schedule_of_derived_for (numProofs : ℕ)
    (family : ComputedStraightLineDeployedFSFamily
      (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)))
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis)) :
    DeployedConstraintXSqueezeSchedule family.toRootFamily
      ((20470 : ℕ) / (Fintype.card Fp : ℝ≥0∞)) := by
  have hk : actionCircuit.n - 1 =
      2047 := by
    rw [actionCircuit.n_eq_two_pow_domainExponent,
      (md_counts_for numProofs).1]
    norm_num [shape]
  have h := deployedConstraintXSqueezeSchedule_of_pinned family.toRootFamily
    (B := 2047) (W := 7) (Dc := 8188) (D := 20470) (Dq := 20470)
    (by norm_num) (le_of_eq hk)
    (fun basis => by
      rw [hvk basis, actionCircuit.toVerifierKey_n, hk])
    (fun basis => by
      rw [hvk basis, actionCircuit.toVerifierKey_gates,
        derived_scalars.2.2.1]
      exact vk_gates_degree_le)
    (fun basis => by
      rw [hvk basis, actionCircuit.toVerifierKey_permutationChunks,
        derived_scalars.2.2.2.2.2.2]
      exact vk_chunk_width_le)
    (fun basis l => by
      rw [hvk basis, actionCircuit.toVerifierKey_lookupInputExprs,
        (derived_lookups l).1]
      exact vk_lookup_input_degree_le _)
    (fun basis l => by
      rw [hvk basis, actionCircuit.toVerifierKey_lookupTableExprs,
        (derived_lookups l).2]
      exact vk_lookup_table_degree_le _)
    (fun basis => by
      rw [hvk basis, actionCircuit.toVerifierKey_n,
        CircuitShape.withProofParams_numQuotientPieces,
        actionCircuit.shape_numQuotientPieces,
        (md_counts_for numProofs).2.2.2.2, ← hk,
        actionCircuit.n_eq_two_pow_domainExponent,
        (md_counts_for numProofs).1]
      exact vk_quotient_tail_le)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    family.constraintXTrace.toPinning
  simpa using h

/-! ## The sequential endpoint: every semantic budget discharged and counted

Captured counting caps transfer to the derived key and discharge every sequential semantic
budget.
-/

theorem actionLookupActivationCount_le :
    (operationEnabledLookups actionCircuit.operations 0).length ≤ 2 ^ 12 := by
  native_decide

theorem actionLookupInputArity_le :
    ∀ i : Fin (operationEnabledLookups actionCircuit.operations 0).length,
      ((operationEnabledLookups actionCircuit.operations 0).get i).argument.inputs.length ≤ 4 := by
  native_decide

/-- The exact per-Action permutation-cell count.  Unlike the old `2^16` envelope, this
tight value keeps the consensus-maximum β budget below `2^46`. -/
theorem resolverPermutationCell_card_eq
    (pp : ProofParams) (urs : URS VestaG)
    (poly : CommitmentId → CPoly)
    (p : Fin pp.numProofs) :
    Fintype.card
        (ResolverPermutationCell (actionCircuit.toVerifierKey urs) poly p actionActiveRows) =
      30630 := by
  rw [resolverPermutationCell_card]
  rw [actionCircuit.shape_numPermutationSets]
  rw [actionCircuit.toVerifierKey_permutationChunks,
    derived_scalars.2.2.2.2.2.2]
  rw [show actionCircuit.permutationSetCount = shape.numPermutationSets by
    simpa only [actionCircuit.shape_numPermutationSets] using
      congrArg CircuitShape.numPermutationSets
        actionCircuitShape_eq_fixtureCircuitShape]
  clear p poly urs pp
  native_decide

private theorem resolverPermutationCell_card_le
    (pp : ProofParams) (urs : URS VestaG)
    (poly : CommitmentId → CPoly)
    (p : Fin pp.numProofs) :
    Fintype.card
        (ResolverPermutationCell (actionCircuit.toVerifierKey urs) poly p actionActiveRows) ≤
      2 ^ 16 := by
  rw [resolverPermutationCell_card_eq pp urs poly p]
  norm_num

/-- The θ budget is linear in the number of Actions. -/
private theorem cap_theta_for (numProofs : ℕ) :
    ∀ (basis : AugmentedIndex
        actionCircuit.n → VestaG)
      (poly : CommitmentId → CPoly),
      TopLevelLookup.thetaBudget actionCircuit
        (actionProofParamsFor numProofs)
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) poly ≤
        numProofs * 2 ^ 25 := by
  intro basis poly
  rw [TopLevelLookup.thetaBudget_eq]
  calc
    ∑ index : TopLevelLookup.ActivationIndex
          actionCircuit (actionProofParamsFor numProofs),
        actionCircuit.usableRowsAt actionCircuit.domainExponent *
          ((operationEnabledLookups actionCircuit.operations 0).get
            index.2).argument.inputs.length
      ≤ ∑ _index : TopLevelLookup.ActivationIndex
          actionCircuit (actionProofParamsFor numProofs), 2 ^ 11 * 4 := by
        gcongr with index
        · change actionActiveRows ≤ 2 ^ 11
          have hrows : actionActiveRows ≤ actionCircuit.n := by
            simpa only [actionDomainSize] using actionActiveRows_le_domainSize
          rw [actionCircuit.n_eq_two_pow_domainExponent,
            action_domainExponent_eq] at hrows
          norm_num at hrows ⊢
          exact hrows
        · exact actionLookupInputArity_le index.2
    _ ≤ numProofs * 2 ^ 25 := by
        simp only [TopLevelLookup.ActivationIndex,
          Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]
        have hscaled :
            (operationEnabledLookups actionCircuit.operations 0).length *
                (2 ^ 11 * 4) ≤ 2 ^ 25 := by
          calc
            (operationEnabledLookups actionCircuit.operations 0).length * (2 ^ 11 * 4)
                ≤ 2 ^ 12 * (2 ^ 11 * 4) :=
              Nat.mul_le_mul_right _ actionLookupActivationCount_le
            _ = 2 ^ 25 := by norm_num
        simpa only [CircuitShape.withProofParams, actionProofParamsFor,
          Nat.cast_id, _root_.mul_assoc] using Nat.mul_le_mul_left numProofs hscaled

/-- The tight β budget is `950835027` per Action, including permutation cells and all three
lookup arguments. -/
private theorem cap_beta_for (numProofs : ℕ) :
    ∀ (basis : AugmentedIndex
        actionCircuit.n → VestaG)
      (poly : CommitmentId → CPoly),
      (∑ p : Fin (actionProofParamsFor numProofs).numProofs,
        (Fintype.card (ResolverPermutationCell
            (vkAt basis) poly p actionActiveRows) + 1) *
          Fintype.card (ResolverPermutationCell
            (vkAt basis) poly p actionActiveRows)) +
      (actionProofParamsFor numProofs).numProofs *
        actionCircuit.lookupCount *
        ((actionCircuit.n -
              actionCircuit.blindingFactors - 2 + 2) *
            (actionCircuit.n -
              actionCircuit.blindingFactors - 2 + 1) +
          (actionCircuit.n -
            actionCircuit.blindingFactors - 2 + 1)) ≤
        numProofs * 950835027 := by
  intro basis poly
  let pp := actionProofParamsFor numProofs
  let urs := ursOfAugmentedBasis actionCircuit.domainExponent basis
  have hcell : ∀ p : Fin pp.numProofs,
      Fintype.card (ResolverPermutationCell (vkAt basis) poly p actionActiveRows) =
        30630 := by
    intro p
    exact resolverPermutationCell_card_eq pp urs poly p
  have hn : actionCircuit.n = 2 ^ 11 := by
    rw [actionCircuit.n_eq_two_pow_domainExponent,
      action_domainExponent_eq]
  have hu : actionCircuit.n - actionCircuit.blindingFactors - 2 ≤ 2 ^ 11 := by
    omega
  change
    (∑ p : Fin pp.numProofs,
      (Fintype.card (ResolverPermutationCell (vkAt basis) poly p actionActiveRows) + 1) *
        Fintype.card (ResolverPermutationCell (vkAt basis) poly p actionActiveRows)) +
      pp.numProofs *
        actionCircuit.lookupCount *
        ((actionCircuit.n - actionCircuit.blindingFactors - 2 + 2) *
            (actionCircuit.n - actionCircuit.blindingFactors - 2 + 1) +
          (actionCircuit.n - actionCircuit.blindingFactors - 2 + 1)) ≤
      numProofs * 950835027
  calc
    _ ≤ (∑ _p : Fin pp.numProofs,
          (30630 + 1) * 30630) +
        pp.numProofs *
          actionCircuit.lookupCount *
          ((2 ^ 11 + 2) * (2 ^ 11 + 1) + (2 ^ 11 + 1)) := by
      gcongr with p
      all_goals rw [hcell p]
    _ = numProofs * 950835027 := by
      have hproofs : pp.numProofs = numProofs := by
        rfl
      have hlookups : actionCircuit.lookupCount = 3 := by
        rw [action_numLookups_eq]
        norm_num [shape]
      rw [hproofs, hlookups]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_id]
      omega

/-- The tight γ budget is `73554` per Action. -/
private theorem cap_gamma_for (numProofs : ℕ) :
    ∀ (basis : AugmentedIndex
        actionCircuit.n → VestaG)
      (poly : CommitmentId → CPoly),
      (∑ p : Fin (actionProofParamsFor numProofs).numProofs,
        2 * Fintype.card (ResolverPermutationCell
          (vkAt basis) poly p actionActiveRows)) +
      (actionProofParamsFor numProofs).numProofs *
        actionCircuit.lookupCount *
        (2 * (actionCircuit.n -
          actionCircuit.blindingFactors - 2 + 1)) ≤
        numProofs * 73554 := by
  intro basis poly
  let pp := actionProofParamsFor numProofs
  let urs := ursOfAugmentedBasis actionCircuit.domainExponent basis
  have hcell : ∀ p : Fin pp.numProofs,
      Fintype.card (ResolverPermutationCell (vkAt basis) poly p actionActiveRows) =
        30630 := by
    intro p
    exact resolverPermutationCell_card_eq pp urs poly p
  have hn : actionCircuit.n = 2 ^ 11 := by
    rw [actionCircuit.n_eq_two_pow_domainExponent,
      action_domainExponent_eq]
  have hu : actionCircuit.n - actionCircuit.blindingFactors - 2 ≤ 2 ^ 11 := by
    omega
  change
    (∑ p : Fin pp.numProofs,
      2 * Fintype.card (ResolverPermutationCell (vkAt basis) poly p actionActiveRows)) +
      pp.numProofs *
        actionCircuit.lookupCount *
        (2 * (actionCircuit.n - actionCircuit.blindingFactors - 2 + 1)) ≤
      numProofs * 73554
  calc
    _ ≤ (∑ _p : Fin pp.numProofs, 2 * 30630) +
        pp.numProofs *
          actionCircuit.lookupCount * (2 * (2 ^ 11 + 1)) := by
      gcongr with p
      all_goals rw [hcell p]
    _ = numProofs * 73554 := by
      have hproofs : pp.numProofs = numProofs := by
        rfl
      have hlookups : actionCircuit.lookupCount = 3 := by
        rw [action_numLookups_eq]
        norm_num [shape]
      rw [hproofs, hlookups]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_id]
      omega

private theorem cap_theta :
    ∀ (basis : AugmentedIndex actionCircuit.n → VestaG)
      (poly : CommitmentId → CPoly),
      TopLevelLookup.thetaBudget actionCircuit actionProofParams
        (ursOfAugmentedBasis actionCircuit.domainExponent basis) poly ≤
        2 ^ 25 := by
  intro basis poly
  rw [TopLevelLookup.thetaBudget_eq]
  calc
    ∑ index : TopLevelLookup.ActivationIndex
          actionCircuit actionProofParams,
        actionCircuit.usableRowsAt actionCircuit.domainExponent *
          ((operationEnabledLookups actionCircuit.operations 0).get
            index.2).argument.inputs.length
      ≤ ∑ _index : TopLevelLookup.ActivationIndex
          actionCircuit actionProofParams, 2 ^ 11 * 4 := by
        gcongr with index
        · change actionActiveRows ≤ 2 ^ 11
          have hrows : actionActiveRows ≤ actionCircuit.n := by
            simpa only [actionDomainSize] using actionActiveRows_le_domainSize
          rw [actionCircuit.n_eq_two_pow_domainExponent,
            action_domainExponent_eq] at hrows
          norm_num at hrows ⊢
          exact hrows
        · exact actionLookupInputArity_le index.2
    _ ≤ 2 ^ 25 := by
        simp only [TopLevelLookup.ActivationIndex,
          Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]
        have hscaled :
            (operationEnabledLookups actionCircuit.operations 0).length *
                (2 ^ 11 * 4) ≤ 2 ^ 25 := by
          calc
            (operationEnabledLookups actionCircuit.operations 0).length * (2 ^ 11 * 4)
                ≤ 2 ^ 12 * (2 ^ 11 * 4) :=
              Nat.mul_le_mul_right _ actionLookupActivationCount_le
            _ = 2 ^ 25 := by norm_num
        simpa only [CircuitShape.withProofParams, actionProofParams, actionProofParamsFor,
          _root_.one_mul, Nat.cast_id] using hscaled

private theorem cap_beta :
    ∀ (basis : AugmentedIndex actionCircuit.n → VestaG)
      (poly : CommitmentId → CPoly),
      (∑ p : Fin actionProofParams.numProofs,
        (Fintype.card (ResolverPermutationCell (vkAt basis) poly p
            actionActiveRows) + 1) *
          Fintype.card (ResolverPermutationCell (vkAt basis) poly p
            actionActiveRows)) +
      actionProofParams.numProofs *
        actionCircuit.lookupCount *
        ((actionCircuit.n - actionCircuit.blindingFactors -
              2 + 2) *
            (actionCircuit.n - actionCircuit.blindingFactors -
              2 + 1) +
          (actionCircuit.n - actionCircuit.blindingFactors -
            2 + 1)) ≤ 2 ^ 35 := by
  intro basis poly
  let urs := ursOfAugmentedBasis
    actionCircuit.domainExponent basis
  have hcell : ∀ p : Fin actionProofParams.numProofs,
      Fintype.card (ResolverPermutationCell (vkAt basis) poly p
        actionActiveRows) ≤ 2 ^ 16 := by
    intro p
    exact resolverPermutationCell_card_le actionProofParams urs poly p
  have hn : actionCircuit.n = 2 ^ 11 := by
    rw [actionCircuit.n_eq_two_pow_domainExponent,
      action_domainExponent_eq]
  have hu : actionCircuit.n -
      actionCircuit.blindingFactors - 2 ≤ 2 ^ 11 := by
    omega
  calc
    (∑ p : Fin actionProofParams.numProofs,
        (Fintype.card (ResolverPermutationCell (vkAt basis) poly p
            actionActiveRows) + 1) *
          Fintype.card (ResolverPermutationCell (vkAt basis) poly p
            actionActiveRows)) +
        actionProofParams.numProofs *
          actionCircuit.lookupCount *
          ((actionCircuit.n -
                actionCircuit.blindingFactors - 2 + 2) *
              (actionCircuit.n -
                actionCircuit.blindingFactors - 2 + 1) +
            (actionCircuit.n -
              actionCircuit.blindingFactors - 2 + 1))
        ≤
      (∑ _p : Fin actionProofParams.numProofs,
          (2 ^ 16 + 1) * 2 ^ 16) +
      actionProofParams.numProofs *
          actionCircuit.lookupCount *
          ((2 ^ 11 + 2) * (2 ^ 11 + 1) + (2 ^ 11 + 1)) := by
      gcongr with p
      all_goals exact hcell p
    _ ≤ 2 ^ 35 := by
      rw [action_numLookups_eq]
      norm_num [actionProofParams, actionProofParamsFor, shape]

private theorem cap_gamma :
    ∀ (basis : AugmentedIndex actionCircuit.n → VestaG)
      (poly : CommitmentId → CPoly),
      (∑ p : Fin actionProofParams.numProofs,
        2 * Fintype.card (ResolverPermutationCell (vkAt basis) poly p
          actionActiveRows)) +
      actionProofParams.numProofs *
        actionCircuit.lookupCount *
        (2 * (actionCircuit.n - actionCircuit.blindingFactors -
          2 + 1)) ≤ 2 ^ 21 := by
  intro basis poly
  let urs := ursOfAugmentedBasis
    actionCircuit.domainExponent basis
  have hcell : ∀ p : Fin actionProofParams.numProofs,
      Fintype.card (ResolverPermutationCell (vkAt basis) poly p
        actionActiveRows) ≤ 2 ^ 16 := by
    intro p
    exact resolverPermutationCell_card_le actionProofParams urs poly p
  have hn : actionCircuit.n = 2 ^ 11 := by
    rw [actionCircuit.n_eq_two_pow_domainExponent,
      action_domainExponent_eq]
  have hu : actionCircuit.n -
      actionCircuit.blindingFactors - 2 ≤ 2 ^ 11 := by
    omega
  calc
    (∑ p : Fin actionProofParams.numProofs,
        2 * Fintype.card (ResolverPermutationCell (vkAt basis) poly p
          actionActiveRows)) +
        actionProofParams.numProofs *
          actionCircuit.lookupCount *
          (2 * (actionCircuit.n -
            actionCircuit.blindingFactors - 2 + 1))
        ≤
      (∑ _p : Fin actionProofParams.numProofs,
          2 * 2 ^ 16) +
      actionProofParams.numProofs *
          actionCircuit.lookupCount *
          (2 * (2 ^ 11 + 1)) := by
      gcongr with p
      all_goals exact hcell p
    _ ≤ 2 ^ 21 := by
      rw [action_numLookups_eq]
      norm_num [actionProofParams, actionProofParamsFor, shape]

private theorem derived_n_ne_zero :
    actionCircuit.n ≠ 0 :=
  actionCircuit.n_ne_zero

private theorem derived_n_yn {L : ℕ} (hL : L ≤ 2 ^ 12) :
    actionCircuit.n * L ≤ 2 ^ 23 := by
  have hn : actionCircuit.n = 2 ^ 11 := by
    rw [actionCircuit.n_eq_two_pow_domainExponent,
      action_domainExponent_eq]
  rw [hn]
  calc 2 ^ 11 * L ≤ 2 ^ 11 * 2 ^ 12 := Nat.mul_le_mul_left _ hL
    _ = 2 ^ 23 := by norm_num

/-- The `y` fold cap is linear in the bundle size once its constraint list is. -/
private theorem derived_n_yn_for (numProofs : ℕ) {L : ℕ}
    (hL : L ≤ numProofs * 2 ^ 12) :
    actionCircuit.n * L ≤
      numProofs * 2 ^ 23 := by
  have hn : actionCircuit.n = 2 ^ 11 := by
    rw [actionCircuit.n_eq_two_pow_domainExponent,
      action_domainExponent_eq]
  rw [hn]
  calc
    2 ^ 11 * L ≤ 2 ^ 11 * (numProofs * 2 ^ 12) := Nat.mul_le_mul_left _ hL
    _ = numProofs * 2 ^ 23 := by
      rw [show (2 : ℕ) ^ 23 = 2 ^ 11 * 2 ^ 12 by norm_num]
      omega

/-- The adaptive Action model has the same captured, shape-determined constraint count for every
prover polynomial assignment. -/
theorem adaptive_action_constraint_count_le
    (basis : AugmentedIndex actionCircuit.n → VestaG)
    (inputs : Fin actionProofParams.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams actionProofParams) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges actionCircuit.domainExponent Fp) :
    (adaptiveActionCommittedModel actionProofParams basis inputs ps source ch).constraints.length
      ≤ 2 ^ 12 := by
  unfold adaptiveActionCommittedModel adaptiveActionCommittedModelOf
    VerifyingKey.constraintModel constraintModelOfResolver
    ConstraintPolyModel.constraints ConstraintPolyModel.subProofConstraints
    ConstraintPolyModel.gateConstraints ConstraintPolyModel.permutationConstraints
    ConstraintPolyModel.lookupConstraints
  simp only [List.length_flatten, permutationExpressions, lookupExpressions,
    permutationChunksOfResolver_length, lookupEntriesOfResolver]
  rw [actionCircuit.toVerifierKey_gates,
    actionCircuit.toVerifierKey_permutationChunks,
    derived_scalars.2.2.1, derived_scalars.2.2.2.2.2.2]
  have hproofs := congrArg Shape.numProofs actionShape_eq_fixtureShape
  have hsets := congrArg (fun proofShape : Shape => proofShape.numPermutationSets)
    actionShape_eq_fixtureShape
  have hlookups := congrArg (fun proofShape : Shape => proofShape.numLookups)
    actionShape_eq_fixtureShape
  norm_num [shape] at hproofs hsets hlookups
  simp [hproofs, hsets, hlookups, permutationSetsOfResolver,
    permutationChunksOfResolver]
  have hm : min vk.permutationChunks.length
      (min 3 actionCircuit.verifierCS.permutationChunks.length) ≤
      vk.permutationChunks.length := Nat.min_le_left _ _
  have hc : vk.gates.length + (vk.permutationChunks.length + 19) ≤ 2 ^ 12 := by
    rw [vk_gates_length, vk_permutationChunks_length]
    norm_num
  omega

/-- The adaptive Action constraint list is linear in the number of bundled Actions. -/
private theorem action_length_flatten_ofFn_le {α : Type*} {n : ℕ}
    (f : Fin n → List α) (c : ℕ) (hf : ∀ i, (f i).length ≤ c) :
    ((List.ofFn f).flatten).length ≤ n * c := by
  rw [List.length_flatten]
  refine le_trans (List.sum_le_card_nsmul _ c ?_) ?_
  · intro m hm
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hm
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    exact hf i
  · rw [List.length_map, List.length_ofFn, smul_eq_mul]

theorem adaptive_action_constraint_count_le_for (numProofs : ℕ)
    (basis : AugmentedIndex
      actionCircuit.n → VestaG)
    (inputs : Fin (actionProofParamsFor numProofs).numProofs →
      PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges actionCircuit.domainExponent Fp) :
    (adaptiveActionCommittedModel (actionProofParamsFor numProofs) basis inputs ps source ch).constraints.length ≤
      numProofs * 2 ^ 12 := by
  unfold ConstraintPolyModel.constraints
  apply action_length_flatten_ofFn_le
  intro p
  unfold adaptiveActionCommittedModel adaptiveActionCommittedModelOf
    VerifyingKey.constraintModel constraintModelOfResolver
    ConstraintPolyModel.subProofConstraints
    ConstraintPolyModel.gateConstraints ConstraintPolyModel.permutationConstraints
    ConstraintPolyModel.lookupConstraints
  simp only [permutationExpressions, lookupExpressions,
    permutationChunksOfResolver_length, lookupEntriesOfResolver]
  rw [actionCircuit.toVerifierKey_gates,
    actionCircuit.toVerifierKey_permutationChunks,
    derived_scalars.2.2.1, derived_scalars.2.2.2.2.2.2]
  have hsets := congrArg (fun proofShape : Shape => proofShape.numPermutationSets)
    (actionShapeFor_eq_fixtureShape numProofs)
  have hlookups := congrArg (fun proofShape : Shape => proofShape.numLookups)
    (actionShapeFor_eq_fixtureShape numProofs)
  norm_num [shape] at hsets hlookups
  simp [hsets, hlookups, permutationSetsOfResolver,
    permutationChunksOfResolver]
  have hm : min vk.permutationChunks.length
      (min 3 actionCircuit.verifierCS.permutationChunks.length) ≤
      vk.permutationChunks.length := Nat.min_le_left _ _
  have hc : vk.gates.length + (vk.permutationChunks.length + 19) ≤ 2 ^ 12 := by
    rw [vk_gates_length, vk_permutationChunks_length]
    norm_num
  omega

/-- The adaptive pre-`x` polynomial is assembled from coordinate vectors of degree below the
captured basis size, so the existing captured degree walk applies without a trace premise. -/
private theorem adaptive_action_x_degree_le_for (numProofs : ℕ)
    (basis : AugmentedIndex
      actionCircuit.n → VestaG)
    (inputs : Fin (actionProofParamsFor numProofs).numProofs →
      PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges actionCircuit.domainExponent Fp) :
    (adaptiveActionPreXDifference (actionProofParamsFor numProofs) basis inputs ps source ch).natDegree ≤
      20470 := by
  let avk := ActionTerminal.vkAt basis
  let ic := actionCircuit.instanceCommitment (ursOfAugmentedBasis
      actionCircuit.domainExponent basis) inputs
  let poly := adaptiveActionCommitmentPolynomial
    (actionProofParamsFor numProofs) basis inputs ps source ch
  have hk : actionCircuit.n - 1 = 2047 := by
    rw [actionCircuit.n_eq_two_pow_domainExponent,
      action_domainExponent_eq]
    norm_num
  have hpoint : ∀ g : VestaG,
      (onlinePointPolynomial
        (shape := actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
        source g).natDegree ≤ 2047 := by
    intro g
    unfold onlinePointPolynomial
    have h := coeffsToPoly_natDegree_lt
      (n := 2 ^ actionCircuit.domainExponent)
      (by positivity)
      (onlinePointCoordinates
        (shape := actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
        source g).1
    have hsize :
        2 ^ actionCircuit.domainExponent = 2048 := by
      rw [action_domainExponent_eq]
      norm_num
    calc
      (onlinePointPolynomial
          (shape := actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
          source g).natDegree ≤ 2 ^ actionCircuit.domainExponent - 1 :=
        Nat.le_sub_one_of_lt h
      _ = 2047 := by rw [hsize]
  have hpoly : ∀ id, (poly id).natDegree ≤ 2047 := by
    intro id
    unfold poly adaptiveActionCommitmentPolynomial
      adaptiveActionCommitmentPolynomialOf adaptiveActionPointPolynomial
    split
    · split
      · exact hpoint _
      · simp
    · simp
  have hresolver : ∀ {n : ℕ} (omega : Fp) (layout : List (ℕ × ℤ))
      (column : ℕ → CPoly),
      (∀ i, (column i).natDegree ≤ 2047) →
      ∀ i, (resolverQueryFeed (n := n) omega layout column i).natDegree ≤ 2047 := by
    intro n omega layout column hcolumn i
    unfold resolverQueryFeed
    split
    · exact natDegree_comp_rotateData_le _ _ (hcolumn _)
    · simp
  have hfixed : ∀ i, (fixedQueryFeedOfResolver avk poly i).natDegree ≤ 2047 :=
    hresolver avk.omega avk.fixedQueryLayout _ (fun _ => hpoly _)
  have hadvice : ∀ p i, (adviceQueryFeedOfResolver avk poly p i).natDegree ≤ 2047 :=
    fun p => hresolver avk.omega avk.adviceQueryLayout _ (fun _ => hpoly _)
  have hinstance : ∀ p i, (instanceQueryFeedOfResolver avk poly p i).natDegree ≤ 2047 :=
    fun p => hresolver avk.omega avk.instanceQueryLayout _ (fun _ => hpoly _)
  have hpermutationColumn :
      ∀ p : Fin (actionProofParamsFor numProofs).numProofs, ∀ cr,
      (permutationColumnPolynomialOfResolver avk poly p cr).natDegree ≤ 2047 := by
    intro p cr
    rcases cr with i | i | i <;>
      simp only [permutationColumnPolynomialOfResolver, ColumnRef.resolve] <;>
      unfold finFn <;> split
    all_goals
      first
      | exact hpoly _
      | simp
  have hnB : actionCircuit.n - 1 ≤ 2047 := by
    rw [derived_scalars.2.1]
    exact vk_n_pred_le
  have hrows : Function.Injective fun i : Fin actionCircuit.n =>
      actionCircuit.omega ^ (i : ℕ) :=
    TopLevelAssignment.domainRowsInjective
      ActionPermutationDomain.domainExponent_lt
  have hblindingVk : avk.blindingFactors < avk.n :=
    actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis
        actionCircuit.domainExponent basis)
  have hn : 0 < actionCircuit.n :=
    Nat.pos_of_ne_zero actionCircuit.n_ne_zero
  have hlookups : ∀ p, ∀ lk ∈ lookupEntriesOfResolver avk poly p,
      (lk.1.productEval.natDegree ≤ 2047 ∧ lk.1.productNextEval.natDegree ≤ 2047 ∧
        lk.1.permutedInputEval.natDegree ≤ 2047 ∧
        lk.1.permutedInputInvEval.natDegree ≤ 2047 ∧
        lk.1.permutedTableEval.natDegree ≤ 2047) ∧
      (∀ e ∈ lk.2.1, e.degreeBound * 2047 ≤ 8188) ∧
      ∀ e ∈ lk.2.2, e.degreeBound * 2047 ≤ 8188 := by
    intro p lk hlk
    obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hlk
    refine ⟨⟨hpoly _, natDegree_comp_rotateData_le _ _ (hpoly _), hpoly _,
      natDegree_comp_rotateData_le _ _ (hpoly _), hpoly _⟩, ?_, ?_⟩
    · dsimp only [avk]
      rw [ActionTerminal.vkAt, actionCircuit.toVerifierKey_lookupInputExprs,
        (derived_lookups l).1]
      exact vk_lookup_input_degree_le _
    · dsimp only [avk]
      rw [ActionTerminal.vkAt, actionCircuit.toVerifierKey_lookupTableExprs,
        (derived_lookups l).2]
      exact vk_lookup_table_degree_le _
  have hmodel :
      adaptiveActionCommittedModel (actionProofParamsFor numProofs) basis inputs ps source ch =
        avk.constraintModel ch poly hblindingVk := by
    rfl
  rw [adaptiveActionPreXDifference_eq]
  rw [hmodel]
  refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
  · apply natDegree_combineConstraints_le (B := 2047) (W := 7)
      (Dc := 8188) (D := 20470)
    · norm_num
    · simpa only [VerifyingKey.constraintModel_fixedCols] using hfixed
    · intro p i
      simpa only [VerifyingKey.constraintModel_adviceCols] using hadvice p i
    · intro p i
      simpa only [VerifyingKey.constraintModel_instanceCols] using hinstance p i
    · have hgates : ∀ e ∈ actionCircuit.verifierCS.gates,
          e.degreeBound * 2047 ≤ 20470 := by
        rw [derived_scalars.2.2.1]
        exact vk_gates_degree_le
      simpa only [VerifyingKey.constraintModel_gates, avk,
        ActionTerminal.vkAt, actionCircuit.toVerifierKey_gates] using hgates
    · intro p s hs
      change s ∈ permutationSetsOfResolver avk poly p at hs
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs
      dsimp only [permutationSetOfResolver]
      refine ⟨hpoly _, ?_⟩
      split
      · simp
      · exact natDegree_comp_rotateData_le _ _ (hpoly _)
    · intro p c hc
      change c ∈ permutationChunksOfResolver avk poly p at hc
      obtain ⟨sc, hsc, rfl⟩ := List.mem_map.mp hc
      obtain ⟨s1, s2⟩ := sc
      obtain ⟨hs1, hs2⟩ := List.of_mem_zip hsc
      dsimp only
      refine ⟨?_, ?_, ?_⟩
      · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hs1
        exact ⟨hpoly _, natDegree_comp_rotateData_le _ _ (hpoly _)⟩
      · dsimp only [avk] at hs2
        rw [ActionTerminal.vkAt, actionCircuit.toVerifierKey_permutationChunks,
          derived_scalars.2.2.2.2.2.2] at hs2
        simpa using vk_chunk_width_le _ hs2
      · intro pr hpr
        obtain ⟨cr, -, hpr'⟩ := List.mem_map.mp hpr
        rw [← hpr']
        exact ⟨hpermutationColumn _ _, hpoly _⟩
    · intro p
      simpa only [VerifyingKey.constraintModel_lookups] using hlookups p
    · simpa only [avk, ActionTerminal.vkAt,
        actionCircuit.toVerifierKey_omega] using
        le_trans (Nat.le_pred_of_lt (by
          simpa [rowSelectorPolynomial] using rowPolynomial_natDegree_lt hrows hn)) hnB
    · simpa only [avk, ActionTerminal.vkAt,
        actionCircuit.toVerifierKey_omega] using
        le_trans (Nat.le_pred_of_lt (by
          simpa [rowSelectorPolynomial] using rowPolynomial_natDegree_lt hrows hn)) hnB
    · simpa only [avk, ActionTerminal.vkAt,
        actionCircuit.toVerifierKey_omega] using
        le_trans (Nat.le_pred_of_lt (by
          simpa [blindSelectorPolynomial] using rowPolynomial_natDegree_lt hrows hn)) hnB
    · norm_num
    · norm_num
    · norm_num
    · norm_num
  · rw [committedPreXQuotient_eq]
    refine le_trans (natDegree_preXQuotient_mul_le (Bq := 2047) _ _ ?_) ?_
    · intro j
      exact hpoint _
    · dsimp only [avk]
      rw [ActionTerminal.vkAt, actionCircuit.toVerifierKey_n,
          derived_scalars.2.1,
        CircuitShape.withProofParams_numQuotientPieces,
        actionCircuit.shape_numQuotientPieces,
        (md_counts_for numProofs).2.2.2.2]
      have hshape : 2 ^ shape.k - 1 = 2047 := by
        norm_num [shape]
      simpa only [hshape] using vk_quotient_tail_le


/-- **The semantic counts at the query ceiling** (issue #128 F7): at `Q ≤ 2^123` the five
counted caps total at most `2^160`. -/
theorem action_semantic_count_le {Q : ℕ} (hQ : Q ≤ 2 ^ 123) :
    (Q + 1) * 20470 + (Q + 1) * 2 ^ 23 + ((Q + 1) * 2 ^ 35 +
      ((Q + 1) * 2 ^ 21 + (Q + 1) * 2 ^ 25)) ≤ 2 ^ 160 := by
  have h1 : 1 ≤ (2 : ℕ) ^ 123 := Nat.one_le_two_pow
  have h2 : (2 : ℕ) ^ 124 = 2 ^ 123 * 2 := pow_succ 2 123
  have hs : (20470 + 2 ^ 23 + (2 ^ 35 + (2 ^ 21 + 2 ^ 25)) : ℕ) ≤ 2 ^ 36 := by norm_num
  have h3 : (2 : ℕ) ^ 160 = 2 ^ 124 * 2 ^ 36 := by rw [← pow_add]
  calc (Q + 1) * 20470 + (Q + 1) * 2 ^ 23 + ((Q + 1) * 2 ^ 35 +
        ((Q + 1) * 2 ^ 21 + (Q + 1) * 2 ^ 25))
      = (Q + 1) * (20470 + 2 ^ 23 + (2 ^ 35 + (2 ^ 21 + 2 ^ 25))) := by ring
    _ ≤ 2 ^ 124 * 2 ^ 36 := Nat.mul_le_mul (by omega) hs
    _ = 2 ^ 160 := h3.symm

/-- The scalar field clears `2^254`: the counted remainder is at most `2^160 / |Fp| ≤ 2^-94`,
ten bits under the compressed model's `2^-84` ceiling. -/
theorem two_pow_254_le_card : 2 ^ 254 ≤ Fintype.card Fp := by
  rw [Zcash.Arithmetic.card_Fp]
  norm_num

/-- The four bundle-linear Action surfaces plus the bundle-independent `x` surface, collapsed to
one numerator.  The coefficient is the exact sum of the proved `y`, `β`, `γ`, and `θ` caps. -/
noncomputable def actionSemanticModelFor (numProofs Q : ℕ) : ENNReal :=
  (((Q + 1) * (20470 + numProofs * 992851621) : ℕ) : ENNReal) /
    Fintype.card Fp

/-- At every consensus-valid Action count and `Q ≤ 2^123`, all five semantic surfaces fit
inside `2^-84`. -/
theorem actionSemanticModelFor_at_2pow123 {numProofs Q : ℕ}
    (hn : numProofs ≤ orchardConsensusMaxProofs) (hQ : Q ≤ 2 ^ 123) :
    actionSemanticModelFor numProofs Q ≤ 1 / (2 ^ 84 : ENNReal) := by
  have hcap : 20470 + numProofs * 992851621 ≤ 2 ^ 46 := by
    calc
      20470 + numProofs * 992851621 ≤
          20470 + orchardConsensusMaxProofs * 992851621 := by omega
      _ ≤ 2 ^ 46 := by norm_num [orchardConsensusMaxProofs]
  have hqueries : Q + 1 ≤ 2 ^ 124 := by
    have hone : 1 ≤ (2 : ℕ) ^ 123 := Nat.one_le_two_pow
    omega
  have hnum : (Q + 1) * (20470 + numProofs * 992851621) ≤ 2 ^ 170 := by
    calc
      (Q + 1) * (20470 + numProofs * 992851621) ≤ 2 ^ 124 * 2 ^ 46 :=
        Nat.mul_le_mul hqueries hcap
      _ = 2 ^ 170 := by rw [← pow_add]
  rw [actionSemanticModelFor]
  calc
    ((((Q + 1) * (20470 + numProofs * 992851621) : ℕ) : ENNReal) /
        Fintype.card Fp) ≤
        ((2 ^ 170 : ℕ) : ENNReal) / Fintype.card Fp := by gcongr
    _ ≤ ((2 ^ 170 : ℕ) : ENNReal) / (2 ^ 254 : ℕ) := by
      gcongr
      exact_mod_cast two_pow_254_le_card
    _ ≤ 1 / (2 ^ 84 : ENNReal) := by
      rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
      rw [show ((2 ^ 254 : ℕ) : ENNReal) =
          (2 ^ 84 : ENNReal) * (2 ^ 170 : ENNReal) by norm_num [← pow_add]]
      rw [div_eq_mul_inv, _root_.one_mul, ← _root_.mul_assoc,
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num), _root_.one_mul]
      norm_num

/-- The compressed straight-line remainder at an arbitrary Action count. -/
noncomputable def actionCompressedStatisticalModelFor (numProofs Q : ℕ) : ENNReal :=
  let shape := actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)
  (Q + 1 : ℕ) * (1 / Fintype.card Fp) +
    (Q + 1 : ℕ) * (actionCircuit.domainExponent * (2 / (Fintype.card Fp : ENNReal))) +
    (Q + (11 + actionCircuit.domainExponent) + 1 : ℕ) *
      algebraicRootBudget shape actionCircuit.domainExponent +
    1 / Fintype.card Fp +
    (Q + 1 : ℕ) * ((20470 : ℕ) / (Fintype.card Fp : ENNReal))

/-- Complete non-DLOG remainder for an `numProofs`-Action bundle. -/
noncomputable def actionStatisticalModelFor (numProofs Q : ℕ) : ENNReal :=
  actionCompressedStatisticalModelFor numProofs Q + actionSemanticModelFor numProofs Q

/-- The bare-adaptive remainder at an arbitrary Action count.  It has the same four
bundle-linear semantic terms and one `x` term, but only one execution of the pinned-root surface. -/
noncomputable def adaptiveActionStatisticalModelFor (numProofs Q : ℕ) : ENNReal :=
  let shape := actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)
  (Q + 1 : ℕ) * (1 / Fintype.card Fp) +
    (Q + 1 : ℕ) * (actionCircuit.domainExponent * (2 / (Fintype.card Fp : ENNReal))) +
    (Q + 1 : ℕ) * algebraicRootBudget shape actionCircuit.domainExponent +
    1 / Fintype.card Fp +
    actionSemanticModelFor numProofs Q

/-- The sequential statistical model safely upper-bounds the bare-adaptive one: it reserves the
larger pinned-root coefficient and an additional compressed-constraint `x` term. -/
private theorem adaptiveActionStatisticalModelFor_le_action (numProofs Q : ℕ) :
    adaptiveActionStatisticalModelFor numProofs Q ≤
      actionStatisticalModelFor numProofs Q := by
  let shape := actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)
  have hcoeff : ((Q + 1 : ℕ) : ENNReal) ≤
      ((Q + (11 + actionCircuit.domainExponent) + 1 : ℕ) : ENNReal) := by
    exact Nat.cast_le.mpr (by omega)
  have hroot :
      (Q + 1 : ℕ) * algebraicRootBudget shape actionCircuit.domainExponent ≤
        (Q + (11 + actionCircuit.domainExponent) + 1 : ℕ) *
          algebraicRootBudget shape actionCircuit.domainExponent := by
    exact mul_le_mul_left hcoeff (algebraicRootBudget shape actionCircuit.domainExponent)
  unfold adaptiveActionStatisticalModelFor actionStatisticalModelFor
    actionCompressedStatisticalModelFor
  dsimp only
  let a : ENNReal :=
    (Q + 1 : ℕ) * (1 / Fintype.card Fp) +
      (Q + 1 : ℕ) *
        (actionCircuit.domainExponent * (2 / (Fintype.card Fp : ENNReal)))
  let e : ENNReal := 1 / Fintype.card Fp
  let x : ENNReal :=
    (Q + 1 : ℕ) * ((20470 : ℕ) / (Fintype.card Fp : ENNReal))
  let s : ENNReal := actionSemanticModelFor numProofs Q
  change a + (Q + 1 : ℕ) * algebraicRootBudget shape actionCircuit.domainExponent + e + s ≤
    a + (Q + (11 + actionCircuit.domainExponent) + 1 : ℕ) *
      algebraicRootBudget shape actionCircuit.domainExponent + e + x + s
  calc
    _ ≤ a + (Q + (11 + actionCircuit.domainExponent) + 1 : ℕ) *
          algebraicRootBudget shape actionCircuit.domainExponent + e + s :=
      add_le_add_left (add_le_add_left (add_le_add_right hroot a) e) s
    _ ≤ _ := add_le_add_left
      (le_add_of_nonneg_right (show 0 ≤ x from bot_le)) s

private theorem actionCompressedStatisticalModelFor_le_consensus
    {numProofs Q : ℕ} (hn : numProofs ≤ orchardConsensusMaxProofs)
    (hQ : Q ≤ 2 ^ 123) :
    actionCompressedStatisticalModelFor numProofs Q ≤
      Zcash.Snark.FixtureMax.consensusStraightLineStatisticalModel (2 ^ 123) := by
  have hk : actionCircuit.domainExponent = 11 := by
    exact action_domainExponent_eq
  have hroot :
      algebraicRootBudget
          (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)) 11 ≤
        algebraicRootBudget
          (Zcash.Snark.FixtureMax.shape orchardConsensusMaxProofs) 11 := by
    rw [actionProofShape_eq_maxShape]
    exact Zcash.Snark.FixtureMax.algebraicRootBudget_at_captured_shape_le_consensus_max hn
  rw [actionCompressedStatisticalModelFor,
    Zcash.Snark.FixtureMax.consensusStraightLineStatisticalModel,
    Zcash.Snark.FixtureMax.consensusPinnedRootMultiopenModel,
    hk]
  gcongr
  all_goals first | exact hroot | assumption_mod_cast | norm_num

/-- Consensus-valid bundles retain the `2^123` work target with a conservative `2^-83`
statistical remainder: one `2^-84` compressed term plus one `2^-84` semantic term. -/
theorem actionStatisticalModelFor_at_2pow123 {numProofs Q : ℕ}
    (hn : numProofs ≤ orchardConsensusMaxProofs) (hQ : Q ≤ 2 ^ 123) :
    actionStatisticalModelFor numProofs Q ≤ 1 / (2 ^ 83 : ENNReal) := by
  calc
    actionStatisticalModelFor numProofs Q =
        actionCompressedStatisticalModelFor numProofs Q +
          actionSemanticModelFor numProofs Q := rfl
    _ ≤ Zcash.Snark.FixtureMax.consensusStraightLineStatisticalModel (2 ^ 123) +
        1 / (2 ^ 84 : ENNReal) :=
      add_le_add (actionCompressedStatisticalModelFor_le_consensus hn hQ)
        (actionSemanticModelFor_at_2pow123 hn hQ)
    _ ≤ 1 / (2 ^ 84 : ENNReal) + 1 / (2 ^ 84 : ENNReal) := by
      gcongr
      exact Zcash.Snark.FixtureMax.consensusStraightLineStatisticalModel_at_2pow123
    _ ≤ 1 / (2 ^ 83 : ENNReal) := by
      rw [ENNReal.div_add_div_same]
      apply (ENNReal.le_div_iff_mul_le (Or.inl (by norm_num))
        (Or.inl (by norm_num))).2
      have h :
          ((1 + 1 : ENNReal) / 2 ^ 84) * 2 ^ 83 =
            ((1 + 1 : ENNReal) * 2 ^ 83) / 2 ^ 84 := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      rw [h]
      apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
      norm_num [← pow_succ]

/-- **The five semantic terms collapse to one count over the field** (issue #128 F7): the
endpoint's added tail is at most `2^160 / |Fp|`, with the count proven at the ceiling and no
absorption assumed. -/
theorem action_semantic_terms_le {Q : ℕ} (hQ : Q ≤ 2 ^ 123) :
    (((Q + 1 : ℕ) : ℝ≥0∞) * (((20470 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) +
        ((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 23 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞))) +
      (((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) +
        (((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 21 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) +
          ((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 25 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞))))
      ≤ ((2 ^ 160 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞) := by
  have hcollapse :
      (((Q + 1 : ℕ) : ℝ≥0∞) * (((20470 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) +
          ((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 23 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞))) +
        (((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 35 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) +
          (((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 21 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)) +
            ((Q + 1 : ℕ) : ℝ≥0∞) * (((2 ^ 25 : ℕ) : ℝ≥0∞) / (Fintype.card Fp : ℝ≥0∞)))) =
        (((Q + 1) * 20470 + (Q + 1) * 2 ^ 23 + ((Q + 1) * 2 ^ 35 +
          ((Q + 1) * 2 ^ 21 + (Q + 1) * 2 ^ 25)) : ℕ) : ℝ≥0∞) /
          (Fintype.card Fp : ℝ≥0∞) := by
    rw [mul_div_assoc', mul_div_assoc', mul_div_assoc', mul_div_assoc', mul_div_assoc',
      ENNReal.div_add_div_same, ENNReal.div_add_div_same, ENNReal.div_add_div_same,
      ENNReal.div_add_div_same]
    norm_cast
  rw [hcollapse]
  gcongr
  exact_mod_cast action_semantic_count_le hQ

/-- The deployed one-Action shape has a much smaller pinned-root numerator than the
consensus-maximum bundle: `queryBudget = 96` and the six root families total `48808 / |Fp|`. -/
theorem action_algebraicRootBudget_eq :
    algebraicRootBudget (actionCircuit.shape.withProofParams actionProofParams)
        actionCircuit.domainExponent =
      (48808 : ENNReal) / Fintype.card Fp := by
  rw [actionShape_eq_fixtureShape]
  rw [action_domainExponent_eq]
  norm_num [algebraicRootBudget, queryBudget, shape]

/-- All non-DLOG terms in the exact Action endpoint, including the five semantic tails. -/
noncomputable def actionStatisticalModel (Q : Nat) : ENNReal :=
  (Q + 1 : Nat) * (1 / Fintype.card Fp) +
    (Q + 1 : Nat) *
      (actionCircuit.domainExponent *
        (2 / (Fintype.card Fp : ENNReal))) +
    (Q + (11 + actionCircuit.domainExponent) + 1 : Nat) *
      algebraicRootBudget (actionCircuit.shape.withProofParams actionProofParams)
        actionCircuit.domainExponent +
    1 / Fintype.card Fp +
    (Q + 1 : Nat) * ((20470 : Nat) / (Fintype.card Fp : ENNReal)) +
    (((Q + 1 : Nat) * (((20470 : Nat) : ENNReal) /
        (Fintype.card Fp : ENNReal)) +
      (Q + 1 : Nat) * (((2 ^ 23 : Nat) : ENNReal) /
        (Fintype.card Fp : ENNReal))) +
      ((Q + 1 : Nat) * (((2 ^ 35 : Nat) : ENNReal) /
          (Fintype.card Fp : ENNReal)) +
        ((Q + 1 : Nat) * (((2 ^ 21 : Nat) : ENNReal) /
            (Fintype.card Fp : ENNReal)) +
          (Q + 1 : Nat) * (((2 ^ 25 : Nat) : ENNReal) /
            (Fintype.card Fp : ENNReal)))))

/-- The non-DLOG remainder on the bare adaptive route.  Its deployed-root walk uses the original
run only; the larger sequential model below is therefore a conservative upper bound. -/
noncomputable def adaptiveActionStatisticalModel (Q : Nat) : ENNReal :=
  (Q + 1 : Nat) * (1 / Fintype.card Fp) +
    actionCircuit.domainExponent *
      ((Q + 1 : Nat) * (2 / (Fintype.card Fp : ENNReal))) +
    (Q + 1 : Nat) * algebraicRootBudget
      (actionCircuit.shape.withProofParams actionProofParams)
      actionCircuit.domainExponent +
    1 / Fintype.card Fp +
    (Q + 1 : Nat) *
      ((((2 ^ 25 : Nat) : ENNReal) / Fintype.card Fp +
        ((2 ^ 35 : Nat) : ENNReal) / Fintype.card Fp) +
        (((2 ^ 21 : Nat) : ENNReal) / Fintype.card Fp +
          (((2 ^ 23 : Nat) : ENNReal) / Fintype.card Fp +
            (20470 : ENNReal) / Fintype.card Fp)))

theorem adaptiveActionSemanticSum_eq :
    (∑ n : Fin 5,
      ((![2 ^ 25, 2 ^ 35, 2 ^ 21, 2 ^ 23, 20470] n : Nat) : ENNReal) /
        Fintype.card Fp) =
      ((((2 ^ 25 : Nat) : ENNReal) / Fintype.card Fp +
        ((2 ^ 35 : Nat) : ENNReal) / Fintype.card Fp) +
        (((2 ^ 21 : Nat) : ENNReal) / Fintype.card Fp +
          (((2 ^ 23 : Nat) : ENNReal) / Fintype.card Fp +
            (20470 : ENNReal) / Fintype.card Fp))) := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_one]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_succ]
  ring

/-- The sequential statistical model conservatively contains the adaptive remainder. -/
theorem adaptiveActionStatisticalModel_le_action (Q : Nat) :
    adaptiveActionStatisticalModel Q ≤ actionStatisticalModel Q := by
  have hk : actionCircuit.domainExponent = 11 := by
    change actionCircuit.domainExponent = 11
    exact action_domainExponent_eq
  have hsplit : actionStatisticalModel Q =
      adaptiveActionStatisticalModel Q +
        22 * algebraicRootBudget (actionCircuit.shape.withProofParams actionProofParams) 11 +
        (Q + 1 : Nat) * ((20470 : Nat) / (Fintype.card Fp : ENNReal)) := by
    rw [actionStatisticalModel, adaptiveActionStatisticalModel, hk]
    push_cast
    ring
  rw [hsplit]
  exact le_add_right (le_add_right le_rfl)

/-- At `Q <= 2^123`, the compressed remainder and all five Action semantic tails together fit
inside `2^-84`.  The semantic numerator is at most `2^160`; the remaining Action-shape terms are
below `2^140`, leaving a wide margin against the 254-bit scalar field. -/
theorem actionStatisticalModel_at_2pow123 {Q : Nat} (hQ : Q <= 2 ^ 123) :
    actionStatisticalModel Q <= 1 / (2 ^ 84 : ENNReal) := by
  have hbase :
      (Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 <= 2 ^ 141 := by
    calc
      (Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 <=
          (2 ^ 123 + 1) * (1 + 11 * 2 + 20470) +
            (2 ^ 123 + 23) * 48808 + 1 := by omega
      _ <= 2 ^ 141 := by norm_num
  have htotal :
      (Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 + 2 ^ 160 <=
        2 ^ 170 := by
    calc
      (Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 + 2 ^ 160 ≤
          2 ^ 141 + 2 ^ 160 := Nat.add_le_add_right hbase _
      _ ≤ 2 ^ 170 := by norm_num
  have hcount :
      actionStatisticalModel Q <=
        (((Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 +
          2 ^ 160 : Nat) : ENNReal) / Fintype.card Fp := by
    rw [actionStatisticalModel, action_algebraicRootBudget_eq]
    have hk : actionCircuit.domainExponent = 11 := by
      change actionCircuit.domainExponent = 11
      exact action_domainExponent_eq
    rw [hk]
    calc
      ((Q + 1 : Nat) : ENNReal) * (1 / (Fintype.card Fp : ENNReal)) +
          ((Q + 1 : Nat) : ENNReal) * (11 * (2 / (Fintype.card Fp : ENNReal))) +
          ((Q + 23 : Nat) : ENNReal) * (48808 / (Fintype.card Fp : ENNReal)) +
          1 / (Fintype.card Fp : ENNReal) +
          ((Q + 1 : Nat) : ENNReal) * (20470 / (Fintype.card Fp : ENNReal)) +
          ((((Q + 1 : Nat) : ENNReal) * (20470 / (Fintype.card Fp : ENNReal)) +
            ((Q + 1 : Nat) : ENNReal) * ((2 ^ 23 : Nat) /
              (Fintype.card Fp : ENNReal))) +
            (((Q + 1 : Nat) : ENNReal) * ((2 ^ 35 : Nat) /
                (Fintype.card Fp : ENNReal)) +
              (((Q + 1 : Nat) : ENNReal) * ((2 ^ 21 : Nat) /
                  (Fintype.card Fp : ENNReal)) +
                ((Q + 1 : Nat) : ENNReal) * ((2 ^ 25 : Nat) /
                  (Fintype.card Fp : ENNReal))))) =
          (((Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 : Nat) :
              ENNReal) / Fintype.card Fp +
            ((((Q + 1 : Nat) : ENNReal) * (20470 / (Fintype.card Fp : ENNReal)) +
              ((Q + 1 : Nat) : ENNReal) * ((2 ^ 23 : Nat) /
                (Fintype.card Fp : ENNReal))) +
              (((Q + 1 : Nat) : ENNReal) * ((2 ^ 35 : Nat) /
                  (Fintype.card Fp : ENNReal)) +
                (((Q + 1 : Nat) : ENNReal) * ((2 ^ 21 : Nat) /
                    (Fintype.card Fp : ENNReal)) +
                  ((Q + 1 : Nat) : ENNReal) * ((2 ^ 25 : Nat) /
                    (Fintype.card Fp : ENNReal))))) := by
        simp only [div_eq_mul_inv]
        push_cast
        ring
      _ ≤
          (((Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 : Nat) :
              ENNReal) / Fintype.card Fp +
            ((2 ^ 160 : Nat) : ENNReal) / Fintype.card Fp := by
        exact add_le_add_right (action_semantic_terms_le hQ) _
      _ = (((Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 +
            2 ^ 160 : Nat) : ENNReal) / Fintype.card Fp := by
        rw [ENNReal.div_add_div_same]
        norm_cast
  refine hcount.trans ?_
  calc
    (((Q + 1) * (1 + 11 * 2 + 20470) + (Q + 23) * 48808 + 1 +
        2 ^ 160 : Nat) : ENNReal) / Fintype.card Fp <=
        ((2 ^ 170 : Nat) : ENNReal) / Fintype.card Fp := by gcongr
    _ <= ((2 ^ 170 : Nat) : ENNReal) / (2 ^ 254 : Nat) := by
      gcongr
      exact_mod_cast two_pow_254_le_card
    _ ≤ 1 / (2 ^ 84 : ENNReal) := by
      rw [ENNReal.div_le_iff (by norm_num) (by norm_num)]
      rw [show ((2 ^ 254 : Nat) : ENNReal) =
          (2 ^ 84 : ENNReal) * (2 ^ 170 : ENNReal) by
            norm_num [← pow_add]]
      rw [div_eq_mul_inv, _root_.one_mul, ← _root_.mul_assoc,
        ENNReal.inv_mul_cancel (by norm_num) (by norm_num), _root_.one_mul]
      norm_num

/-- The combined constraint-plus-Action finder stays within the same conservative three-bit
query envelope at the `2^123` adversary target. -/
theorem action_dlog_queries_le_2pow126
    (family : ComputedStraightLineDeployedFSFamily
      (actionCircuit.shape.withProofParams actionProofParams))
    (hQ : family.Q ≤ 2 ^ 123) :
    actionDlogRandomOracleQueries actionProofParams family ≤ 2 ^ 126 := by
  unfold actionDlogRandomOracleQueries
  have hk : actionCircuit.domainExponent = 11 := by
    exact action_domainExponent_eq
  rw [hk]
  calc
    6 * family.Q + 6 * (11 + 11) ≤ 6 * 2 ^ 123 + 6 * (11 + 11) := by omega
    _ ≤ 8 * 2 ^ 123 := by norm_num
    _ = 2 ^ 126 := by norm_num

/-- If prover and terminal-reduction group work each fit the `2^123` target, the combined
six-call finder fits the matching `2^126` DLOG-solver envelope. -/
theorem action_dlog_groupWork_le_2pow126
    {proverGroupWork reductionGroupWork : Nat}
    (hprover : proverGroupWork ≤ 2 ^ 123)
    (hreduction : reductionGroupWork ≤ 2 ^ 123) :
    actionDlogGroupWork proverGroupWork reductionGroupWork ≤ 2 ^ 126 := by
  unfold actionDlogGroupWork
  calc
    6 * proverGroupWork + reductionGroupWork ≤ 6 * 2 ^ 123 + 2 ^ 123 := by omega
    _ ≤ 8 * 2 ^ 123 := by norm_num
    _ = 2 ^ 126 := by norm_num

/-! ## Exact false-Action-statement endpoints -/

/-- **The exact captured Action soundness bound.**  Its left-hand event is literal deployed
acceptance with a false `BundleStatement`.  The combined profile prices IPA, unbatching, quotient,
and Action-terminal relation branches once. -/
theorem orchard_action_acceptFalseStatement_prob_le_captured
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex actionCircuit.n → T)
    (hquery : Function.Injective query)
    (family : ComputedStraightLineDeployedFSFamily
      (actionCircuit.shape.withProofParams actionProofParams))
    (inputs : Fin actionProofParams.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey
      (ursOfAugmentedBasis actionCircuit.domainExponent basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.domainExponent basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis actionCircuit.domainExponent basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.domainExponent basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder)
    (profile : StraightLineActionDlogProfile actionProofParams family
      (staticChecks_of_derived family hvk) inputs hvk hI hchar B)
    {xyBound betaBound gammaBound thetaBound : ENNReal}
    (hXY : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams actionProofParams) family.init.length 10
            + 3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelXYFailureEvent actionCircuit actionProofParams family
            (staticChecks_of_derived family hvk) inputs hvk hI hchar) ≤ xyBound)
    (hBeta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams actionProofParams) family.init.length 10
            + 3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelBetaFailureEvent actionCircuit actionProofParams family
            (staticChecks_of_derived family hvk) inputs hvk hI hchar) ≤ betaBound)
    (hGamma : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams actionProofParams) family.init.length 10
            + 3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelGammaFailureEvent actionCircuit actionProofParams family
            (staticChecks_of_derived family hvk) inputs hvk hI hchar) ≤ gammaBound)
    (hTheta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams actionProofParams) family.init.length 10
            + 3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelThetaFailureEvent actionCircuit actionProofParams family
            (staticChecks_of_derived family hvk) inputs hvk hI hchar) ≤ thetaBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams actionProofParams) family.init.length 10
            + 3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionAcceptFalseStatementEvent family inputs) ≤
      ((family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          (family.Q + 1 : Nat) *
            (actionCircuit.domainExponent *
              (2 / (Fintype.card Fp : ENNReal))) +
          (family.Q + (11 + actionCircuit.domainExponent) + 1 : Nat) *
            algebraicRootBudget (actionCircuit.shape.withProofParams actionProofParams)
              actionCircuit.domainExponent +
          (profile.advantage (actionDlogRandomOracleQueries actionProofParams family)
              (actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
            1 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * ((20470 : Nat) / (Fintype.card Fp : ENNReal))) +
        (xyBound + (betaBound + (gammaBound + thetaBound))) :=
  actionBundleStatementFailure_prob_le_of_base_union_bound actionProofParams family
    (staticChecks_of_derived family hvk) inputs hvk hI hchar query
    (actionRelationFinder actionProofParams family (staticChecks_of_derived family hvk)
      inputs hvk hI hchar)
    (actionRelationFinder_covers actionProofParams family
      (staticChecks_of_derived family hvk) inputs hvk hI hchar)
    (actionBaseUnion_prob_le_of_dlogProfile actionProofParams family
      (staticChecks_of_derived family hvk) inputs hvk hI hchar B hB query hquery
      (schedule_of_derived family hvk) profile)
    hXY hBeta hGamma hTheta

/-- The exact captured Action reduction at an arbitrary bundle size.  The captured certificate
supplies only circuit-owned data; `numProofs` remains visible in the statement and in all four
semantic budgets. -/
theorem orchard_action_acceptFalseStatement_prob_le_captured_for
    (numProofs : ℕ) {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex
      actionCircuit.n → T)
    (hquery : Function.Injective query)
    (family : ComputedStraightLineDeployedFSFamily
      (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)))
    (inputs : Fin (actionProofParamsFor numProofs).numProofs →
      PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder)
    (profile : StraightLineActionDlogProfile (actionProofParamsFor numProofs) family
      (staticChecks_of_derived_for numProofs family hvk) inputs hvk hI hchar B)
    {xyBound betaBound gammaBound thetaBound : ENNReal}
    (hXY : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
            family.init.length 10 +
            3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelXYFailureEvent actionCircuit (actionProofParamsFor numProofs) family
            (staticChecks_of_derived_for numProofs family hvk) inputs hvk hI hchar) ≤ xyBound)
    (hBeta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
            family.init.length 10 +
            3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelBetaFailureEvent actionCircuit (actionProofParamsFor numProofs) family
            (staticChecks_of_derived_for numProofs family hvk) inputs hvk hI hchar) ≤ betaBound)
    (hGamma : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
            family.init.length 10 +
            3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelGammaFailureEvent actionCircuit (actionProofParamsFor numProofs) family
            (staticChecks_of_derived_for numProofs family hvk) inputs hvk hI hchar) ≤ gammaBound)
    (hTheta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
            family.init.length 10 +
            3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelThetaFailureEvent actionCircuit (actionProofParamsFor numProofs) family
            (staticChecks_of_derived_for numProofs family hvk) inputs hvk hI hchar) ≤ thetaBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
            family.init.length 10 +
            3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionAcceptFalseStatementEventFor numProofs family inputs) ≤
      ((family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          (family.Q + 1 : Nat) *
            (actionCircuit.domainExponent *
              (2 / (Fintype.card Fp : ENNReal))) +
          (family.Q +
              (11 + actionCircuit.domainExponent) + 1 : Nat) *
            algebraicRootBudget
              (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
              actionCircuit.domainExponent +
          (profile.advantage
              (actionDlogRandomOracleQueries (actionProofParamsFor numProofs) family)
              (actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
            1 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * ((20470 : Nat) / (Fintype.card Fp : ENNReal))) +
        (xyBound + (betaBound + (gammaBound + thetaBound))) :=
  actionBundleStatementFailure_prob_le_of_base_union_bound
    (actionProofParamsFor numProofs) family
    (staticChecks_of_derived_for numProofs family hvk) inputs hvk hI hchar query
    (actionRelationFinder (actionProofParamsFor numProofs) family
      (staticChecks_of_derived_for numProofs family hvk) inputs hvk hI hchar)
    (actionRelationFinder_covers (actionProofParamsFor numProofs) family
      (staticChecks_of_derived_for numProofs family hvk) inputs hvk hI hchar)
    (actionBaseUnion_prob_le_of_dlogProfile (actionProofParamsFor numProofs) family
      (staticChecks_of_derived_for numProofs family hvk) inputs hvk hI hchar B hB query hquery
      (schedule_of_derived_for numProofs family hvk) profile)
    hXY hBeta hGamma hTheta

/-- Captured false-statement bound for a bare adaptive online-AGM family, with one profiled finder
and five annotation-aware semantic surfaces. -/
theorem orchard_action_acceptFalseStatement_prob_le_adaptive
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex actionCircuit.n → T)
    (hquery : Function.Injective query)
    (family : ComputedAdaptiveOnlineAGMFSFamily
      (actionCircuit.shape.withProofParams actionProofParams))
    (inputs : Fin actionProofParams.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey
      (ursOfAugmentedBasis actionCircuit.domainExponent basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.domainExponent basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis actionCircuit.domainExponent basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.domainExponent basis) inputs)
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O) < scalarFieldOrder)
    (profile : AdaptiveActionDlogProfile actionProofParams family inputs hvk hI hchar B) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams actionProofParams) family.init.length 10
            + 3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
      ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
        adaptiveActionAcceptFalseStatementEvent actionProofParams family inputs) ≤
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        (actionCircuit.domainExponent *
          ((family.Q + 1 : Nat) * (2 / (Fintype.card Fp : ENNReal))) +
        ((family.Q + 1 : Nat) *
          algebraicRootBudget (actionCircuit.shape.withProofParams actionProofParams)
            actionCircuit.domainExponent +
        ((profile.advantage (adaptiveActionDlogRandomOracleQueries actionProofParams family)
              (adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
            1 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * ∑ n : Fin 5,
            ((![2 ^ 25, 2 ^ 35, 2 ^ 21, 2 ^ 23, 20470] n : Nat) : ENNReal) /
              Fintype.card Fp))) := by
  let epsilon : Fin 5 → ENNReal := fun n =>
    ((![2 ^ 25, 2 ^ 35, 2 ^ 21, 2 ^ 23, 20470] n : Nat) : ENNReal) /
      Fintype.card Fp
  have hsurface : ∀
      (basis : AugmentedIndex
        actionCircuit.n → VestaG)
      (n : Fin 5)
      (ps : ProofString (actionCircuit.shape.withProofParams actionProofParams) Fp VestaG)
      (_hwf : PsWellFormed ps)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (n : Nat) → Fp),
      uniformChallenge.toOuterMeasure
          (adaptiveActionSurfaceAt actionProofParams basis inputs n ps source earlier) ≤
        epsilon n := by
    intro basis n ps _hwf source earlier
    fin_cases n
    · refine le_trans
        (adaptiveActionThetaSurface_measure_le actionProofParams basis inputs ps source earlier) ?_
      dsimp only [epsilon]
      gcongr
      exact_mod_cast cap_theta basis
        (adaptiveActionCommitmentPolynomial actionProofParams basis inputs ps source
          (chRecord (fun _ => 0) (fun _ => 0)))
    · have h := adaptiveActionBetaSurface_measure_le
        actionProofParams basis inputs ps source earlier
      dsimp only at h
      refine le_trans h ?_
      dsimp only [epsilon]
      rw [ENNReal.div_add_div_same]
      gcongr
      exact_mod_cast cap_beta basis
        (adaptiveActionCommitmentPolynomial actionProofParams basis inputs ps source
          (chRecord (fun i => if h : (i : Nat) < 1 then earlier ⟨i, h⟩ else 0)
            (fun _ => 0)))
    · have h := adaptiveActionGammaSurface_measure_le
        actionProofParams basis inputs ps source earlier
      dsimp only at h
      refine le_trans h ?_
      dsimp only [epsilon]
      rw [ENNReal.div_add_div_same]
      gcongr
      exact_mod_cast cap_gamma basis
        (adaptiveActionCommitmentPolynomial actionProofParams basis inputs ps source
          (chRecord (fun i => if h : (i : Nat) < 2 then earlier ⟨i, h⟩ else 0)
            (fun _ => 0)))
    · have h := adaptiveActionYSurface_measure_le
        actionProofParams basis inputs ps source earlier derived_n_ne_zero
      dsimp only at h
      refine le_trans h ?_
      dsimp only [epsilon]
      gcongr
      exact_mod_cast derived_n_yn
        (adaptive_action_constraint_count_le basis inputs ps source
          (chRecord (fun i => if h : (i : Nat) < 3 then earlier ⟨i, h⟩ else 0)
            (fun _ => 0)))
    · have h := adaptiveActionXSurface_measure_le
        actionProofParams basis inputs ps source earlier
      dsimp only at h
      refine le_trans h ?_
      dsimp only [epsilon]
      gcongr
      simpa only [Zcash.Snark.Keygen.actionProofParamsFor_one] using
        (adaptive_action_x_degree_le_for 1 basis inputs ps source
          (chRecord (fun i => if h : (i : Nat) < 4 then earlier ⟨i, h⟩ else 0)
            (fun _ => 0)))
  have hevent := adaptiveActionEvent_prob_eq_of_uniformURS actionProofParams family
    (orchardGeneratorROSetup query) B (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO
      actionCircuit.domainExponent B hB query hquery)
    (adaptiveActionAcceptFalseStatementEvent actionProofParams family inputs)
  calc
    _ = _ := hevent
    _ ≤ _ := by
      simpa only [epsilon] using
        (adaptiveActionAcceptFalseStatement_prob_le actionProofParams family inputs hvk hI hchar
          B epsilon profile hsurface)

/-- Bare adaptive Action composition for every bundle size.  The five surface bounds are derived
from the captured circuit data and scale only where the verifier processes one item per Action. -/
theorem orchard_action_acceptFalseStatement_prob_le_adaptive_for
    (numProofs : ℕ) {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex
      actionCircuit.n → T)
    (hquery : Function.Injective query)
    (family : ComputedAdaptiveOnlineAGMFSFamily
      (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)))
    (inputs : Fin (actionProofParamsFor numProofs).numProofs →
      PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) inputs)
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O) < scalarFieldOrder)
    (profile : AdaptiveActionDlogProfile (actionProofParamsFor numProofs)
      family inputs hvk hI hchar B) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
            family.init.length 10 +
            3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
      ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
        adaptiveActionAcceptFalseStatementEvent
          (actionProofParamsFor numProofs) family inputs) ≤
      (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (actionCircuit.domainExponent *
          ((family.Q + 1 : ℕ) * (2 / (Fintype.card Fp : ENNReal))) +
        ((family.Q + 1 : ℕ) *
          algebraicRootBudget
            (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
            actionCircuit.domainExponent +
        ((profile.advantage
              (adaptiveActionDlogRandomOracleQueries (actionProofParamsFor numProofs) family)
              (adaptiveActionDlogGroupWork
                profile.proverGroupWork profile.reductionGroupWork) +
            1 / Fintype.card Fp) +
          (family.Q + 1 : ℕ) * ∑ i : Fin 5,
            ((![numProofs * 2 ^ 25, numProofs * 950835027, numProofs * 73554,
                numProofs * 2 ^ 23, 20470] i : ℕ) : ENNReal) /
              Fintype.card Fp))) := by
  let epsilon : Fin 5 → ENNReal := fun i =>
    ((![numProofs * 2 ^ 25, numProofs * 950835027, numProofs * 73554,
        numProofs * 2 ^ 23, 20470] i : ℕ) : ENNReal) / Fintype.card Fp
  have hsurface : ∀
      (basis : AugmentedIndex
        actionCircuit.n → VestaG)
      (i : Fin 5)
      (ps : ProofString
        (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)) Fp VestaG)
      (_hwf : PsWellFormed ps)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (i : ℕ) → Fp),
      uniformChallenge.toOuterMeasure
          (adaptiveActionSurfaceAt (actionProofParamsFor numProofs)
            basis inputs i ps source earlier) ≤ epsilon i := by
    intro basis i ps _hwf source earlier
    fin_cases i
    · refine le_trans
        (adaptiveActionThetaSurface_measure_le (actionProofParamsFor numProofs)
          basis inputs ps source earlier) ?_
      dsimp only [epsilon]
      gcongr
      exact_mod_cast cap_theta_for numProofs basis
        (adaptiveActionCommitmentPolynomial (actionProofParamsFor numProofs)
          basis inputs ps source (chRecord (fun _ => 0) (fun _ => 0)))
    · have h := adaptiveActionBetaSurface_measure_le
        (actionProofParamsFor numProofs) basis inputs ps source earlier
      dsimp only at h
      refine le_trans h ?_
      dsimp only [epsilon]
      rw [ENNReal.div_add_div_same]
      gcongr
      exact_mod_cast cap_beta_for numProofs basis
        (adaptiveActionCommitmentPolynomial (actionProofParamsFor numProofs)
          basis inputs ps source
          (chRecord (fun j => if hj : (j : ℕ) < 1 then earlier ⟨j, hj⟩ else 0)
            (fun _ => 0)))
    · have h := adaptiveActionGammaSurface_measure_le
        (actionProofParamsFor numProofs) basis inputs ps source earlier
      dsimp only at h
      refine le_trans h ?_
      dsimp only [epsilon]
      rw [ENNReal.div_add_div_same]
      gcongr
      exact_mod_cast cap_gamma_for numProofs basis
        (adaptiveActionCommitmentPolynomial (actionProofParamsFor numProofs)
          basis inputs ps source
          (chRecord (fun j => if hj : (j : ℕ) < 2 then earlier ⟨j, hj⟩ else 0)
            (fun _ => 0)))
    · have h := adaptiveActionYSurface_measure_le
        (actionProofParamsFor numProofs) basis inputs ps source earlier
        derived_n_ne_zero
      dsimp only at h
      refine le_trans h ?_
      dsimp only [epsilon]
      gcongr
      exact_mod_cast derived_n_yn_for numProofs
        (adaptive_action_constraint_count_le_for numProofs basis inputs ps source
          (chRecord (fun j => if hj : (j : ℕ) < 3 then earlier ⟨j, hj⟩ else 0)
            (fun _ => 0)))
    · have h := adaptiveActionXSurface_measure_le
        (actionProofParamsFor numProofs) basis inputs ps source earlier
      dsimp only at h
      refine le_trans h ?_
      dsimp only [epsilon]
      gcongr
      exact_mod_cast adaptive_action_x_degree_le_for numProofs basis inputs ps source
        (chRecord (fun j => if hj : (j : ℕ) < 4 then earlier ⟨j, hj⟩ else 0)
          (fun _ => 0))
  have hevent := adaptiveActionEvent_prob_eq_of_uniformURS
    (actionProofParamsFor numProofs) family
    (orchardGeneratorROSetup query) B (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO
      actionCircuit.domainExponent B hB query hquery)
    (adaptiveActionAcceptFalseStatementEvent (actionProofParamsFor numProofs) family inputs)
  calc
    _ = _ := hevent
    _ ≤ _ := by
      simpa only [epsilon] using
        (adaptiveActionAcceptFalseStatement_prob_le (actionProofParamsFor numProofs)
          family inputs hvk hI hchar B epsilon profile hsurface)

/-- Captured five-surface bound shared by ordinary and knowledge soundness. -/
theorem orchard_adaptiveActionSurface_measure_le_for
    (numProofs : ℕ)
    (basis : AugmentedIndex
      (2 ^ actionCircuit.domainExponent) → VestaG)
    (inputs : Fin (actionProofParamsFor numProofs).numProofs →
      PublicInputs Fp)
    (i : Fin 5)
    (ps : ProofString
      (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)) Fp VestaG)
    (_hwf : PsWellFormed ps)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (earlier : Fin (i : ℕ) → Fp) :
    uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAt (actionProofParamsFor numProofs)
          basis inputs i ps source earlier) ≤
      ((![numProofs * 2 ^ 25, numProofs * 950835027, numProofs * 73554,
          numProofs * 2 ^ 23, 20470] i : ℕ) : ENNReal) / Fintype.card Fp := by
  fin_cases i
  · refine le_trans
      (adaptiveActionThetaSurface_measure_le (actionProofParamsFor numProofs)
        basis inputs ps source earlier) ?_
    gcongr
    exact_mod_cast cap_theta_for numProofs basis
      (adaptiveActionCommitmentPolynomial (actionProofParamsFor numProofs)
        basis inputs ps source (chRecord (fun _ => 0) (fun _ => 0)))
  · have h := adaptiveActionBetaSurface_measure_le
      (actionProofParamsFor numProofs) basis inputs ps source earlier
    dsimp only at h
    refine le_trans h ?_
    rw [ENNReal.div_add_div_same]
    gcongr
    exact_mod_cast cap_beta_for numProofs basis
      (adaptiveActionCommitmentPolynomial (actionProofParamsFor numProofs)
        basis inputs ps source
        (chRecord (fun j => if hj : (j : ℕ) < 1 then earlier ⟨j, hj⟩ else 0)
          (fun _ => 0)))
  · have h := adaptiveActionGammaSurface_measure_le
      (actionProofParamsFor numProofs) basis inputs ps source earlier
    dsimp only at h
    refine le_trans h ?_
    rw [ENNReal.div_add_div_same]
    gcongr
    exact_mod_cast cap_gamma_for numProofs basis
      (adaptiveActionCommitmentPolynomial (actionProofParamsFor numProofs)
        basis inputs ps source
        (chRecord (fun j => if hj : (j : ℕ) < 2 then earlier ⟨j, hj⟩ else 0)
          (fun _ => 0)))
  · have h := adaptiveActionYSurface_measure_le
      (actionProofParamsFor numProofs) basis inputs ps source earlier
      derived_n_ne_zero
    dsimp only at h
    refine le_trans h ?_
    gcongr
    exact_mod_cast derived_n_yn_for numProofs
      (adaptive_action_constraint_count_le_for numProofs basis inputs ps source
        (chRecord (fun j => if hj : (j : ℕ) < 3 then earlier ⟨j, hj⟩ else 0)
          (fun _ => 0)))
  · have h := adaptiveActionXSurface_measure_le
      (actionProofParamsFor numProofs) basis inputs ps source earlier
    dsimp only at h
    refine le_trans h ?_
    gcongr
    exact_mod_cast adaptive_action_x_degree_le_for numProofs basis inputs ps source
      (chRecord (fun j => if hj : (j : ℕ) < 4 then earlier ⟨j, hj⟩ else 0)
        (fun _ => 0))

/-- **Consensus-generic adaptive Action knowledge soundness.**  The event is literal acceptance
with failure of the executable private-witness extractor, not merely a false existential
statement. -/
theorem orchard_action_knowledgeFailure_prob_le_adaptive_for
    (numProofs : ℕ) {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex
      (2 ^ actionCircuit.domainExponent) → T)
    (hquery : Function.Injective query)
    (family : ComputedAdaptiveOnlineAGMFSFamily
      (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)))
    (inputs : Fin (actionProofParamsFor numProofs).numProofs →
      PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) inputs)
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O) < scalarFieldOrder)
    (profile : AdaptiveActionDlogProfile (actionProofParamsFor numProofs)
      family inputs hvk hI hchar B) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
            family.init.length 10 +
            3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
      ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
        adaptiveActionKnowledgeFailureEvent
          (actionProofParamsFor numProofs) family inputs hvk hI hchar) ≤
      (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        (actionCircuit.domainExponent *
          ((family.Q + 1 : ℕ) * (2 / (Fintype.card Fp : ENNReal))) +
        ((family.Q + 1 : ℕ) *
          algebraicRootBudget
            (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
            actionCircuit.domainExponent +
        ((profile.advantage
              (adaptiveActionDlogRandomOracleQueries (actionProofParamsFor numProofs) family)
              (adaptiveActionDlogGroupWork
                profile.proverGroupWork profile.reductionGroupWork) +
            1 / Fintype.card Fp) +
          (family.Q + 1 : ℕ) * ∑ i : Fin 5,
            ((![numProofs * 2 ^ 25, numProofs * 950835027, numProofs * 73554,
                numProofs * 2 ^ 23, 20470] i : ℕ) : ENNReal) /
              Fintype.card Fp))) := by
  let epsilon : Fin 5 → ENNReal := fun i =>
    ((![numProofs * 2 ^ 25, numProofs * 950835027, numProofs * 73554,
        numProofs * 2 ^ 23, 20470] i : ℕ) : ENNReal) / Fintype.card Fp
  have hsurface : ∀
      (basis : AugmentedIndex
        (2 ^ actionCircuit.domainExponent) → VestaG)
      (i : Fin 5)
      (ps : ProofString
        (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)) Fp VestaG)
      (_hwf : PsWellFormed ps)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (i : ℕ) → Fp),
      uniformChallenge.toOuterMeasure
          (adaptiveActionSurfaceAt (actionProofParamsFor numProofs)
            basis inputs i ps source earlier) ≤ epsilon i := by
    intro basis i ps hwf source earlier
    exact orchard_adaptiveActionSurface_measure_le_for
      numProofs basis inputs i ps hwf source earlier
  have hevent := adaptiveActionEvent_prob_eq_of_uniformURS
    (actionProofParamsFor numProofs) family
    (orchardGeneratorROSetup query) B (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO
      actionCircuit.domainExponent B hB query hquery)
    (adaptiveActionKnowledgeFailureEvent
      (actionProofParamsFor numProofs) family inputs hvk hI hchar)
  calc
    _ = _ := hevent
    _ ≤ _ := by
      simpa only [epsilon] using
        (adaptiveActionKnowledgeFailure_prob_le (actionProofParamsFor numProofs)
          family inputs hvk hI hchar B epsilon profile
          hsurface)

/-- **Concrete bare-adaptive Action capstone.**  At `Q <= 2^123`, the complete adaptive finder
fits a conservative `2^127` random-oracle/group-work envelope (eight uncached represented runs),
while the direct-coordinate decoder fits `2^123`.  The statistical remainder remains `2^-84`. -/
theorem orchard_action_acceptFalseStatement_adaptive_2pow123_workFactor_generatorRO
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex actionCircuit.n → T)
    (hquery : Function.Injective query)
    (family : ComputedAdaptiveOnlineAGMFSFamily
      (actionCircuit.shape.withProofParams actionProofParams))
    (inputs : Fin actionProofParams.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey
      (ursOfAugmentedBasis actionCircuit.domainExponent basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.domainExponent basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis actionCircuit.domainExponent basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.domainExponent basis) inputs)
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O) < scalarFieldOrder)
    (profile : AdaptiveActionDirectDlogProfile actionProofParams family inputs hvk hI hchar B
      (2 ^ 123)) :
    ((independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams actionProofParams) family.init.length 10
            + 3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          adaptiveActionAcceptFalseStatementEvent actionProofParams family inputs) ≤
      profile.advantage (2 ^ 127) (2 ^ 127) + 1 / (2 ^ 84 : ENNReal)) ∧
      adaptiveActionDlogRandomOracleQueries actionProofParams family ≤ 2 ^ 127 ∧
      adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
        2 ^ 127 ∧
      ∀ basis O, 2 * adaptiveActionDirectDecodeOps actionProofParams family basis O ≤
        2 ^ 123 := by
  have hcost := profile.solverCost_le
  have hqueries : adaptiveActionDlogRandomOracleQueries actionProofParams family ≤
      2 ^ 127 := by
    calc
      adaptiveActionDlogRandomOracleQueries actionProofParams family ≤ 16 * 2 ^ 123 :=
        hcost.1
      _ = 2 ^ 127 := by norm_num
  have hgroup :
      adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
        2 ^ 127 := by
    calc
      adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
          16 * 2 ^ 123 := hcost.2.1
      _ = 2 ^ 127 := by norm_num
  refine ⟨?_, hqueries, hgroup, hcost.2.2⟩
  refine le_trans
    (orchard_action_acceptFalseStatement_prob_le_adaptive B hB query hquery family inputs
      hvk hI hchar profile.toAdaptiveActionDlogProfile) ?_
  rw [adaptiveActionSemanticSum_eq]
  calc
    _ =
        profile.advantage (adaptiveActionDlogRandomOracleQueries actionProofParams family)
            (adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
          adaptiveActionStatisticalModel family.Q := by
      unfold adaptiveActionStatisticalModel
      ring
    _ ≤ profile.advantage (2 ^ 127) (2 ^ 127) + 1 / (2 ^ 84 : ENNReal) :=
      add_le_add (profile.advantage_mono hqueries hgroup)
        (le_trans (adaptiveActionStatisticalModel_le_action family.Q)
          (actionStatisticalModel_at_2pow123 profile.queryBound))

/-- Consensus-generic adaptive capstone: `2^123` direct work, `2^127` DLOG resources, `2^-83`
statistical remainder, and explicit transcript bias. -/
theorem orchard_action_acceptFalseStatement_adaptive_2pow123_workFactor_generatorRO_for
    (numProofs : ℕ) (hn : numProofs ≤ orchardConsensusMaxProofs)
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex
      actionCircuit.n → T)
    (hquery : Function.Injective query)
    (family : ComputedAdaptiveOnlineAGMFSFamily
      (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)))
    (inputs : Fin (actionProofParamsFor numProofs).numProofs →
      PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) inputs)
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O) < scalarFieldOrder)
    (profile : AdaptiveActionDirectDlogProfile (actionProofParamsFor numProofs)
      family inputs hvk hI hchar B (2 ^ 123)) :
    ((independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
            family.init.length 10 +
            3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          adaptiveActionAcceptFalseStatementEvent
            (actionProofParamsFor numProofs) family inputs) ≤
      profile.advantage (2 ^ 127) (2 ^ 127) + 1 / (2 ^ 83 : ENNReal)) ∧
      adaptiveActionDlogRandomOracleQueries (actionProofParamsFor numProofs) family ≤
        2 ^ 127 ∧
      adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
        2 ^ 127 ∧
      (∀ basis O,
        2 * adaptiveActionDirectDecodeOps
          (actionProofParamsFor numProofs) family basis O ≤ 2 ^ 123) ∧
      ∀ (actual : PMF
          ((↥(Set.range query) → VestaG) ×
            (BTranscript Fp VestaG
              (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
                family.init.length 10 +
                3 * actionCircuit.domainExponent) → Fp)))
        (εBias : ENNReal),
        PMFEventBiasLE actual
          (independentProductPMF (orchardGeneratorROSetup query)
            (PMF.uniformOfFintype
              (BTranscript Fp VestaG
                (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
                  family.init.length 10 +
                  3 * actionCircuit.domainExponent) → Fp)))
          εBias →
        actual.toOuterMeasure
            ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
              adaptiveActionAcceptFalseStatementEvent
                (actionProofParamsFor numProofs) family inputs) ≤
          (profile.advantage (2 ^ 127) (2 ^ 127) + 1 / (2 ^ 83 : ENNReal)) + εBias := by
  have hcost := profile.solverCost_le
  have hqueries :
      adaptiveActionDlogRandomOracleQueries (actionProofParamsFor numProofs) family ≤
        2 ^ 127 := by
    calc
      adaptiveActionDlogRandomOracleQueries (actionProofParamsFor numProofs) family ≤
          16 * 2 ^ 123 := hcost.1
      _ = 2 ^ 127 := by norm_num
  have hgroup :
      adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
        2 ^ 127 := by
    calc
      adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
          16 * 2 ^ 123 := hcost.2.1
      _ = 2 ^ 127 := by norm_num
  have hprob :
      (independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype
          (BTranscript Fp VestaG
            (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
              family.init.length 10 +
              3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
          ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
            adaptiveActionAcceptFalseStatementEvent
              (actionProofParamsFor numProofs) family inputs) ≤
        profile.advantage (2 ^ 127) (2 ^ 127) + 1 / (2 ^ 83 : ENNReal) := by
    refine le_trans
      (orchard_action_acceptFalseStatement_prob_le_adaptive_for numProofs B hB query hquery
        family inputs hvk hI hchar profile.toAdaptiveActionDlogProfile) ?_
    refine le_trans ?_
      (add_le_add (profile.advantage_mono hqueries hgroup)
        (actionStatisticalModelFor_at_2pow123 hn profile.queryBound))
    refine le_trans ?_ (add_le_add le_rfl
      (adaptiveActionStatisticalModelFor_le_action numProofs family.Q))
    have hsum :
        (∑ i : Fin 5,
          ((![numProofs * 2 ^ 25, numProofs * 950835027, numProofs * 73554,
              numProofs * 2 ^ 23, 20470] i : ℕ) : ENNReal) / Fintype.card Fp) =
          (((numProofs * 992851621 + 20470 : ℕ) : ENNReal) /
            Fintype.card Fp) := by
      norm_num [Fin.sum_univ_succ]
      simp only [div_eq_mul_inv]
      ring
    rw [hsum]
    unfold adaptiveActionStatisticalModelFor actionSemanticModelFor
    dsimp only
    push_cast
    simp only [div_eq_mul_inv]
    ring_nf
    exact le_rfl
  refine ⟨hprob, hqueries, hgroup, hcost.2.2, ?_⟩
  intro actual εBias hbias
  exact event_measure_le_of_bias hbias _ hprob

/-- Consensus-generic knowledge capstone: extractor failure is bounded by one profiled Vesta-DLOG
advantage plus `2^-83`. -/
theorem orchard_action_knowledgeFailure_adaptive_2pow123_workFactor_generatorRO_for
    (numProofs : ℕ) (hn : numProofs ≤ orchardConsensusMaxProofs)
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex
      (2 ^ actionCircuit.domainExponent) → T)
    (hquery : Function.Injective query)
    (family : ComputedAdaptiveOnlineAGMFSFamily
      (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)))
    (inputs : Fin (actionProofParamsFor numProofs).numProofs →
      PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) inputs)
      (adaptiveActionRunOutput family basis O).1.proof.1
      (adaptiveActionRunRecord family basis O) < scalarFieldOrder)
    (profile : AdaptiveActionDirectDlogProfile (actionProofParamsFor numProofs)
      family inputs hvk hI hchar B (2 ^ 123)) :
    ((independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
            family.init.length 10 +
            3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          adaptiveActionKnowledgeFailureEvent
            (actionProofParamsFor numProofs) family inputs hvk hI hchar) ≤
      profile.advantage (2 ^ 127) (2 ^ 127) + 1 / (2 ^ 83 : ENNReal)) ∧
      adaptiveActionKnowledgeExtractorRandomOracleQueries
          (actionProofParamsFor numProofs) family ≤ 2 ^ 127 ∧
      adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
        2 ^ 127 ∧
      (∀ basis O,
        2 * adaptiveActionDirectDecodeOps
          (actionProofParamsFor numProofs) family basis O ≤ 2 ^ 123) ∧
      ∀ (actual : PMF
          ((↥(Set.range query) → VestaG) ×
            (BTranscript Fp VestaG
              (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
                family.init.length 10 +
                3 * actionCircuit.domainExponent) → Fp)))
        (εBias : ENNReal),
        PMFEventBiasLE actual
          (independentProductPMF (orchardGeneratorROSetup query)
            (PMF.uniformOfFintype
              (BTranscript Fp VestaG
                (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
                  family.init.length 10 +
                  3 * actionCircuit.domainExponent) → Fp)))
          εBias →
        actual.toOuterMeasure
            ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
              adaptiveActionKnowledgeFailureEvent
                (actionProofParamsFor numProofs) family inputs hvk hI hchar) ≤
          (profile.advantage (2 ^ 127) (2 ^ 127) + 1 / (2 ^ 83 : ENNReal)) + εBias := by
  have hcost := profile.knowledgeExtractorCost_le
  have hqueries :
      adaptiveActionKnowledgeExtractorRandomOracleQueries
          (actionProofParamsFor numProofs) family ≤ 2 ^ 127 := by
    calc
      adaptiveActionKnowledgeExtractorRandomOracleQueries
          (actionProofParamsFor numProofs) family ≤ 16 * 2 ^ 123 := hcost.1
      _ = 2 ^ 127 := by norm_num
  have hqueriesDlog :
      adaptiveActionDlogRandomOracleQueries (actionProofParamsFor numProofs) family ≤
        2 ^ 127 := by
    simpa only [adaptiveActionKnowledgeExtractorRandomOracleQueries_eq] using hqueries
  have hgroup :
      adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
        2 ^ 127 := by
    calc
      adaptiveActionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
          16 * 2 ^ 123 := hcost.2.1
      _ = 2 ^ 127 := by norm_num
  have hprob :
      (independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype
          (BTranscript Fp VestaG
            (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
              family.init.length 10 +
              3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
          ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
            adaptiveActionKnowledgeFailureEvent
              (actionProofParamsFor numProofs) family inputs hvk hI hchar) ≤
        profile.advantage (2 ^ 127) (2 ^ 127) + 1 / (2 ^ 83 : ENNReal) := by
    refine le_trans
      (orchard_action_knowledgeFailure_prob_le_adaptive_for numProofs B hB query hquery
        family inputs hvk hI hchar profile.toAdaptiveActionDlogProfile) ?_
    refine le_trans ?_
      (add_le_add (profile.advantage_mono hqueriesDlog hgroup)
        (actionStatisticalModelFor_at_2pow123 hn profile.queryBound))
    refine le_trans ?_ (add_le_add le_rfl
      (adaptiveActionStatisticalModelFor_le_action numProofs family.Q))
    have hsum :
        (∑ i : Fin 5,
          ((![numProofs * 2 ^ 25, numProofs * 950835027, numProofs * 73554,
              numProofs * 2 ^ 23, 20470] i : ℕ) : ENNReal) / Fintype.card Fp) =
          (((numProofs * 992851621 + 20470 : ℕ) : ENNReal) /
            Fintype.card Fp) := by
      norm_num [Fin.sum_univ_succ]
      simp only [div_eq_mul_inv]
      ring
    rw [hsum]
    unfold adaptiveActionStatisticalModelFor actionSemanticModelFor
    dsimp only
    push_cast
    simp only [div_eq_mul_inv]
    ring_nf
    exact le_rfl
  refine ⟨hprob, hqueries, hgroup, hcost.2.2, ?_⟩
  intro actual εBias hbias
  exact event_measure_le_of_bias hbias _ hprob

/-- Sequential false-statement capstone generated from executable root, IPA, constraint-`x`, and
Action phases. -/
theorem orchard_action_acceptFalseStatement_prob_le_sequential
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex actionCircuit.n → T)
    (hquery : Function.Injective query)
    (prover : SequentialOnlineAGMProver
      (actionCircuit.shape.withProofParams actionProofParams))
    (inputs : Fin actionProofParams.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, prover.toFamily.vk basis = actionCircuit.toVerifierKey
      (ursOfAugmentedBasis actionCircuit.domainExponent basis))
    (hI : ∀ basis, prover.toFamily.instanceCommitment basis =
      actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.domainExponent basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis actionCircuit.domainExponent basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.domainExponent basis) inputs)
      (straightLineRunOutput prover.toFamily basis O).1.proof.1
      (straightLineRunRecord prover.toFamily basis O) < scalarFieldOrder)
    (profile : StraightLineActionDlogProfile actionProofParams prover.toFamily
      (staticChecks_of_derived prover.toFamily hvk) inputs hvk hI hchar B)
    {L : Nat} (hL : L ≤ 2 ^ 12)
    (execution : ActionSequentialExecution actionProofParams prover.toFamily
      (staticChecks_of_derived prover.toFamily hvk) inputs hvk hI hchar 20470 L) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams actionProofParams) prover.toFamily.init.length 10
            + 3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionAcceptFalseStatementEvent prover.toFamily inputs) ≤
      ((prover.toFamily.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          (prover.toFamily.Q + 1 : Nat) *
            (actionCircuit.domainExponent *
              (2 / (Fintype.card Fp : ENNReal))) +
          (prover.toFamily.Q + (11 + actionCircuit.domainExponent) + 1 : Nat) *
            algebraicRootBudget (actionCircuit.shape.withProofParams actionProofParams)
              actionCircuit.domainExponent +
          (profile.advantage (actionDlogRandomOracleQueries actionProofParams prover.toFamily)
              (actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
            1 / Fintype.card Fp) +
          (prover.toFamily.Q + 1 : Nat) * ((20470 : Nat) / (Fintype.card Fp : ENNReal))) +
        (((prover.toFamily.Q + 1 : Nat) * (((20470 : Nat) : ENNReal) /
            (Fintype.card Fp : ENNReal)) +
          (prover.toFamily.Q + 1 : Nat) * (((2 ^ 23 : Nat) : ENNReal) /
            (Fintype.card Fp : ENNReal))) +
          ((prover.toFamily.Q + 1 : Nat) * (((2 ^ 35 : Nat) : ENNReal) /
              (Fintype.card Fp : ENNReal)) +
            ((prover.toFamily.Q + 1 : Nat) * (((2 ^ 21 : Nat) : ENNReal) /
                (Fintype.card Fp : ENNReal)) +
              (prover.toFamily.Q + 1 : Nat) * (((2 ^ 25 : Nat) : ENNReal) /
                (Fintype.card Fp : ENNReal))))) :=
  orchard_action_acceptFalseStatement_prob_le_captured B hB query hquery prover.toFamily inputs hvk hI
    hchar profile
    (execution.toCuts.xy_prob_le actionProofParams prover.toFamily
      (staticChecks_of_derived prover.toFamily hvk) inputs
      hvk hI hchar query derived_n_ne_zero (derived_n_yn hL))
    (execution.toCuts.beta_prob_le actionProofParams prover.toFamily
      (staticChecks_of_derived prover.toFamily hvk) inputs
      hvk hI hchar query cap_beta)
    (execution.toCuts.gamma_prob_le actionProofParams prover.toFamily
      (staticChecks_of_derived prover.toFamily hvk) inputs
      hvk hI hchar query cap_gamma)
    (execution.toCuts.theta_prob_le actionProofParams prover.toFamily
      (staticChecks_of_derived prover.toFamily hvk) inputs
      hvk hI hchar query cap_theta)

/-- Sequential exact-Action capstone for every bundle size.  All semantic surfaces are discharged
with tight linear caps, and the result is packaged as one DLOG advantage plus the complete
`numProofs`-indexed statistical model. -/
theorem orchard_action_acceptFalseStatement_prob_le_sequential_for
    (numProofs : ℕ) {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex
      actionCircuit.n → T)
    (hquery : Function.Injective query)
    (prover : SequentialOnlineAGMProver
      (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)))
    (inputs : Fin (actionProofParamsFor numProofs).numProofs →
      PublicInputs Fp)
    (hvk : ∀ basis, prover.toFamily.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis))
    (hI : ∀ basis, prover.toFamily.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) inputs)
      (straightLineRunOutput prover.toFamily basis O).1.proof.1
      (straightLineRunRecord prover.toFamily basis O) < scalarFieldOrder)
    (profile : StraightLineActionDlogProfile (actionProofParamsFor numProofs) prover.toFamily
      (staticChecks_of_derived_for numProofs prover.toFamily hvk) inputs hvk hI hchar B)
    {L : ℕ} (hL : L ≤ numProofs * 2 ^ 12)
    (execution : ActionSequentialExecution (actionProofParamsFor numProofs) prover.toFamily
      (staticChecks_of_derived_for numProofs prover.toFamily hvk) inputs hvk hI hchar 20470 L) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
            prover.toFamily.init.length 10 +
            3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionAcceptFalseStatementEventFor numProofs prover.toFamily inputs) ≤
      profile.advantage
          (actionDlogRandomOracleQueries (actionProofParamsFor numProofs) prover.toFamily)
          (actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
        actionStatisticalModelFor numProofs prover.toFamily.Q := by
  let static := staticChecks_of_derived_for numProofs prover.toFamily hvk
  refine le_trans
    (orchard_action_acceptFalseStatement_prob_le_captured_for numProofs B hB query hquery
      prover.toFamily inputs hvk hI hchar profile
      (xyBound :=
        (prover.toFamily.Q + 1 : ℕ) *
            ((20470 : ℕ) / (Fintype.card Fp : ENNReal)) +
          (prover.toFamily.Q + 1 : ℕ) *
            ((numProofs * 2 ^ 23 : ℕ) / (Fintype.card Fp : ENNReal)))
      (betaBound := (prover.toFamily.Q + 1 : ℕ) *
        ((numProofs * 950835027 : ℕ) / (Fintype.card Fp : ENNReal)))
      (gammaBound := (prover.toFamily.Q + 1 : ℕ) *
        ((numProofs * 73554 : ℕ) / (Fintype.card Fp : ENNReal)))
      (thetaBound := (prover.toFamily.Q + 1 : ℕ) *
        ((numProofs * 2 ^ 25 : ℕ) / (Fintype.card Fp : ENNReal)))
      ?_ ?_ ?_ ?_) ?_
  · exact execution.toCuts.xy_prob_le (actionProofParamsFor numProofs) prover.toFamily
      static inputs hvk hI hchar query derived_n_ne_zero
      (derived_n_yn_for numProofs hL)
  · exact execution.toCuts.beta_prob_le (actionProofParamsFor numProofs) prover.toFamily
      static inputs hvk hI hchar query (cap_beta_for numProofs)
  · exact execution.toCuts.gamma_prob_le (actionProofParamsFor numProofs) prover.toFamily
      static inputs hvk hI hchar query (cap_gamma_for numProofs)
  · exact execution.toCuts.theta_prob_le (actionProofParamsFor numProofs) prover.toFamily
      static inputs hvk hI hchar query (cap_theta_for numProofs)
  · unfold actionStatisticalModelFor actionCompressedStatisticalModelFor
      actionSemanticModelFor
    dsimp only
    push_cast
    simp only [div_eq_mul_inv]
    ring_nf
    apply le_rfl

/-- **Concrete exact-Action work-factor endpoint.**  The query ceiling is carried by the direct
profile, all six prover runs and terminal postprocessing are charged once to the combined DLOG
solver, and the compressed plus semantic statistical remainder is composed into `2^-84`. -/
theorem orchard_action_acceptFalseStatement_2pow123_workFactor_generatorRO
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex actionCircuit.n → T)
    (hquery : Function.Injective query)
    (prover : SequentialOnlineAGMProver
      (actionCircuit.shape.withProofParams actionProofParams))
    (inputs : Fin actionProofParams.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, prover.toFamily.vk basis = actionCircuit.toVerifierKey
      (ursOfAugmentedBasis actionCircuit.domainExponent basis))
    (hI : ∀ basis, prover.toFamily.instanceCommitment basis =
      actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.domainExponent basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis actionCircuit.domainExponent basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.domainExponent basis) inputs)
      (straightLineRunOutput prover.toFamily basis O).1.proof.1
      (straightLineRunRecord prover.toFamily basis O) < scalarFieldOrder)
    (profile : StraightLineActionDirectDlogProfile actionProofParams prover.toFamily
      (staticChecks_of_derived prover.toFamily hvk) inputs hvk hI hchar B (2 ^ 123))
    {L : Nat} (hL : L ≤ 2 ^ 12)
    (execution : ActionSequentialExecution actionProofParams prover.toFamily
      (staticChecks_of_derived prover.toFamily hvk) inputs hvk hI hchar 20470 L) :
    ((independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams actionProofParams) prover.toFamily.init.length 10
            + 3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionAcceptFalseStatementEvent prover.toFamily inputs) ≤
      profile.advantage (2 ^ 126) (2 ^ 126) + 1 / (2 ^ 84 : ENNReal)) ∧
      actionDlogRandomOracleQueries actionProofParams prover.toFamily ≤ 2 ^ 126 ∧
      actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤ 2 ^ 126 ∧
      ∀ basis O, 2 * prover.toFamily.straightLineDirectDecodeOps basis O ≤ 2 ^ 123 := by
  have hcost := profile.solverCost_le
  have hqueries : actionDlogRandomOracleQueries actionProofParams prover.toFamily ≤
      2 ^ 126 := by
    calc
      actionDlogRandomOracleQueries actionProofParams prover.toFamily ≤ 8 * 2 ^ 123 := hcost.1
      _ = 2 ^ 126 := by norm_num
  have hgroup : actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
      2 ^ 126 := by
    calc
      actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
          8 * 2 ^ 123 := hcost.2.1
      _ = 2 ^ 126 := by norm_num
  refine ⟨?_, hqueries, hgroup, hcost.2.2⟩
  refine le_trans
    (orchard_action_acceptFalseStatement_prob_le_sequential B hB query hquery prover inputs
      hvk hI hchar profile.toStraightLineActionDlogProfile hL execution) ?_
  calc
    ((prover.toFamily.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          (prover.toFamily.Q + 1 : Nat) *
            (actionCircuit.domainExponent *
              (2 / (Fintype.card Fp : ENNReal))) +
          (prover.toFamily.Q + (11 + actionCircuit.domainExponent) + 1 : Nat) *
            algebraicRootBudget (actionCircuit.shape.withProofParams actionProofParams)
              actionCircuit.domainExponent +
          (profile.advantage (actionDlogRandomOracleQueries actionProofParams prover.toFamily)
              (actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
            1 / Fintype.card Fp) +
          (prover.toFamily.Q + 1 : Nat) * ((20470 : Nat) /
            (Fintype.card Fp : ENNReal))) +
        (((prover.toFamily.Q + 1 : Nat) * (((20470 : Nat) : ENNReal) /
            (Fintype.card Fp : ENNReal)) +
          (prover.toFamily.Q + 1 : Nat) * (((2 ^ 23 : Nat) : ENNReal) /
            (Fintype.card Fp : ENNReal))) +
          ((prover.toFamily.Q + 1 : Nat) * (((2 ^ 35 : Nat) : ENNReal) /
              (Fintype.card Fp : ENNReal)) +
            ((prover.toFamily.Q + 1 : Nat) * (((2 ^ 21 : Nat) : ENNReal) /
                (Fintype.card Fp : ENNReal)) +
              (prover.toFamily.Q + 1 : Nat) * (((2 ^ 25 : Nat) : ENNReal) /
                (Fintype.card Fp : ENNReal))))) =
        profile.advantage (actionDlogRandomOracleQueries actionProofParams prover.toFamily)
            (actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
          actionStatisticalModel prover.toFamily.Q := by
      unfold actionStatisticalModel
      ring
    _ ≤ profile.advantage (2 ^ 126) (2 ^ 126) + 1 / (2 ^ 84 : ENNReal) :=
      add_le_add (profile.advantage_mono hqueries hgroup)
        (actionStatisticalModel_at_2pow123 profile.queryBound)

/-- Consensus-generic sequential capstone: `2^123` work reduces to `2^126` DLOG resources with a
`2^-83` statistical remainder and explicit transcript bias. -/
theorem orchard_action_acceptFalseStatement_2pow123_workFactor_generatorRO_for
    (numProofs : ℕ) (hn : numProofs ≤ orchardConsensusMaxProofs)
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex
      actionCircuit.n → T)
    (hquery : Function.Injective query)
    (prover : SequentialOnlineAGMProver
      (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs)))
    (inputs : Fin (actionProofParamsFor numProofs).numProofs →
      PublicInputs Fp)
    (hvk : ∀ basis, prover.toFamily.vk basis =
      actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis))
    (hI : ∀ basis, prover.toFamily.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis
          actionCircuit.domainExponent basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis
          actionCircuit.domainExponent basis) inputs)
      (straightLineRunOutput prover.toFamily basis O).1.proof.1
      (straightLineRunRecord prover.toFamily basis O) < scalarFieldOrder)
    (profile : StraightLineActionDirectDlogProfile
      (actionProofParamsFor numProofs) prover.toFamily
      (staticChecks_of_derived_for numProofs prover.toFamily hvk) inputs hvk hI hchar B
      (2 ^ 123))
    {L : ℕ} (hL : L ≤ numProofs * 2 ^ 12)
    (execution : ActionSequentialExecution (actionProofParamsFor numProofs) prover.toFamily
      (staticChecks_of_derived_for numProofs prover.toFamily hvk) inputs hvk hI hchar 20470 L) :
    ((independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
            prover.toFamily.init.length 10 +
            3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionAcceptFalseStatementEventFor numProofs prover.toFamily inputs) ≤
      profile.advantage (2 ^ 126) (2 ^ 126) + 1 / (2 ^ 83 : ENNReal)) ∧
      actionDlogRandomOracleQueries (actionProofParamsFor numProofs) prover.toFamily ≤
        2 ^ 126 ∧
      actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤ 2 ^ 126 ∧
      (∀ basis O, 2 * prover.toFamily.straightLineDirectDecodeOps basis O ≤ 2 ^ 123) ∧
      ∀ (actual : PMF
          ((↥(Set.range query) → VestaG) ×
            (BTranscript Fp VestaG
              (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
                prover.toFamily.init.length 10 +
                3 * actionCircuit.domainExponent) → Fp)))
        (εBias : ENNReal),
        PMFEventBiasLE actual
          (independentProductPMF (orchardGeneratorROSetup query)
            (PMF.uniformOfFintype
              (BTranscript Fp VestaG
                (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
                  prover.toFamily.init.length 10 +
                  3 * actionCircuit.domainExponent) → Fp)))
          εBias →
        actual.toOuterMeasure
            ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
              actionAcceptFalseStatementEventFor numProofs prover.toFamily inputs) ≤
          (profile.advantage (2 ^ 126) (2 ^ 126) + 1 / (2 ^ 83 : ENNReal)) + εBias := by
  have hcost := profile.solverCost_le
  have hqueries :
      actionDlogRandomOracleQueries (actionProofParamsFor numProofs) prover.toFamily ≤
        2 ^ 126 := by
    calc
      actionDlogRandomOracleQueries (actionProofParamsFor numProofs) prover.toFamily ≤
          8 * 2 ^ 123 := hcost.1
      _ = 2 ^ 126 := by norm_num
  have hgroup :
      actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
        2 ^ 126 := by
    calc
      actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork ≤
          8 * 2 ^ 123 := hcost.2.1
      _ = 2 ^ 126 := by norm_num
  have hprob :
      (independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype
          (BTranscript Fp VestaG
            (preIpaLen (actionCircuit.shape.withProofParams (actionProofParamsFor numProofs))
              prover.toFamily.init.length 10 +
              3 * actionCircuit.domainExponent) → Fp))).toOuterMeasure
          ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
            actionAcceptFalseStatementEventFor numProofs prover.toFamily inputs) ≤
        profile.advantage (2 ^ 126) (2 ^ 126) + 1 / (2 ^ 83 : ENNReal) := by
    refine le_trans
      (orchard_action_acceptFalseStatement_prob_le_sequential_for numProofs B hB query hquery
        prover inputs hvk hI hchar profile.toStraightLineActionDlogProfile hL execution) ?_
    exact add_le_add (profile.advantage_mono hqueries hgroup)
      (actionStatisticalModelFor_at_2pow123 hn profile.queryBound)
  refine ⟨hprob, hqueries, hgroup, hcost.2.2, ?_⟩
  intro actual εBias hbias
  exact event_measure_le_of_bias hbias _ hprob

end Zcash.Snark.Fixture
