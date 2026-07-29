import Zcash.Snark.Fixtures.SingleAction.StaticChecks
import Zcash.Snark.Soundness.Composition.ScheduleBudget
import Zcash.Snark.Soundness.AGM.StraightLineFiniteSecurity
import Zcash.Snark.Keygen.Certificate
import Zcash.Circuits.Integration.StraightLineActionEvent

/-!
# The captured Action capstone event and its composed bound

Issue #128's assembly, first stage: the exact terminal event, the captured static checks and
`x`-squeeze schedule rebuilt at the circuit-derived shape, and the composition of the compressed
straight-line bound with the Action bundle-statement fusion.

Everything here lives at `actionProofParams.mergeDerived actionCircuit` — the derived one-proof
shape the Action semantics are stated at — with no shape casts in any statement: the derived
verifying key's scalar fields never read the URS, so the single-Action captured facts transfer
through nine field equalities.

The four semantic challenge budgets remain premises at this stage; instantiating them concretely
is the remaining #128 pricing work.
-/

namespace Zcash.Snark.Fixture

open Zcash.Snark
open Zcash.Snark.ActionTerminal
open Zcash.Snark.Keygen (actionProofParams shape_eq_mergeDerived vk_eq_toVerifierKey)
open Zcash.Circuits Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder URS)
open scoped ENNReal

/-! ## The exact terminal event -/

/-- **The end-to-end failure event** (issue #128 F1): the deployed verifier accepts and the
Orchard Action bundle statement does not hold — modulo the explicit nontrivial-relation branch,
which the reduction converts into a Vesta DLOG break rather than assuming away. -/
noncomputable def actionAcceptFalseEvent
    (family : ComputedStraightLineDeployedFSFamily
      (actionProofParams.mergeDerived actionCircuit))
    (inputs : Fin (actionProofParams.mergeDerived actionCircuit).numProofs →
      PublicInputs Fp) :
    Set ((AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionProofParams.mergeDerived actionCircuit) family.init.length 10
          + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp)) :=
  family.straightLineConstraintSemanticFailureEvent
    (actionStatementDecoded actionProofParams family inputs)

/-! ## The derived key's captured scalars -/

/-- Field projections commute with the shape cast when the field's type does not mention the
shape. -/
private theorem castVk_field {s₁ s₂ : Shape} (h : s₁ = s₂)
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
private theorem castVk_lookup {s₁ s₂ : Shape} (h : s₁ = s₂)
    (K : VerifyingKey s₁ Fp VestaG) (l : Fin s₁.numLookups) :
    K.lookupInputExprs l =
      (h ▸ K : VerifyingKey s₂ Fp VestaG).lookupInputExprs
        (Fin.cast (congrArg Shape.numLookups h) l) ∧
    K.lookupTableExprs l =
      (h ▸ K : VerifyingKey s₂ Fp VestaG).lookupTableExprs
        (Fin.cast (congrArg Shape.numLookups h) l) := by
  cases h
  exact ⟨rfl, rfl⟩

/-- **The derived Action key carries the captured scalar data at every URS.**  The scalar fields
never read the URS, and at the captured URS the keygen certificate pins them to the capture. -/
theorem derived_scalars (urs : URS VestaG) :
    (actionCircuit.toVerifierKey actionProofParams urs).omega = vk.omega ∧
    (actionCircuit.toVerifierKey actionProofParams urs).n = vk.n ∧
    (actionCircuit.toVerifierKey actionProofParams urs).gates = vk.gates ∧
    (actionCircuit.toVerifierKey actionProofParams urs).instanceQueryLayout =
      vk.instanceQueryLayout ∧
    (actionCircuit.toVerifierKey actionProofParams urs).adviceQueryLayout =
      vk.adviceQueryLayout ∧
    (actionCircuit.toVerifierKey actionProofParams urs).fixedQueryLayout =
      vk.fixedQueryLayout ∧
    (actionCircuit.toVerifierKey actionProofParams urs).permutationChunks =
      vk.permutationChunks := by
  have hcast := castVk_field shape_eq_mergeDerived
    (actionCircuit.toVerifierKey actionProofParams capturedURS)
  have hvk : (shape_eq_mergeDerived ▸
      actionCircuit.toVerifierKey actionProofParams capturedURS :
      VerifyingKey shape Fp VestaG) = vk := vk_eq_toVerifierKey.symm
  exact ⟨hcast.1.trans (congrArg VerifyingKey.omega hvk),
    hcast.2.1.trans (congrArg VerifyingKey.n hvk),
    hcast.2.2.1.trans (congrArg VerifyingKey.gates hvk),
    hcast.2.2.2.1.trans (congrArg VerifyingKey.instanceQueryLayout hvk),
    hcast.2.2.2.2.1.trans (congrArg VerifyingKey.adviceQueryLayout hvk),
    hcast.2.2.2.2.2.1.trans (congrArg VerifyingKey.fixedQueryLayout hvk),
    hcast.2.2.2.2.2.2.trans (congrArg VerifyingKey.permutationChunks hvk)⟩

/-- The derived key's lookup expressions are the captured ones, up to the index cast. -/
theorem derived_lookups (urs : URS VestaG)
    (l : Fin (actionProofParams.mergeDerived actionCircuit).numLookups) :
    (actionCircuit.toVerifierKey actionProofParams urs).lookupInputExprs l =
      vk.lookupInputExprs
        (Fin.cast (congrArg Shape.numLookups shape_eq_mergeDerived) l) ∧
    (actionCircuit.toVerifierKey actionProofParams urs).lookupTableExprs l =
      vk.lookupTableExprs
        (Fin.cast (congrArg Shape.numLookups shape_eq_mergeDerived) l) := by
  have hcast := castVk_lookup shape_eq_mergeDerived
    (actionCircuit.toVerifierKey actionProofParams capturedURS) l
  have hvk : (shape_eq_mergeDerived ▸
      actionCircuit.toVerifierKey actionProofParams capturedURS :
      VerifyingKey shape Fp VestaG) = vk := vk_eq_toVerifierKey.symm
  constructor
  · exact hcast.1.trans (by rw [hvk])
  · exact hcast.2.trans (by rw [hvk])

/-! ## The captured checks and schedule at the derived shape -/

/-- The derived shape's count fields are the captured ones. -/
private theorem md_counts :
    (actionProofParams.mergeDerived actionCircuit).k = shape.k ∧
    (actionProofParams.mergeDerived actionCircuit).numAdviceQueries =
      shape.numAdviceQueries ∧
    (actionProofParams.mergeDerived actionCircuit).numInstanceQueries =
      shape.numInstanceQueries ∧
    (actionProofParams.mergeDerived actionCircuit).numFixedQueries =
      shape.numFixedQueries ∧
    (actionProofParams.mergeDerived actionCircuit).numQuotientPieces =
      shape.numQuotientPieces :=
  ⟨congrArg Shape.k shape_eq_mergeDerived,
    congrArg Shape.numAdviceQueries shape_eq_mergeDerived,
    congrArg Shape.numInstanceQueries shape_eq_mergeDerived,
    congrArg Shape.numFixedQueries shape_eq_mergeDerived,
    congrArg Shape.numQuotientPieces shape_eq_mergeDerived⟩

/-- **The captured static checks at the derived key** (issue #128 F3): the five decided facts,
transferred through the derived key's scalar equalities. -/
theorem staticChecks_of_derived
    (family : ComputedStraightLineDeployedFSFamily
      (actionProofParams.mergeDerived actionCircuit))
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey actionProofParams
      (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis)) :
    DeployedConstraintStaticChecks family.toRootFamily where
  adviceLength := fun basis => by
    rw [hvk basis, (derived_scalars _).2.2.2.2.1, md_counts.2.1]
    exact vk_advice_layout_length
  instanceLength := fun basis => by
    rw [hvk basis, (derived_scalars _).2.2.2.1, md_counts.2.2.1]
    exact vk_instance_layout_length
  fixedLength := fun basis => by
    rw [hvk basis, (derived_scalars _).2.2.2.2.2.1, md_counts.2.2.2.1]
    exact vk_fixed_layout_length
  omegaOrder := fun basis => by
    rw [hvk basis, (derived_scalars _).1, (derived_scalars _).2.1]
    exact vk_omega_order
  characteristic := fun basis => by
    rw [hvk basis, (derived_scalars _).2.1]
    exact vk_n_cast_ne_zero

/-- **The captured `x`-squeeze schedule at the derived key** (issue #128 F3): the degree caps
transfer through the scalar equalities, and pinning is the family's own derived projection. -/
noncomputable def schedule_of_derived
    (family : ComputedStraightLineDeployedFSFamily
      (actionProofParams.mergeDerived actionCircuit))
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey actionProofParams
      (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis)) :
    DeployedConstraintXSqueezeSchedule family.toRootFamily
      ((20470 : ℕ) / (Fintype.card Fp : ℝ≥0∞)) := by
  have hk : 2 ^ (actionProofParams.mergeDerived actionCircuit).k - 1 = 2047 := by
    rw [md_counts.1]
    norm_num [shape]
  have h := deployedConstraintXSqueezeSchedule_of_pinned family.toRootFamily
    (B := 2047) (W := 7) (Dc := 8188) (D := 20470) (Dq := 20470)
    (by norm_num) (le_of_eq hk)
    (fun basis => by rw [hvk basis, (derived_scalars _).2.1]; exact vk_n_pred_le)
    (fun basis => by rw [hvk basis, (derived_scalars _).2.2.1]; exact vk_gates_degree_le)
    (fun basis => by
      rw [hvk basis, (derived_scalars _).2.2.2.2.2.2]; exact vk_chunk_width_le)
    (fun basis l => by
      rw [hvk basis, (derived_lookups _ l).1]
      exact vk_lookup_input_degree_le _)
    (fun basis l => by
      rw [hvk basis, (derived_lookups _ l).2]
      exact vk_lookup_table_degree_le _)
    (fun basis => by
      rw [hvk basis, (derived_scalars _).2.1, md_counts.2.2.2.2, ← hk, md_counts.1]
      exact vk_quotient_tail_le)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    family.constraintXTrace.toPinning
  simpa using h

/-! ## The composed bound -/

/-- **The captured Action failure bound, composed** (issue #128 F4/F5): the probability of the
end-to-end failure event is at most the compressed straight-line knowledge error at the derived
key plus the four semantic challenge budgets.  The terminal data — batch openings, member
decodes, acceptance, and the canonical quotient — all come from the same straight-line decoded
run, via the fusion this bound instantiates.

The four budgets remain premises here; the remaining #128 pricing work discharges them
concretely. -/
theorem orchard_action_acceptFalse_prob_le_captured
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ (actionProofParams.mergeDerived actionCircuit).k) → T)
    (hquery : Function.Injective query)
    (family : ComputedStraightLineDeployedFSFamily
      (actionProofParams.mergeDerived actionCircuit))
    (inputs : Fin (actionProofParams.mergeDerived actionCircuit).numProofs →
      PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey actionProofParams
      (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis) inputs)
    (hchar : ∀ basis O, deployedX4PairCount
      (actionCircuit.toVerifierKey actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment actionProofParams
        (ursOfAugmentedBasis (actionProofParams.mergeDerived actionCircuit).k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder)
    (profile : family.StraightLineConstraintDlogProfile B)
    {xyBound betaBound gammaBound thetaBound : ENNReal}
    (hXY : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionProofParams.mergeDerived actionCircuit) family.init.length 10
            + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionXYFailureEvent actionProofParams family
            (staticChecks_of_derived family hvk) inputs hvk hI hchar) ≤ xyBound)
    (hBeta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionProofParams.mergeDerived actionCircuit) family.init.length 10
            + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionBetaFailureEvent actionProofParams family
            (staticChecks_of_derived family hvk) inputs hvk hI hchar) ≤ betaBound)
    (hGamma : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionProofParams.mergeDerived actionCircuit) family.init.length 10
            + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionGammaFailureEvent actionProofParams family
            (staticChecks_of_derived family hvk) inputs hvk hI hchar) ≤ gammaBound)
    (hTheta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionProofParams.mergeDerived actionCircuit) family.init.length 10
            + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionThetaFailureEvent actionProofParams family
            (staticChecks_of_derived family hvk) inputs hvk hI hchar) ≤ thetaBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionProofParams.mergeDerived actionCircuit) family.init.length 10
            + 3 * (actionProofParams.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionAcceptFalseEvent family inputs)
      ≤ ((family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
          (family.Q + 1 : ℕ) *
            ((actionProofParams.mergeDerived actionCircuit).k *
              (2 / (Fintype.card Fp : ENNReal))) +
          (family.Q + (11 + (actionProofParams.mergeDerived actionCircuit).k) + 1 : ℕ) *
            algebraicRootBudget (actionProofParams.mergeDerived actionCircuit)
              (actionProofParams.mergeDerived actionCircuit).k +
          (profile.advantage family.straightLineDlogRandomOracleQueries
              (ComputedStraightLineDeployedFSFamily.straightLineDlogGroupWork
                profile.proverGroupWork profile.reductionGroupWork) +
            1 / Fintype.card Fp) +
          (family.Q + 1 : ℕ) * ((20470 : ℕ) / (Fintype.card Fp : ℝ≥0∞))) +
        (xyBound + (betaBound + (gammaBound + thetaBound))) :=
  actionBundleStatementFailure_prob_le_of_compressed_bound actionProofParams family
    (staticChecks_of_derived family hvk) inputs hvk hI hchar query
    (family.straightLineConstraintFailure_prob_le_of_generatorRO_dlogProfile B hB query hquery
      (staticChecks_of_derived family hvk) (schedule_of_derived family hvk) profile)
    hXY hBeta hGamma hTheta

end Zcash.Snark.Fixture
