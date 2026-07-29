import Zcash.Snark.Fixtures.MultiAction.StaticChecks
import Zcash.Snark.Fixtures.MultiAction.Schedule
import Zcash.Snark.Soundness.AGM.StraightLineFiniteSecurity

/-!
# Captured-key straight-line AGM knowledge-error endpoint

This is the deployed AGM endpoint, stated through the fixed-call straight-line relation finder.
-/

namespace Zcash.Snark.Fixture2

open Zcash.Snark
open Zcash.Snark.ComputedStraightLineDeployedFSFamily (straightLineDlogGroupWork)
open scoped ENNReal

/-- Captured-key straight-line AGM **compressed-identity** capstone: soundness against every
bounded sequential online-AGM Fiat–Shamir adversary — `SequentialPreXProver.lift` presents any
such prover as a family, and this bound applies to the result.  The family supplies the staged
IPA representation trace, the deployed root chronology, and the constraint-`x` chronology
`x` pinning is derived from; the captured key discharges the static checks and degree budget.
The captured premise pins scalar metadata, layouts, and expressions only — no literal fixture
commitment equality across sampled AGM bases.  The only computational term is the explicit
finite-security Vesta DLOG profile.  Row-level semantics require the four additional budgets of
`straightLineConstraintSemanticFailure_prob_le_of_generatorRO_dlogProfile`. -/
theorem orchard_deployed_knowledge_error_captured_straightLine
    (B : VestaG)
    (family : ComputedStraightLineDeployedFSFamily shape)
    (hvk : forall basis, CapturedVerifierKeyProfile (family.vk basis))
    (profile : family.StraightLineConstraintDlogProfile B) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        (family.straightLineConstraintFailureSet B
          (deployedConstraintStaticChecks_of_captured family.toRootFamily hvk)) <=
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          (shape.k * (2 / (Fintype.card Fp : ENNReal))) +
        (family.Q + (11 + shape.k) + 1 : Nat) *
          algebraicRootBudget shape shape.k +
        (profile.advantage family.straightLineDlogRandomOracleQueries
            (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
          1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          ((20470 : Nat) / (Fintype.card Fp : ENNReal)) :=
  family.straightLineConstraintFailure_prob_le_of_dlogProfile B
    (deployedConstraintStaticChecks_of_captured family.toRootFamily hvk)
    (deployedConstraintXSqueezeSchedule_captured family.toConstraintFamily hvk) profile

/-- Generator-random-oracle form of the captured straight-line **compressed-identity** endpoint;
row-level semantics are the four-budget promotion
`straightLineConstraintSemanticFailure_prob_le_of_generatorRO_dlogProfile`. -/
theorem orchard_deployed_knowledge_error_captured_straightLine_generatorRO
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T) (hquery : Function.Injective query)
    (family : ComputedStraightLineDeployedFSFamily shape)
    (hvk : forall basis, CapturedVerifierKeyProfile (family.vk basis))
    (profile : family.StraightLineConstraintDlogProfile B) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintFailureEvent
            (deployedConstraintStaticChecks_of_captured family.toRootFamily hvk)) <=
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          (shape.k * (2 / (Fintype.card Fp : ENNReal))) +
        (family.Q + (11 + shape.k) + 1 : Nat) *
          algebraicRootBudget shape shape.k +
        (profile.advantage family.straightLineDlogRandomOracleQueries
            (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
          1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          ((20470 : Nat) / (Fintype.card Fp : ENNReal)) :=
  family.straightLineConstraintFailure_prob_le_of_generatorRO_dlogProfile
    B hB query hquery (deployedConstraintStaticChecks_of_captured family.toRootFamily hvk)
    (deployedConstraintXSqueezeSchedule_captured family.toConstraintFamily hvk) profile

/-- **Direct captured-key adapter endpoint.**  Unlike the theorem above, this form does not ask a
caller to supply an already assembled `ComputedStraightLineDeployedFSFamily`.  It starts at the
representation-carrying online prover model produced by `ComputedOnlineMemberFSFamily.ofProofData`
and combines its deployed-root, IPA-round, and constraint-`x` traces with `ofCovered`.  The
captured fixture supplies the verifier's scalar/layout profile; no new proof fixture is needed. -/
theorem orchard_deployed_knowledge_error_captured_straightLine_direct_generatorRO
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T) (hquery : Function.Injective query)
    (online : ComputedOnlineMemberFSFamily shape)
    (rootTrace : DeployedRootOnlineTrace online.toFamily
      (deployedRootOutcomeOfCovered online))
    (ipaTrace : StraightLineIpaOnlineTrace online.toFamily)
    (xTrace : DeployedConstraintXOnlineTrace
      (ComputedDeployedRootFSFamily.ofCovered online rootTrace))
    (hvk : forall basis, CapturedVerifierKeyProfile (online.vk basis))
    (profile :
      let family := ComputedStraightLineDeployedFSFamily.ofCovered
        online rootTrace ipaTrace xTrace
      family.StraightLineConstraintDlogProfile B) :
    let family := ComputedStraightLineDeployedFSFamily.ofCovered
      online rootTrace ipaTrace xTrace
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintFailureEvent
            (deployedConstraintStaticChecks_of_captured family.toRootFamily hvk)) <=
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          (shape.k * (2 / (Fintype.card Fp : ENNReal))) +
        (family.Q + (11 + shape.k) + 1 : Nat) *
          algebraicRootBudget shape shape.k +
        (profile.advantage family.straightLineDlogRandomOracleQueries
            (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
          1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          ((20470 : Nat) / (Fintype.card Fp : ENNReal)) := by
  dsimp only
  exact orchard_deployed_knowledge_error_captured_straightLine_generatorRO
    B hB query hquery
    (ComputedStraightLineDeployedFSFamily.ofCovered online rootTrace ipaTrace xTrace)
    hvk profile

end Zcash.Snark.Fixture2
