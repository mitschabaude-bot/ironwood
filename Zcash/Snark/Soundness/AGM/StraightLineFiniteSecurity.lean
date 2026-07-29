import Zcash.Snark.Soundness.Composition.StraightLineConstraint
import Zcash.Snark.Soundness.Composition.DirectPathCost

/-!
# Finite-security profiles for the primary straight-line AGM reduction

The probability capstone and the work-factor interpretation are deliberately separate.  This
module records random-oracle queries, group work, and the actual direct-coordinate field/data work
as distinct quantities.  It does not assert a generic-group DLOG success formula.  A caller
supplies the finite-security Vesta DLOG advantage for the resulting concrete solver cost.
-/

namespace Zcash.Snark

open scoped ENNReal

local instance vestaInhabitedStraightLineFiniteSecurity : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

namespace ComputedStraightLineDeployedFSFamily

/-- Conservative random-oracle work of the complete straight-line finder.  One direct IPA run
uses `Q` queries.  The three possible wrapped replays each add the `11+k` designated reads. -/
def straightLineDlogRandomOracleQueries
    (family : ComputedStraightLineDeployedFSFamily shape) : Nat :=
  4 * family.Q + 3 * (11 + shape.k)

/-- Concrete group-work accounting: at most four prover invocations plus the algebraic
postprocessing performed by the reduction. -/
def straightLineDlogGroupWork (proverGroupWork reductionGroupWork : Nat) : Nat :=
  4 * proverGroupWork + reductionGroupWork

/-- The modeled non-group work of the actual direct-coordinate decode on one oracle table.  The
source length is not a caller-chosen reduction-work number: it is read from the represented proof
and verifier-fixed representations that the finder itself consumes. -/
def straightLineDirectDecodeOps
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) : Nat :=
  let pnu := (wrappedAdversary family.toFamily basis).run O
  deployedDirectDecodeOps (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
    (wrappedPreIpaRecord pnu)
    (pnu.1.algebraicProof.preX1AssemblySource
      (family.fixedRepresentations basis)).length

/-- The direct-coordinate component of the reduction has the proved field-independent
shape-polynomial cost, instantiated at the exact source traversed on this run.  Group operations
are absent from this path; this counts its field operations and data traversal. -/
theorem straightLineDirectDecodeOps_le
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) :
    family.straightLineDirectDecodeOps basis O <=
      (shape.numPointSets + 1) *
        (queryBudget shape *
            ((((wrappedAdversary family.toFamily basis).run O).1.algebraicProof.preX1AssemblySource
                (family.fixedRepresentations basis)).length +
              2 * 2 ^ shape.k + 5) +
          (2 ^ shape.k + 2)) := by
  exact deployedDirectDecodeOps_le _ _ _ _ _

/-- Finite-security DLOG premise for the complete straight-line finder.  The advantage function
receives random-oracle queries and group operations separately; the profile also records the
prover and postprocessing components used to obtain the latter. -/
structure StraightLineConstraintDlogProfile (B : VestaG)
    (family : ComputedStraightLineDeployedFSFamily shape) where
  proverGroupWork : Nat
  reductionGroupWork : Nat
  advantage : Nat -> Nat -> ENNReal
  advantage_mono : forall {q q' g g'}, q <= q' -> g <= g' ->
    advantage q g <= advantage q' g'
  hardness : TextbookDLWithCoinsAdvantageLE B
    family.straightLineConstraintRelationFinder
    (advantage family.straightLineDlogRandomOracleQueries
      (straightLineDlogGroupWork proverGroupWork reductionGroupWork))

/-- The profile automatically supplies the fixed-call DLOG premise because the pointwise
four-invocation bound is proved by the finder itself. -/
theorem StraightLineConstraintDlogProfile.fixedCalls
    {B : VestaG} {family : ComputedStraightLineDeployedFSFamily shape}
    (profile : StraightLineConstraintDlogProfile B family) :
    TextbookDLWithCoinsFixedCallsAdvantageLE B
      family.straightLineConstraintRelationFinder
      family.straightLineConstraintRelationFinderCalls 4
      (profile.advantage family.straightLineDlogRandomOracleQueries
        (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork)) :=
  (family.straightLineConstraint_fixedCalls_iff B).2 profile.hardness

/-- Finite-security spelling of the straight-line constraint capstone. -/
theorem straightLineConstraintFailure_prob_le_of_dlogProfile
    (B : VestaG) (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    {epsilonX : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family.toRootFamily epsilonX)
    (profile : StraightLineConstraintDlogProfile B family) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) -> Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        (family.straightLineConstraintFailureSet B static) <=
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          (shape.k * (2 / (Fintype.card Fp : ENNReal))) +
        (family.Q + (11 + shape.k) + 1 : Nat) *
          algebraicRootBudget shape shape.k +
        (profile.advantage family.straightLineDlogRandomOracleQueries
            (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
          1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) * epsilonX :=
  family.straightLineConstraintFailure_prob_le_of_fixedCallsTextbookDL B static schedule
    profile.fixedCalls

/-- Generator-random-oracle form of the finite-security capstone. -/
theorem straightLineConstraintFailure_prob_le_of_generatorRO_dlogProfile
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T) (hquery : Function.Injective query)
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    {epsilonX : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family.toRootFamily epsilonX)
    (profile : StraightLineConstraintDlogProfile B family) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintFailureEvent static) <=
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          (shape.k * (2 / (Fintype.card Fp : ENNReal))) +
        (family.Q + (11 + shape.k) + 1 : Nat) *
          algebraicRootBudget shape shape.k +
        (profile.advantage family.straightLineDlogRandomOracleQueries
            (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
          1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) * epsilonX := by
  rw [family.straightLineConstraintFailure_prob_eq_of_uniformURS
    (orchardGeneratorROSetup query) B static (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO shape.k B hB query hquery)]
  exact family.straightLineConstraintFailure_prob_le_of_dlogProfile B static schedule profile

/-- **Semantic straight-line capstone.** The compressed-identity finite-security bound is
augmented by the four named challenge budgets; `hsemantic` supplies the row-level upgrade exactly
as on the recursive side. -/
theorem straightLineConstraintSemanticFailure_prob_le_of_generatorRO_dlogProfile
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T) (hquery : Function.Injective query)
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (semanticDecoded : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) -> Prop)
    (badY badBeta badGamma badTheta :
      Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)))
    {epsilonX yBound betaBound gammaBound thetaBound : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family.toRootFamily epsilonX)
    (profile : StraightLineConstraintDlogProfile B family)
    (hsemantic : family.StraightLineConstraintSemanticUpgradeContained static
      semanticDecoded badY badBeta badGamma badTheta)
    (hY : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badY) <= yBound)
    (hBeta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badBeta) <= betaBound)
    (hGamma : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badGamma) <= gammaBound)
    (hTheta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badTheta) <= thetaBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintSemanticFailureEvent semanticDecoded)
      <= ((family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          (family.Q + 1 : Nat) *
            (shape.k * (2 / (Fintype.card Fp : ENNReal))) +
          (family.Q + (11 + shape.k) + 1 : Nat) *
            algebraicRootBudget shape shape.k +
          (profile.advantage family.straightLineDlogRandomOracleQueries
              (straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
            1 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * epsilonX)
        + (yBound + (betaBound + (gammaBound + thetaBound))) :=
  family.straightLineConstraintSemanticFailure_prob_le_of_compressed_bound query static
    semanticDecoded badY badBeta badGamma badTheta hsemantic
    (family.straightLineConstraintFailure_prob_le_of_generatorRO_dlogProfile
      B hB query hquery static schedule profile)
    hY hBeta hGamma hTheta

/-! ## Work-factor arithmetic -/

/-- A four-call reduction with at most twenty-eight adversary-work units of postprocessing has at
most a five-bit multiplicative overhead.  The `28` is an explicit profile obligation, not an
unstated claim about the implementation. -/
theorem straightLineDlogGroupWork_le_32_mul
    {T proverGroupWork reductionGroupWork : Nat}
    (hprover : proverGroupWork <= T)
    (hreduction : reductionGroupWork <= 28 * T) :
    straightLineDlogGroupWork proverGroupWork reductionGroupWork <= 32 * T := by
  unfold straightLineDlogGroupWork
  omega

/-- At the consensus IPA depth, the random-oracle side also fits the same five-bit overhead for
every nonzero work target. -/
theorem straightLineDlogRandomOracleQueries_le_32_mul
    (family : ComputedStraightLineDeployedFSFamily shape) {T : Nat}
    (hk : shape.k = 11) (hT : 3 <= T) (hQ : family.Q <= T) :
    family.straightLineDlogRandomOracleQueries <= 32 * T := by
  unfold straightLineDlogRandomOracleQueries
  omega

/-- At the consensus IPA depth, the exact query formula needs only three overhead bits once the
work target is at least seventeen: `4*Q + 66 <= 8*T`. -/
theorem straightLineDlogRandomOracleQueries_le_eight_mul
    (family : ComputedStraightLineDeployedFSFamily shape) {T : Nat}
    (hk : shape.k = 11) (hT : 17 <= T) (hQ : family.Q <= T) :
    family.straightLineDlogRandomOracleQueries <= 8 * T := by
  unfold straightLineDlogRandomOracleQueries
  omega

/-- Four prover invocations plus an explicitly bounded postprocessing allowance fit an eightfold
group-work envelope.  The allowance covers the verifier MSM evaluated by the IPA relation finder;
only the direct-coordinate decoder itself is group-free. -/
theorem straightLineDlogGroupWork_le_eight_mul
    {T proverGroupWork reductionGroupWork : Nat}
    (hprover : proverGroupWork <= T) (hreduction : reductionGroupWork <= T) :
    straightLineDlogGroupWork proverGroupWork reductionGroupWork <= 8 * T := by
  unfold straightLineDlogGroupWork
  omega

/-- Primary cost profile for the direct straight-line route.  It keeps the direct decoder's
group-free cost separate from the complete relation finder: `reductionGroupWork` explicitly
accounts for the verifier MSM and other group postprocessing outside the prover invocations.  The
field/data certificate covers both possible direct-decode executions on the fallback path.  The
reduction group-work bound remains an explicit profile premise until the verifier MSM is
instrumented with an operational counter. -/
structure StraightLineDirectDlogProfile (B : VestaG)
    (family : ComputedStraightLineDeployedFSFamily shape) (T : Nat) where
  proverGroupWork : Nat
  reductionGroupWork : Nat
  advantage : Nat -> Nat -> ENNReal
  advantage_mono : forall {q q' g g'}, q <= q' -> g <= g' ->
    advantage q g <= advantage q' g'
  hardness : TextbookDLWithCoinsAdvantageLE B
    family.straightLineConstraintRelationFinder
    (advantage family.straightLineDlogRandomOracleQueries
      (straightLineDlogGroupWork proverGroupWork reductionGroupWork))
  ipaDepth : shape.k = 11
  targetAtLeastSeventeen : 17 <= T
  queryBound : family.Q <= T
  proverWorkBound : proverGroupWork <= T
  reductionWorkBound : reductionGroupWork <= T
  directDecodeWorkBound : forall basis O,
    2 * family.straightLineDirectDecodeOps basis O <= T

/-- Forget the explicit direct-route cost certificates while retaining the DLOG premise. -/
def StraightLineDirectDlogProfile.toStraightLineConstraintDlogProfile
    {B : VestaG} {family : ComputedStraightLineDeployedFSFamily shape} {T : Nat}
    (profile : StraightLineDirectDlogProfile B family T) :
    StraightLineConstraintDlogProfile B family where
  proverGroupWork := profile.proverGroupWork
  reductionGroupWork := profile.reductionGroupWork
  advantage := profile.advantage
  advantage_mono := profile.advantage_mono
  hardness := profile.hardness

/-- Solver-resource consequences of the direct profile: three bits for oracle queries and complete
group work, plus a pointwise bound covering both possible direct-decode executions. -/
theorem StraightLineDirectDlogProfile.solverCost_le
    {B : VestaG} {family : ComputedStraightLineDeployedFSFamily shape} {T : Nat}
    (profile : StraightLineDirectDlogProfile B family T) :
    family.straightLineDlogRandomOracleQueries <= 8 * T ∧
      straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork <= 8 * T ∧
      forall basis O, 2 * family.straightLineDirectDecodeOps basis O <= T := by
  exact
    ⟨family.straightLineDlogRandomOracleQueries_le_eight_mul
        profile.ipaDepth profile.targetAtLeastSeventeen profile.queryBound,
      straightLineDlogGroupWork_le_eight_mul
        profile.proverWorkBound profile.reductionWorkBound,
      profile.directDecodeWorkBound⟩

/-- Compatibility profile for a caller-supplied five-bit envelope.  This is not the primary
deployed interpretation: its `reductionWorkBound` is deliberately abstract, whereas
`StraightLineDirectDlogProfile` separately accounts for reduction group work and carries the
two-execution direct-decode cost. -/
structure StraightLineFiveBitDlogProfile (B : VestaG)
    (family : ComputedStraightLineDeployedFSFamily shape) (T : Nat)
    extends StraightLineConstraintDlogProfile B family where
  ipaDepth : shape.k = 11
  targetAtLeastThree : 3 <= T
  queryBound : family.Q <= T
  proverWorkBound : toStraightLineConstraintDlogProfile.proverGroupWork <= T
  reductionWorkBound :
    toStraightLineConstraintDlogProfile.reductionGroupWork <= 28 * T

/-- Both separately recorded solver resources fit the five-bit overhead promised by the profile.
-/
theorem StraightLineFiveBitDlogProfile.solverCost_le
    {B : VestaG} {family : ComputedStraightLineDeployedFSFamily shape} {T : Nat}
    (profile : StraightLineFiveBitDlogProfile B family T) :
    family.straightLineDlogRandomOracleQueries <= 32 * T ∧
      straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork <= 32 * T := by
  constructor
  · exact family.straightLineDlogRandomOracleQueries_le_32_mul
      profile.ipaDepth profile.targetAtLeastThree profile.queryBound
  · exact straightLineDlogGroupWork_le_32_mul
      profile.proverWorkBound profile.reductionWorkBound

/-- Exact arithmetic behind the conservative work-factor wording: five bits of total reduction
overhead map a `2^122` adversary budget to a `2^127` DLOG-solver budget. -/
theorem five_bit_overhead_at_2pow122 :
    32 * 2 ^ 122 = 2 ^ 127 := by norm_num

/-- At the concrete target, a five-bit profile bounds both solver resources by `2^127`. -/
theorem StraightLineFiveBitDlogProfile.solverCost_at_2pow122
    {B : VestaG} {family : ComputedStraightLineDeployedFSFamily shape}
    (profile : StraightLineFiveBitDlogProfile B family (2 ^ 122)) :
    family.straightLineDlogRandomOracleQueries <= 2 ^ 127 ∧
      straightLineDlogGroupWork profile.proverGroupWork profile.reductionGroupWork <= 2 ^ 127 := by
  have h := profile.solverCost_le
  rw [five_bit_overhead_at_2pow122] at h
  exact h

end ComputedStraightLineDeployedFSFamily

end Zcash.Snark
