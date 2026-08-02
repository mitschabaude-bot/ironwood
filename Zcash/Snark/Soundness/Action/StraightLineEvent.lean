import Zcash.Snark.Soundness.Action.StraightLineTerminal
import Zcash.Snark.Soundness.Composition.PrefixedSqueeze
import Zcash.Snark.Soundness.AGM.StraightLineFiniteSecurity
import Zcash.Snark.Soundness.StraightLine.TopLevelEvent

/-!
# Action soundness and knowledge soundness as priced straight-line events

Prices straight-line false-statement and extraction failures. Witness and relation projections
share one executable outcome.
-/

namespace Zcash.Snark

namespace ActionTerminal

open Halo2 CompPoly.CPolynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder)
open scoped ENNReal

local instance vestaInhabitedStraightLineActionEvent : Inhabited VestaG := ⟨0⟩

private theorem outerMeasure_preimage_union_le {A B : Type*}
    (mu : MeasureTheory.OuterMeasure A) (f : A → B) (s t : Set B) :
    mu (f ⁻¹' (s ∪ t)) ≤ mu (f ⁻¹' s) + mu (f ⁻¹' t) := by
  simpa only [Set.preimage_union] using
    (MeasureTheory.measure_union_le (μ := mu) (f ⁻¹' s) (f ⁻¹' t))

attribute [local irreducible] actionCircuit TopLevelCircuit.toVerifierKey
  TopLevelCircuit.instanceCommitment actionKnowledgeOutcome
  actionTerminalWitnessOrRelationFinder StraightLineAcceptedView.actionTerminalOutcome?
  topLevelRunView

variable (pp : ProofParams)
  (family : ComputedStraightLineDeployedFSFamily (actionCircuit.shape.withProofParams pp))
  (static : DeployedConstraintStaticChecks family.toRootFamily)
  (inputs : Fin pp.numProofs → PublicInputs Fp)

/-- Runs on which an executable Action-terminal finder returns explicit augmented-basis relation
coefficients.  The finder, not propositional relation existence, is the DLOG-priced event. -/
def actionTerminalRelationEvent
    (finder :
      (basis : AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * actionCircuit.shape.k) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis)) :
    Set ((AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * actionCircuit.shape.k) → Fp)) :=
  {q | (finder q.1 q.2).isSome}

variable
  (hvk : ∀ basis, family.vk basis =
    actionCircuit.toVerifierKey
      (ursOfAugmentedBasis actionCircuit.shape.k basis))
  (hI : ∀ basis, family.instanceCommitment basis =
    actionCircuit.instanceCommitment (ursOfAugmentedBasis actionCircuit.shape.k basis) inputs)
  (hchar : ∀ basis O, deployedX4PairCount
    (actionCircuit.toVerifierKey
      (ursOfAugmentedBasis actionCircuit.shape.k basis))
    (actionCircuit.instanceCommitment (ursOfAugmentedBasis actionCircuit.shape.k basis) inputs)
    (straightLineRunOutput family basis O).1.proof.1
    (straightLineRunRecord family basis O) < scalarFieldOrder)

/-- Knowledge-soundness failure for the straight-line/sequential presentation: the verifier
accepts, but the executable projection of the shared terminal outcome returns no private Action
witness bundle. -/
def actionKnowledgeFailureEvent :
    Set ((AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * actionCircuit.shape.k) → Fp)) :=
  {q | fsWinsFull (family.adversary q.1)
      (fullAlgebraicAcceptDeployed q.1 (family.vk q.1)
        (family.instanceCommitment q.1))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) q.2 ∧
    actionKnowledgeExtractor pp family static inputs hvk hI hchar q.1 q.2 = none}

/-- The successful run presented once at the Action circuit's identified artifacts. -/
def actionRunView
    (basis : AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * actionCircuit.shape.k) → Fp)
    (h : family.straightLineConstraintDecoded static basis O) :
    StraightLineAcceptedView family basis O
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis actionCircuit.shape.k basis))
      (actionCircuit.instanceCommitment
        (ursOfAugmentedBasis actionCircuit.shape.k basis) inputs) where
  decode := actionRunDecode pp family static basis O inputs (hvk basis) (hI basis) h
  accepts := actionRunAccepts pp family static basis O inputs (hvk basis) (hI basis) h

/-- The generic and Action presentations of the same accepted run agree. -/
private theorem topLevelRunView_eq_actionRunView
    (basis : AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * actionCircuit.shape.k) → Fp)
    (hdecoded : family.straightLineConstraintDecoded static basis O) :
    topLevelRunView actionCircuit pp family static inputs hvk hI basis O hdecoded =
      actionRunView pp family static inputs hvk hI basis O hdecoded := by
  apply StraightLineAcceptedView.ext
  exact (topLevelRunView_decode
    actionCircuit pp family static inputs hvk hI basis O hdecoded).trans
      (actionRunDecode_eq_straightLineRunDecodeAt
        pp family static basis O inputs (hvk basis) (hI basis) hdecoded).symm

/-- The decoded Action run and the success branch of the same constraint outcome select the same
transported deployed decode. -/
private theorem actionRunDecode_eq_constraintSuccess
    (basis : AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * actionCircuit.shape.k) → Fp)
    (hdecoded : family.straightLineConstraintDecoded static basis O)
    (success : ComputedStraightLineDeployedFSFamily.StraightLineConstraintSuccess
      family basis O)
    (hout : family.straightLineConstraintOutcome? static basis O = some (PSum.inl success)) :
    actionRunDecode pp family static basis O inputs
        (hvk basis) (hI basis) hdecoded =
      (success.acceptedViewAt
        (actionCircuit.toVerifierKey
          (ursOfAugmentedBasis actionCircuit.shape.k basis))
        (actionCircuit.instanceCommitment
          (ursOfAugmentedBasis actionCircuit.shape.k basis) inputs)
        (hvk basis) (hI basis)).decode := by
  have hsuccess := family.straightLineConstraintSuccess_eq_of_outcome
    static basis O hdecoded success hout
  simp only [actionRunDecode,
    ComputedStraightLineDeployedFSFamily.StraightLineConstraintSuccess.acceptedViewAt,
    straightLineDecode, straightLineConstraintWitness, hsuccess,
    ComputedStraightLineDeployedFSFamily.StraightLineConstraintSuccess.decodeAt]

private def actionSuccessView
    (basis : AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * actionCircuit.shape.k) → Fp)
    (success : ComputedStraightLineDeployedFSFamily.StraightLineConstraintSuccess
      family basis O) : StraightLineAcceptedView family basis O
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

private theorem actionRunView_eq_constraintSuccess
    (basis : AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * actionCircuit.shape.k) → Fp)
    (hdecoded : family.straightLineConstraintDecoded static basis O)
    (success : ComputedStraightLineDeployedFSFamily.StraightLineConstraintSuccess
      family basis O)
    (hout : family.straightLineConstraintOutcome? static basis O = some (PSum.inl success)) :
    actionRunView pp family static inputs hvk hI basis O hdecoded =
      actionSuccessView pp family inputs hvk hI basis O success := by
  apply StraightLineAcceptedView.ext
  exact actionRunDecode_eq_constraintSuccess
    pp family static inputs hvk hI basis O hdecoded success hout

private theorem actionTerminalOutcome_isSome_of_success
    (basis : AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * actionCircuit.shape.k) → Fp)
    (hdecoded : family.straightLineConstraintDecoded static basis O)
    (success : ComputedStraightLineDeployedFSFamily.StraightLineConstraintSuccess
      family basis O)
    (hout : family.straightLineConstraintOutcome? static basis O = some (PSum.inl success))
    (hxy : TopLevelXYExclusions actionCircuit pp family static inputs hvk hI hchar
      basis O hdecoded)
    (hbeta : TopLevelBetaExclusions actionCircuit pp family static inputs hvk hI hchar
      basis O hdecoded)
    (hgamma : TopLevelGammaExclusions actionCircuit pp family static inputs hvk hI hchar
      basis O hdecoded)
    (htheta : TopLevelThetaExclusions actionCircuit pp family static inputs hvk hI hchar
      basis O hdecoded) :
    (StraightLineAcceptedView.actionTerminalOutcome? pp inputs
      (success.acceptedViewAt
        (actionCircuit.toVerifierKey
          (ursOfAugmentedBasis actionCircuit.shape.k basis))
        (actionCircuit.instanceCommitment
          (ursOfAugmentedBasis actionCircuit.shape.k basis) inputs)
        (hvk basis) (hI basis)) (hchar basis O)).isSome := by
  unfold TopLevelXYExclusions at hxy
  unfold TopLevelBetaExclusions at hbeta
  unfold TopLevelGammaExclusions at hgamma
  unfold TopLevelThetaExclusions at htheta
  let runView := actionRunView pp family static inputs hvk hI basis O hdecoded
  let successView := actionSuccessView pp family inputs hvk hI basis O success
  have hgenericView :
      topLevelRunView actionCircuit pp family static inputs hvk hI basis O hdecoded =
        runView := by
    simpa only [runView] using
      topLevelRunView_eq_actionRunView
        pp family static inputs hvk hI basis O hdecoded
  simp only [topLevelRunModel, topLevelRunPolynomial, hgenericView] at hxy hbeta hgamma htheta
  have hview : runView = successView :=
    actionRunView_eq_constraintSuccess
      pp family static inputs hvk hI basis O hdecoded success hout
  have hxgood := hxy.1
  have hgoodY := hxy.2
  have hpermutation : ResolverPermutationChallengeExclusions
      pp.numProofs (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis actionCircuit.shape.k basis))
      (straightLineRunRecord family basis O)
      (runView.polynomial (hchar basis O)) actionActiveRows := {
    gamma := by simpa only [actionActiveRows] using hgamma.1
    beta := by simpa only [actionActiveRows] using hbeta.1 }
  have hlookup : TopLevelLookup.ChallengeExclusions
      actionCircuit pp
      (ursOfAugmentedBasis actionCircuit.shape.k basis)
      (straightLineRunRecord family basis O)
      (runView.polynomial (hchar basis O)) := {
    gamma := by simpa only [actionCircuit.toVerifierKey_n,
      actionCircuit.toVerifierKey_blindingFactors] using hgamma.2
    beta := by simpa only [actionCircuit.toVerifierKey_n,
      actionCircuit.toVerifierKey_blindingFactors] using hbeta.2
    theta := htheta }
  have hxgood' := by
    simpa only [actionCircuit.toVerifierKey_n] using hxgood
  have hgoodY' := by
    simpa only [actionCircuit.toVerifierKey_n] using hgoodY
  have hrun := StraightLineAcceptedView.actionTerminalOutcome?_isSome_of
    pp inputs runView (hchar basis O) hxgood' hgoodY' hpermutation hlookup
  have hsuccess :
      (StraightLineAcceptedView.actionTerminalOutcome?
        pp inputs successView (hchar basis O)).isSome := hview ▸ hrun
  simpa only [successView, actionSuccessView] using hsuccess

/-- Outside the four semantic challenge surfaces, a decoded run's terminal fallback computes
either all private witnesses or explicit relation data. -/
private theorem actionTerminalWitnessOrRelationFinder_isSome_of_good
    (basis : AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * actionCircuit.shape.k) → Fp)
    (hdecoded : family.straightLineConstraintDecoded static basis O)
    (hXY : (basis, O) ∉ topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar)
    (hBeta : (basis, O) ∉ topLevelBetaFailureEvent actionCircuit pp family static inputs hvk hI hchar)
    (hGamma : (basis, O) ∉ topLevelGammaFailureEvent actionCircuit pp family static inputs hvk hI hchar)
    (hTheta : (basis, O) ∉ topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar) :
    (actionTerminalWitnessOrRelationFinder
      pp family static inputs hvk hI hchar basis O).isSome := by
  obtain ⟨success, hout⟩ :=
    family.straightLineConstraintOutcome?_eq_some_of_decoded static basis O hdecoded
  have hxy := topLevelXYExclusions_of_not_mem
    actionCircuit pp family static inputs hvk hI hchar hdecoded hXY
  have hbeta := topLevelBetaExclusions_of_not_mem
    actionCircuit pp family static inputs hvk hI hchar hdecoded hBeta
  have hgamma := topLevelGammaExclusions_of_not_mem
    actionCircuit pp family static inputs hvk hI hchar hdecoded hGamma
  have htheta := topLevelThetaExclusions_of_not_mem
    actionCircuit pp family static inputs hvk hI hchar hdecoded hTheta
  unfold actionTerminalWitnessOrRelationFinder
  rw [hout]
  simp only
  exact actionTerminalOutcome_isSome_of_success
    pp family static inputs hvk hI hchar basis O hdecoded success hout
      hxy hbeta hgamma htheta

/-- Outside the four semantic challenge surfaces, a decoded run computes either all private
witnesses or explicit relation data. -/
theorem actionKnowledgeOutcome_isSome_of_good
    (basis : AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * actionCircuit.shape.k) → Fp)
    (hdecoded : family.straightLineConstraintDecoded static basis O)
    (hXY : (basis, O) ∉ topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar)
    (hBeta : (basis, O) ∉ topLevelBetaFailureEvent actionCircuit pp family static inputs hvk hI hchar)
    (hGamma : (basis, O) ∉ topLevelGammaFailureEvent actionCircuit pp family static inputs hvk hI hchar)
    (hTheta : (basis, O) ∉ topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar) :
    (actionKnowledgeOutcome pp family static inputs hvk hI hchar basis O).isSome := by
  unfold actionKnowledgeOutcome
  split
  · rfl
  · exact actionTerminalWitnessOrRelationFinder_isSome_of_good
      pp family static inputs hvk hI hchar basis O hdecoded hXY hBeta hGamma hTheta

/-- The relation projection covers every good decoded run whose extracted witness would
contradict a claimed false bundle statement. -/
theorem actionRelationFinder_covers :
    topLevelTerminalRelationFinderCovers actionCircuit pp family static inputs hvk hI hchar
      (actionRelationFinder pp family static inputs hvk hI hchar) := by
  intro basis O hdecoded hXY hBeta hGamma hTheta hfalse
  have hsome := actionKnowledgeOutcome_isSome_of_good pp family static inputs hvk hI hchar
    basis O hdecoded hXY hBeta hGamma hTheta
  obtain ⟨outcome, houtcome⟩ := Option.isSome_iff_exists.mp hsome
  cases outcome with
  | inl witness => exact False.elim (hfalse witness.statement)
  | inr relation =>
      unfold actionRelationFinder
      rw [houtcome]
      rfl

/-- Straight-line knowledge failure is covered by the same compressed failure, computed DLOG
relation, and four semantic challenge surfaces as ordinary Action soundness. -/
theorem actionKnowledgeFailure_subset_union :
    actionKnowledgeFailureEvent pp family static inputs hvk hI hchar ⊆
      (family.straightLineConstraintFailureEvent static ∪
        family.straightLineRelationEvent
          (actionRelationFinder pp family static inputs hvk hI hchar)) ∪
      (topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar ∪
        (topLevelBetaFailureEvent actionCircuit pp family static inputs hvk hI hchar ∪
          (topLevelGammaFailureEvent actionCircuit pp family static inputs hvk hI hchar ∪
            topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar))) := by
  rintro q ⟨haccept, hextractor⟩
  by_cases hdecoded : family.straightLineConstraintDecoded static q.1 q.2
  · by_cases hXY : q ∈ topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar
    · exact Or.inr (Or.inl hXY)
    by_cases hBeta : q ∈ topLevelBetaFailureEvent actionCircuit pp family static inputs hvk hI hchar
    · exact Or.inr (Or.inr (Or.inl hBeta))
    by_cases hGamma : q ∈ topLevelGammaFailureEvent actionCircuit pp family static inputs hvk hI hchar
    · exact Or.inr (Or.inr (Or.inr (Or.inl hGamma)))
    by_cases hTheta : q ∈ topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar
    · exact Or.inr (Or.inr (Or.inr (Or.inr hTheta)))
    have hsome := actionKnowledgeOutcome_isSome_of_good pp family static inputs hvk hI hchar
      q.1 q.2 hdecoded hXY hBeta hGamma hTheta
    obtain ⟨outcome, houtcome⟩ := Option.isSome_iff_exists.mp hsome
    cases outcome with
    | inl witness =>
        have hextracted := actionKnowledgeExtractor_eq_some_of_outcome_eq_inl
          pp family static inputs hvk hI hchar q.1 q.2 witness houtcome
        cases hextracted.symm.trans hextractor
    | inr relation =>
        refine Or.inl (Or.inr ?_)
        change (actionRelationFinder pp family static inputs hvk hI hchar q.1 q.2).isSome
        have hfinder := actionRelationFinder_eq_some_of_outcome_eq_inr
          pp family static inputs hvk hI hchar q.1 q.2 relation houtcome
        rw [hfinder]
        rfl
  · exact Or.inl (Or.inl ⟨haccept, hdecoded⟩)

/-- Conservative black-box calls of the combined finder: the existing constraint finder has its
proved four-call bound, and the terminal fallback performs at most two further represented-run
evaluations. -/
def actionRelationFinderCalls
    (basis : AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * actionCircuit.shape.k) → Fp) : Nat :=
  family.straightLineConstraintRelationFinderCalls basis O + 2

theorem actionRelationFinderCalls_le_six
    (basis : AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * actionCircuit.shape.k) → Fp) :
    actionRelationFinderCalls pp family basis O ≤ 6 := by
  unfold actionRelationFinderCalls
  have hcalls := family.straightLineConstraintRelationFinderCalls_le_four basis O
  omega

/-- Random-oracle work of the combined constraint-plus-Action solver.  All six represented prover
runs include their own `11+k` designated transcript reads; no cache-sharing convention is assumed.
-/
def actionDlogRandomOracleQueries : Nat :=
  6 * family.Q + 6 * (11 + actionCircuit.domainExponent)

/-- The sequential witness extractor is the other projection of the same six-call outcome. -/
def actionKnowledgeExtractorRandomOracleQueries : Nat :=
  actionDlogRandomOracleQueries pp family

@[simp] theorem actionKnowledgeExtractorRandomOracleQueries_eq :
    actionKnowledgeExtractorRandomOracleQueries pp family =
      actionDlogRandomOracleQueries pp family := rfl

/-- Group-work envelope of the combined solver.  Terminal comparison work is included in the
explicit reduction component. -/
def actionDlogGroupWork (proverGroupWork reductionGroupWork : Nat) : Nat :=
  6 * proverGroupWork + reductionGroupWork

/-- One finite-security premise for the complete constraint-plus-Action relation finder. -/
structure StraightLineActionDlogProfile (B : VestaG) where
  proverGroupWork : Nat
  reductionGroupWork : Nat
  advantage : Nat → Nat → ENNReal
  advantage_mono : ∀ {q q' g g'}, q ≤ q' → g ≤ g' →
    advantage q g ≤ advantage q' g'
  hardness : TextbookDLWithCoinsAdvantageLE B
    (actionRelationFinder pp family static inputs hvk hI hchar)
    (advantage (actionDlogRandomOracleQueries pp family)
      (actionDlogGroupWork proverGroupWork reductionGroupWork))

/-- Direct-route profile covering prover, postprocessing, and both possible decoder executions. -/
structure StraightLineActionDirectDlogProfile (B : VestaG) (T : Nat)
    extends StraightLineActionDlogProfile pp family static inputs hvk hI hchar B where
  scheduleOverheadBound : 3 * (11 + actionCircuit.domainExponent) <= T
  queryBound : family.Q <= T
  proverWorkBound : toStraightLineActionDlogProfile.proverGroupWork <= T
  reductionWorkBound : toStraightLineActionDlogProfile.reductionGroupWork <= T
  directDecodeWorkBound : forall basis O,
    2 * family.straightLineDirectDecodeOps basis O <= T

/-- The concrete Action profile bounds both DLOG-solver resources by an eightfold envelope and
retains the direct-decoder certificate used by the straight-line implementation. -/
theorem StraightLineActionDirectDlogProfile.solverCost_le
    {B : VestaG} {T : Nat}
    (profile : StraightLineActionDirectDlogProfile pp family static inputs
      hvk hI hchar B T) :
    actionDlogRandomOracleQueries pp family <= 8 * T /\
      actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork <= 8 * T /\
      forall basis O, 2 * family.straightLineDirectDecodeOps basis O <= T := by
  constructor
  · unfold actionDlogRandomOracleQueries
    have hT := profile.scheduleOverheadBound
    calc
      6 * family.Q + 6 * (11 + actionCircuit.domainExponent) <=
          6 * T + 6 * (11 + actionCircuit.domainExponent) := by
        gcongr
        exact profile.queryBound
      _ <= 8 * T := by omega
  constructor
  · unfold actionDlogGroupWork
    calc
      6 * profile.proverGroupWork + profile.reductionGroupWork <= 6 * T + T := by
        gcongr
        · exact profile.proverWorkBound
        · exact profile.reductionWorkBound
      _ <= 8 * T := by omega
  · exact profile.directDecodeWorkBound

/-- Runtime accounting for the sequential witness projection: it shares the profiled combined
outcome and therefore adds no seventh represented-prover run. -/
theorem StraightLineActionDirectDlogProfile.knowledgeExtractorCost_le
    {B : VestaG} {T : Nat}
    (profile : StraightLineActionDirectDlogProfile pp family static inputs
      hvk hI hchar B T) :
    actionKnowledgeExtractorRandomOracleQueries pp family <= 8 * T /\
      actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork <= 8 * T /\
      forall basis O, 2 * family.straightLineDirectDecodeOps basis O <= T := by
  simpa only [actionKnowledgeExtractorRandomOracleQueries_eq] using profile.solverCost_le

/-- The combined finder exactly extends the old constraint finder on every successful old branch.
-/
theorem actionRelationFinder_extends_constraint
    (basis : AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
        + 3 * actionCircuit.shape.k) → Fp) :
    (family.straightLineConstraintRelationFinder basis O).isSome →
      (actionRelationFinder pp family static inputs hvk hI hchar basis O).isSome := by
  intro hsome
  unfold actionRelationFinder
  cases hfinder : family.straightLineConstraintRelationFinder basis O with
  | none => simp [hfinder] at hsome
  | some relation =>
      have hout : actionKnowledgeOutcome pp family static inputs hvk hI hchar basis O =
          some (Sum.inr relation) := by
        unfold actionKnowledgeOutcome
        simp only [hfinder]
      rw [hout]
      rfl

/-- Generator-random-oracle bound for compressed failure union the complete Action relation event.
The combined DLOG advantage occurs once. -/
theorem actionBaseUnion_prob_le_of_dlogProfile
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ actionCircuit.shape.k) → T)
    (hquery : Function.Injective query)
    {epsilonX : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family.toRootFamily epsilonX)
    (profile : StraightLineActionDlogProfile pp family static inputs hvk hI hchar B) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * actionCircuit.shape.k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          (family.straightLineConstraintFailureEvent static ∪
            family.straightLineRelationEvent
              (actionRelationFinder pp family static inputs hvk hI hchar))) ≤
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) *
          (actionCircuit.shape.k *
            (2 / (Fintype.card Fp : ENNReal))) +
        (family.Q + (11 + actionCircuit.shape.k) + 1 : Nat) *
          algebraicRootBudget (actionCircuit.shape.withProofParams pp)
            actionCircuit.shape.k +
        (profile.advantage (actionDlogRandomOracleQueries pp family)
            (actionDlogGroupWork profile.proverGroupWork profile.reductionGroupWork) +
          1 / Fintype.card Fp) +
        (family.Q + 1 : Nat) * epsilonX := by
  have htransfer := family.straightLineConstraintFailure_union_relation_prob_eq_of_uniformURS
    (orchardGeneratorROSetup query) B static
    (actionRelationFinder pp family static inputs hvk hI hchar)
    (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO
      actionCircuit.shape.k B hB query hquery)
  have hbound :=
    family.straightLineConstraintFailure_union_relation_prob_le_of_relationSupersetTextbookDL
    B static (actionRelationFinder pp family static inputs hvk hI hchar)
    (actionRelationFinder_extends_constraint pp family static inputs hvk hI hchar)
    schedule profile.hardness
  simpa only [CircuitShape.withProofParams_k] using htransfer.le.trans hbound

/-- **Exact Action-statement containment.**  Outside the compressed decode failure and the four
challenge surfaces, a false Action statement forces the good-run terminal onto its relation
branch.  A covering computed finder therefore turns that branch into the explicit event priced
by DLOG. -/
theorem actionBundleStatementUpgradeContained
    (finder :
      (basis : AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * actionCircuit.shape.k) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis))
    (hcovers : topLevelTerminalRelationFinderCovers actionCircuit pp family static inputs hvk hI hchar finder) :
    family.StraightLineConstraintSemanticUpgradeContained static
      (topLevelBundleStatementDecoded actionCircuit pp family inputs)
      (topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar)
      (topLevelBetaFailureEvent actionCircuit pp family static inputs hvk hI hchar)
      (topLevelGammaFailureEvent actionCircuit pp family static inputs hvk hI hchar)
      (topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar ∪
        actionTerminalRelationEvent pp family finder) := by
  rintro q ⟨hdecoded, hfalse⟩
  by_cases hXY : q ∈ topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar
  · exact Or.inl hXY
  by_cases hBeta : q ∈ topLevelBetaFailureEvent actionCircuit pp family static inputs hvk hI hchar
  · exact Or.inr (Or.inl hBeta)
  by_cases hGamma : q ∈ topLevelGammaFailureEvent actionCircuit pp family static inputs hvk hI hchar
  · exact Or.inr (Or.inr (Or.inl hGamma))
  by_cases hTheta : q ∈ topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar
  · exact Or.inr (Or.inr (Or.inr (Or.inl hTheta)))
  refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
  exact hcovers q.1 q.2 hdecoded hXY hBeta hGamma hTheta hfalse

/-- Literal accepting-false-Action runs are covered by the *single* base union (compressed decode
failure or the combined relation finder) plus the four semantic challenge surfaces.  The finder
event is not added again after the compressed bound. -/
theorem actionBundleStatementFailure_subset_union
    (finder :
      (basis : AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * actionCircuit.shape.k) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis))
    (hcovers : topLevelTerminalRelationFinderCovers actionCircuit pp family static inputs hvk hI hchar finder) :
    family.straightLineConstraintSemanticFailureEvent
        (topLevelBundleStatementDecoded actionCircuit pp family inputs) <=
      (family.straightLineConstraintFailureEvent static ∪
        family.straightLineRelationEvent finder) ∪
      (topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar ∪
        (topLevelBetaFailureEvent actionCircuit pp family static inputs hvk hI hchar ∪
          (topLevelGammaFailureEvent actionCircuit pp family static inputs hvk hI hchar ∪
            topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar))) := by
  rintro q ⟨haccept, hfalse⟩
  by_cases hdecoded : family.straightLineConstraintDecoded static q.1 q.2
  · have hsemantic : family.straightLineConstraintDecoded static q.1 q.2 ∧
        ¬topLevelBundleStatementDecoded actionCircuit pp family inputs q.1 q.2 :=
      ⟨hdecoded, hfalse⟩
    rcases actionBundleStatementUpgradeContained pp family static inputs hvk hI hchar
        finder hcovers hsemantic with hXY | hBeta | hGamma | hTheta | hrelation
    · exact Or.inr (Or.inl hXY)
    · exact Or.inr (Or.inr (Or.inl hBeta))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hGamma)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hTheta)))
    · exact Or.inl (Or.inr hrelation)
  · exact Or.inl (Or.inl ⟨haccept, hdecoded⟩)

/-- Exact Action probability composition with the combined relation event priced once. -/
theorem actionBundleStatementFailure_prob_le_of_base_union_bound
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ actionCircuit.shape.k) → T)
    (finder :
      (basis : AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * actionCircuit.shape.k) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis))
    (hcovers : topLevelTerminalRelationFinderCovers actionCircuit pp family static inputs hvk hI hchar finder)
    {baseBound xyBound betaBound gammaBound thetaBound : ENNReal}
    (hbase : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * actionCircuit.shape.k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          (family.straightLineConstraintFailureEvent static ∪
            family.straightLineRelationEvent finder)) ≤ baseBound)
    (hXY : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype _)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ xyBound)
    (hBeta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype _)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelBetaFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ betaBound)
    (hGamma : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype _)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelGammaFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ gammaBound)
    (hTheta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype _)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ thetaBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * actionCircuit.shape.k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintSemanticFailureEvent
            (topLevelBundleStatementDecoded actionCircuit pp family inputs)) <=
      baseBound + (xyBound + (betaBound + (gammaBound + thetaBound))) := by
  refine le_trans (MeasureTheory.measure_mono
    (Set.preimage_mono (actionBundleStatementFailure_subset_union pp family static inputs
      hvk hI hchar finder hcovers))) ?_
  refine le_trans (outerMeasure_preimage_union_le _ _ _ _) ?_
  refine add_le_add hbase ?_
  refine le_trans (outerMeasure_preimage_union_le _ _ _ _) ?_
  refine add_le_add hXY ?_
  refine le_trans (outerMeasure_preimage_union_le _ _ _ _) ?_
  refine add_le_add hBeta ?_
  refine le_trans (outerMeasure_preimage_union_le _ _ _ _) ?_
  exact add_le_add hGamma hTheta

/-- End-to-end straight-line Action knowledge soundness, factored through the same profiled base
union and four semantic challenge bounds as the ordinary-soundness endpoint. -/
theorem actionKnowledgeFailure_prob_le_of_base_union_bound
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ actionCircuit.shape.k) → T)
    {baseBound xyBound betaBound gammaBound thetaBound : ENNReal}
    (hbase : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * actionCircuit.shape.k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          (family.straightLineConstraintFailureEvent static ∪
            family.straightLineRelationEvent
              (actionRelationFinder pp family static inputs hvk hI hchar))) ≤ baseBound)
    (hXY : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype _)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ xyBound)
    (hBeta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype _)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelBetaFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ betaBound)
    (hGamma : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype _)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelGammaFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ gammaBound)
    (hTheta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype _)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ thetaBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * actionCircuit.shape.k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionKnowledgeFailureEvent pp family static inputs hvk hI hchar) ≤
      baseBound + (xyBound + (betaBound + (gammaBound + thetaBound))) := by
  refine le_trans (MeasureTheory.measure_mono
    (Set.preimage_mono (actionKnowledgeFailure_subset_union pp family static inputs
      hvk hI hchar))) ?_
  rw [Set.preimage_union, Set.preimage_union, Set.preimage_union, Set.preimage_union]
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add hbase ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add hXY ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  refine add_le_add hBeta ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  exact add_le_add hGamma hTheta

/-- Bounds literal false-statement acceptance, leaving the computed relation event to a DLOG
profile. -/
theorem actionBundleStatementFailure_prob_le_of_compressed_bound
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ actionCircuit.shape.k) → T)
    (finder :
      (basis : AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
          + 3 * actionCircuit.shape.k) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis))
    (hcovers : topLevelTerminalRelationFinderCovers actionCircuit pp family static inputs hvk hI hchar finder)
    {compressedBound xyBound betaBound gammaBound thetaBound relationBound : ENNReal}
    (hcompressed : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * actionCircuit.shape.k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintFailureEvent static) ≤ compressedBound)
    (hXY : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * actionCircuit.shape.k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelXYFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ xyBound)
    (hBeta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * actionCircuit.shape.k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelBetaFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ betaBound)
    (hGamma : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * actionCircuit.shape.k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelGammaFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ gammaBound)
    (hTheta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * actionCircuit.shape.k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          topLevelThetaFailureEvent actionCircuit pp family static inputs hvk hI hchar) ≤ thetaBound)
    (hRelation : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * actionCircuit.shape.k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionTerminalRelationEvent pp family finder) ≤ relationBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10
            + 3 * actionCircuit.shape.k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintSemanticFailureEvent
            (topLevelBundleStatementDecoded actionCircuit pp family inputs))
      ≤ compressedBound +
          (xyBound + (betaBound + (gammaBound + (thetaBound + relationBound)))) := by
  have hRelation' :
      (independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype _)).toOuterMeasure
          ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
            family.straightLineRelationEvent finder) ≤ relationBound := by
    simpa only [actionTerminalRelationEvent,
      ComputedStraightLineDeployedFSFamily.straightLineRelationEvent,
      CircuitShape.withProofParams_k] using hRelation
  have hbase :
      (independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype _)).toOuterMeasure
          ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
            (family.straightLineConstraintFailureEvent static ∪
              family.straightLineRelationEvent finder)) ≤
        compressedBound + relationBound :=
    le_trans (outerMeasure_preimage_union_le _ _ _ _)
      (add_le_add hcompressed hRelation')
  have hbound := actionBundleStatementFailure_prob_le_of_base_union_bound pp family static inputs
    hvk hI hchar query finder hcovers
    (baseBound := compressedBound + relationBound)
    (xyBound := xyBound) (betaBound := betaBound) (gammaBound := gammaBound)
    (thetaBound := thetaBound) hbase hXY hBeta hGamma hTheta
  calc
    _ ≤ (compressedBound + relationBound) +
        (xyBound + (betaBound + (gammaBound + thetaBound))) := hbound
    _ = compressedBound +
        (xyBound + (betaBound + (gammaBound + (thetaBound + relationBound)))) := by
      ac_rfl

end ActionTerminal

end Zcash.Snark
