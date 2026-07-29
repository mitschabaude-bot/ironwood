import Zcash.Snark.Soundness.AGM.OnlineConstraint
import Zcash.Snark.Soundness.Composition.DeployedRootContainment

/-!
# Composite constraint bound for the rewind-free AGM path

This module carries any additional explicit relation produced while upgrading the deployed member
decode to the concrete constraint relation through the same textbook-DLOG finder.  The remaining
`x`-challenge failure is an additive event supplied by the concrete pre-`x` schedule; no multiopen
rewind or fourth-root threshold appears.
-/

namespace Zcash.Snark

open Classical
open ComputedAlgebraicFSFamily
open ComputedDeployedRootFSFamily
open scoped ENNReal

variable {shape : Shape}

local instance vestaInhabitedDeployedConstraintContainment : Inhabited VestaG := ⟨0⟩

/-- Verifying-key facts that do not depend on the adversary run.  The captured Orchard fixture
discharges these once; deployed acceptance supplies the remaining per-run routing checks. -/
structure DeployedConstraintStaticChecks (family : ComputedDeployedRootFSFamily shape) : Prop where
  adviceLength : forall basis,
    shape.numAdviceQueries <= (family.vk basis).adviceQueryLayout.length
  instanceLength : forall basis,
    shape.numInstanceQueries <= (family.vk basis).instanceQueryLayout.length
  fixedLength : forall basis,
    shape.numFixedQueries <= (family.vk basis).fixedQueryLayout.length
  omegaOrder : forall basis, (family.vk basis).omega ^ (family.vk basis).n = 1
  characteristic : forall basis, (((family.vk basis).n : Nat) : Fp) ≠ 0

/-- **The total pre-`x` constraint difference** (issue #127): built from the run's own pre-`x`
representation source over the family's retained list.  It mentions no root witness, batch
witness, decode, or outcome branch, so it is defined on every run — honest, cheating, or
degenerate. -/
def deployedConstraintDifferencePreX
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (coins : family.toFamily.Coins) :
    Polynomial Fp :=
  let pnu := deployedRootRunOutput family basis coins
  committedPreXConstraintDifference
    (deployedConstraintPointPolynomial family basis pnu)
    (fun i => coeffsToPoly
      (deployedConstraintPieceCoordinates family basis pnu i).1)
    (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
    (wrappedPreIpaRecord pnu)

/-- Run the concrete online constraint adapter from a successful root decode and deployed
acceptance.  The result still preserves the explicit quotient-collision relation branch. -/
def deployedConstraintOutcomeOfRoot
    (family : ComputedDeployedRootFSFamily shape)
    (static : DeployedConstraintStaticChecks family)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (coins : family.toFamily.Coins)
    (haccept : fsWinsFull (family.adversary basis)
      (fullAlgebraicAcceptDeployed basis (family.vk basis)
        (family.instanceCommitment basis))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins.1)
    (root : DeployedRootDecodeWitness family basis coins)
    (hxgood : (wrappedPreIpaRecord (deployedRootRunOutput family basis coins)).x ∉
      szBadSet (deployedConstraintDifferencePreX family basis coins)) :
    let pnu := deployedRootRunOutput family basis coins
    DeployedConstraintWitness (ursOfAugmentedBasis shape.k basis) rfl
        (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
        (wrappedPreIpaRecord pnu) (pnu.1.aMulti (wrappedPreIpaReads pnu))
        (pnu.1.multiU (wrappedPreIpaReads pnu))
        (pnu.1.multiBlind (wrappedPreIpaReads pnu)) ⊕'
      AugmentedRelationWitness (F := Fp) (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u
        (ursOfAugmentedBasis shape.k basis).w := by
  let pnu := deployedRootRunOutput family basis coins
  have hdeployed := deployedAccepts_of_fsWinsFull family.toFamily basis coins.1 haccept
  have hdeployed' : DeployedAccepts (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis coins.1)) := by
    simpa [pnu, deployedRootRunOutput, wrappedAdversary_run_fst,
      wrappedPreIpaReads_run] using hdeployed
  let checks := DeployedConstraintChecks.of_accepts_chRecord
    (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
    (family.instanceCommitment basis) pnu.1.proof.1 (wrappedPreIpaReads pnu)
    (runRounds family.toFamily basis coins.1) hdeployed'
  exact deployedOnlineConstraintOutcomeOfDecode family basis pnu root.batchWitness
    (family.outcome_source basis coins.1 root.batchWitness root.outcome_eq) root.decoded
    root.batches_eq checks (static.adviceLength basis) (static.instanceLength basis)
    (static.fixedLength basis) (static.omegaOrder basis) (static.characteristic basis) hxgood

/-- A relation returned by the proof-producing root adapter is exactly the relation returned by
the standalone computable quotient comparison. -/
theorem deployedConstraintOutcomeOfRoot_relation_eq_online
    (family : ComputedDeployedRootFSFamily shape)
    (static : DeployedConstraintStaticChecks family)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (coins : family.toFamily.Coins)
    (haccept : fsWinsFull (family.adversary basis)
      (fullAlgebraicAcceptDeployed basis (family.vk basis)
        (family.instanceCommitment basis))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins.1)
    (root : DeployedRootDecodeWitness family basis coins)
    (hxgood : (wrappedPreIpaRecord (deployedRootRunOutput family basis coins)).x ∉
      szBadSet (deployedConstraintDifferencePreX family basis coins))
    (relation : AugmentedRelationWitness (F := Fp)
      (ursOfAugmentedBasis shape.k basis).g
      (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w)
    (hout : deployedConstraintOutcomeOfRoot family static basis coins haccept root hxgood =
      PSum.inr relation) :
    deployedConstraintQuotientAgreementOrRelation family basis
      (deployedRootRunOutput family basis coins) = PSum.inr relation := by
  let pnu := deployedRootRunOutput family basis coins
  have hdeployed := deployedAccepts_of_fsWinsFull family.toFamily basis coins.1 haccept
  have hdeployed' : DeployedAccepts (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis coins.1)) := by
    simpa [pnu, deployedRootRunOutput, wrappedAdversary_run_fst,
      wrappedPreIpaReads_run] using hdeployed
  let checks := DeployedConstraintChecks.of_accepts_chRecord
    (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
    (family.instanceCommitment basis) pnu.1.proof.1 (wrappedPreIpaReads pnu)
    (runRounds family.toFamily basis coins.1) hdeployed'
  apply deployedOnlineConstraintOutcome_relation_eq_online family basis pnu root.batchWitness
    (family.outcome_source basis coins.1 root.batchWitness root.outcome_eq)
    root.decoded root.batches_eq checks (static.adviceLength basis) (static.instanceLength basis)
    (static.fixedLength basis) (static.omegaOrder basis) (static.characteristic basis) hxgood
    relation
  simpa [deployedConstraintOutcomeOfRoot, pnu, checks] using hout

/-- Proposition that the actual root-decode data yields a concrete constraint witness.  The
polynomial witness is executable finite data; every relation branch is also exposed by the
standalone computable `deployedConstraintQuotientFinder`. -/
def deployedConstraintDecodedOfRoot
    (family : ComputedDeployedRootFSFamily shape)
    (static : DeployedConstraintStaticChecks family)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (coins : family.toFamily.Coins) : Prop :=
  ∃ (haccept : fsWinsFull (family.adversary basis)
      (fullAlgebraicAcceptDeployed basis (family.vk basis)
        (family.instanceCommitment basis))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins.1)
    (root : DeployedRootDecodeWitness family basis coins)
    (hxgood : (wrappedPreIpaRecord
        (deployedRootRunOutput family basis coins)).x ∉
        szBadSet (deployedConstraintDifferencePreX family basis coins)),
    ∃ witness, deployedConstraintOutcomeOfRoot family static basis coins haccept root hxgood =
      PSum.inl witness

/-- The concrete pre-`x` failure event: the run's `x` answer lands in the total constraint
difference's root set.  No decode or witness guard (issue #127). -/
def deployedConstraintBadXEvent (family : ComputedDeployedRootFSFamily shape) :
    Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins) :=
  {p | (wrappedPreIpaRecord (deployedRootRunOutput family p.1 p.2)).x ∈
    szBadSet (deployedConstraintDifferencePreX family p.1 p.2)}

/-- **The total constraint-difference root set of one oracle table** (issue #127): `szBadSet` of
the total pre-`x` difference, with no existential or success guard.  The run output ignores the
recursive tape, so the tape below is a dummy index, not a choice. -/
def deployedConstraintXBadSet (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) : Set Fp :=
  {x | ∃ tape : RecursiveForkTape Fp shape.k,
    x ∈ szBadSet (deployedConstraintDifferencePreX family basis (O, tape))}

/-- A sufficient chronological condition for the constraint root set. This is stronger than the
live interface below: a reverse-unbatching decoder may legitimately consume challenges after `x`
while still being invariant under changing `x` itself. -/
def DeployedConstraintXPrefixDetermined
    (family : ComputedDeployedRootFSFamily shape) : Prop :=
  forall basis
    (O O' : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp),
    (forall t : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k),
      t.val.length < preIpaLen shape family.init.length 4 -> O t = O' t) ->
    deployedConstraintXBadSet family basis O =
      deployedConstraintXBadSet family basis O'

/-- **The exact causal property at `x`.** Changing only the run's priced `x` answer leaves the
constraint-difference bad set unchanged. Unlike strict prefix determination, this permits the
reverse-unbatching decoder to use later batching challenges. -/
def DeployedConstraintXPinning
    (family : ComputedDeployedRootFSFamily shape) : Prop :=
  forall basis
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) (v : Fp),
    deployedConstraintXBadSet family basis
        (Function.update O (algebraicFullPrefixesPre family.init
          ((family.adversary basis).run O) 4) v) =
      deployedConstraintXBadSet family basis O

/-- Strict pre-`x` determination implies the exact self-reprogramming equality consumed by
`PinnedRootEvent`.  The update point has the `x` prefix's own length, hence is outside the strict
prefix restriction. -/
theorem deployedConstraintXPinning_of_prefixDetermined
    (family : ComputedDeployedRootFSFamily shape)
    (hcausal : DeployedConstraintXPrefixDetermined family) :
    DeployedConstraintXPinning family := by
  intro basis O v
  apply hcausal basis _ O
  intro t ht
  rw [Function.update_apply, if_neg]
  intro hEq
  have hlen : (algebraicFullPrefixesPre family.init
      ((family.adversary basis).run O) 4).val.length =
      preIpaLen shape family.init.length 4 :=
    preIpaSqueezePoints_length_eq family.init _
      ((family.adversary basis).run O).proof.2 4
  rw [hEq, hlen] at ht
  exact lt_irrefl _ ht

/-- A computation of the constraint-difference root set that stops short of the deployed `x`
squeeze. `fresh` records that the selected `x` point was not queried, while `agrees` connects the
stage result to the final decoded root witness. -/
structure DeployedConstraintXOnlineTrace
    (family : ComputedDeployedRootFSFamily shape) where
  stage :
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      OracleComp
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k)) Fp (Set Fp)
  agrees : forall (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
      (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp),
    (stage basis).run O = deployedConstraintXBadSet family basis O
  fresh : forall (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
      (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp),
    algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 4 ∉
      (stage basis).queries O

/-- The staged pre-`x` trace derives the exact pinning equation used by the schedule. -/
theorem DeployedConstraintXOnlineTrace.toPinning
    {family : ComputedDeployedRootFSFamily shape}
    (trace : DeployedConstraintXOnlineTrace family) :
    DeployedConstraintXPinning family := by
  intro basis O v
  let updated := Function.update O (algebraicFullPrefixesPre family.init
    ((family.adversary basis).run O) 4) v
  calc
    deployedConstraintXBadSet family basis updated = (trace.stage basis).run updated :=
      (trace.agrees basis updated).symm
    _ = (trace.stage basis).run O :=
      OracleComp.run_update_of_not_mem_queries _ _ _ _ (trace.fresh basis O)
    _ = deployedConstraintXBadSet family basis O := trace.agrees basis O

/-- The deployed constraint family: direct root extraction plus the staged trace at `x`.
Both pinning equations used by the capstone are derived projections of its two traces. -/
/-
Inhabited twice.  `Composition.StraightLineWitness` does it at the degenerate witness shape;
`Composition.ZeroStraightLine` does it over the shape-generic zero prover, and
`Fixtures.MultiAction.CapturedZeroFamily` instantiates that at the captured key's own scalar
metadata, layouts and domain — so the six staged root events run against captured query layouts
and the staged IPA trace carries eleven live rounds rather than quantifying over `Fin 0`.

The total event of issue #127 removed this interface's old decode guard, so the zero prover
also inhabits it at the full captured shape (`Fixtures.MultiAction.CapturedZeroFamily`): with
sub-proofs the pre-`x` difference is a nonzero polynomial, and the stage prices its root set
from the four folding squeezes alone.
-/
structure ComputedDeployedConstraintFSFamily (shape : Shape)
    extends ComputedDeployedRootFSFamily shape where
  constraintXTrace :
    DeployedConstraintXOnlineTrace toComputedDeployedRootFSFamily

namespace ComputedDeployedConstraintFSFamily

/-- Forget the constraint-`x` trace while retaining the deployed root trace. -/
abbrev toRootFamily (family : ComputedDeployedConstraintFSFamily shape) :
    ComputedDeployedRootFSFamily shape := family.toComputedDeployedRootFSFamily

/-- Forget both deployed chronology refinements. -/
abbrev toFamily (family : ComputedDeployedConstraintFSFamily shape) :
    ComputedAlgebraicFSFamily shape := family.toRootFamily.toFamily

/-- Package a deployed root family with its staged constraint-`x` trace. -/
def ofRoot (family : ComputedDeployedRootFSFamily shape)
    (trace : DeployedConstraintXOnlineTrace family) :
    ComputedDeployedConstraintFSFamily shape where
  toComputedDeployedRootFSFamily := family
  constraintXTrace := trace

/-- Exact constraint-`x` pinning derived from the family's staged trace. -/
theorem pinnedX (family : ComputedDeployedConstraintFSFamily shape) :
    DeployedConstraintXPinning family.toRootFamily :=
  family.constraintXTrace.toPinning

end ComputedDeployedConstraintFSFamily

/-- Causal condition at the `x` squeeze: the constraint-difference root set carries a uniform
bound and is unchanged when the run's own `x` answer is reprogrammed.  It may consume the earlier
`θ`/`β`/`γ`/`y` answers and the retained representations, but cannot be chosen after seeing
`x`. -/
structure DeployedConstraintXSqueezeSchedule (family : ComputedDeployedRootFSFamily shape)
    (epsilonX : ENNReal) where
  measure_le : forall basis O,
    (PMF.uniformOfFintype Fp).toOuterMeasure
      (deployedConstraintXBadSet family basis O) <= epsilonX
  pinned : DeployedConstraintXPinning family

/-- The single pinned event for the constraint evaluation challenge. -/
noncomputable def deployedConstraintXPinnedEvent
    (family : ComputedDeployedRootFSFamily shape) {epsilonX : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family epsilonX)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) :
    PinnedRootEvent (family.adversary basis) where
  point := fun p => algebraicFullPrefixesPre family.init p 4
  bad := fun _p O => deployedConstraintXBadSet family basis O
  budget := epsilonX
  measure_le := fun _p O => schedule.measure_le basis O
  pinned := fun O v => schedule.pinned basis O v

/-- The root-backed bad-`x` event lands in its run's exact pinned root set. -/
theorem deployedConstraintBadX_subset_landing
    (family : ComputedDeployedRootFSFamily shape) {epsilonX : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family epsilonX)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) :
    {coins : family.toFamily.Coins | (basis, coins) ∈ deployedConstraintBadXEvent family} <=
      {coins : family.toFamily.Coins |
        (deployedConstraintXPinnedEvent family schedule basis).Landing coins.1} := by
  rintro coins hx
  change coins.1 (algebraicFullPrefixesPre family.init
      ((family.adversary basis).run coins.1) 4) ∈
    deployedConstraintXBadSet family basis coins.1
  refine ⟨coins.2, ?_⟩
  simpa [deployedConstraintBadXEvent, deployedRootRunOutput, wrappedPreIpaRecord, chRecord,
    wrappedPreIpaReads_run, runReads, runProof] using hx

/-- The exact constraint bad-root event has the direct additive cost `(Q + 1) * epsilonX`.
There is no multiopen rewind, continuation threshold, or fourth-root loss. -/
theorem deployedConstraintBadX_prob_le
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ shape.k) -> T)
    (family : ComputedDeployedRootFSFamily shape) {epsilonX : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family epsilonX) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          deployedConstraintBadXEvent family)
      <= (family.Q + 1 : Nat) * epsilonX := by
  have hset : (fun p : (↥(Set.range query) -> VestaG) × family.toFamily.Coins =>
        (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
        deployedConstraintBadXEvent family =
      {x : (↥(Set.range query) -> VestaG) × family.toFamily.Coins | x.2 ∈
        (fun setup => {coins : family.toFamily.Coins |
          (orchardGeneratorROBasis query setup, coins) ∈
            deployedConstraintBadXEvent family}) x.1} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [hset]
  refine independentProductPMF_fiber_bound (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype family.toFamily.Coins)
    (fun setup => {coins : family.toFamily.Coins |
      (orchardGeneratorROBasis query setup, coins) ∈
        deployedConstraintBadXEvent family}) ?_
  intro setup
  let basis := orchardGeneratorROBasis query setup
  refine le_trans (MeasureTheory.measure_mono
    (deployedConstraintBadX_subset_landing family schedule basis)) ?_
  refine uniformOfFintype_prod_fiber_bound
    (fun _ : RecursiveForkTape Fp shape.k =>
      {O | (deployedConstraintXPinnedEvent family schedule basis).Landing O})
    (fun _ => ?_)
  exact (deployedConstraintXPinnedEvent family schedule basis).landing_measure_le
    (family.queryBound basis)

/-- Extend the recursive/multiopen relation finder with the explicit relation branch produced by
the constraint adapter. -/
def deployedConstraintRelationFinder (family : ComputedDeployedRootFSFamily shape)
    (constraintFinder : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Option (AlgebraicRelationWitness (F := Fp) basis)) :
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.toFamily.Coins ->
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis coins =>
    match family.deployedRelationFinder basis coins with
    | some relation => some relation
    | none => constraintFinder basis coins

/-- Black-box adversary calls made by the concrete combined finder.  The recursive branch is
charged by `instanceAttempt.runs`.  If it fails, the direct-coordinate outcome costs one wrapped
run; if that also returns no relation, `deployedConstraintQuotientFinder` costs two further runs
(one wrapped output and one repeat of the direct-coordinate outcome).  Algebraic postprocessing is
not a black-box call and remains part of the external PPT premise. -/
def deployedConstraintRelationFinderCalls (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (coins : family.toFamily.Coins) : Nat :=
  (family.toFamily.instanceAttempt basis coins).runs +
    match family.toFamily.relationFinder basis coins with
    | some _ => 0
    | none =>
        match family.outcome basis coins.1 with
        | PSum.inr _ => 1
        | PSum.inl _ => 3

/-- The concrete combined finder has at most three black-box calls beyond the recursive
extractor: one direct-coordinate attempt, then the wrapped-output and repeated-outcome calls in
the quotient fallback. -/
theorem deployedConstraintRelationFinderCalls_le
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (coins : family.toFamily.Coins) :
    deployedConstraintRelationFinderCalls family basis coins <=
      (family.toFamily.instanceAttempt basis coins).runs + 3 := by
  unfold deployedConstraintRelationFinderCalls
  cases hrecursive : family.toFamily.relationFinder basis coins with
  | some relation => simp
  | none =>
      cases houtcome : family.outcome basis coins.1 with
      | inl witness => simp
      | inr relation => simp

/-- Expected black-box call bound for the concrete deployed combined relation finder. -/
def DeployedConstraintReductionEfficient (family : ComputedDeployedRootFSFamily shape)
    (R : Nat) : Prop :=
  forall basis : AugmentedIndex (2 ^ shape.k) -> VestaG,
    ∑ coins : family.toFamily.Coins, deployedConstraintRelationFinderCalls family basis coins
      <= R * Fintype.card family.toFamily.Coins

/-- The unconditional AFK bound survives the direct-coordinate and quotient fallbacks with an
additive three-call overhead. -/
theorem deployedConstraintReductionEfficient_poly
    (family : ComputedDeployedRootFSFamily shape) :
    DeployedConstraintReductionEfficient family (afkRunBound family.Q shape.k + 3) := by
  intro basis
  calc
    ∑ coins : family.toFamily.Coins, deployedConstraintRelationFinderCalls family basis coins
        <= ∑ coins : family.toFamily.Coins,
            ((family.toFamily.instanceAttempt basis coins).runs + 3) :=
      Finset.sum_le_sum fun coins _ =>
        deployedConstraintRelationFinderCalls_le family basis coins
    _ = (∑ coins : family.toFamily.Coins,
          (family.toFamily.instanceAttempt basis coins).runs) +
          Fintype.card family.toFamily.Coins * 3 := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ <= afkRunBound family.Q shape.k * Fintype.card family.toFamily.Coins +
          Fintype.card family.toFamily.Coins * 3 :=
      Nat.add_le_add_right (family.toFamily.reductionEfficient_poly basis) _
    _ = (afkRunBound family.Q shape.k + 3) * Fintype.card family.toFamily.Coins := by
      ring

/-- The combined relation event used by the constraint capstone. -/
def deployedConstraintRelationEvent (family : ComputedDeployedRootFSFamily shape)
    (constraintFinder : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Option (AlgebraicRelationWitness (F := Fp) basis)) :
    Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins) :=
  {p | (deployedConstraintRelationFinder family constraintFinder p.1 p.2).isSome}

/-- The existing deployed relation event is contained in the combined constraint finder. -/
theorem deployedRelationEvent_subset_constraintRelationEvent
    (family : ComputedDeployedRootFSFamily shape)
    (constraintFinder : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Option (AlgebraicRelationWitness (F := Fp) basis)) :
    family.deployedRelationEvent <=
      deployedConstraintRelationEvent family constraintFinder := by
  rintro ⟨basis, coins⟩ hrelation
  simp only [deployedConstraintRelationEvent, Set.mem_setOf_eq,
    deployedConstraintRelationFinder]
  change (family.deployedRelationFinder basis coins).isSome at hrelation
  cases h : family.deployedRelationFinder basis coins with
  | none => simp [h] at hrelation
  | some relation => simp

/-- Transfer an arbitrary explicit family relation finder across the uniform-URS basis
identification. -/
theorem deployedConstraintRelation_prob_eq_of_uniformURS {Omega : Type*} (setup : PMF Omega)
    (B : VestaG) (family : ComputedDeployedRootFSFamily shape)
    (constraintFinder : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Option (AlgebraicRelationWitness (F := Fp) basis))
    (basisOf : Omega -> AugmentedIndex (2 ^ shape.k) -> VestaG)
    (hURS : OrchardUniformURSIdentification setup shape.k B basisOf) :
    (independentProductPMF setup
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (basisOf p.1, p.2)) ⁻¹'
          deployedConstraintRelationEvent family constraintFinder) =
      (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) -> Fp) × family.toFamily.Coins)).toOuterMeasure
        (relSetWithCoins B (deployedConstraintRelationFinder family constraintFinder)) := by
  let coinPMF := PMF.uniformOfFintype family.toFamily.Coins
  have hprod :
      (independentProductPMF setup coinPMF).map (fun p => (basisOf p.1, p.2)) =
        (independentProductPMF
          (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) coinPMF).map
            (fun p => (scalarBasis B p.1, p.2)) := by
    calc
      _ = independentProductPMF (setup.map basisOf) coinPMF :=
        independentProductPMF_map_left setup coinPMF basisOf
      _ = independentProductPMF
          ((PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)).map (scalarBasis B))
          coinPMF := congrArg (fun p => independentProductPMF p coinPMF) hURS
      _ = _ := (independentProductPMF_map_left
        (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) coinPMF
        (scalarBasis B)).symm
  have hmeasure := congrArg
    (fun p : PMF ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins) =>
      p.toOuterMeasure (deployedConstraintRelationEvent family constraintFinder)) hprod
  change ((independentProductPMF setup coinPMF).map
      (fun p => (basisOf p.1, p.2))).toOuterMeasure
        (deployedConstraintRelationEvent family constraintFinder) =
    ((independentProductPMF
      (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) coinPMF).map
        (fun p => (scalarBasis B p.1, p.2))).toOuterMeasure
          (deployedConstraintRelationEvent family constraintFinder) at hmeasure
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply] at hmeasure
  calc
    _ = (independentProductPMF
          (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) -> Fp)) coinPMF).toOuterMeasure
          ((fun p => (scalarBasis B p.1, p.2)) ⁻¹'
            deployedConstraintRelationEvent family constraintFinder) := hmeasure
    _ = (PMF.uniformOfFintype
          ((AugmentedIndex (2 ^ shape.k) -> Fp) × family.toFamily.Coins)).toOuterMeasure
          (relSetWithCoins B (deployedConstraintRelationFinder family constraintFinder)) := by
      rw [independentProductPMF_uniform]
      congr 1
      ext p
      simp only [Set.mem_preimage, deployedConstraintRelationEvent, Set.mem_setOf_eq,
        relSetWithCoins, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Generator-random-oracle form of the combined relation bound.  Recursive IPA, algebraic
multiopen, and constraint-binding relations are all charged to one textbook-DLOG assumption. -/
theorem deployedConstraintRelation_prob_le_of_generatorRO_textbookDL
    {T : Type*} [DecidableEq T] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T) (hquery : Function.Injective query)
    (family : ComputedDeployedRootFSFamily shape)
    (constraintFinder : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Option (AlgebraicRelationWitness (F := Fp) basis))
    {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      (deployedConstraintRelationFinder family constraintFinder) bound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          deployedConstraintRelationEvent family constraintFinder)
      <= (bound + 1 / Fintype.card Fp) := by
  rw [deployedConstraintRelation_prob_eq_of_uniformURS
    (orchardGeneratorROSetup query) B family constraintFinder
    (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO shape.k B hB query hquery)]
  exact relationWithCoins_prob_le_of_textbookDL B
    (deployedConstraintRelationFinder family constraintFinder) hDL

/-- Runtime-aware generator-random-oracle relation bound for the concrete combined finder.  The
fixed-budget DLOG solver pays the programmed-basis `1/|Fp|` term, while truncating the unconditional
expected call bound contributes `(afkRunBound Q k + 3)/(L+1)`. -/
theorem deployedConstraintRelation_prob_le_of_generatorRO_truncated_textbookDL
    {T : Type*} [DecidableEq T] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T) (hquery : Function.Injective query)
    (family : ComputedDeployedRootFSFamily shape) {L : Nat} {bound : ENNReal}
    (hDL : TextbookDLWithCoinsTruncatedAdvantageLE B
      (deployedConstraintRelationFinder family
        (deployedConstraintQuotientFinder family))
      (deployedConstraintRelationFinderCalls family) L bound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          deployedConstraintRelationEvent family
            (deployedConstraintQuotientFinder family))
      <= bound + 1 / Fintype.card Fp +
        ((afkRunBound family.Q shape.k + 3 : Nat) : ENNReal) / (L + 1 : Nat) := by
  rw [deployedConstraintRelation_prob_eq_of_uniformURS
    (orchardGeneratorROSetup query) B family (deployedConstraintQuotientFinder family)
    (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO shape.k B hB query hquery)]
  have hExpected : RelationFinderExpectedCallsLE
      (deployedConstraintRelationFinderCalls family)
      (afkRunBound family.Q shape.k + 3) := by
    simpa only [RelationFinderExpectedCallsLE, DeployedConstraintReductionEfficient] using
      deployedConstraintReductionEfficient_poly family
  exact relationWithCoins_prob_le_of_truncated_textbookDL B
    (deployedConstraintRelationFinder family (deployedConstraintQuotientFinder family))
    (deployedConstraintRelationFinderCalls family) hExpected hDL

/-- Deterministic containment needed by the final constraint capstone.  Once the root decode is
available, failure to obtain the constraint relation must either make the combined finder return
an explicit relation or hit the pre-`x` bad event. -/
def DeployedConstraintUpgradeContained (family : ComputedDeployedRootFSFamily shape)
    (constraintFinder : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Option (AlgebraicRelationWitness (F := Fp) basis))
    (constraintDecoded : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Prop)
    (badX : Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins)) : Prop :=
  {p | fsWinsFull (family.adversary p.1)
      (fullAlgebraicAcceptDeployed p.1 (family.vk p.1)
        (family.instanceCommitment p.1))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) p.2.1 ∧
    deployedRootDecoded family p.1 p.2 ∧ ¬ constraintDecoded p.1 p.2} <=
    deployedConstraintRelationEvent family constraintFinder ∪ badX

/-- The root-backed decoded predicate closes the deterministic upgrade seam: on an accepting
root-decode run, either the constraint witness exists, the computable quotient finder exposes
concrete relation coefficients, or the run's `x` challenge lies in the exact constraint-difference
root set. -/
theorem deployedConstraintUpgradeContained_of_root
    (family : ComputedDeployedRootFSFamily shape)
    (static : DeployedConstraintStaticChecks family) :
    DeployedConstraintUpgradeContained family
      (deployedConstraintQuotientFinder family)
      (deployedConstraintDecodedOfRoot family static)
      (deployedConstraintBadXEvent family) := by
  rintro ⟨basis, coins⟩ ⟨haccept, hroot, hnotDecoded⟩
  rcases hroot with ⟨root⟩
  by_cases hxgood : (wrappedPreIpaRecord
      (deployedRootRunOutput family basis coins)).x ∉
      szBadSet (deployedConstraintDifferencePreX family basis coins)
  · cases hout : deployedConstraintOutcomeOfRoot family static basis coins haccept root hxgood with
    | inl witness =>
        exfalso
        apply hnotDecoded
        exact ⟨haccept, root, hxgood, witness, hout⟩
    | inr relation =>
        apply Or.inl
        simp only [deployedConstraintRelationEvent, Set.mem_setOf_eq,
          deployedConstraintRelationFinder]
        cases hbase : family.deployedRelationFinder basis coins with
        | some baseRelation => simp
        | none =>
            have hrelation := deployedConstraintOutcomeOfRoot_relation_eq_online family static
              basis coins haccept root hxgood relation hout
            simp [deployedConstraintQuotientFinder, root.outcome_eq, hrelation]
  · apply Or.inr
    exact Classical.not_not.mp hxgood

/-- Full deterministic decomposition for the concrete constraint endpoint. -/
theorem deployedConstraintFailure_subset_union
    (family : ComputedDeployedRootFSFamily shape)
    (constraintFinder : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Option (AlgebraicRelationWitness (F := Fp) basis))
    (constraintDecoded : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Prop)
    (badX : Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins))
    (hupgrade : DeployedConstraintUpgradeContained family constraintFinder
      constraintDecoded badX) :
    snarkExtractionFailureEventDeployed family.toFamily constraintDecoded <=
      deployedNonRelationFailureEvent family ∪
        (deployedConstraintRelationEvent family constraintFinder ∪
          (cleanButNotExtractedDeployed family.toFamily (deployedRootExtracted family) ∪
            badX)) := by
  rintro p ⟨haccept, hnotConstraint⟩
  by_cases hroot : deployedRootDecoded family p.1 p.2
  · rcases hupgrade ⟨haccept, hroot, hnotConstraint⟩ with hrelation | hbad
    · exact Or.inr (Or.inl hrelation)
    · exact Or.inr (Or.inr (Or.inr hbad))
  · have hdecodeFailure : p ∈
        snarkExtractionFailureEventDeployed family.toFamily (deployedRootDecoded family) :=
      ⟨haccept, hroot⟩
    rcases deployedDecodeFailure_subset_union family hdecodeFailure with
        hnonRelation | hrelation | hresidual
    · exact Or.inl hnonRelation
    · exact Or.inr (Or.inl
        (deployedRelationEvent_subset_constraintRelationEvent family constraintFinder hrelation))
    · exact Or.inr (Or.inr (Or.inl hresidual))

/-- Composite bound for the concrete constraint endpoint, factored over an explicit bound for the
combined relation event.  DLOG reductions, including fixed-budget truncations, enter only through
`hrelation`; `badXBound` is instantiated separately by the pre-`x` prefix schedule. -/
theorem snarkConstraintsDeployed_prob_le_via_deployed_roots_of_relation_bound
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ shape.k) -> T)
    (family : ComputedDeployedRootFSFamily shape)
    (constraintFinder : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Option (AlgebraicRelationWitness (F := Fp) basis))
    (constraintDecoded : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Prop)
    (badX : Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins))
    (hupgrade : DeployedConstraintUpgradeContained family constraintFinder
      constraintDecoded badX)
    {relationBound badXBound : ENNReal}
    (hrelation : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          deployedConstraintRelationEvent family constraintFinder) <= relationBound)
    (hbadX : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badX) <= badXBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily constraintDecoded)
      <= ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          relationBound)
        + (family.Q + (11 + shape.k) + 1 : Nat) * algebraicRootBudget shape shape.k
        + badXBound := by
  let setup := orchardGeneratorROSetup query
  let coinPMF := PMF.uniformOfFintype family.toFamily.Coins
  let basisOf := orchardGeneratorROBasis query
  let nonRelationBound : ENNReal :=
    (family.Q + shape.k) * (3 / Fintype.card Fp) +
      (family.Q + 1 : Nat) * (1 / Fintype.card Fp)
  let rootBound : ENNReal :=
    (family.Q + (11 + shape.k) + 1 : Nat) * algebraicRootBudget shape shape.k
  have hnonRelation := deployedNonRelationFailure_prob_le_of_generatorRO query family
  have hroots :
      (independentProductPMF setup coinPMF).toOuterMeasure
          ((fun p => (basisOf p.1, p.2)) ⁻¹'
            cleanButNotExtractedDeployed family.toFamily (deployedRootExtracted family))
        <= rootBound := by
    exact residual_le_via_wrapped_deployed_pinned_roots query family.toFamily
      (deployedRootExtracted family) (family.pinnedRoots)
      (family.pinnedRoots_budget_le) (deployedRootFailure_subset_landing family)
  calc
    (independentProductPMF setup coinPMF).toOuterMeasure
        ((fun p => (basisOf p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily constraintDecoded)
      <= (independentProductPMF setup coinPMF).toOuterMeasure
          ((fun p => (basisOf p.1, p.2)) ⁻¹'
            (deployedNonRelationFailureEvent family ∪
              (deployedConstraintRelationEvent family constraintFinder ∪
                (cleanButNotExtractedDeployed family.toFamily (deployedRootExtracted family) ∪
                  badX)))) := MeasureTheory.measure_mono
        (Set.preimage_mono
          (deployedConstraintFailure_subset_union family constraintFinder constraintDecoded
            badX hupgrade))
    _ = (independentProductPMF setup coinPMF).toOuterMeasure
          (((fun p => (basisOf p.1, p.2)) ⁻¹' deployedNonRelationFailureEvent family) ∪
            (((fun p => (basisOf p.1, p.2)) ⁻¹'
                deployedConstraintRelationEvent family constraintFinder) ∪
              (((fun p => (basisOf p.1, p.2)) ⁻¹'
                  cleanButNotExtractedDeployed family.toFamily (deployedRootExtracted family)) ∪
                ((fun p => (basisOf p.1, p.2)) ⁻¹' badX)))) := by
      simp only [Set.preimage_union]
    _ <= (independentProductPMF setup coinPMF).toOuterMeasure
          ((fun p => (basisOf p.1, p.2)) ⁻¹' deployedNonRelationFailureEvent family) +
        ((independentProductPMF setup coinPMF).toOuterMeasure
            ((fun p => (basisOf p.1, p.2)) ⁻¹'
              deployedConstraintRelationEvent family constraintFinder) +
          ((independentProductPMF setup coinPMF).toOuterMeasure
              ((fun p => (basisOf p.1, p.2)) ⁻¹'
                cleanButNotExtractedDeployed family.toFamily (deployedRootExtracted family)) +
            (independentProductPMF setup coinPMF).toOuterMeasure
              ((fun p => (basisOf p.1, p.2)) ⁻¹' badX))) := by
      exact (MeasureTheory.measure_union_le _ _).trans
        (add_le_add le_rfl ((MeasureTheory.measure_union_le _ _).trans
          (add_le_add le_rfl (MeasureTheory.measure_union_le _ _))))
    _ <= nonRelationBound + (relationBound + (rootBound + badXBound)) :=
      add_le_add hnonRelation (add_le_add hrelation (add_le_add hroots hbadX))
    _ = ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          relationBound)
        + (family.Q + (11 + shape.k) + 1 : Nat) * algebraicRootBudget shape shape.k
        + badXBound := by
      simp only [nonRelationBound, rootBound]
      ac_rfl

/-- DLOG-based composite bound for the concrete constraint endpoint.  This runtime-free wrapper is
retained for callers that already supply hardness for the untruncated combined finder. -/
theorem snarkConstraintsDeployed_prob_le_via_deployed_roots
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T) (hquery : Function.Injective query)
    (family : ComputedDeployedRootFSFamily shape)
    (constraintFinder : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Option (AlgebraicRelationWitness (F := Fp) basis))
    (constraintDecoded : (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      family.toFamily.Coins -> Prop)
    (badX : Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins))
    (hupgrade : DeployedConstraintUpgradeContained family constraintFinder
      constraintDecoded badX)
    {dlogBound badXBound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      (deployedConstraintRelationFinder family constraintFinder) dlogBound)
    (hbadX : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badX) <= badXBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily constraintDecoded)
      <= ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          (dlogBound + 1 / Fintype.card Fp))
        + (family.Q + (11 + shape.k) + 1 : Nat) * algebraicRootBudget shape shape.k
        + badXBound := by
  apply snarkConstraintsDeployed_prob_le_via_deployed_roots_of_relation_bound query family
    constraintFinder constraintDecoded badX hupgrade
  · exact deployedConstraintRelation_prob_le_of_generatorRO_textbookDL
      B hB query hquery family constraintFinder hDL
  · exact hbadX

/-- Specialization of the composite bound to the concrete online constraint outcome provider. -/
theorem snarkConstraintsDeployed_prob_le_of_online_outcome
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T) (hquery : Function.Injective query)
    (family : ComputedDeployedRootFSFamily shape)
    (provider : DeployedConstraintOutcomeProvider family)
    (badX : Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins))
    (hupgrade : DeployedConstraintUpgradeContained family
      (deployedConstraintFinderOfOutcome family provider)
      (deployedConstraintDecodedOfOutcome family provider) badX)
    {dlogBound badXBound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      (deployedConstraintRelationFinder family
        (deployedConstraintFinderOfOutcome family provider)) dlogBound)
    (hbadX : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badX) <= badXBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily
            (deployedConstraintDecodedOfOutcome family provider))
      <= ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          (dlogBound + 1 / Fintype.card Fp))
        + (family.Q + (11 + shape.k) + 1 : Nat) * algebraicRootBudget shape shape.k
        + badXBound :=
  snarkConstraintsDeployed_prob_le_via_deployed_roots B hB query hquery family
    (deployedConstraintFinderOfOutcome family provider)
    (deployedConstraintDecodedOfOutcome family provider) badX hupgrade hDL hbadX

/-- Concrete rewind-free **compressed-identity** capstone.  The only computational premise is
textbook single-instance DLOG for the executable combined finder; the schedule prices the bad-`x`
event additively at `(Q + 1) * epsilonX`.  This theorem does not claim row-level circuit semantics;
that conclusion is the separately budgeted semantic capstone below. -/
theorem snarkConstraintsDeployed_prob_le_of_root_schedule
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T) (hquery : Function.Injective query)
    (family : ComputedDeployedRootFSFamily shape)
    (static : DeployedConstraintStaticChecks family)
    {epsilonX dlogBound : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family epsilonX)
    (hDL : TextbookDLWithCoinsAdvantageLE B
      (deployedConstraintRelationFinder family
        (deployedConstraintQuotientFinder family)) dlogBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily
            (deployedConstraintDecodedOfRoot family static))
      <= ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          (dlogBound + 1 / Fintype.card Fp))
        + (family.Q + (11 + shape.k) + 1 : Nat) * algebraicRootBudget shape shape.k
        + (family.Q + 1 : Nat) * epsilonX := by
  exact snarkConstraintsDeployed_prob_le_via_deployed_roots B hB query hquery family
    (deployedConstraintQuotientFinder family)
    (deployedConstraintDecodedOfRoot family static)
    (deployedConstraintBadXEvent family)
    (deployedConstraintUpgradeContained_of_root family static) hDL
    (deployedConstraintBadX_prob_le query family schedule)

/-- Runtime-aware rewind-free **compressed-identity** capstone.  Standard fixed-call DLOG hardness
is applied to the combined finder truncated at `L`; finite Markov conversion from its unconditional
expected call bound contributes the explicit tail `(afkRunBound Q k + 3)/(L+1)`.  Like the
schedule-only capstone above, this is a compressed-identity statement: row-level gate, permutation,
and lookup semantics are the four-budget promotion
`snarkConstraintsSemanticDeployed_prob_le_of_root_schedule_runtime` below. -/
theorem snarkConstraintsDeployed_prob_le_of_root_schedule_runtime
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T) (hquery : Function.Injective query)
    (family : ComputedDeployedRootFSFamily shape)
    (static : DeployedConstraintStaticChecks family)
    {L : Nat} {epsilonX dlogBound : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family epsilonX)
    (hDL : TextbookDLWithCoinsTruncatedAdvantageLE B
      (deployedConstraintRelationFinder family
        (deployedConstraintQuotientFinder family))
      (deployedConstraintRelationFinderCalls family) L dlogBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily
            (deployedConstraintDecodedOfRoot family static))
      <= ((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          (dlogBound + 1 / Fintype.card Fp +
            ((afkRunBound family.Q shape.k + 3 : Nat) : ENNReal) / (L + 1 : Nat)))
        + (family.Q + (11 + shape.k) + 1 : Nat) * algebraicRootBudget shape shape.k
        + (family.Q + 1 : Nat) * epsilonX := by
  apply snarkConstraintsDeployed_prob_le_via_deployed_roots_of_relation_bound query family
    (deployedConstraintQuotientFinder family)
    (deployedConstraintDecodedOfRoot family static)
    (deployedConstraintBadXEvent family)
    (deployedConstraintUpgradeContained_of_root family static)
  · exact deployedConstraintRelation_prob_le_of_generatorRO_truncated_textbookDL
      B hB query hquery family hDL
  · exact deployedConstraintBadX_prob_le query family schedule

/-! ## Promotion from the compressed identity to circuit semantics

The constraint witness above proves the verifier's identity only after `y` has compressed the
constraint list and `beta`, `gamma`, and `theta` have compressed the permutation and lookup values.
Calling that semantic circuit satisfaction is unsound without pricing collisions at those four
earlier squeezes. The interface below makes the step explicit: the caller supplies the semantic
predicate, the four failure events, and a proof that a compressed witness outside them has the
intended semantics.
-/

/-- Outside the four challenge-failure events, a compressed constraint witness upgrades to the
caller's row-level semantic predicate. In a concrete Orchard instantiation, `ConstraintRelations`
supplies this implication from the good-`y` fold split, good permutation `beta`/`gamma`, and good
lookup-tuple `theta` hypotheses. -/
def DeployedConstraintSemanticUpgradeContained
    (family : ComputedDeployedRootFSFamily shape)
    (compressedDecoded semanticDecoded :
      (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.toFamily.Coins -> Prop)
    (badY badBeta badGamma badTheta :
      Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins)) : Prop :=
  {p | compressedDecoded p.1 p.2 ∧ ¬ semanticDecoded p.1 p.2} <=
    badY ∪ (badBeta ∪ (badGamma ∪ badTheta))

/-- Failure of the semantic predicate is either failure of the compressed-identity extractor or
one of the four explicitly priced challenge surfaces. -/
theorem deployedConstraintSemanticFailure_subset_union
    (family : ComputedDeployedRootFSFamily shape)
    (compressedDecoded semanticDecoded :
      (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.toFamily.Coins -> Prop)
    (badY badBeta badGamma badTheta :
      Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins))
    (hsemantic : DeployedConstraintSemanticUpgradeContained family compressedDecoded
      semanticDecoded badY badBeta badGamma badTheta) :
    snarkExtractionFailureEventDeployed family.toFamily semanticDecoded <=
      snarkExtractionFailureEventDeployed family.toFamily compressedDecoded ∪
        (badY ∪ (badBeta ∪ (badGamma ∪ badTheta))) := by
  rintro p ⟨haccept, hnotSemantic⟩
  by_cases hcompressed : compressedDecoded p.1 p.2
  · exact Or.inr (hsemantic ⟨hcompressed, hnotSemantic⟩)
  · exact Or.inl ⟨haccept, hcompressed⟩

/-- The four-budget semantic promotion, factored over an arbitrary bound for the
compressed-identity failure event.  Both the schedule-only and the runtime-aware capstones pass
through this one calculation. -/
theorem snarkConstraintsSemanticDeployed_prob_le_of_compressed_bound
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ shape.k) -> T)
    (family : ComputedDeployedRootFSFamily shape)
    (compressedDecoded semanticDecoded :
      (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.toFamily.Coins -> Prop)
    (badY badBeta badGamma badTheta :
      Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins))
    {compressedBound yBound betaBound gammaBound thetaBound : ENNReal}
    (hsemantic : DeployedConstraintSemanticUpgradeContained family
      compressedDecoded semanticDecoded badY badBeta badGamma badTheta)
    (hcompressed : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily compressedDecoded)
      <= compressedBound)
    (hY : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badY) <= yBound)
    (hBeta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badBeta) <= betaBound)
    (hGamma : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badGamma) <= gammaBound)
    (hTheta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badTheta) <= thetaBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily semanticDecoded)
      <= compressedBound + (yBound + (betaBound + (gammaBound + thetaBound))) := by
  let mu := (independentProductPMF (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
  let basisCoins : ((↥(Set.range query) -> VestaG) × family.toFamily.Coins) ->
      ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins) :=
    fun p => (orchardGeneratorROBasis query p.1, p.2)
  change mu (basisCoins ⁻¹'
      snarkExtractionFailureEventDeployed family.toFamily semanticDecoded) <= _
  have hsubset : basisCoins ⁻¹'
        snarkExtractionFailureEventDeployed family.toFamily semanticDecoded <=
      basisCoins ⁻¹'
        (snarkExtractionFailureEventDeployed family.toFamily compressedDecoded ∪
          (badY ∪ (badBeta ∪ (badGamma ∪ badTheta)))) :=
    Set.preimage_mono
      (deployedConstraintSemanticFailure_subset_union family compressedDecoded semanticDecoded
        badY badBeta badGamma badTheta hsemantic)
  calc
    mu (basisCoins ⁻¹'
        snarkExtractionFailureEventDeployed family.toFamily semanticDecoded)
        <= mu (basisCoins ⁻¹'
          (snarkExtractionFailureEventDeployed family.toFamily compressedDecoded ∪
            (badY ∪ (badBeta ∪ (badGamma ∪ badTheta))))) :=
      MeasureTheory.measure_mono hsubset
    _ = mu ((basisCoins ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily compressedDecoded) ∪
        ((basisCoins ⁻¹' badY) ∪
          ((basisCoins ⁻¹' badBeta) ∪
            ((basisCoins ⁻¹' badGamma) ∪ (basisCoins ⁻¹' badTheta))))) := by
      simp only [Set.preimage_union]
    _ <= mu (basisCoins ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily compressedDecoded) +
        (mu (basisCoins ⁻¹' badY) +
          (mu (basisCoins ⁻¹' badBeta) +
            (mu (basisCoins ⁻¹' badGamma) + mu (basisCoins ⁻¹' badTheta)))) := by
      exact (MeasureTheory.measure_union_le _ _).trans
        (add_le_add le_rfl ((MeasureTheory.measure_union_le _ _).trans
          (add_le_add le_rfl ((MeasureTheory.measure_union_le _ _).trans
            (add_le_add le_rfl (MeasureTheory.measure_union_le _ _))))))
    _ <= compressedBound + (yBound + (betaBound + (gammaBound + thetaBound))) :=
      add_le_add hcompressed (add_le_add hY (add_le_add hBeta (add_le_add hGamma hTheta)))

/-- **Semantic constraint capstone.** The compressed-identity knowledge error is augmented by
four named additive budgets. No conclusion about row-level gate, permutation, or lookup semantics
is available from the compressed payload unless `hsemantic` and all four measure bounds are
provided. -/
theorem snarkConstraintsSemanticDeployed_prob_le_of_root_schedule
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T) (hquery : Function.Injective query)
    (family : ComputedDeployedRootFSFamily shape)
    (static : DeployedConstraintStaticChecks family)
    (semanticDecoded :
      (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.toFamily.Coins -> Prop)
    (badY badBeta badGamma badTheta :
      Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins))
    {epsilonX dlogBound yBound betaBound gammaBound thetaBound : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family epsilonX)
    (hDL : TextbookDLWithCoinsAdvantageLE B
      (deployedConstraintRelationFinder family
        (deployedConstraintQuotientFinder family)) dlogBound)
    (hsemantic : DeployedConstraintSemanticUpgradeContained family
      (deployedConstraintDecodedOfRoot family static)
      semanticDecoded badY badBeta badGamma badTheta)
    (hY : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badY) <= yBound)
    (hBeta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badBeta) <= betaBound)
    (hGamma : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badGamma) <= gammaBound)
    (hTheta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badTheta) <= thetaBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily semanticDecoded)
      <= (((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          (dlogBound + 1 / Fintype.card Fp))
        + (family.Q + (11 + shape.k) + 1 : Nat) * algebraicRootBudget shape shape.k
        + (family.Q + 1 : Nat) * epsilonX)
        + (yBound + (betaBound + (gammaBound + thetaBound))) :=
  snarkConstraintsSemanticDeployed_prob_le_of_compressed_bound query family
    (deployedConstraintDecodedOfRoot family static) semanticDecoded
    badY badBeta badGamma badTheta hsemantic
    (snarkConstraintsDeployed_prob_le_of_root_schedule B hB query hquery
      family static schedule hDL)
    hY hBeta hGamma hTheta

/-- **Runtime-aware semantic constraint capstone.** The four-budget semantic promotion applied to
the fixed-call runtime endpoint: standard fixed-call DLOG hardness for the truncated combined
finder, the explicit AFK truncation tail, and the four named challenge budgets, with row-level
semantics supplied by `hsemantic`. -/
theorem snarkConstraintsSemanticDeployed_prob_le_of_root_schedule_runtime
    {T : Type*} [DecidableEq T]
    (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) -> T) (hquery : Function.Injective query)
    (family : ComputedDeployedRootFSFamily shape)
    (static : DeployedConstraintStaticChecks family)
    (semanticDecoded :
      (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.toFamily.Coins -> Prop)
    (badY badBeta badGamma badTheta :
      Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) × family.toFamily.Coins))
    {L : Nat} {epsilonX dlogBound yBound betaBound gammaBound thetaBound : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family epsilonX)
    (hDL : TextbookDLWithCoinsTruncatedAdvantageLE B
      (deployedConstraintRelationFinder family
        (deployedConstraintQuotientFinder family))
      (deployedConstraintRelationFinderCalls family) L dlogBound)
    (hsemantic : DeployedConstraintSemanticUpgradeContained family
      (deployedConstraintDecodedOfRoot family static)
      semanticDecoded badY badBeta badGamma badTheta)
    (hY : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badY) <= yBound)
    (hBeta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badBeta) <= betaBound)
    (hGamma : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badGamma) <= gammaBound)
    (hTheta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' badTheta) <= thetaBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily semanticDecoded)
      <= (((family.Q + shape.k) * (3 / Fintype.card Fp) +
          (family.Q + 1 : Nat) * (1 / Fintype.card Fp) +
          (dlogBound + 1 / Fintype.card Fp +
            ((afkRunBound family.Q shape.k + 3 : Nat) : ENNReal) / (L + 1 : Nat)))
        + (family.Q + (11 + shape.k) + 1 : Nat) * algebraicRootBudget shape shape.k
        + (family.Q + 1 : Nat) * epsilonX)
        + (yBound + (betaBound + (gammaBound + thetaBound))) :=
  snarkConstraintsSemanticDeployed_prob_le_of_compressed_bound query family
    (deployedConstraintDecodedOfRoot family static) semanticDecoded
    badY badBeta badGamma badTheta hsemantic
    (snarkConstraintsDeployed_prob_le_of_root_schedule_runtime B hB query hquery
      family static schedule hDL)
    hY hBeta hGamma hTheta

end Zcash.Snark
