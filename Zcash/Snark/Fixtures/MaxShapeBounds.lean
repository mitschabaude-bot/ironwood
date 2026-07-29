import Zcash.Snark.Fixtures.MaxShape
import Zcash.Snark.Soundness.Composition.AlgebraicRootBudget
import Zcash.Snark.Soundness.Composition.DeployedConstraintContainment
import Zcash.Snark.Soundness.Composition.DirectPathCost

/-!
# Concrete composite-bound inputs for the captured Orchard shape

This module specializes the pinned AGM root budget to the captured Orchard verifier
dimensions while leaving the adversary query count explicit.  The resulting term is additive;
there is no continuation threshold or fourth-root conversion in this path.
-/

namespace Zcash.Snark.FixtureMax

open Zcash.Arithmetic (card_Fp scalarFieldOrder)

open Zcash.Snark
open scoped ENNReal

local instance vestaInhabitedMaxShapeBounds : Inhabited VestaG := ⟨0⟩

/-- Cross-multiplication for finite positive natural denominators, packaged for the concrete
arithmetic below. -/
private theorem ennreal_nat_div_le_one_div {a p m : ℕ} (hp : 0 < p) (hm : 0 < m)
    (h : a * m ≤ p) :
    (a : ℝ≥0∞) / p ≤ 1 / (m : ℝ≥0∞) := by
  apply (ENNReal.div_le_iff (Nat.cast_ne_zero.mpr hp.ne')
    (ENNReal.natCast_ne_top p)).2
  have hcast : (a : ℝ≥0∞) * (m : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by exact_mod_cast h
  have hdiv := (ENNReal.le_div_iff_mul_le
    (Or.inl (Nat.cast_ne_zero.mpr hm.ne'))
    (Or.inl (ENNReal.natCast_ne_top m))).2 hcast
  simpa only [div_eq_mul_inv, one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm] using hdiv

/-- The captured shape contributes fifty opening queries per action and forty-six shared queries. -/
theorem queryBudget_at_captured_shape (n : ℕ) :
    queryBudget (shape n) = 50 * n + 46 := by
  simp [queryBudget, shape]
  omega

/-! ## Direct-path total cost at the captured shape -/

/-- **The direct-coordinate decode's total cost at any captured shape is linear in the action
count.**  Six columns, each traversing at most `50·n + 46` members at `sourceLen + 4101` steps
each plus a `2050`-coordinate aggregate fold — field-independent throughout. -/
theorem deployedDirectDecodeOps_at_captured_shape {n : ℕ}
    (vk : VerifyingKey (shape n) Fp VestaG)
    (instanceCommitment : Fin (shape n).numProofs → ℕ → VestaG)
    (ps : ProofString (shape n) Fp VestaG) (ch : Challenges (shape n).k Fp)
    (sourceLen : ℕ) :
    deployedDirectDecodeOps vk instanceCommitment ps ch sourceLen ≤
      6 * ((50 * n + 46) * (sourceLen + 4101) + 2050) := by
  refine le_trans
    (deployedDirectDecodeOps_le vk instanceCommitment ps ch sourceLen) ?_
  rw [queryBudget_at_captured_shape,
    show (shape n).numPointSets = 5 from rfl, show (shape n).k = 11 from rfl]
  norm_num

/-- **At the consensus maximum, the direct path is negligible against the `2^122` work target.**
Even with a generous `2^90` covered-source length, the modeled cost stays below `2^122` — the
direct-coordinate postprocessing never threatens the adversary-work accounting. -/
theorem deployedDirectDecodeOps_at_consensus_max {n : ℕ}
    (hn : n ≤ orchardConsensusMaxProofs)
    (vk : VerifyingKey (shape n) Fp VestaG)
    (instanceCommitment : Fin (shape n).numProofs → ℕ → VestaG)
    (ps : ProofString (shape n) Fp VestaG) (ch : Challenges (shape n).k Fp)
    {sourceLen : ℕ} (hsource : sourceLen ≤ 2 ^ 90) :
    deployedDirectDecodeOps vk instanceCommitment ps ch sourceLen ≤ 2 ^ 122 := by
  refine le_trans
    (deployedDirectDecodeOps_at_captured_shape vk instanceCommitment ps ch sourceLen) ?_
  have hn' : n ≤ 2 ^ 16 - 1 := hn
  calc
    6 * ((50 * n + 46) * (sourceLen + 4101) + 2050)
        ≤ 6 * ((50 * (2 ^ 16 - 1) + 46) * (2 ^ 90 + 4101) + 2050) := by
      have hq : 50 * n + 46 ≤ 50 * (2 ^ 16 - 1) + 46 := by omega
      have hs : sourceLen + 4101 ≤ 2 ^ 90 + 4101 := by omega
      exact Nat.mul_le_mul_left 6
        (Nat.add_le_add_right (Nat.mul_le_mul hq hs) 2050)
    _ ≤ 2 ^ 122 := by norm_num

/-! ## Pinned AGM root budget

The direct-root construction uses a conservative all-members/all-nodes union.  The wrapped
machine makes `11 + k = 22` extra reads and a one-squeeze root event costs
`Q + 22 + 1 = Q + 23` at `k = 11`.
-/

/-- Exact conservative sum of all AGM root budgets at the consensus maximum. -/
theorem algebraicRootBudget_at_consensus_max :
    algebraicRootBudget (shape orchardConsensusMaxProofs) 11 =
      53_686_986_342_456 / (Fintype.card Fp : ENNReal) := by
  rw [algebraicRootBudget, queryBudget_at_captured_shape]
  norm_num [shape, orchardConsensusMaxProofs]

/-- Every consensus-valid captured shape has algebraic-root budget at most the budget computed at
the consensus maximum. -/
theorem algebraicRootBudget_at_captured_shape_le_consensus_max {n : Nat}
    (hn : n ≤ orchardConsensusMaxProofs) :
    algebraicRootBudget (shape n) 11 ≤
      algebraicRootBudget (shape orchardConsensusMaxProofs) 11 :=
  algebraicRootBudget_mono 11 hn rfl rfl rfl rfl rfl rfl le_rfl

/-- The concrete multiopen contribution of the pinned-root theorem under `Q <= T`. -/
noncomputable def consensusPinnedRootMultiopenModel (T : Nat) : ENNReal :=
  (T + 23 : Nat) * algebraicRootBudget (shape orchardConsensusMaxProofs) 11

theorem consensusPinnedRootMultiopenModel_eq (T : Nat) :
    consensusPinnedRootMultiopenModel T =
      ((T + 23 : Nat) : ENNReal) * 53_686_986_342_456 / Fintype.card Fp := by
  rw [consensusPinnedRootMultiopenModel, algebraicRootBudget_at_consensus_max]
  simp only [div_eq_mul_inv]
  ring

/-- At `T = 2^122`, the conservative pinned-root term is still below `2^-86`.  This arithmetic
fact does not assume a generic-group formula for DLOG advantage. -/
theorem consensusPinnedRootMultiopenModel_at_2pow122 :
    consensusPinnedRootMultiopenModel (2 ^ 122) <= (1 / (2 ^ 86 : ENNReal)) := by
  rw [consensusPinnedRootMultiopenModel_eq, card_Fp]
  convert ennreal_nat_div_le_one_div
    (a := (2 ^ 122 + 23) * 53_686_986_342_456)
    (p := scalarFieldOrder) (m := 2 ^ 86)
    (by norm_num [scalarFieldOrder, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    (by norm_num)
    (by norm_num [scalarFieldOrder, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]) using 1 <;>
    norm_num

/-! ## Reduction efficiency

The `dlogBound` premise below is the advantage of the *combined finder*, not of the raw adversary.
Its per-run cost model stays outside Lean, like the random-oracle model: one run of the wrapped
adversary (`Q + 11 + k` oracle reads), one direct-coordinate decode of the retained
representations, and a constant number of field solves.

`T = 2^122` cannot double as that finder's call budget. At `k = 11` the proved
Attema–Fehr–Klooß-style (AFK) expectation is between `2^161` and `2^162` calls, and pushing the
generic Markov tail below `2^-86` would need an `L+1` between `2^247` and `2^248`. So the
recursive endpoint at deployed parameters is a structural polynomial bound, not a concrete
security margin — a solver with either budget can Pollard-rho Vesta directly. The concrete margin
is the straight-line endpoint's, in `StraightLineMaxShapeBounds`.

The finder's unconditional expected call bound is `afkRunBound Q 11 + 3`: the AFK recursive bound
plus the direct-coordinate and quotient fallbacks. The theorems below truncate the solver at a
separate fixed budget `L`, so fixed-call DLOG hardness supplies `dlogBound` and Markov conversion
contributes `(afkRunBound Q 11 + 3)/(L+1)`. The query cap `T` controls the statistical terms
only. -/

/-- Expected black-box calls of the combined finder at the consensus shape, bounded using `Q <= T`.
The additive three is the direct-coordinate and quotient fallback overhead. -/
def consensusCombinedFinderExpectedCallsModel (T : Nat) : Nat :=
  afkRunBound T 11 + 3

/-- The `T = 2^122` AFK expectation is roughly `2^161.54`, not `2^122`. -/
theorem consensusCombinedFinderExpectedCallsModel_at_2pow122_bounds :
    2 ^ 161 < consensusCombinedFinderExpectedCallsModel (2 ^ 122) ∧
      consensusCombinedFinderExpectedCallsModel (2 ^ 122) < 2 ^ 162 := by
  norm_num [consensusCombinedFinderExpectedCallsModel, afkRunBound]

/-- A generic Markov tail of at most `2^-86` needs `L+1` at least `R·2^86`; for this AFK bound
that sufficient budget lies between `2^247` and `2^248`. -/
theorem consensusCombinedFinderBudgetForTail86_at_2pow122_bounds :
    2 ^ 247 < consensusCombinedFinderExpectedCallsModel (2 ^ 122) * 2 ^ 86 ∧
      consensusCombinedFinderExpectedCallsModel (2 ^ 122) * 2 ^ 86 < 2 ^ 248 := by
  norm_num [consensusCombinedFinderExpectedCallsModel, afkRunBound]

/-- **The composite compressed-identity bound for every consensus-valid captured shape** —
row-level semantics remain the four-budget promotion
`snarkConstraintsSemanticDeployed_prob_le_of_root_schedule_runtime`. For any action count
`n ≤ 2¹⁶ − 1` and adversary query budget `Q ≤ T`, monotonicity bounds the shape's multiopen
contribution by `consensusPinnedRootMultiopenModel T`, the consensus-maximum term evaluated at
`≤ 2⁻⁸⁶` for `T = 2¹²²` above. The independent fixed solver budget `L` and its truncation tail
remain explicit. -/
theorem snarkConstraintsDeployed_prob_le_of_consensus_bound
    {n : Nat} (hn : n ≤ orchardConsensusMaxProofs)
    {T' : Type*} [DecidableEq T'] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ (shape n).k) → T')
    (hquery : Function.Injective query)
    (family : ComputedDeployedRootFSFamily (shape n))
    (static : DeployedConstraintStaticChecks family)
    {L : Nat} {epsilonX dlogBound : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family epsilonX)
    (hDL : TextbookDLWithCoinsTruncatedAdvantageLE B
      (deployedConstraintRelationFinder family
        (deployedConstraintQuotientFinder family))
      (deployedConstraintRelationFinderCalls family) L dlogBound)
    {T : ℕ} (hQ : family.Q ≤ T) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily
            (deployedConstraintDecodedOfRoot family static))
      ≤ ((T + 11) * (3 / Fintype.card Fp) +
          (T + 1 : ℕ) * (1 / Fintype.card Fp) +
          (dlogBound + 1 / Fintype.card Fp +
            ((afkRunBound family.Q 11 + 3 : Nat) : ENNReal) / (L + 1 : Nat)))
        + consensusPinnedRootMultiopenModel T
        + (T + 1 : ℕ) * epsilonX := by
  refine le_trans (snarkConstraintsDeployed_prob_le_of_root_schedule_runtime B hB query hquery
    family static schedule hDL) ?_
  rw [consensusPinnedRootMultiopenModel]
  have hk : (shape n).k = 11 := rfl
  simp only [hk]
  gcongr
  · norm_num
  · exact algebraicRootBudget_at_captured_shape_le_consensus_max hn

/-- **The exact consensus-maximum instance.** This compatibility theorem is the maximum-action
specialization of `snarkConstraintsDeployed_prob_le_of_consensus_bound`; the quantified theorem,
not this endpoint alone, justifies applying the maximum model to smaller consensus-valid bundles. -/
theorem snarkConstraintsDeployed_prob_le_at_consensus_max
    {T' : Type*} [DecidableEq T'] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ (shape orchardConsensusMaxProofs).k) → T')
    (hquery : Function.Injective query)
    (family : ComputedDeployedRootFSFamily (shape orchardConsensusMaxProofs))
    (static : DeployedConstraintStaticChecks family)
    {L : Nat} {epsilonX dlogBound : ENNReal}
    (schedule : DeployedConstraintXSqueezeSchedule family epsilonX)
    (hDL : TextbookDLWithCoinsTruncatedAdvantageLE B
      (deployedConstraintRelationFinder family
        (deployedConstraintQuotientFinder family))
      (deployedConstraintRelationFinderCalls family) L dlogBound)
    {T : ℕ} (hQ : family.Q ≤ T) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.toFamily.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          snarkExtractionFailureEventDeployed family.toFamily
            (deployedConstraintDecodedOfRoot family static))
      ≤ ((T + 11) * (3 / Fintype.card Fp) +
          (T + 1 : ℕ) * (1 / Fintype.card Fp) +
          (dlogBound + 1 / Fintype.card Fp +
            ((afkRunBound family.Q 11 + 3 : Nat) : ENNReal) / (L + 1 : Nat)))
        + consensusPinnedRootMultiopenModel T
        + (T + 1 : ℕ) * epsilonX :=
  snarkConstraintsDeployed_prob_le_of_consensus_bound (Nat.le_refl _)
    B hB query hquery family static schedule hDL hQ

end Zcash.Snark.FixtureMax
