import Zcash.Circuits.Integration.StraightLineActionEvent
import Zcash.Snark.Soundness.Composition.SequentialLift
import Zcash.Snark.Soundness.Composition.ChallengeReads
import Zcash.Snark.Soundness.Composition.SemanticChallengeRemainder

/-!
# Pricing the Action semantic failure events from sequential cuts

The capstone takes four bounds as premises: the run's `θ`, `β`, `γ` and `x`/`y` challenges
landing in their terminal exclusion sets.  This module discharges each from a sequential cut at
the challenge's own squeeze index and a *view* — the exclusion set's inputs read off the cut
state.  The chain per challenge:

1. the run record's challenge is the oracle's answer at its squeeze prefix
   (`straightLineRunReads_eq`);
2. the exclusion set reads only data the view supplies (`ChallengeReads` congruences, or the
   model view outright for `x`/`y`), so the failure event is contained in the cut's state
   surface (`SequentialCut.surfaceEvent`);
3. the surface costs `(Q + 1) * epsilon` (`SequentialCut.surfaceEvent_prob_le`).

The view-agreement premises are the sequential model's content: a prover that commits its
columns before `θ` is squeezed determines, at that moment, everything the `θ` set reads.  The
final endpoint quantifies over families equipped with such cuts.
-/

namespace Zcash.Snark

namespace ActionTerminal

open Halo2 Polynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder)
open Classical MeasureTheory
open scoped ENNReal

local instance vestaInhabitedStraightLineActionBudgets : Inhabited VestaG := ⟨0⟩

variable (pp : ProofParams)
  (family : ComputedStraightLineDeployedFSFamily (pp.mergeDerived actionCircuit))
  (static : DeployedConstraintStaticChecks family.toRootFamily)
  (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
  (hvk : ∀ basis, family.vk basis =
    actionCircuit.toVerifierKey pp
      (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
  (hI : ∀ basis, family.instanceCommitment basis =
    actionCircuit.instanceCommitment pp
      (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
  (hchar : ∀ basis O, deployedX4PairCount
    (actionCircuit.toVerifierKey pp
      (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
    (actionCircuit.instanceCommitment pp
      (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
    (straightLineRunOutput family basis O).1.proof.1
    (straightLineRunRecord family basis O) < scalarFieldOrder)

/-- The deployed Action key at one basis. -/
noncomputable abbrev vkAt
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) :
    VerifyingKey (pp.mergeDerived actionCircuit) Fp VestaG :=
  actionCircuit.toVerifierKey pp (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)

/-- A challenge record carrying only `θ` and `β` — the fields a pre-`x` exclusion set reads. -/
noncomputable def semanticChRecord (theta beta : Fp) {k : ℕ} : Challenges k Fp :=
  chRecord (fun i => if i = 0 then theta else if i = 1 then beta else 0) (fun _ => 0)

@[simp] theorem semanticChRecord_theta (theta beta : Fp) {k : ℕ} :
    (semanticChRecord theta beta (k := k)).theta = theta := rfl

@[simp] theorem semanticChRecord_beta (theta beta : Fp) {k : ℕ} :
    (semanticChRecord theta beta (k := k)).beta = beta := rfl

/-- The run record's challenge at squeeze index `i` is the oracle's answer at the index-`i`
squeeze prefix. -/
theorem straightLineRunRecord_read (basis : AugmentedIndex (2 ^ (pp.mergeDerived
      actionCircuit).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp) (i : Fin 11) :
    wrappedPreIpaReads (straightLineRunOutput family basis O) i =
      O (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) i) :=
  congrFun (straightLineRunReads_eq family basis O) i

/-! ## `θ` (squeeze index 0) -/

/-- **The `θ` failure event is a state surface.**  The `θ` exclusion set reads only the query
columns, which the index-0 view supplies. -/
theorem actionThetaFailureEvent_subset
    (cut : SequentialCut family.toComputedAlgebraicFSFamily 0)
    (view : cut.State → CommitmentId → Polynomial Fp)
    (hview : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ∀ id, id.isColumnInput →
        actionRunPolynomial pp family static inputs hvk hI hchar basis O h id =
          view ((cut.pre basis).run O) id) :
    actionThetaFailureEvent pp family static inputs hvk hI hchar ⊆
      cut.surfaceEvent (fun basis s =>
        ↑(TopLevelLookupCoherence.allTopLevelLookupThetaBadSet actionCircuit pp
          (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) (view s))) := by
  rintro ⟨basis, O⟩ ⟨h, hmem⟩
  dsimp only at hmem
  have hin := not_not.mp hmem
  rw [TopLevelLookupCoherence.allTopLevelLookupThetaBadSet_congr actionCircuit pp
    (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)
    (fun id hid => hview basis O h id hid)] at hin
  have hproj : (straightLineRunRecord family basis O).theta =
      O (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 0) :=
    straightLineRunRecord_read pp family basis O 0
  rw [hproj] at hin
  exact Finset.mem_coe.mpr hin

/-- The `θ` failure probability: `(Q + 1)` times the per-state `θ` set measure. -/
theorem actionThetaFailureEvent_prob_le {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → T)
    (cut : SequentialCut family.toComputedAlgebraicFSFamily 0)
    (view : cut.State → CommitmentId → Polynomial Fp)
    (hview : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ∀ id, id.isColumnInput →
        actionRunPolynomial pp family static inputs hvk hI hchar basis O h id =
          view ((cut.pre basis).run O) id)
    {epsilon : ENNReal}
    (hbad : ∀ (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
      (s : cut.State), (PMF.uniformOfFintype Fp).toOuterMeasure
      ↑(TopLevelLookupCoherence.allTopLevelLookupThetaBadSet actionCircuit pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) (view s)) ≤ epsilon) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype (BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionThetaFailureEvent pp family static inputs hvk hI hchar)
      ≤ (family.Q + 1 : ℕ) * epsilon := by
  refine le_trans (measure_mono (Set.preimage_mono
    (actionThetaFailureEvent_subset pp family static inputs hvk hI hchar cut view hview))) ?_
  exact cut.surfaceEvent_prob_le query _ hbad

/-! ## `β` (squeeze index 1) -/

/-- **The `β` failure event is a state surface.**  The permutation `β` set reads the permutation
input slots; the lookup `β` set reads the lookup input slots and, of the record, only `θ` —
squeezed one index earlier, so the state supplies it. -/
theorem actionBetaFailureEvent_subset
    (cut : SequentialCut family.toComputedAlgebraicFSFamily 1)
    (view : cut.State → CommitmentId → Polynomial Fp)
    (thetaOf : cut.State → Fp)
    (hview : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ∀ id, id.isPermutationInput ∨ id.isLookupInput →
        actionRunPolynomial pp family static inputs hvk hI hchar basis O h id =
          view ((cut.pre basis).run O) id)
    (htheta : ∀ basis O, (straightLineRunRecord family basis O).theta =
      thetaOf ((cut.pre basis).run O)) :
    actionBetaFailureEvent pp family static inputs hvk hI hchar ⊆
      cut.surfaceEvent (fun basis s =>
        ↑(allResolverPermutationBetaBadSet (vkAt pp basis) (view s) actionActiveRows) ∪
        ↑(allResolverLookupBetaBadSet (vkAt pp basis)
          (semanticChRecord (thetaOf s) 0) (view s)
          ((vkAt pp basis).n - (vkAt pp basis).blindingFactors - 2))) := by
  rintro ⟨basis, O⟩ ⟨h, hmem⟩
  dsimp only at hmem
  have hproj : (straightLineRunRecord family basis O).beta =
      O (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 1) :=
    straightLineRunRecord_read pp family basis O 1
  rcases not_and_or.mp hmem with hperm | hlook
  · have hin := not_not.mp hperm
    rw [allResolverPermutationBetaBadSet_congr (vkAt pp basis) actionActiveRows
      (fun id hid => hview basis O h id (Or.inl hid)), hproj] at hin
    exact Set.mem_union_left _ (Finset.mem_coe.mpr hin)
  · have hin := not_not.mp hlook
    rw [allResolverLookupBetaBadSet_congr (vkAt pp basis)
      ((vkAt pp basis).n - (vkAt pp basis).blindingFactors - 2)
      ((htheta basis O).trans (semanticChRecord_theta _ _).symm)
      (fun id hid => hview basis O h id (Or.inr hid)), hproj] at hin
    exact Set.mem_union_right _ (Finset.mem_coe.mpr hin)

/-- The `β` failure probability: `(Q + 1)` times the per-state measure of the union of the two
`β` exclusion sets. -/
theorem actionBetaFailureEvent_prob_le {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → T)
    (cut : SequentialCut family.toComputedAlgebraicFSFamily 1)
    (view : cut.State → CommitmentId → Polynomial Fp)
    (thetaOf : cut.State → Fp)
    (hview : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ∀ id, id.isPermutationInput ∨ id.isLookupInput →
        actionRunPolynomial pp family static inputs hvk hI hchar basis O h id =
          view ((cut.pre basis).run O) id)
    (htheta : ∀ basis O, (straightLineRunRecord family basis O).theta =
      thetaOf ((cut.pre basis).run O))
    {epsilon : ENNReal}
    (hbad : ∀ (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
      (s : cut.State), (PMF.uniformOfFintype Fp).toOuterMeasure
      (↑(allResolverPermutationBetaBadSet (vkAt pp basis) (view s) actionActiveRows) ∪
        ↑(allResolverLookupBetaBadSet (vkAt pp basis)
          (semanticChRecord (thetaOf s) 0) (view s)
          ((vkAt pp basis).n - (vkAt pp basis).blindingFactors - 2))) ≤ epsilon) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype (BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionBetaFailureEvent pp family static inputs hvk hI hchar)
      ≤ (family.Q + 1 : ℕ) * epsilon := by
  refine le_trans (measure_mono (Set.preimage_mono
    (actionBetaFailureEvent_subset pp family static inputs hvk hI hchar
      cut view thetaOf hview htheta))) ?_
  exact cut.surfaceEvent_prob_le query _ hbad

/-! ## `γ` (squeeze index 2) -/

/-- **The `γ` failure event is a state surface.**  Both `γ` sets read their input slots and, of
the record, only `θ` and `β` — squeezed earlier, so the state supplies them. -/
theorem actionGammaFailureEvent_subset
    (cut : SequentialCut family.toComputedAlgebraicFSFamily 2)
    (view : cut.State → CommitmentId → Polynomial Fp)
    (thetaOf betaOf : cut.State → Fp)
    (hview : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ∀ id, id.isPermutationInput ∨ id.isLookupInput →
        actionRunPolynomial pp family static inputs hvk hI hchar basis O h id =
          view ((cut.pre basis).run O) id)
    (htheta : ∀ basis O, (straightLineRunRecord family basis O).theta =
      thetaOf ((cut.pre basis).run O))
    (hbeta : ∀ basis O, (straightLineRunRecord family basis O).beta =
      betaOf ((cut.pre basis).run O)) :
    actionGammaFailureEvent pp family static inputs hvk hI hchar ⊆
      cut.surfaceEvent (fun basis s =>
        ↑(allResolverPermutationGammaBadSet (vkAt pp basis)
          (semanticChRecord (thetaOf s) (betaOf s)) (view s) actionActiveRows) ∪
        ↑(allResolverLookupGammaBadSet (vkAt pp basis)
          (semanticChRecord (thetaOf s) (betaOf s)) (view s)
          ((vkAt pp basis).n - (vkAt pp basis).blindingFactors - 2))) := by
  rintro ⟨basis, O⟩ ⟨h, hmem⟩
  dsimp only at hmem
  have hproj : (straightLineRunRecord family basis O).gamma =
      O (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 2) :=
    straightLineRunRecord_read pp family basis O 2
  rcases not_and_or.mp hmem with hperm | hlook
  · have hin := not_not.mp hperm
    rw [allResolverPermutationGammaBadSet_congr (vkAt pp basis) actionActiveRows
      ((hbeta basis O).trans (semanticChRecord_beta _ _).symm)
      (fun id hid => hview basis O h id (Or.inl hid)), hproj] at hin
    exact Set.mem_union_left _ (Finset.mem_coe.mpr hin)
  · have hin := not_not.mp hlook
    rw [allResolverLookupGammaBadSet_congr (vkAt pp basis)
      ((vkAt pp basis).n - (vkAt pp basis).blindingFactors - 2)
      ((htheta basis O).trans (semanticChRecord_theta _ _).symm)
      ((hbeta basis O).trans (semanticChRecord_beta _ _).symm)
      (fun id hid => hview basis O h id (Or.inr hid)), hproj] at hin
    exact Set.mem_union_right _ (Finset.mem_coe.mpr hin)

/-- The `γ` failure probability: `(Q + 1)` times the per-state measure of the union of the two
`γ` exclusion sets. -/
theorem actionGammaFailureEvent_prob_le {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → T)
    (cut : SequentialCut family.toComputedAlgebraicFSFamily 2)
    (view : cut.State → CommitmentId → Polynomial Fp)
    (thetaOf betaOf : cut.State → Fp)
    (hview : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ∀ id, id.isPermutationInput ∨ id.isLookupInput →
        actionRunPolynomial pp family static inputs hvk hI hchar basis O h id =
          view ((cut.pre basis).run O) id)
    (htheta : ∀ basis O, (straightLineRunRecord family basis O).theta =
      thetaOf ((cut.pre basis).run O))
    (hbeta : ∀ basis O, (straightLineRunRecord family basis O).beta =
      betaOf ((cut.pre basis).run O))
    {epsilon : ENNReal}
    (hbad : ∀ (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
      (s : cut.State), (PMF.uniformOfFintype Fp).toOuterMeasure
      (↑(allResolverPermutationGammaBadSet (vkAt pp basis)
          (semanticChRecord (thetaOf s) (betaOf s)) (view s) actionActiveRows) ∪
        ↑(allResolverLookupGammaBadSet (vkAt pp basis)
          (semanticChRecord (thetaOf s) (betaOf s)) (view s)
          ((vkAt pp basis).n - (vkAt pp basis).blindingFactors - 2))) ≤ epsilon) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype (BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionGammaFailureEvent pp family static inputs hvk hI hchar)
      ≤ (family.Q + 1 : ℕ) * epsilon := by
  refine le_trans (measure_mono (Set.preimage_mono
    (actionGammaFailureEvent_subset pp family static inputs hvk hI hchar
      cut view thetaOf betaOf hview htheta hbeta))) ?_
  exact cut.surfaceEvent_prob_le query _ hbad

/-! ## `x` and `y` (squeeze indices 4 and 3) -/

/-- **The fused `x`/`y` failure event splits into two state surfaces.**  The `y` fold set reads
the accepted model's constraints — every input committed before `y` — and the `x` set reads the
model, `y` itself, and the vanishing commitment, all committed before `x`.  The index-3 and
index-4 views supply them. -/
theorem actionXYFailureEvent_subset
    (cutY : SequentialCut family.toComputedAlgebraicFSFamily 3)
    (cutX : SequentialCut family.toComputedAlgebraicFSFamily 4)
    (modelY : cutY.State → ConstraintPolyModel (pp.mergeDerived actionCircuit).numProofs)
    (modelX : cutX.State → ConstraintPolyModel (pp.mergeDerived actionCircuit).numProofs)
    (yOf : cutX.State → Fp) (vanishingOf : cutX.State → Polynomial Fp)
    (hmodelY : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      actionRunModel pp family static inputs hvk hI hchar basis O h =
        modelY ((cutY.pre basis).run O))
    (hmodelX : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      actionRunModel pp family static inputs hvk hI hchar basis O h =
        modelX ((cutX.pre basis).run O))
    (hy : ∀ basis O, (straightLineRunRecord family basis O).y =
      yOf ((cutX.pre basis).run O))
    (hvanishing : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      actionRunPolynomial pp family static inputs hvk hI hchar basis O h
          CommitmentId.vanishingH =
        vanishingOf ((cutX.pre basis).run O)) :
    actionXYFailureEvent pp family static inputs hvk hI hchar ⊆
      cutX.surfaceEvent (fun basis s =>
        ↑(szBadSet (combineConstraints (modelX s).fixedCols (modelX s).adviceCols
          (modelX s).instanceCols (modelX s).gates (modelX s).sets (modelX s).chunks
          (modelX s).lookups (modelX s).beta (modelX s).gamma (modelX s).delta
          (modelX s).theta (yOf s) (modelX s).chunkLen (modelX s).l0 (modelX s).lLast
          (modelX s).lBlind -
          vanishingOf s * (X ^ (vkAt pp basis).n - 1)))) ∪
      cutY.surfaceEvent (fun basis s =>
        ⋃ j, ↑(szBadSet (foldSplitWitness (modelY s).constraints (vkAt pp basis).n j))) := by
  rintro ⟨basis, O⟩ ⟨h, hmem⟩
  dsimp only at hmem
  have hprojX : (straightLineRunRecord family basis O).x =
      O (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 4) :=
    straightLineRunRecord_read pp family basis O 4
  have hprojY : (straightLineRunRecord family basis O).y =
      O (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 3) :=
    straightLineRunRecord_read pp family basis O 3
  rcases not_and_or.mp hmem with hx | hy'
  · have hin := not_not.mp hx
    rw [hmodelX basis O h, hy basis O, hvanishing basis O h, hprojX] at hin
    exact Set.mem_union_left _ (Finset.mem_coe.mpr hin)
  · rw [not_forall] at hy'
    obtain ⟨j, hj⟩ := hy'
    have hin := not_not.mp hj
    rw [hmodelY basis O h, hprojY] at hin
    exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨j, Finset.mem_coe.mpr hin⟩)

/-- The fused `x`/`y` failure probability: each half pays its own state surface price. -/
theorem actionXYFailureEvent_prob_le {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → T)
    (cutY : SequentialCut family.toComputedAlgebraicFSFamily 3)
    (cutX : SequentialCut family.toComputedAlgebraicFSFamily 4)
    (modelY : cutY.State → ConstraintPolyModel (pp.mergeDerived actionCircuit).numProofs)
    (modelX : cutX.State → ConstraintPolyModel (pp.mergeDerived actionCircuit).numProofs)
    (yOf : cutX.State → Fp) (vanishingOf : cutX.State → Polynomial Fp)
    (hmodelY : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      actionRunModel pp family static inputs hvk hI hchar basis O h =
        modelY ((cutY.pre basis).run O))
    (hmodelX : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      actionRunModel pp family static inputs hvk hI hchar basis O h =
        modelX ((cutX.pre basis).run O))
    (hy : ∀ basis O, (straightLineRunRecord family basis O).y =
      yOf ((cutX.pre basis).run O))
    (hvanishing : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      actionRunPolynomial pp family static inputs hvk hI hchar basis O h
          CommitmentId.vanishingH =
        vanishingOf ((cutX.pre basis).run O))
    {epsilonX epsilonY : ENNReal}
    (hbadX : ∀ (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
      (s : cutX.State), (PMF.uniformOfFintype Fp).toOuterMeasure
      ↑(szBadSet (combineConstraints (modelX s).fixedCols (modelX s).adviceCols
        (modelX s).instanceCols (modelX s).gates (modelX s).sets (modelX s).chunks
        (modelX s).lookups (modelX s).beta (modelX s).gamma (modelX s).delta
        (modelX s).theta (yOf s) (modelX s).chunkLen (modelX s).l0 (modelX s).lLast
        (modelX s).lBlind -
        vanishingOf s * (X ^ (vkAt pp basis).n - 1))) ≤ epsilonX)
    (hbadY : ∀ (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
      (s : cutY.State), (PMF.uniformOfFintype Fp).toOuterMeasure
      (⋃ j, ↑(szBadSet (foldSplitWitness (modelY s).constraints (vkAt pp basis).n j))) ≤
        epsilonY) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype (BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionXYFailureEvent pp family static inputs hvk hI hchar)
      ≤ (family.Q + 1 : ℕ) * epsilonX + (family.Q + 1 : ℕ) * epsilonY := by
  refine le_trans (measure_mono (Set.preimage_mono
    (actionXYFailureEvent_subset pp family static inputs hvk hI hchar cutY cutX
      modelY modelX yOf vanishingOf hmodelY hmodelX hy hvanishing))) ?_
  rw [Set.preimage_union]
  refine le_trans (measure_union_le _ _) (add_le_add ?_ ?_)
  · exact cutX.surfaceEvent_prob_le query _ hbadX
  · exact cutY.surfaceEvent_prob_le query _ hbadY

/-! ## Per-state measures

Each surface's `hbad` premise is a counting statement at one state.  The counts are the staged
remainder's: the row-by-arity budget for `θ`, cell counts for the permutation sets, `(u + 1)`
polynomials of the lookup sets, and `n` times the constraint count for `y`.  The `x` set is one
Schwartz–Zippel exclusion, priced by `uniformChallenge_szBadSet` at its fold degree.
-/

/-- The per-state `θ` measure: the row-by-arity budget over the field size. -/
theorem actionThetaBadSet_measure_le
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (poly : CommitmentId → Polynomial Fp) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
      ↑(TopLevelLookupCoherence.allTopLevelLookupThetaBadSet actionCircuit pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) poly) ≤
      (TopLevelLookupCoherence.topLevelLookupThetaBudget actionCircuit pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) poly : ℝ≥0∞) /
        (Fintype.card Fp : ℝ≥0∞) :=
  TopLevelLookupCoherence.uniformChallenge_allTopLevelLookupThetaBadSet
    TopLevelLookupCoherence.ofTopLevel poly

/-- The per-state `β` measure: permutation cells plus lookup pair counts. -/
theorem actionBetaBadSets_measure_le
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (theta : Fp) (poly : CommitmentId → Polynomial Fp) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
      (↑(allResolverPermutationBetaBadSet (vkAt pp basis) poly actionActiveRows) ∪
        ↑(allResolverLookupBetaBadSet (vkAt pp basis) (semanticChRecord theta 0) poly
          ((vkAt pp basis).n - (vkAt pp basis).blindingFactors - 2))) ≤
      ((∑ p : Fin (pp.mergeDerived actionCircuit).numProofs,
        (Fintype.card (ResolverPermutationCell (vkAt pp basis) poly p actionActiveRows) + 1) *
          Fintype.card (ResolverPermutationCell (vkAt pp basis) poly p actionActiveRows) :
            ℕ) : ℝ≥0∞) / Fintype.card Fp +
      (((pp.mergeDerived actionCircuit).numProofs * (pp.mergeDerived actionCircuit).numLookups *
        (((vkAt pp basis).n - (vkAt pp basis).blindingFactors - 2 + 2) *
            ((vkAt pp basis).n - (vkAt pp basis).blindingFactors - 2 + 1) +
          ((vkAt pp basis).n - (vkAt pp basis).blindingFactors - 2 + 1)) : ℕ) : ℝ≥0∞) /
        Fintype.card Fp :=
  le_trans (measure_union_le _ _)
    (add_le_add
      (allResolverPermutationBetaBadSet_measure_le (vkAt pp basis) poly actionActiveRows)
      (allResolverLookupBetaBadSet_measure_le (vkAt pp basis) (semanticChRecord theta 0) poly
        ((vkAt pp basis).n - (vkAt pp basis).blindingFactors - 2)))

/-- The per-state `γ` measure: doubled permutation cells plus lookup pair counts. -/
theorem actionGammaBadSets_measure_le
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (theta beta : Fp) (poly : CommitmentId → Polynomial Fp) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
      (↑(allResolverPermutationGammaBadSet (vkAt pp basis)
          (semanticChRecord theta beta) poly actionActiveRows) ∪
        ↑(allResolverLookupGammaBadSet (vkAt pp basis) (semanticChRecord theta beta) poly
          ((vkAt pp basis).n - (vkAt pp basis).blindingFactors - 2))) ≤
      ((∑ p : Fin (pp.mergeDerived actionCircuit).numProofs,
        2 * Fintype.card (ResolverPermutationCell (vkAt pp basis) poly p actionActiveRows) :
          ℕ) : ℝ≥0∞) / Fintype.card Fp +
      (((pp.mergeDerived actionCircuit).numProofs * (pp.mergeDerived actionCircuit).numLookups *
        (2 * ((vkAt pp basis).n - (vkAt pp basis).blindingFactors - 2 + 1)) : ℕ) : ℝ≥0∞) /
        Fintype.card Fp :=
  le_trans (measure_union_le _ _)
    (add_le_add
      (allResolverPermutationGammaBadSet_measure_le (vkAt pp basis)
        (semanticChRecord theta beta) poly actionActiveRows)
      (allResolverLookupGammaBadSet_measure_le (vkAt pp basis) (semanticChRecord theta beta)
        poly ((vkAt pp basis).n - (vkAt pp basis).blindingFactors - 2)))

/-- The per-state `y` measure: `n` times the constraint count over the field size. -/
theorem actionYBadSet_measure_le
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (constraints : List (Polynomial Fp)) (hn : (vkAt pp basis).n ≠ 0) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
      (⋃ j, ↑(szBadSet (foldSplitWitness constraints (vkAt pp basis).n j))) ≤
      (((vkAt pp basis).n * constraints.length : ℕ) : ℝ≥0∞) /
        (Fintype.card Fp : ℝ≥0∞) := by
  have hset : (⋃ j, ↑(szBadSet (foldSplitWitness constraints (vkAt pp basis).n j))) =
      {y : Fp | ∃ j, y ∈ szBadSet (foldSplitWitness constraints (vkAt pp basis).n j)} := by
    ext y
    simp [Set.mem_iUnion]
  rw [hset]
  exact goodY_failure_measure_le constraints hn

end ActionTerminal

end Zcash.Snark
