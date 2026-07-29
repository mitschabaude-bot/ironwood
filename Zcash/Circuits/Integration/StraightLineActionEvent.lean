import Zcash.Circuits.Integration.StraightLineActionTerminal
import Zcash.Snark.Soundness.Composition.PrefixedSqueeze

/-!
# The Action bundle statement as a priced straight-line event

`StraightLineActionTerminal` reaches the Action bundle statement from one decoding run, leaving
the challenge exclusions open.  This module prices that gap: the runs where the statement fails
are contained in the compressed constraint failure event plus four per-challenge exclusion
events, so the semantic endpoint bounds the probability that an accepting run carries neither
the bundle statement nor a nontrivial relation.

- `actionStatementDecoded` — the semantic target: the bundle statement or a relation exists.
- `actionXYFailureEvent`, `actionBetaFailureEvent`, `actionGammaFailureEvent`,
  `actionThetaFailureEvent` — a decoding run whose `x`/`y`, `β`, `γ`, or `θ` challenge lands in
  the terminal's exclusion set.  The `x` event is charged here at the terminal's own constraint
  difference rather than aligned with the decode-level difference the compressed event already
  prices: the alignment is a deep pipeline equality, and the extra charge is one more
  per-challenge term.
- `actionSemanticUpgradeContained` — the containment, proved from the terminal bridge.
- `actionBundleStatementFailure_prob_le_of_compressed_bound` — the endpoint, event bounds as
  premises.
- `actionBundleStatementFailure_prob_le_of_surfaces` — the same endpoint with every event bound
  discharged from the squeeze machinery, given prefix-determined covers and per-challenge
  measures.
-/

namespace Zcash.Snark

namespace ActionTerminal

open Halo2 Polynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder)
open scoped ENNReal

local instance vestaInhabitedStraightLineActionEvent : Inhabited VestaG := ⟨0⟩

variable (pp : ProofParams)
  (family : ComputedStraightLineDeployedFSFamily (pp.mergeDerived actionCircuit))
  (static : DeployedConstraintStaticChecks family.toRootFamily)
  (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)

/-- **The semantic target.**  *Either* the Action bundle statement holds *or* a nontrivial
relation over the run's basis is exhibited — the conclusion of the terminal, as a proposition. -/
def actionStatementDecoded :
    (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
    (BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp) → Prop :=
  fun basis _ =>
    Nonempty (BundleStatement inputs ⊕'
      NontrivialRelation (F := Fp)
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis).g
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis).u
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis).w)

variable
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

/-- The accepted constraint model at the run's own decode. -/
noncomputable abbrev actionRunModel
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp)
    (h : family.straightLineConstraintDecoded static basis O) :=
  CanonicalMemberConstraintRelation.acceptedModel
    (memberDecode := fun i hi =>
      (actionRunDecode pp family static basis O inputs (hvk basis) (hI basis) h).toMemberDecode
        (hchar basis O) i hi)
    (hblinding := ActionPermutationDomain.blindingFactors_lt pp
      (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
    (actionRunAccepts pp family static basis O inputs (hvk basis) (hI basis) h)

/-- The accepted member polynomial at the run's own decode. -/
noncomputable abbrev actionRunPolynomial
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp)
    (h : family.straightLineConstraintDecoded static basis O) :=
  CanonicalMemberConstraintRelation.acceptedPolynomial
    (memberDecode := fun i hi =>
      (actionRunDecode pp family static basis O inputs (hvk basis) (hI basis) h).toMemberDecode
        (hchar basis O) i hi)
    (actionRunAccepts pp family static basis O inputs (hvk basis) (hI basis) h)

/-- Decoding runs whose `x` or `y` challenge lands in the terminal's constraint-fold exclusion
sets: `x` in the combined-constraint difference roots, `y` in a fold-split witness. -/
noncomputable def actionXYFailureEvent :
    Set ((AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → Fp)) :=
  {q | ∃ h : family.straightLineConstraintDecoded static q.1 q.2,
    ¬(((straightLineRunRecord family q.1 q.2).x ∉ szBadSet
        (combineConstraints
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).fixedCols
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).adviceCols
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).instanceCols
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).gates
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).sets
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).chunks
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).lookups
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).beta
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).gamma
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).delta
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).theta
          (straightLineRunRecord family q.1 q.2).y
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).chunkLen
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).l0
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).lLast
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).lBlind -
          actionRunPolynomial pp family static inputs hvk hI hchar q.1 q.2 h
              CommitmentId.vanishingH *
            (X ^ (actionCircuit.toVerifierKey pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k q.1)).n - 1))) ∧
      ∀ j, (straightLineRunRecord family q.1 q.2).y ∉ szBadSet
        (foldSplitWitness
          (actionRunModel pp family static inputs hvk hI hchar q.1 q.2 h).constraints
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k q.1)).n j))}

/-- Decoding runs whose `β` challenge lands in a permutation or lookup resolver exclusion set. -/
noncomputable def actionBetaFailureEvent :
    Set ((AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → Fp)) :=
  {q | ∃ h : family.straightLineConstraintDecoded static q.1 q.2,
    ¬(((straightLineRunRecord family q.1 q.2).beta ∉ allResolverPermutationBetaBadSet
        (actionCircuit.toVerifierKey pp
          (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k q.1))
        (actionRunPolynomial pp family static inputs hvk hI hchar q.1 q.2 h)
        actionActiveRows) ∧
      (straightLineRunRecord family q.1 q.2).beta ∉ allResolverLookupBetaBadSet
        (actionCircuit.toVerifierKey pp
          (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k q.1))
        (straightLineRunRecord family q.1 q.2)
        (actionRunPolynomial pp family static inputs hvk hI hchar q.1 q.2 h)
        ((actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k q.1)).n -
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k q.1)).blindingFactors - 2))}

/-- Decoding runs whose `γ` challenge lands in a permutation or lookup resolver exclusion set. -/
noncomputable def actionGammaFailureEvent :
    Set ((AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → Fp)) :=
  {q | ∃ h : family.straightLineConstraintDecoded static q.1 q.2,
    ¬(((straightLineRunRecord family q.1 q.2).gamma ∉ allResolverPermutationGammaBadSet
        (actionCircuit.toVerifierKey pp
          (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k q.1))
        (straightLineRunRecord family q.1 q.2)
        (actionRunPolynomial pp family static inputs hvk hI hchar q.1 q.2 h)
        actionActiveRows) ∧
      (straightLineRunRecord family q.1 q.2).gamma ∉ allResolverLookupGammaBadSet
        (actionCircuit.toVerifierKey pp
          (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k q.1))
        (straightLineRunRecord family q.1 q.2)
        (actionRunPolynomial pp family static inputs hvk hI hchar q.1 q.2 h)
        ((actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k q.1)).n -
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k q.1)).blindingFactors - 2))}

/-- Decoding runs whose `θ` challenge lands in the top-level lookup exclusion set. -/
noncomputable def actionThetaFailureEvent :
    Set ((AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → Fp)) :=
  {q | ∃ h : family.straightLineConstraintDecoded static q.1 q.2,
    ¬((straightLineRunRecord family q.1 q.2).theta ∉
      TopLevelLookupCoherence.allTopLevelLookupThetaBadSet actionCircuit pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k q.1)
        (actionRunPolynomial pp family static inputs hvk hI hchar q.1 q.2 h))}

/-- **The containment behind the fusion.**  A decoding run without the bundle statement or a
relation must have a challenge in one of the terminal's exclusion sets: otherwise the terminal
bridge produces the statement.  Stepped through in the body. -/
theorem actionSemanticUpgradeContained :
    family.StraightLineConstraintSemanticUpgradeContained static
      (actionStatementDecoded pp family inputs)
      (actionXYFailureEvent pp family static inputs hvk hI hchar)
      (actionBetaFailureEvent pp family static inputs hvk hI hchar)
      (actionGammaFailureEvent pp family static inputs hvk hI hchar)
      (actionThetaFailureEvent pp family static inputs hvk hI hchar) := by
  intro q hq
  obtain ⟨hdecoded, hsem⟩ := hq
  by_contra hnot
  simp only [Set.mem_union, not_or] at hnot
  obtain ⟨hXY, hBeta, hGamma, hTheta⟩ := hnot
  -- Non-membership in each event gives the corresponding exclusion at the run's own decode.
  have hxy := not_exists.mp hXY hdecoded
  rw [not_not] at hxy
  have hbeta := not_exists.mp hBeta hdecoded
  rw [not_not] at hbeta
  have hgamma := not_exists.mp hGamma hdecoded
  rw [not_not] at hgamma
  have htheta := not_exists.mp hTheta hdecoded
  rw [not_not] at htheta
  -- The terminal bridge assembles the exclusions into the statement.
  exact hsem ⟨action_bundleStatement_or_relation_of_straightLineDecoded pp family static
    q.1 q.2 inputs (hvk q.1) (hI q.1) hdecoded (hchar q.1 q.2)
    hxy.1 hxy.2 ⟨hgamma.1, hbeta.1⟩ ⟨hgamma.2, hbeta.2, htheta⟩⟩

/-- **The Action bundle statement, priced.**  The probability that an accepting straight-line
run carries neither the bundle statement nor a nontrivial relation is at most the compressed
constraint failure bound plus the four per-challenge exclusion bounds. -/
theorem actionBundleStatementFailure_prob_le_of_compressed_bound
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → T)
    {compressedBound xyBound betaBound gammaBound thetaBound : ENNReal}
    (hcompressed : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintFailureEvent static) ≤ compressedBound)
    (hXY : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionXYFailureEvent pp family static inputs hvk hI hchar) ≤ xyBound)
    (hBeta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionBetaFailureEvent pp family static inputs hvk hI hchar) ≤ betaBound)
    (hGamma : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionGammaFailureEvent pp family static inputs hvk hI hchar) ≤ gammaBound)
    (hTheta : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          actionThetaFailureEvent pp family static inputs hvk hI hchar) ≤ thetaBound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintSemanticFailureEvent
            (actionStatementDecoded pp family inputs))
      ≤ compressedBound + (xyBound + (betaBound + (gammaBound + thetaBound))) :=
  family.straightLineConstraintSemanticFailure_prob_le_of_compressed_bound query static
    (actionStatementDecoded pp family inputs)
    (actionXYFailureEvent pp family static inputs hvk hI hchar)
    (actionBetaFailureEvent pp family static inputs hvk hI hchar)
    (actionGammaFailureEvent pp family static inputs hvk hI hchar)
    (actionThetaFailureEvent pp family static inputs hvk hI hchar)
    (actionSemanticUpgradeContained pp family static inputs hvk hI hchar)
    hcompressed hXY hBeta hGamma hTheta

/-! ## Pricing the events over their squeezes

Each failure event fires on one challenge, and the run reads that challenge from the oracle at
its own squeeze prefix (`straightLineRunReads_eq`).  A caller who covers the run's exclusion set
with a prefix-determined bad-value function embeds the event into the index-generic squeeze
surface, so it costs `(Q + 1)` times a per-challenge measure.  Covering with a prefix-determined
function is a family-level fact — an AGM family's decode is pinned by the transcript prefix —
supplied here as the `hcompat` premises.
-/

/-- The `θ` event embeds into the index-`0` squeeze surface. -/
theorem actionThetaFailureEvent_subset_surface
    (badF : (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) →
      (Fin 0 → Fp) → Set Fp)
    (hcompat : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ↑(TopLevelLookupCoherence.allTopLevelLookupThetaBadSet actionCircuit pp
          (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)
          (actionRunPolynomial pp family static inputs hvk hI hchar basis O h)) ⊆
        badF basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 0)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (0 : Fin 11).isLt))))) :
    actionThetaFailureEvent pp family static inputs hvk hI hchar ⊆
      squeezeSurfaceEvent 0 family.toFamily badF := by
  rintro q ⟨h, hbad⟩
  rw [not_not] at hbad
  have hread : (straightLineRunRecord family q.1 q.2).theta =
      q.2 (algebraicFullPrefixesPre family.init ((family.adversary q.1).run q.2) 0) :=
    congrFun (straightLineRunReads_eq family q.1 q.2) 0
  have hmem := hcompat q.1 q.2 h (Finset.mem_coe.mpr hbad)
  rw [hread] at hmem
  exact hmem

/-- The `β` event embeds into the index-`1` squeeze surface. -/
theorem actionBetaFailureEvent_subset_surface
    (badF : (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) →
      (Fin 1 → Fp) → Set Fp)
    (hcompat : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ↑(allResolverPermutationBetaBadSet
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
          (actionRunPolynomial pp family static inputs hvk hI hchar basis O h)
          actionActiveRows ∪
        allResolverLookupBetaBadSet
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
          (straightLineRunRecord family basis O)
          (actionRunPolynomial pp family static inputs hvk hI hchar basis O h)
          ((actionCircuit.toVerifierKey pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).n -
            (actionCircuit.toVerifierKey pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).blindingFactors
            - 2)) ⊆
        badF basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 1)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (1 : Fin 11).isLt))))) :
    actionBetaFailureEvent pp family static inputs hvk hI hchar ⊆
      squeezeSurfaceEvent 1 family.toFamily badF := by
  rintro q ⟨h, hbad⟩
  rw [not_and_or, not_not, not_not] at hbad
  have hread : (straightLineRunRecord family q.1 q.2).beta =
      q.2 (algebraicFullPrefixesPre family.init ((family.adversary q.1).run q.2) 1) :=
    congrFun (straightLineRunReads_eq family q.1 q.2) 1
  have hmem := hcompat q.1 q.2 h (Finset.mem_coe.mpr (by
    rcases hbad with hperm | hlookup
    · exact Finset.mem_union_left _ hperm
    · exact Finset.mem_union_right _ hlookup))
  rw [hread] at hmem
  exact hmem

/-- The `γ` event embeds into the index-`2` squeeze surface. -/
theorem actionGammaFailureEvent_subset_surface
    (badF : (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) →
      (Fin 2 → Fp) → Set Fp)
    (hcompat : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ↑(allResolverPermutationGammaBadSet
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
          (straightLineRunRecord family basis O)
          (actionRunPolynomial pp family static inputs hvk hI hchar basis O h)
          actionActiveRows ∪
        allResolverLookupGammaBadSet
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
          (straightLineRunRecord family basis O)
          (actionRunPolynomial pp family static inputs hvk hI hchar basis O h)
          ((actionCircuit.toVerifierKey pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).n -
            (actionCircuit.toVerifierKey pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).blindingFactors
            - 2)) ⊆
        badF basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 2)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (2 : Fin 11).isLt))))) :
    actionGammaFailureEvent pp family static inputs hvk hI hchar ⊆
      squeezeSurfaceEvent 2 family.toFamily badF := by
  rintro q ⟨h, hbad⟩
  rw [not_and_or, not_not, not_not] at hbad
  have hread : (straightLineRunRecord family q.1 q.2).gamma =
      q.2 (algebraicFullPrefixesPre family.init ((family.adversary q.1).run q.2) 2) :=
    congrFun (straightLineRunReads_eq family q.1 q.2) 2
  have hmem := hcompat q.1 q.2 h (Finset.mem_coe.mpr (by
    rcases hbad with hperm | hlookup
    · exact Finset.mem_union_left _ hperm
    · exact Finset.mem_union_right _ hlookup))
  rw [hread] at hmem
  exact hmem

/-- The `x`/`y` event embeds into the union of the index-`4` and index-`3` squeeze surfaces. -/
theorem actionXYFailureEvent_subset_surfaces
    (badFX : (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) →
      (Fin 4 → Fp) → Set Fp)
    (badFY : (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) →
      (Fin 3 → Fp) → Set Fp)
    (hcompatX : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ↑(szBadSet
        (combineConstraints
          (actionRunModel pp family static inputs hvk hI hchar basis O h).fixedCols
          (actionRunModel pp family static inputs hvk hI hchar basis O h).adviceCols
          (actionRunModel pp family static inputs hvk hI hchar basis O h).instanceCols
          (actionRunModel pp family static inputs hvk hI hchar basis O h).gates
          (actionRunModel pp family static inputs hvk hI hchar basis O h).sets
          (actionRunModel pp family static inputs hvk hI hchar basis O h).chunks
          (actionRunModel pp family static inputs hvk hI hchar basis O h).lookups
          (actionRunModel pp family static inputs hvk hI hchar basis O h).beta
          (actionRunModel pp family static inputs hvk hI hchar basis O h).gamma
          (actionRunModel pp family static inputs hvk hI hchar basis O h).delta
          (actionRunModel pp family static inputs hvk hI hchar basis O h).theta
          (straightLineRunRecord family basis O).y
          (actionRunModel pp family static inputs hvk hI hchar basis O h).chunkLen
          (actionRunModel pp family static inputs hvk hI hchar basis O h).l0
          (actionRunModel pp family static inputs hvk hI hchar basis O h).lLast
          (actionRunModel pp family static inputs hvk hI hchar basis O h).lBlind -
          actionRunPolynomial pp family static inputs hvk hI hchar basis O h
              CommitmentId.vanishingH *
            (X ^ (actionCircuit.toVerifierKey pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).n - 1))) ⊆
        badFX basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 4)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (4 : Fin 11).isLt)))))
    (hcompatY : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      {v : Fp | ∃ j, v ∈ szBadSet
        (foldSplitWitness
          (actionRunModel pp family static inputs hvk hI hchar basis O h).constraints
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).n j)} ⊆
        badFY basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 3)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (3 : Fin 11).isLt))))) :
    actionXYFailureEvent pp family static inputs hvk hI hchar ⊆
      squeezeSurfaceEvent 4 family.toFamily badFX ∪
        squeezeSurfaceEvent 3 family.toFamily badFY := by
  rintro q ⟨h, hbad⟩
  rw [not_and_or, not_not] at hbad
  rcases hbad with hx | hy
  · have hread : (straightLineRunRecord family q.1 q.2).x =
        q.2 (algebraicFullPrefixesPre family.init ((family.adversary q.1).run q.2) 4) :=
      congrFun (straightLineRunReads_eq family q.1 q.2) 4
    have hmem := hcompatX q.1 q.2 h (Finset.mem_coe.mpr hx)
    rw [hread] at hmem
    exact Set.mem_union_left _ hmem
  · rw [not_forall] at hy
    obtain ⟨j, hj⟩ := hy
    rw [not_not] at hj
    have hread : (straightLineRunRecord family q.1 q.2).y =
        q.2 (algebraicFullPrefixesPre family.init ((family.adversary q.1).run q.2) 3) :=
      congrFun (straightLineRunReads_eq family q.1 q.2) 3
    have hmem := hcompatY q.1 q.2 h ⟨j, hj⟩
    rw [hread] at hmem
    exact Set.mem_union_right _ hmem

/-- **The surface-form fusion.**  Every event bound is discharged from the squeeze machinery:
the caller supplies a prefix-determined cover for each exclusion set, prefix-determinism at the
five squeeze indices, and a per-challenge measure apiece, and the bundle-statement failure
probability is

`compressed + (Q+1)·(εx + εy) + (Q+1)·εβ + (Q+1)·εγ + (Q+1)·εθ`. -/
theorem actionBundleStatementFailure_prob_le_of_surfaces
    {T : Type*} [DecidableEq T]
    (query : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → T)
    (badFX : (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → (Fin 4 → Fp) → Set Fp)
    (badFY : (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → (Fin 3 → Fp) → Set Fp)
    (badFBeta : (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → (Fin 1 → Fp) → Set Fp)
    (badFGamma : (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → (Fin 2 → Fp) → Set Fp)
    (badFTheta : (AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG) →
      BTranscript Fp VestaG
        (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
          + 3 * (pp.mergeDerived actionCircuit).k) → (Fin 0 → Fp) → Set Fp)
    (hcompatX : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ↑(szBadSet
        (combineConstraints
          (actionRunModel pp family static inputs hvk hI hchar basis O h).fixedCols
          (actionRunModel pp family static inputs hvk hI hchar basis O h).adviceCols
          (actionRunModel pp family static inputs hvk hI hchar basis O h).instanceCols
          (actionRunModel pp family static inputs hvk hI hchar basis O h).gates
          (actionRunModel pp family static inputs hvk hI hchar basis O h).sets
          (actionRunModel pp family static inputs hvk hI hchar basis O h).chunks
          (actionRunModel pp family static inputs hvk hI hchar basis O h).lookups
          (actionRunModel pp family static inputs hvk hI hchar basis O h).beta
          (actionRunModel pp family static inputs hvk hI hchar basis O h).gamma
          (actionRunModel pp family static inputs hvk hI hchar basis O h).delta
          (actionRunModel pp family static inputs hvk hI hchar basis O h).theta
          (straightLineRunRecord family basis O).y
          (actionRunModel pp family static inputs hvk hI hchar basis O h).chunkLen
          (actionRunModel pp family static inputs hvk hI hchar basis O h).l0
          (actionRunModel pp family static inputs hvk hI hchar basis O h).lLast
          (actionRunModel pp family static inputs hvk hI hchar basis O h).lBlind -
          actionRunPolynomial pp family static inputs hvk hI hchar basis O h
              CommitmentId.vanishingH *
            (X ^ (actionCircuit.toVerifierKey pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).n - 1))) ⊆
        badFX basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 4)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (4 : Fin 11).isLt)))))
    (hcompatY : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      {v : Fp | ∃ j, v ∈ szBadSet
        (foldSplitWitness
          (actionRunModel pp family static inputs hvk hI hchar basis O h).constraints
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).n j)} ⊆
        badFY basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 3)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (3 : Fin 11).isLt)))))
    (hcompatBeta : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ↑(allResolverPermutationBetaBadSet
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
          (actionRunPolynomial pp family static inputs hvk hI hchar basis O h)
          actionActiveRows ∪
        allResolverLookupBetaBadSet
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
          (straightLineRunRecord family basis O)
          (actionRunPolynomial pp family static inputs hvk hI hchar basis O h)
          ((actionCircuit.toVerifierKey pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).n -
            (actionCircuit.toVerifierKey pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).blindingFactors
            - 2)) ⊆
        badFBeta basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 1)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (1 : Fin 11).isLt)))))
    (hcompatGamma : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ↑(allResolverPermutationGammaBadSet
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
          (straightLineRunRecord family basis O)
          (actionRunPolynomial pp family static inputs hvk hI hchar basis O h)
          actionActiveRows ∪
        allResolverLookupGammaBadSet
          (actionCircuit.toVerifierKey pp
            (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
          (straightLineRunRecord family basis O)
          (actionRunPolynomial pp family static inputs hvk hI hchar basis O h)
          ((actionCircuit.toVerifierKey pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).n -
            (actionCircuit.toVerifierKey pp
              (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)).blindingFactors
            - 2)) ⊆
        badFGamma basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 2)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (2 : Fin 11).isLt)))))
    (hcompatTheta : ∀ basis O (h : family.straightLineConstraintDecoded static basis O),
      ↑(TopLevelLookupCoherence.allTopLevelLookupThetaBadSet actionCircuit pp
          (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis)
          (actionRunPolynomial pp family static inputs hvk hI hchar basis O h)) ⊆
        badFTheta basis (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 0)
          (fun i => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt (0 : Fin 11).isLt)))))
    (hdetX : PrefixDeterminedAt family.toFamily 4)
    (hdetY : PrefixDeterminedAt family.toFamily 3)
    (hdetBeta : PrefixDeterminedAt family.toFamily 1)
    (hdetGamma : PrefixDeterminedAt family.toFamily 2)
    (hdetTheta : PrefixDeterminedAt family.toFamily 0)
    {compressedBound epsX epsY epsBeta epsGamma epsTheta : ENNReal}
    (hcompressed : (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintFailureEvent static) ≤ compressedBound)
    (hbadX : ∀ basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badFX basis t nu) ≤ epsX)
    (hbadY : ∀ basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badFY basis t nu) ≤ epsY)
    (hbadBeta : ∀ basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badFBeta basis t nu) ≤ epsBeta)
    (hbadGamma : ∀ basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badFGamma basis t nu) ≤ epsGamma)
    (hbadTheta : ∀ basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badFTheta basis t nu) ≤ epsTheta) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype
        (BTranscript Fp VestaG
          (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
            + 3 * (pp.mergeDerived actionCircuit).k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          family.straightLineConstraintSemanticFailureEvent
            (actionStatementDecoded pp family inputs))
      ≤ compressedBound +
          (((family.Q + 1 : ℕ) * epsX + (family.Q + 1 : ℕ) * epsY) +
            ((family.Q + 1 : ℕ) * epsBeta +
              ((family.Q + 1 : ℕ) * epsGamma + (family.Q + 1 : ℕ) * epsTheta))) := by
  refine actionBundleStatementFailure_prob_le_of_compressed_bound pp family static inputs
    hvk hI hchar query hcompressed ?_ ?_ ?_ ?_
  · calc (independentProductPMF (orchardGeneratorROSetup query)
        (PMF.uniformOfFintype _)).toOuterMeasure
          ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
            actionXYFailureEvent pp family static inputs hvk hI hchar)
        ≤ (independentProductPMF (orchardGeneratorROSetup query)
          (PMF.uniformOfFintype _)).toOuterMeasure
            (((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
              squeezeSurfaceEvent 4 family.toFamily badFX) ∪
              ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
                squeezeSurfaceEvent 3 family.toFamily badFY)) := by
          refine MeasureTheory.measure_mono ?_
          rw [← Set.preimage_union]
          exact Set.preimage_mono
            (actionXYFailureEvent_subset_surfaces pp family static inputs hvk hI hchar
              badFX badFY hcompatX hcompatY)
      _ ≤ (family.Q + 1 : ℕ) * epsX + (family.Q + 1 : ℕ) * epsY :=
          (MeasureTheory.measure_union_le _ _).trans (add_le_add
            (squeezeSurfaceEvent_prob_le 4 query family.toFamily badFX
              (hstab_of_prefixDeterminedAt family.toFamily 4 hdetX) hbadX)
            (squeezeSurfaceEvent_prob_le 3 query family.toFamily badFY
              (hstab_of_prefixDeterminedAt family.toFamily 3 hdetY) hbadY))
  · exact le_trans
      (MeasureTheory.measure_mono (Set.preimage_mono
        (actionBetaFailureEvent_subset_surface pp family static inputs hvk hI hchar
          badFBeta hcompatBeta)))
      (squeezeSurfaceEvent_prob_le 1 query family.toFamily badFBeta
        (hstab_of_prefixDeterminedAt family.toFamily 1 hdetBeta) hbadBeta)
  · exact le_trans
      (MeasureTheory.measure_mono (Set.preimage_mono
        (actionGammaFailureEvent_subset_surface pp family static inputs hvk hI hchar
          badFGamma hcompatGamma)))
      (squeezeSurfaceEvent_prob_le 2 query family.toFamily badFGamma
        (hstab_of_prefixDeterminedAt family.toFamily 2 hdetGamma) hbadGamma)
  · exact le_trans
      (MeasureTheory.measure_mono (Set.preimage_mono
        (actionThetaFailureEvent_subset_surface pp family static inputs hvk hI hchar
          badFTheta hcompatTheta)))
      (squeezeSurfaceEvent_prob_le 0 query family.toFamily badFTheta
        (hstab_of_prefixDeterminedAt family.toFamily 0 hdetTheta) hbadTheta)

end ActionTerminal

end Zcash.Snark
