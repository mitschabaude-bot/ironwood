import Zcash.Snark.Soundness.ActionVesta
import Zcash.Circuits.Integration.ActionTerminal
import Zcash.Snark.Keygen.Certificate
import Zcash.Snark.Keygen.InstanceCapture
import Zcash.Snark.Soundness.Canonical.Vesta
import Zcash.Snark.Soundness.Multiopen.CanonicalSelection

/-!
# Deployed Action soundness capstone

This module is the Action-specific deployed capstone of the Vesta
constraint-soundness bridge, stated at the captured fixture artifacts: the
captured verifying key `Fixture.vk`, the fixture `shape`, the captured URS, and
the deployed instance commitment. It is the generic Action/Vesta capstone
`action_bundleStatement_or_relation_of_deployedAccepts` transported to those
artifacts along the keygen certificate equalities (`shape_eq_mergeDerived`,
`vk_eq_derived`).

The capstone has no free proposition, encoding callback, or member decoder. Its
circuit model and decoder are both determined by deployed acceptance.

Like its generic parent this is the **rewind-based** route, and it additionally pays the `x₁`
accept-measure premises.  `Circuits.Integration.StraightLineActionTerminal` reaches the same
conclusion from a represented decode with no rewind and no accept measure; the two are retained
side by side because their assumption sets differ.

The transport ingredients are local: the fixture `k`-match and blinding-factor
side conditions. The public-instance commitment is the generic circuit-derived
`actionCircuit.instanceCommitment actionProofParams capturedURS`, used directly
at both the circuit-derived and captured fixture shapes.
-/

namespace Zcash.Snark

open Polynomial
open Classical
open scoped ENNReal
open Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Snark.Fixture

/-- The captured `Shape`'s IPA depth matches the captured URS: both record the
literal deployed `k = 11`. -/
theorem shape_k_eq_capturedURS_k : Fixture.shape.k = capturedURS.k := rfl

set_option maxRecDepth 100000 in
/-- The deployed verifying key's blinding factors are below its domain size
(`5 < 2048` on the captured record). -/
theorem vk_blindingFactors_lt : Fixture.vk.blindingFactors < Fixture.vk.n := by
  decide

namespace Deployed

set_option maxRecDepth 1000000 in
/--
Transport of the generic Action/Vesta capstone to a shape/key pair identified
with the captured circuit-derived artifacts. `subst` on the certificate
equalities `shape_eq_mergeDerived` and `vk_eq_derived` reduces the goal to the
generic capstone at `(actionProofParams, capturedURS)`; both equalities are
ordinary `Eq`s, so no cast appears in the statement or proof.
-/
private noncomputable def action_bundleStatement_or_relation_of_deployedAccepts_transport
    (s : Shape)
    (hs : actionProofParams.mergeDerived actionCircuit = s)
    (K : VerifyingKey s Fp G)
    (hK : K = derivedActionVk s capturedURS)
    (hk : s.k = capturedURS.k)
    (hbl : K.blindingFactors < K.n)
    (inputs : Fin s.numProofs → PublicInputs Fp)
    (ps : ProofString s Fp G)
    (ch : Challenges s.k Fp)
    (pU pW : Fp)
    (hpoly : Polynomial Fp)
    {a₀ : Fin (2 ^ capturedURS.k) → Fp}
    (pbatch :
      OpenedBatchOpenings capturedURS (evalVector capturedURS.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := actionCircuit.instanceCommitment actionProofParams capturedURS inputs)
          capturedURS hk K ps ch)
        (x4BatchEvals
          (instanceCommitment := actionCircuit.instanceCommitment actionProofParams capturedURS inputs)
          K ps ch)
        a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount K
        (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch →
      0 < (deployedSetQueries K
        (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount K
        (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch →
      (((deployedSetQueries K
          (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch i).length - 1 :
          ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure
          (Finset.univ.filter
            (OpenedX1Accept capturedURS hk K
              (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch)))
    (haccepts :
      DeployedAccepts capturedURS hk K
        (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch)
    (i m : ℕ)
    (hm : m < (deployedSetQueries K
      (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch i).length)
    (colPoly : Fin (deployedSetQueries K
      (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch i).length →
        Polynomial Fp)
    (hbindAll : ∀ (idx : Fin ((constructIntermediateSets
          (assembleQueries K
            (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch)).points.getD
              i []).length)
        (m₀ : Fin (deployedSetQueries K
          (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch i).length),
      (colPoly m₀).eval
          (((constructIntermediateSets
            (assembleQueries K
              (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch)).points.getD
                i [])[idx]) =
        ((deployedSetQueries K
          (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch i).getD
            (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0 ⊕'
        NontrivialRelation (F := Fp)
          capturedURS.g capturedURS.u capturedURS.w)
    (hquot : hpoly = colPoly ⟨m, hm⟩)
    (hroute : (constructIntermediateSets
      (assembleQueries K
        (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch)).points.getD
          i [] = [ch.x])
    (hevals : ∀ d₀,
      ((deployedSetQueries K
        (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch i).getD
          m d₀).2 =
        [expectedHEval
          (allExpressions K ps ch
            (lagrangeBasis K.omega K.n
              K.blindingFactors (ch.x ^ K.n) ch.x).1
            (lagrangeBasis K.omega K.n
              K.blindingFactors
              (ch.x ^ K.n) ch.x).2.1
            (lagrangeBasis K.omega K.n
              K.blindingFactors
              (ch.x ^ K.n) ch.x).2.2)
          ch.y (ch.x ^ K.n)])
    (claimed :
      AcceptedModelClaimedEvaluations
        (memberDecode :=
          vestaExtractedMemberDecode capturedURS hk
            K (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch
            pbatch hlen hprob1 haccepts)
        (hblinding := hbl) haccepts)
    (hxgood :
      ch.x ∉ szBadSet
        (let model :=
          CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode :=
              vestaExtractedMemberDecode capturedURS hk
                K (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch
                pbatch hlen hprob1 haccepts)
            (hblinding := hbl) haccepts
        combineConstraints model.fixedCols model.adviceCols model.instanceCols
          model.gates model.sets model.chunks model.lookups
          model.beta model.gamma model.delta model.theta ch.y model.chunkLen
          model.l0 model.lLast model.lBlind -
            hpoly * (X ^ K.n - 1)))
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode :=
              vestaExtractedMemberDecode capturedURS hk
                K (actionCircuit.instanceCommitment actionProofParams capturedURS inputs)
                ps ch pbatch hlen hprob1 haccepts)
            (hblinding := hbl) haccepts).constraints
          K.n j))
    (permGamma :
      ch.gamma ∉ allResolverPermutationGammaBadSet K ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS hk
              K (actionCircuit.instanceCommitment actionProofParams capturedURS inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        actionActiveRows)
    (permBeta :
      ch.beta ∉ allResolverPermutationBetaBadSet K
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS hk
              K (actionCircuit.instanceCommitment actionProofParams capturedURS inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        actionActiveRows)
    (lookupGamma :
      ch.gamma ∉ allResolverLookupGammaBadSet K ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS hk
              K (actionCircuit.instanceCommitment actionProofParams capturedURS inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        (K.n - K.blindingFactors - 2))
    (lookupBeta :
      ch.beta ∉ allResolverLookupBetaBadSet K ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS hk
              K (actionCircuit.instanceCommitment actionProofParams capturedURS inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        (K.n - K.blindingFactors - 2))
    (lookupTheta :
      ch.theta ∉ TopLevelLookupCoherence.allTopLevelLookupThetaBadSet
        actionCircuit actionProofParams capturedURS
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS hk
              K (actionCircuit.instanceCommitment actionProofParams capturedURS inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)) :
    BundleStatement inputs ⊕'
      NontrivialRelation (F := Fp)
        capturedURS.g capturedURS.u capturedURS.w := by
  subst hs
  rw [← Keygen.toVerifierKey_action actionProofParams capturedURS] at hK
  subst hK
  exact
    action_bundleStatement_or_relation_of_deployedAccepts
      actionProofParams capturedURS hk inputs ps ch pU pW hpoly (a₀ := a₀)
      pbatch hξcur hlen hprob1 haccepts i m hm colPoly hbindAll hquot
      hroute hevals claimed hxgood hgoodY ⟨permGamma, permBeta⟩
      ⟨lookupGamma, lookupBeta, lookupTheta⟩

attribute [local irreducible] deployedSetQueries deployedSetCommIds
  deployedX4PairCount x4BatchCommitments x4BatchEvals
  Fixture.vk Fixture.shape capturedURS
  Halo2.TopLevelCircuit.instanceCommitment

set_option maxRecDepth 1000000 in
/--
The deployed Action soundness capstone at the captured fixture, obtained by
transporting the generic Action/Vesta capstone to the deployed artifacts.

This capstone exposes no arbitrary proposition `S`, no encoding callback, and no
freely chosen member decoder. Deployed acceptance determines the decoder and
canonical constraint model; the accepted route determines the advice and
instance member selections.
-/
noncomputable def action_bundleStatement_or_relation_of_deployedAccepts
    (inputs : Fin Fixture.shape.numProofs → PublicInputs Fp)
    (ps : ProofString Fixture.shape Fp Fixture.G)
    (ch : Challenges Fixture.shape.k Fp)
    (pU pW : Fp)
    (hpoly : Polynomial Fp)
    {a₀ : Fin (2 ^ capturedURS.k) → Fp}
    (pbatch :
      OpenedBatchOpenings capturedURS (evalVector capturedURS.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := actionCircuit.instanceCommitment actionProofParams capturedURS inputs)
          capturedURS shape_k_eq_capturedURS_k Fixture.vk ps ch)
        (x4BatchEvals
          (instanceCommitment := actionCircuit.instanceCommitment actionProofParams capturedURS inputs)
          Fixture.vk ps ch)
        a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount Fixture.vk
        (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch →
      0 < (deployedSetQueries Fixture.vk
        (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount Fixture.vk
        (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch →
      (((deployedSetQueries Fixture.vk
          (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch i).length - 1 :
          ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure
          (Finset.univ.filter
            (OpenedX1Accept capturedURS shape_k_eq_capturedURS_k Fixture.vk
              (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch)))
    (haccepts :
      DeployedAccepts capturedURS shape_k_eq_capturedURS_k Fixture.vk
        (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch)
    (i m : ℕ)
    (hm : m < (deployedSetQueries Fixture.vk
      (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch i).length)
    (colPoly : Fin (deployedSetQueries Fixture.vk
      (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch i).length →
        Polynomial Fp)
    (hbindAll : ∀ (idx : Fin ((constructIntermediateSets
          (assembleQueries Fixture.vk
            (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch)).points.getD
              i []).length)
        (m₀ : Fin (deployedSetQueries Fixture.vk
          (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch i).length),
      (colPoly m₀).eval
          (((constructIntermediateSets
            (assembleQueries Fixture.vk
              (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch)).points.getD
                i [])[idx]) =
        ((deployedSetQueries Fixture.vk
          (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch i).getD
            (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0 ⊕'
        NontrivialRelation (F := Fp)
          capturedURS.g capturedURS.u capturedURS.w)
    (hquot : hpoly = colPoly ⟨m, hm⟩)
    (hroute : (constructIntermediateSets
      (assembleQueries Fixture.vk
        (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch)).points.getD
          i [] = [ch.x])
    (hevals : ∀ d₀,
      ((deployedSetQueries Fixture.vk
        (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch i).getD
          m d₀).2 =
        [expectedHEval
          (allExpressions Fixture.vk ps ch
            (lagrangeBasis Fixture.vk.omega Fixture.vk.n
              Fixture.vk.blindingFactors (ch.x ^ Fixture.vk.n) ch.x).1
            (lagrangeBasis Fixture.vk.omega Fixture.vk.n
              Fixture.vk.blindingFactors
              (ch.x ^ Fixture.vk.n) ch.x).2.1
            (lagrangeBasis Fixture.vk.omega Fixture.vk.n
              Fixture.vk.blindingFactors
              (ch.x ^ Fixture.vk.n) ch.x).2.2)
          ch.y (ch.x ^ Fixture.vk.n)])
    (claimed :
      AcceptedModelClaimedEvaluations
        (memberDecode :=
          vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
            Fixture.vk (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch
            pbatch hlen hprob1 haccepts)
        (hblinding := vk_blindingFactors_lt) haccepts)
    (hxgood :
      ch.x ∉ szBadSet
        (let model :=
          CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode :=
              vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
                Fixture.vk (actionCircuit.instanceCommitment actionProofParams capturedURS inputs) ps ch
                pbatch hlen hprob1 haccepts)
            (hblinding := vk_blindingFactors_lt) haccepts
        combineConstraints model.fixedCols model.adviceCols model.instanceCols
          model.gates model.sets model.chunks model.lookups
          model.beta model.gamma model.delta model.theta ch.y model.chunkLen
          model.l0 model.lLast model.lBlind -
            hpoly * (X ^ Fixture.vk.n - 1)))
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode :=
              vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
                Fixture.vk (actionCircuit.instanceCommitment actionProofParams capturedURS inputs)
                ps ch pbatch hlen hprob1 haccepts)
            (hblinding := vk_blindingFactors_lt) haccepts).constraints
          Fixture.vk.n j))
    (permGamma :
      ch.gamma ∉ allResolverPermutationGammaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (actionCircuit.instanceCommitment actionProofParams capturedURS inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        actionActiveRows)
    (permBeta :
      ch.beta ∉ allResolverPermutationBetaBadSet Fixture.vk
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (actionCircuit.instanceCommitment actionProofParams capturedURS inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        actionActiveRows)
    (lookupGamma :
      ch.gamma ∉ allResolverLookupGammaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (actionCircuit.instanceCommitment actionProofParams capturedURS inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        (Fixture.vk.n - Fixture.vk.blindingFactors - 2))
    (lookupBeta :
      ch.beta ∉ allResolverLookupBetaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (actionCircuit.instanceCommitment actionProofParams capturedURS inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        (Fixture.vk.n - Fixture.vk.blindingFactors - 2))
    (lookupTheta :
      ch.theta ∉ TopLevelLookupCoherence.allTopLevelLookupThetaBadSet
        actionCircuit actionProofParams capturedURS
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (actionCircuit.instanceCommitment actionProofParams capturedURS inputs)
              ps ch pbatch hlen hprob1 haccepts) haccepts)) :
    BundleStatement inputs ⊕'
      NontrivialRelation (F := Fp)
        capturedURS.g capturedURS.u capturedURS.w :=
  action_bundleStatement_or_relation_of_deployedAccepts_transport
    Fixture.shape Keygen.shape_eq_mergeDerived
    Fixture.vk Keygen.vk_eq_derived
    shape_k_eq_capturedURS_k vk_blindingFactors_lt
    inputs ps ch pU pW hpoly pbatch hξcur hlen hprob1 haccepts
    i m hm colPoly hbindAll hquot hroute hevals claimed hxgood hgoodY
    permGamma permBeta lookupGamma lookupBeta lookupTheta

assert_no_sorry action_bundleStatement_or_relation_of_deployedAccepts

set_option maxRecDepth 1000000 in
/--
**The deployed Action capstone over an abstract instance-commitment family.**

Identical to `action_bundleStatement_or_relation_of_deployedAccepts`, except that the
public-instance commitments are a supplied family `icf` together with the equation `hicf`
identifying it with the circuit-derived one. Callers holding a *differently spelled* family —
the fixture's `Fixture.derivedInstanceCommitment`, say — can then state acceptance and the
challenge exclusions in their own vocabulary instead of the circuit's.

The generalization is free: `hicf` is substituted away, so this is the same theorem.
-/
noncomputable def action_bundleStatement_or_relation_of_deployedAccepts_family
    (inputs : Fin Fixture.shape.numProofs → PublicInputs Fp)
    (icf : Fin Fixture.shape.numProofs → ℕ → Fixture.G)
    (hicf : icf = actionCircuit.instanceCommitment actionProofParams capturedURS inputs)
    (ps : ProofString Fixture.shape Fp Fixture.G)
    (ch : Challenges Fixture.shape.k Fp)
    (pU pW : Fp)
    (hpoly : Polynomial Fp)
    {a₀ : Fin (2 ^ capturedURS.k) → Fp}
    (pbatch :
      OpenedBatchOpenings capturedURS (evalVector capturedURS.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := icf)
          capturedURS shape_k_eq_capturedURS_k Fixture.vk ps ch)
        (x4BatchEvals
          (instanceCommitment := icf)
          Fixture.vk ps ch)
        a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount Fixture.vk
        (icf) ps ch →
      0 < (deployedSetQueries Fixture.vk
        (icf) ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount Fixture.vk
        (icf) ps ch →
      (((deployedSetQueries Fixture.vk
          (icf) ps ch i).length - 1 :
          ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure
          (Finset.univ.filter
            (OpenedX1Accept capturedURS shape_k_eq_capturedURS_k Fixture.vk
              (icf) ps ch)))
    (haccepts :
      DeployedAccepts capturedURS shape_k_eq_capturedURS_k Fixture.vk
        (icf) ps ch)
    (i m : ℕ)
    (hm : m < (deployedSetQueries Fixture.vk
      (icf) ps ch i).length)
    (colPoly : Fin (deployedSetQueries Fixture.vk
      (icf) ps ch i).length →
        Polynomial Fp)
    (hbindAll : ∀ (idx : Fin ((constructIntermediateSets
          (assembleQueries Fixture.vk
            (icf) ps ch)).points.getD
              i []).length)
        (m₀ : Fin (deployedSetQueries Fixture.vk
          (icf) ps ch i).length),
      (colPoly m₀).eval
          (((constructIntermediateSets
            (assembleQueries Fixture.vk
              (icf) ps ch)).points.getD
                i [])[idx]) =
        ((deployedSetQueries Fixture.vk
          (icf) ps ch i).getD
            (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0 ⊕'
        NontrivialRelation (F := Fp)
          capturedURS.g capturedURS.u capturedURS.w)
    (hquot : hpoly = colPoly ⟨m, hm⟩)
    (hroute : (constructIntermediateSets
      (assembleQueries Fixture.vk
        (icf) ps ch)).points.getD
          i [] = [ch.x])
    (hevals : ∀ d₀,
      ((deployedSetQueries Fixture.vk
        (icf) ps ch i).getD
          m d₀).2 =
        [expectedHEval
          (allExpressions Fixture.vk ps ch
            (lagrangeBasis Fixture.vk.omega Fixture.vk.n
              Fixture.vk.blindingFactors (ch.x ^ Fixture.vk.n) ch.x).1
            (lagrangeBasis Fixture.vk.omega Fixture.vk.n
              Fixture.vk.blindingFactors
              (ch.x ^ Fixture.vk.n) ch.x).2.1
            (lagrangeBasis Fixture.vk.omega Fixture.vk.n
              Fixture.vk.blindingFactors
              (ch.x ^ Fixture.vk.n) ch.x).2.2)
          ch.y (ch.x ^ Fixture.vk.n)])
    (claimed :
      AcceptedModelClaimedEvaluations
        (memberDecode :=
          vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
            Fixture.vk (icf) ps ch
            pbatch hlen hprob1 haccepts)
        (hblinding := vk_blindingFactors_lt) haccepts)
    (hxgood :
      ch.x ∉ szBadSet
        (let model :=
          CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode :=
              vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
                Fixture.vk (icf) ps ch
                pbatch hlen hprob1 haccepts)
            (hblinding := vk_blindingFactors_lt) haccepts
        combineConstraints model.fixedCols model.adviceCols model.instanceCols
          model.gates model.sets model.chunks model.lookups
          model.beta model.gamma model.delta model.theta ch.y model.chunkLen
          model.l0 model.lLast model.lBlind -
            hpoly * (X ^ Fixture.vk.n - 1)))
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode :=
              vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
                Fixture.vk (icf)
                ps ch pbatch hlen hprob1 haccepts)
            (hblinding := vk_blindingFactors_lt) haccepts).constraints
          Fixture.vk.n j))
    (permGamma :
      ch.gamma ∉ allResolverPermutationGammaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (icf)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        actionActiveRows)
    (permBeta :
      ch.beta ∉ allResolverPermutationBetaBadSet Fixture.vk
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (icf)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        actionActiveRows)
    (lookupGamma :
      ch.gamma ∉ allResolverLookupGammaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (icf)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        (Fixture.vk.n - Fixture.vk.blindingFactors - 2))
    (lookupBeta :
      ch.beta ∉ allResolverLookupBetaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (icf)
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        (Fixture.vk.n - Fixture.vk.blindingFactors - 2))
    (lookupTheta :
      ch.theta ∉ TopLevelLookupCoherence.allTopLevelLookupThetaBadSet
        actionCircuit actionProofParams capturedURS
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk (icf)
              ps ch pbatch hlen hprob1 haccepts) haccepts)) :
    BundleStatement inputs ⊕'
      NontrivialRelation (F := Fp)
        capturedURS.g capturedURS.u capturedURS.w := by
  subst hicf
  exact action_bundleStatement_or_relation_of_deployedAccepts
    inputs ps ch pU pW hpoly pbatch hξcur hlen hprob1 haccepts
    i m hm colPoly hbindAll hquot hroute hevals claimed hxgood hgoodY
    permGamma permBeta lookupGamma lookupBeta lookupTheta

assert_no_sorry action_bundleStatement_or_relation_of_deployedAccepts_family

/--
**The deployed Action capstone at the captured instance commitments.**

The capstones above read their instance commitments from `actionCircuit.instanceCommitment`, computed
from the public inputs the way halo2's `verify_proof` computes them from its `instances` argument.
The captured artifacts are exercised against the fixture's own family
`Fixture.derivedInstanceCommitment`, which `Fixture.instance_commitments_derived` pins to the captured
points `capturedInstanceCommitments` (ironwood#65/#85). Nothing joined the two, so the capstone could
not be instantiated at the captured proof.

`Keygen.instanceCommitment_capturedActionInputs` is that join, and supplying it here as `hicf` carries
the whole capstone — every acceptance premise, every challenge exclusion, and the conclusion — onto
the captured family. This is the last step of ironwood#86: sound handling of public instances now
reaches the deployed artifacts, not merely a derived commitment family the capture was never tied to.

The statement is written out rather than inferred: this is the deployed endpoint, and a reader
should be able to see what is claimed without elaborating it.
-/
noncomputable def action_bundleStatement_or_relation_at_capturedInstances
    (ps : ProofString Fixture.shape Fp Fixture.G)
    (ch : Challenges Fixture.shape.k Fp)
    (pU pW : Fp)
    (hpoly : Polynomial Fp)
    {a₀ : Fin (2 ^ capturedURS.k) → Fp}
    (pbatch :
      OpenedBatchOpenings capturedURS (evalVector capturedURS.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := Fixture.derivedInstanceCommitment)
          capturedURS shape_k_eq_capturedURS_k Fixture.vk ps ch)
        (x4BatchEvals
          (instanceCommitment := Fixture.derivedInstanceCommitment)
          Fixture.vk ps ch)
        a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i < deployedX4PairCount Fixture.vk
        Fixture.derivedInstanceCommitment ps ch →
      0 < (deployedSetQueries Fixture.vk
        Fixture.derivedInstanceCommitment ps ch i).length)
    (hprob1 : ∀ i, i < deployedX4PairCount Fixture.vk
        Fixture.derivedInstanceCommitment ps ch →
      (((deployedSetQueries Fixture.vk
          Fixture.derivedInstanceCommitment ps ch i).length - 1 :
          ℕ) : ℝ≥0∞) / Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure
          (Finset.univ.filter
            (OpenedX1Accept capturedURS shape_k_eq_capturedURS_k Fixture.vk
              Fixture.derivedInstanceCommitment ps ch)))
    (haccepts :
      DeployedAccepts capturedURS shape_k_eq_capturedURS_k Fixture.vk
        Fixture.derivedInstanceCommitment ps ch)
    (i m : ℕ)
    (hm : m < (deployedSetQueries Fixture.vk
      Fixture.derivedInstanceCommitment ps ch i).length)
    (colPoly : Fin (deployedSetQueries Fixture.vk
      Fixture.derivedInstanceCommitment ps ch i).length →
        Polynomial Fp)
    (hbindAll : ∀ (idx : Fin ((constructIntermediateSets
          (assembleQueries Fixture.vk
            Fixture.derivedInstanceCommitment ps ch)).points.getD
              i []).length)
        (m₀ : Fin (deployedSetQueries Fixture.vk
          Fixture.derivedInstanceCommitment ps ch i).length),
      (colPoly m₀).eval
          (((constructIntermediateSets
            (assembleQueries Fixture.vk
              Fixture.derivedInstanceCommitment ps ch)).points.getD
                i [])[idx]) =
        ((deployedSetQueries Fixture.vk
          Fixture.derivedInstanceCommitment ps ch i).getD
            (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0 ⊕'
        NontrivialRelation (F := Fp)
          capturedURS.g capturedURS.u capturedURS.w)
    (hquot : hpoly = colPoly ⟨m, hm⟩)
    (hroute : (constructIntermediateSets
      (assembleQueries Fixture.vk
        Fixture.derivedInstanceCommitment ps ch)).points.getD
          i [] = [ch.x])
    (hevals : ∀ d₀,
      ((deployedSetQueries Fixture.vk
        Fixture.derivedInstanceCommitment ps ch i).getD
          m d₀).2 =
        [expectedHEval
          (allExpressions Fixture.vk ps ch
            (lagrangeBasis Fixture.vk.omega Fixture.vk.n
              Fixture.vk.blindingFactors (ch.x ^ Fixture.vk.n) ch.x).1
            (lagrangeBasis Fixture.vk.omega Fixture.vk.n
              Fixture.vk.blindingFactors
              (ch.x ^ Fixture.vk.n) ch.x).2.1
            (lagrangeBasis Fixture.vk.omega Fixture.vk.n
              Fixture.vk.blindingFactors
              (ch.x ^ Fixture.vk.n) ch.x).2.2)
          ch.y (ch.x ^ Fixture.vk.n)])
    (claimed :
      AcceptedModelClaimedEvaluations
        (memberDecode :=
          vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
            Fixture.vk Fixture.derivedInstanceCommitment ps ch
            pbatch hlen hprob1 haccepts)
        (hblinding := vk_blindingFactors_lt) haccepts)
    (hxgood :
      ch.x ∉ szBadSet
        (let model :=
          CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode :=
              vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
                Fixture.vk Fixture.derivedInstanceCommitment ps ch
                pbatch hlen hprob1 haccepts)
            (hblinding := vk_blindingFactors_lt) haccepts
        combineConstraints model.fixedCols model.adviceCols model.instanceCols
          model.gates model.sets model.chunks model.lookups
          model.beta model.gamma model.delta model.theta ch.y model.chunkLen
          model.l0 model.lLast model.lBlind -
            hpoly * (X ^ Fixture.vk.n - 1)))
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode :=
              vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
                Fixture.vk Fixture.derivedInstanceCommitment
                ps ch pbatch hlen hprob1 haccepts)
            (hblinding := vk_blindingFactors_lt) haccepts).constraints
          Fixture.vk.n j))
    (permGamma :
      ch.gamma ∉ allResolverPermutationGammaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk Fixture.derivedInstanceCommitment
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        actionActiveRows)
    (permBeta :
      ch.beta ∉ allResolverPermutationBetaBadSet Fixture.vk
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk Fixture.derivedInstanceCommitment
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        actionActiveRows)
    (lookupGamma :
      ch.gamma ∉ allResolverLookupGammaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk Fixture.derivedInstanceCommitment
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        (Fixture.vk.n - Fixture.vk.blindingFactors - 2))
    (lookupBeta :
      ch.beta ∉ allResolverLookupBetaBadSet Fixture.vk ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk Fixture.derivedInstanceCommitment
              ps ch pbatch hlen hprob1 haccepts) haccepts)
        (Fixture.vk.n - Fixture.vk.blindingFactors - 2))
    (lookupTheta :
      ch.theta ∉ TopLevelLookupCoherence.allTopLevelLookupThetaBadSet
        actionCircuit actionProofParams capturedURS
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode capturedURS shape_k_eq_capturedURS_k
              Fixture.vk Fixture.derivedInstanceCommitment
              ps ch pbatch hlen hprob1 haccepts) haccepts)) :
    BundleStatement Keygen.capturedActionInputs ⊕'
      NontrivialRelation (F := Fp)
        capturedURS.g capturedURS.u capturedURS.w :=
  action_bundleStatement_or_relation_of_deployedAccepts_family
    Keygen.capturedActionInputs Fixture.derivedInstanceCommitment
    Keygen.instanceCommitment_capturedActionInputs.symm
    ps ch pU pW hpoly pbatch hξcur hlen hprob1 haccepts
    i m hm colPoly hbindAll hquot hroute hevals claimed hxgood hgoodY
    permGamma permBeta lookupGamma lookupBeta lookupTheta

assert_no_sorry action_bundleStatement_or_relation_at_capturedInstances

end Deployed

end Zcash.Snark
