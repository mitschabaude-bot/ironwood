import Zcash.Snark.Soundness.Canonical.Vesta
import Zcash.Snark.Soundness.TopLevelTerminal

/-!
# Circuit-generic Vesta soundness capstone

This module combines the verifier-native Vesta terminal with the generic
`TopLevelCircuit` soundness terminal.  It is generic over the circuit and its
public-instance commitments; circuit-specific presentation theorems may turn the
resulting `TopLevelBundleStatement` into a friendlier external specification.
-/

namespace Zcash.Snark

open Polynomial
open Classical
open scoped ENNReal

open Halo2 Keygen

set_option maxHeartbeats 20000

local instance topLevelVestaInhabited : Inhabited VestaG := ⟨0⟩

attribute [local irreducible] deployedSetQueries deployedSetCommIds
  deployedX4PairCount x4BatchCommitments x4BatchEvals

set_option maxRecDepth 1000000 in
/--
The Vesta soundness capstone for an arbitrary top-level circuit and arbitrary
proof multiplicity.

Acceptance fixes the canonical polynomial assignment.  The caller supplies the
circuit's named component-level correctness package for that assignment, not an
opaque implication to the desired statement.
-/
theorem topLevelBundleStatement_or_relation_of_deployedAccepts
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS VestaG)
    (hk : (pp.mergeDerived top).k = urs.k)
    (instanceCommitment :
      Fin (pp.mergeDerived top).numProofs → ℕ → VestaG)
    (ps : ProofString (pp.mergeDerived top) Fp VestaG)
    (ch : Challenges (pp.mergeDerived top).k Fp)
    (pU pW : Fp)
    (hpoly : Polynomial Fp)
    {a₀ : Fin (2 ^ urs.k) → Fp}
    (pbatch :
      OpenedBatchOpenings urs (evalVector urs.k ch.x3)
        (x4BatchCommitments
          (instanceCommitment := instanceCommitment)
          urs hk (top.toVerifierKey pp urs) ps ch)
        (x4BatchEvals
          (instanceCommitment := instanceCommitment)
          (top.toVerifierKey pp urs) ps ch)
        a₀ pU pW)
    (hξcur : pbatch.batchChallenge pbatch.current = ch.x4)
    (hlen : ∀ i, i <
        deployedX4PairCount
          (top.toVerifierKey pp urs) instanceCommitment ps ch →
      0 < (deployedSetQueries
        (top.toVerifierKey pp urs) instanceCommitment ps ch i).length)
    (hprob1 : ∀ i, i <
        deployedX4PairCount
          (top.toVerifierKey pp urs) instanceCommitment ps ch →
      (((deployedSetQueries
          (top.toVerifierKey pp urs) instanceCommitment ps ch i).length - 1 :
            ℕ) : ℝ≥0∞) /
          Fintype.card Fp
        < (PMF.uniformOfFintype Fp).toOuterMeasure
          (Finset.univ.filter
            (OpenedX1Accept urs hk
              (top.toVerifierKey pp urs) instanceCommitment ps ch)))
    (haccepts :
      DeployedAccepts urs hk
        (top.toVerifierKey pp urs) instanceCommitment ps ch)
    (hblinding :
      (top.toVerifierKey pp urs).blindingFactors <
        (top.toVerifierKey pp urs).n)
    (gateCoherence : TopLevelGateCoherence top pp urs)
    (i m : ℕ)
    (hm : m < (deployedSetQueries
      (top.toVerifierKey pp urs) instanceCommitment ps ch i).length)
    (colPoly : Fin (deployedSetQueries
      (top.toVerifierKey pp urs) instanceCommitment ps ch i).length →
        Polynomial Fp)
    (hbindAll : ∀ (idx : Fin ((constructIntermediateSets
          (assembleQueries
            (top.toVerifierKey pp urs) instanceCommitment ps ch)).points.getD
              i []).length)
        (m₀ : Fin (deployedSetQueries
          (top.toVerifierKey pp urs) instanceCommitment ps ch i).length),
      (colPoly m₀).eval
          (((constructIntermediateSets
            (assembleQueries
              (top.toVerifierKey pp urs) instanceCommitment ps ch)).points.getD
                i [])[idx]) =
        ((deployedSetQueries
          (top.toVerifierKey pp urs) instanceCommitment ps ch i).getD
            (m₀ : ℕ) (.point 0, [])).2.getD (idx : ℕ) 0
        ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (hquot : hpoly = colPoly ⟨m, hm⟩)
    (hroute : (constructIntermediateSets
      (assembleQueries
        (top.toVerifierKey pp urs) instanceCommitment ps ch)).points.getD
          i [] = [ch.x])
    (hevals : ∀ d₀,
      ((deployedSetQueries
        (top.toVerifierKey pp urs) instanceCommitment ps ch i).getD m d₀).2 =
        [expectedHEval
          (allExpressions
            (top.toVerifierKey pp urs) ps ch
            (lagrangeBasis
              (top.toVerifierKey pp urs).omega
              (top.toVerifierKey pp urs).n
              (top.toVerifierKey pp urs).blindingFactors
              (ch.x ^ (top.toVerifierKey pp urs).n) ch.x).1
            (lagrangeBasis
              (top.toVerifierKey pp urs).omega
              (top.toVerifierKey pp urs).n
              (top.toVerifierKey pp urs).blindingFactors
              (ch.x ^ (top.toVerifierKey pp urs).n) ch.x).2.1
            (lagrangeBasis
              (top.toVerifierKey pp urs).omega
              (top.toVerifierKey pp urs).n
              (top.toVerifierKey pp urs).blindingFactors
              (ch.x ^ (top.toVerifierKey pp urs).n) ch.x).2.2)
          ch.y (ch.x ^ (top.toVerifierKey pp urs).n)])
    (claimed :
      AcceptedModelClaimedEvaluations
        (memberDecode :=
          vestaExtractedMemberDecode urs hk
            (top.toVerifierKey pp urs) instanceCommitment ps ch
            pbatch hlen hprob1 haccepts)
        (hblinding := hblinding) haccepts)
    (hxgood :
      ch.x ∉ szBadSet
        (let model :=
          CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode :=
              vestaExtractedMemberDecode urs hk
                (top.toVerifierKey pp urs) instanceCommitment ps ch
                pbatch hlen hprob1 haccepts)
            (hblinding := hblinding) haccepts
        combineConstraints model.fixedCols model.adviceCols model.instanceCols
          model.gates model.sets model.chunks model.lookups
          model.beta model.gamma model.delta model.theta ch.y model.chunkLen
          model.l0 model.lLast model.lBlind -
            hpoly * (X ^ (top.toVerifierKey pp urs).n - 1)))
    (hgoodY : ∀ j,
      ch.y ∉ szBadSet
        (foldSplitWitness
          (CanonicalMemberConstraintRelation.acceptedModel
            (memberDecode :=
              vestaExtractedMemberDecode urs hk
                (top.toVerifierKey pp urs) instanceCommitment ps ch
                pbatch hlen hprob1 haccepts)
            (hblinding := hblinding) haccepts).constraints
          (top.toVerifierKey pp urs).n j))
    {cell : Type} [DecidableEq cell] [Fintype cell]
    (correctness : ∀
      (_hsatisfied :
        (CanonicalMemberConstraintRelation.acceptedModel
          (memberDecode :=
            vestaExtractedMemberDecode urs hk
              (top.toVerifierKey pp urs) instanceCommitment ps ch
              pbatch hlen hprob1 haccepts)
          (hblinding := hblinding) haccepts).CircuitSat
            ch.y hpoly (top.toVerifierKey pp urs).n a₀),
      TopLevelCircuitCorrectness top pp urs ch
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode urs hk
              (top.toVerifierKey pp urs) instanceCommitment ps ch
              pbatch hlen hprob1 haccepts)
          haccepts)
        cell
        (HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)) :
    TopLevelBundleStatement top pp
        (CanonicalMemberConstraintRelation.acceptedPolynomial
          (memberDecode :=
            vestaExtractedMemberDecode urs hk
              (top.toVerifierKey pp urs) instanceCommitment ps ch
              pbatch hlen hprob1 haccepts)
          haccepts) ∨
      HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  let vk := top.toVerifierKey pp urs
  let memberDecode :=
    vestaExtractedMemberDecode urs hk vk instanceCommitment ps ch
      pbatch hlen hprob1 haccepts
  have hterminal :=
    acceptedModel_circuitSat_or_relation_of_acceptedSelections
      urs hk vk instanceCommitment ps ch pU pW hpoly
      pbatch hξcur hlen hprob1 haccepts hblinding
      gateCoherence.adviceQueryCount gateCoherence.instanceQueryCount
      i m hm colPoly hbindAll hquot hroute hevals claimed hxgood
  rcases hterminal with hsatisfied | hrelation
  · let relation :=
      CanonicalMemberConstraintRelation.ofAcceptedCircuitSat
        haccepts hsatisfied
    have hpolynomial :
        relation.polynomial =
          CanonicalMemberConstraintRelation.acceptedPolynomial
            (memberDecode := memberDecode) haccepts := by
      rfl
    have hn : vk.n ≠ 0 := by
      change 2 ^ top.domainExponent ≠ 0
      positivity
    have hsatisfaction :=
      relation.constraintSatisfaction hn
        (by
          simpa only [
            CanonicalMemberConstraintRelation.model,
            hpolynomial] using hgoodY)
    apply
      topLevelBundleStatement_or_bad_of_constraintSatisfaction
        (top := top) (pp := pp) (urs := urs) (ch := ch)
        (cell := cell) hblinding
    · simpa only [hpolynomial] using hsatisfaction
    · exact correctness hsatisfied
  · exact Or.inr hrelation

assert_no_sorry topLevelBundleStatement_or_relation_of_deployedAccepts

end Zcash.Snark
