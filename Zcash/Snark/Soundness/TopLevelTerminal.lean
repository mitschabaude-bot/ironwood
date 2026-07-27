import Zcash.Circuits.Integration.TopLevelCorrectness
import Zcash.Circuits.Integration.TopLevelAssignment
import Zcash.Snark.Soundness.Multiopen.CanonicalRelation

/-!
# Generic top-level circuit soundness terminal

This module is the core soundness endpoint for a Clean `TopLevelCircuit`.  It
turns satisfaction of the verifier-native canonical constraint model into the
circuit's own statement for every proof in the bundle.

The Clean/Ironwood representation work remains exposed as named component
conditions.  In particular, `TopLevelCircuitCorrectness` does not contain the
desired statement or an opaque encoding implication.
-/

namespace Zcash.Snark

open Halo2 Polynomial

set_option maxHeartbeats 20000

/--
Canonical constraint satisfaction plus the component-level circuit correctness
package implies the circuit-owned statement for every proof, preserving the one
shared exceptional event.
-/
theorem topLevelBundleStatement_or_bad_of_constraintSatisfaction
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    {top : TopLevelCircuit Fp Config PublicInput}
    {pp : Keygen.ProofParams} {urs : URS G}
    {ch : Challenges (pp.mergeDerived top).k Fp}
    {poly : CommitmentId → Polynomial Fp}
    {cell : Type} [DecidableEq cell] [Fintype cell]
    {Bad : Prop}
    (hblinding :
      (top.toVerifierKey pp urs).blindingFactors <
        (top.toVerifierKey pp urs).n)
    (satisfaction :
      ConstraintSatisfaction
        (canonicalConstraintModelOfPermutationResolver
          (top.toVerifierKey pp urs) ch poly hblinding)
        (top.toVerifierKey pp urs).n)
    (correctness :
      TopLevelCircuitCorrectness top pp urs ch poly cell Bad) :
    TopLevelBundleStatement top pp poly ∨ Bad := by
  classical
  by_cases hbad : Bad
  · exact Or.inr hbad
  · apply Or.inl
    intro proofIndex
    let assignment :
        TopLevelAssignment top (pp.mergeDerived top).numProofs proofIndex :=
      { polynomial := poly }
    have hfixed := (correctness.fixed proofIndex).resolve_right hbad
    have hfixedEncoding :=
      (correctness.fixedEncoding proofIndex).resolve_right hbad
    have hcopies := (correctness.copies proofIndex).resolve_right hbad
    have hlookups := (correctness.lookups proofIndex).resolve_right hbad
    have hrows :=
      TopLevelAssignment.domainRowsInjective
        (top := top) correctness.gates.domainExponent_lt
    have hroot :=
      TopLevelAssignment.domainRoot
        (top := top) correctness.gates.domainExponent_lt
    let bridge :=
      FullCircuitBridge.ofTopLevelCanonical
        correctness.gates ch poly proofIndex hblinding satisfaction
        hrows hroot hfixed.1 hfixed.2 hcopies.some hlookups
    have henvironment :=
      assignment.resolverEnvironment_eq_environment
        pp urs hfixedEncoding
    have canonicalBridge :
        FullCircuitBridge top.placement assignment.environment
          top.operations 0 cell Bad := by
      rw [← henvironment]
      exact bridge
    have hsound :=
      FullCircuitBridge.topLevelSoundness_or_bad
        top assignment.proofAssignment canonicalBridge
    exact hsound.resolve_right hbad

assert_no_sorry topLevelBundleStatement_or_bad_of_constraintSatisfaction

end Zcash.Snark
