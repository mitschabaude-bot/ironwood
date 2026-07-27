import Zcash.Circuits.Integration.TopLevelBridge
import Zcash.Circuits.Integration.TopLevelAssignment

/-!
# Top-level circuit correctness interface

This module packages the named Clean/Ironwood representation boundaries consumed
by the generic soundness terminal.  It deliberately contains no final circuit
statement and no opaque encoding implication.
-/

namespace Zcash.Snark

open Halo2 Polynomial

set_option maxHeartbeats 20000

/--
The statement owned by a top-level circuit, simultaneously for every polynomial
assignment decoded from one accepted proof bundle.
-/
def TopLevelBundleStatement
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams)
    (poly : CommitmentId → Polynomial Fp) : Prop :=
  ∀ proofIndex : Fin (pp.mergeDerived top).numProofs,
    let environment := ({
        polynomial := poly
      } : TopLevelAssignment top
            (pp.mergeDerived top).numProofs proofIndex).environment
    top.Statement (top.extractPublicInput environment)

namespace TopLevelBundleStatement

/--
Present the circuit-owned bundle statement at externally supplied public inputs once
the canonical polynomial assignments are known to encode them through the circuit's
declared instance-cell layout.
-/
theorem of_publicInputEncoding
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams)
    (poly : CommitmentId → Polynomial Fp)
    (inputs : Fin (pp.mergeDerived top).numProofs → PublicInput Fp)
    (hencoding : ∀ proofIndex,
      let assignment : TopLevelAssignment top
          (pp.mergeDerived top).numProofs proofIndex :=
        { polynomial := poly }
      assignment.PublicInputEncoding (inputs proofIndex))
    (htop : TopLevelBundleStatement top pp poly) :
    ∀ proofIndex, top.Statement (inputs proofIndex) := by
  intro proofIndex
  let assignment : TopLevelAssignment top
      (pp.mergeDerived top).numProofs proofIndex :=
    { polynomial := poly }
  have hstatement := htop proofIndex
  change top.Statement
    (top.extractPublicInput assignment.environment) at hstatement
  rw [assignment.extractPublicInput_eq
    (inputs proofIndex) (hencoding proofIndex)] at hstatement
  exact hstatement

end TopLevelBundleStatement

/--
The representation-boundary facts needed to interpret one canonical polynomial
assignment as an execution of a top-level circuit.

Each field names one of the four Clean constraint families.  The shared `Bad`
alternative is retained componentwise so that commitment-binding failures can be
joined without turning this record into an opaque statement-level hypothesis.
-/
structure TopLevelCircuitCorrectness
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (ch : Challenges (pp.mergeDerived top).k Fp)
    (poly : CommitmentId → Polynomial Fp)
    (cell : Type) [DecidableEq cell] [Fintype cell]
    (Bad : Prop) : Prop where
  gates : TopLevelGateCoherence top pp urs
  fixedEncoding : ∀ proofIndex,
    let assignment :
        TopLevelAssignment top (pp.mergeDerived top).numProofs proofIndex :=
      { polynomial := poly }
    assignment.FixedColumnEncoding pp urs ∨ Bad
  fixed : ∀ proofIndex,
    (SelectorActivationsRealized
        top.selectorMap top.selectorActivations
        (resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent)) ∧
      CircuitConstraintFamily.constraints .fixed top.placement
        (resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))
        (top.operations) 0) ∨ Bad
  copies : ∀ proofIndex,
    Nonempty
      (CopyReplayWitness top.placement
        (resolverEnvironment
          (top.toVerifierKey pp urs) poly proofIndex
          (top.usableRowsAt top.domainExponent))
        (top.operations) cell Bad) ∨ Bad
  lookups : ∀ proofIndex,
    TopLevelLookupCoherence.TopLevelLookupWitnessConditions
      top pp urs ch poly proofIndex ∨ Bad

end Zcash.Snark
