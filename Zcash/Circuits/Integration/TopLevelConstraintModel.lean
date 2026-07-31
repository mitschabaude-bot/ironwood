import Zcash.Snark.Keygen.Pipeline
import Zcash.Snark.Soundness.Canonical.ConstraintModel

/-!
# Circuit-derived canonical constraint models

This module closes the domain-law boundary between a Clean top-level circuit and
Ironwood's verifier-native canonical constraint model. Arbitrary verification
keys still require an explicit proof that their blinding rows fit the domain;
a key derived from `TopLevelCircuit` carries that fact by construction.
-/

namespace Halo2.TopLevelCircuit

open Zcash.Snark
open Zcash
open Zcash.Snark.Keygen
open Halo2 CompPoly.CPolynomial

variable
    {G : Type} [AddCommGroup G] [Inhabited G]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

/--
The canonical resolver model for a circuit's own verification key.

Unlike the arbitrary-key constructor, this interface has no domain-law
argument: domain fitting follows from the `TopLevelCircuit` compilation.
-/
def constraintModel {k : ℕ}
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (ch : Challenges k Fp) (poly : CommitmentId → CPoly) :
    ConstraintPolyModel pp.numProofs :=
  let vk := top.toVerifierKey pp urs
  let selectors := canonicalLagrangePolynomials vk.omega
    (top.toVerifierKey_blindingFactors_lt_n pp urs)
  constraintModelOfResolver
    (numProofs := pp.numProofs)
    (k := k)
    vk ch poly
    (permutationSetsOfResolver vk poly)
    (permutationChunksOfResolver vk poly)
    selectors.1 selectors.2.1 selectors.2.2

/-- The top-level canonical model exposes the resolver construction used by its
verification key without requiring consumers to unfold circuit compilation. -/
theorem constraintModel_eq_constraintModelOfResolver
    {k : ℕ} (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (ch : Challenges k Fp) (poly : CommitmentId → CPoly) :
    let selectors := canonicalLagrangePolynomials top.omega
      (top.toVerifierKey_blindingFactors_lt_n pp urs)
    top.constraintModel pp urs ch poly =
      constraintModelOfResolver
        (numProofs := pp.numProofs)
        (k := k)
        (top.toVerifierKey pp urs) ch poly
        (permutationSetsOfResolver (top.toVerifierKey pp urs) poly)
        (permutationChunksOfResolver (top.toVerifierKey pp urs) poly)
        selectors.1 selectors.2.1 selectors.2.2 := by
  rfl

@[simp] theorem constraintModel_l0
    {k : ℕ} (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (ch : Challenges k Fp) (poly : CommitmentId → CPoly) :
    (top.constraintModel pp urs ch poly).l0 =
      (canonicalLagrangePolynomials top.omega
        (top.toVerifierKey_blindingFactors_lt_n pp urs)).1 := by
  rfl

@[simp] theorem constraintModel_lLast
    {k : ℕ} (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (ch : Challenges k Fp) (poly : CommitmentId → CPoly) :
    (top.constraintModel pp urs ch poly).lLast =
      (canonicalLagrangePolynomials top.omega
        (top.toVerifierKey_blindingFactors_lt_n pp urs)).2.1 := by
  rfl

@[simp] theorem constraintModel_lBlind
    {k : ℕ} (top : TopLevelCircuit Fp Config PublicInput)
    (pp : Keygen.ProofParams) (urs : URS G)
    (ch : Challenges k Fp) (poly : CommitmentId → CPoly) :
    (top.constraintModel pp urs ch poly).lBlind =
      (canonicalLagrangePolynomials top.omega
        (top.toVerifierKey_blindingFactors_lt_n pp urs)).2.2 := by
  rfl

end Halo2.TopLevelCircuit
