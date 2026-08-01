import Zcash.Snark.Keygen.Pipeline
import Zcash.Snark.Soundness.Canonical.ConstraintModel
import Zcash.Circuits.Integration.PermutationCompiler
import Zcash.Circuits.Integration.TopLevelAssignment

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
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges k Fp) (poly : CommitmentId → CPoly) :
    ConstraintPolyModel pp.numProofs :=
  let vk := top.toVerifierKey urs
  let selectors := canonicalLagrangePolynomials vk.omega
    (top.toVerifierKey_blindingFactors_lt_n urs)
  constraintModelOfResolver
    (numProofs := pp.numProofs)
    (k := k)
    vk ch poly
    (permutationSetsOfResolver
      (shape := top.shape.withProofParams pp) vk poly)
    (permutationChunksOfResolver
      (shape := top.shape.withProofParams pp) vk poly)
    selectors.1 selectors.2.1 selectors.2.2

/-- The top-level canonical model exposes the resolver construction used by its
verification key without requiring consumers to unfold circuit compilation. -/
theorem constraintModel_eq_constraintModelOfResolver
    {k : ℕ} (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges k Fp) (poly : CommitmentId → CPoly) :
    let selectors := canonicalLagrangePolynomials top.omega
      (top.toVerifierKey_blindingFactors_lt_n urs)
    top.constraintModel pp urs ch poly =
      constraintModelOfResolver
        (numProofs := pp.numProofs)
        (k := k)
        (top.toVerifierKey urs) ch poly
        (permutationSetsOfResolver
          (shape := top.shape.withProofParams pp)
          (top.toVerifierKey urs) poly)
        (permutationChunksOfResolver
          (shape := top.shape.withProofParams pp)
          (top.toVerifierKey urs) poly)
        selectors.1 selectors.2.1 selectors.2.2 := by
  rfl

@[simp] theorem constraintModel_l0
    {k : ℕ} (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges k Fp) (poly : CommitmentId → CPoly) :
    (top.constraintModel pp urs ch poly).l0 =
      (canonicalLagrangePolynomials top.omega
        (top.toVerifierKey_blindingFactors_lt_n urs)).1 := by
  rfl

@[simp] theorem constraintModel_lLast
    {k : ℕ} (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges k Fp) (poly : CommitmentId → CPoly) :
    (top.constraintModel pp urs ch poly).lLast =
      (canonicalLagrangePolynomials top.omega
        (top.toVerifierKey_blindingFactors_lt_n urs)).2.1 := by
  rfl

@[simp] theorem constraintModel_lBlind
    {k : ℕ} (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges k Fp) (poly : CommitmentId → CPoly) :
    (top.constraintModel pp urs ch poly).lBlind =
      (canonicalLagrangePolynomials top.omega
        (top.toVerifierKey_blindingFactors_lt_n urs)).2.2 := by
  rfl

/-- Resolver pairing preserves the compiler-prescribed width of every
circuit-derived permutation chunk. -/
theorem resolverPermutationPairs_length
    (top : TopLevelCircuit Fp Config PublicInput)
    {numProofs : ℕ} (urs : URS G) (poly : CommitmentId → CPoly)
    (proofIndex : Fin numProofs)
    (chunk : Fin top.shape.numPermutationSets) :
    (ResolverPermutationPairs
        (top.toVerifierKey urs) poly proofIndex chunk).length =
      min top.chunkLen
        (top.permutationColumnCount - (chunk : ℕ) * top.chunkLen) := by
  simp only [ResolverPermutationPairs,
    permutationChunkPairsOfResolver, List.length_map]
  apply top.toVerifierKey_permutationChunks_getD_length
  rw [top.toVerifierKey_permutationChunks_length]
  exact chunk.isLt

/-- The canonical model of a circuit-derived key satisfies the complete
permutation-domain interface. Only support for the circuit's evaluation-domain
exponent is external; chunking and blinding bounds follow from compilation. -/
theorem resolverPermutationDomain
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (ch : Challenges top.shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hdomainExponent : top.domainExponent < 33) :
    let model := top.constraintModel pp urs ch poly
    ResolverPermutationDomain (top.toVerifierKey urs)
      model.l0 model.lLast model.lBlind
      top.n (top.n - top.blindingFactors - 1) := by
  simpa only [top.toVerifierKey_n,
    top.toVerifierKey_blindingFactors] using
    ResolverPermutationDomain.ofCanonicalConstraintModel
      (top.toVerifierKey urs) ch poly
      (top.toVerifierKey_blindingFactors_lt_n urs)
      (TopLevelAssignment.toVerifierKey_domainRowsInjective
        urs hdomainExponent)
      (TopLevelAssignment.toVerifierKey_domainRoot
        urs hdomainExponent)
      (top.toVerifierKey_permutationChunks_length urs)

/-- The last usable row of a circuit-derived verifier domain is the verifier's
canonical negative blinding rotation. -/
theorem toVerifierKey_lastUsableRowRotation
    (top : TopLevelCircuit Fp Config PublicInput)
    (urs : URS G)
    (hdomainExponent : top.domainExponent < 33) :
    (top.toVerifierKey urs).omega ^
        ((top.toVerifierKey urs).n -
          (top.toVerifierKey urs).blindingFactors - 1) =
      (top.toVerifierKey urs).omega ^
        (-(((top.toVerifierKey urs).blindingFactors : ℤ) + 1)) := by
  rw [show (top.toVerifierKey urs).n -
      (top.toVerifierKey urs).blindingFactors - 1 =
        (top.toVerifierKey urs).n -
          ((top.toVerifierKey urs).blindingFactors + 1) by omega]
  exact domain_pow_sub_eq_zpow_neg
    (by
      have hblinding := top.toVerifierKey_blindingFactors_lt_n urs
      omega)
    (TopLevelAssignment.toVerifierKey_domainRoot
      urs hdomainExponent)

end Halo2.TopLevelCircuit
