import Zcash.Snark.Soundness.Canonical.DomainSelectors
import Zcash.Snark.Soundness.Canonical.PermutationSemantics
import Zcash.Snark.Soundness.Canonical.LookupSemantics

/-!
# Canonical resolver-backed constraint models

The deployed vanishing check computes its Lagrange selectors from the evaluation
domain at every transcript challenge. The polynomial soundness argument must use
one fixed selector triple across those challenges. This module installs the
canonical fixed triple directly into the generic commitment-ID resolver model.

No circuit or concrete verifying key is selected here. A caller supplies only
the generic domain well-formedness facts needed to identify evaluation of the
fixed polynomials with the verifier's deployed `lagrangeBasis` computation.
-/

namespace Zcash.Snark

open CompPoly.CPolynomial

set_option maxHeartbeats 20000

namespace VerifyingKey

/--
The full commitment-ID resolver model with its selector polynomials determined
by the verification key's domain and blinding count.
-/
def constraintModel
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n) :
    ConstraintPolyModel numProofs :=
  let selectors :=
    canonicalLagrangePolynomials vk.omega hblinding
  constraintModelOfResolver (numProofs := numProofs) vk ch poly
    (permutationSetsOfResolver (numProofs := numProofs) vk poly)
    (permutationChunksOfResolver (numProofs := numProofs) vk poly)
    selectors.1 selectors.2.1 selectors.2.2

@[simp] theorem constraintModel_fixedCols
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n) :
    (vk.constraintModel (numProofs := numProofs) ch poly hblinding).fixedCols =
      fixedQueryFeedOfResolver vk poly :=
  rfl

@[simp] theorem constraintModel_adviceCols
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n) :
    (vk.constraintModel (numProofs := numProofs) ch poly hblinding).adviceCols =
      fun proofIndex : Fin numProofs =>
        adviceQueryFeedOfResolver vk poly proofIndex :=
  rfl

@[simp] theorem constraintModel_instanceCols
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n) :
    (vk.constraintModel (numProofs := numProofs) ch poly hblinding).instanceCols =
      fun proofIndex : Fin numProofs =>
        instanceQueryFeedOfResolver vk poly proofIndex :=
  rfl

@[simp] theorem constraintModel_gates
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n) :
    (vk.constraintModel (numProofs := numProofs) ch poly hblinding).gates = vk.gates :=
  rfl

@[simp] theorem constraintModel_sets
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n)
    (proofIndex : Fin numProofs) :
    (vk.constraintModel (numProofs := numProofs) ch poly hblinding).sets proofIndex =
      permutationSetsOfResolver vk poly proofIndex :=
  rfl

@[simp] theorem constraintModel_chunks
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n)
    (proofIndex : Fin numProofs) :
    (vk.constraintModel (numProofs := numProofs) ch poly hblinding).chunks proofIndex =
      permutationChunksOfResolver vk poly proofIndex :=
  rfl

@[simp] theorem constraintModel_lookups
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n)
    (proofIndex : Fin numProofs) :
    (vk.constraintModel (numProofs := numProofs) ch poly hblinding).lookups proofIndex =
      lookupEntriesOfResolver vk poly proofIndex :=
  rfl

/--
Expose the resolver-backed construction without forcing downstream proofs to
unfold the computable polynomial implementation.
-/
theorem constraintModel_eq_constraintModelOfResolver
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n) :
    vk.constraintModel (numProofs := numProofs) ch poly hblinding =
      constraintModelOfResolver (numProofs := numProofs) vk ch poly
        (permutationSetsOfResolver (numProofs := numProofs) vk poly)
        (permutationChunksOfResolver (numProofs := numProofs) vk poly)
        (vk.constraintModel (numProofs := numProofs) ch poly hblinding).l0
        (vk.constraintModel (numProofs := numProofs) ch poly hblinding).lLast
        (vk.constraintModel (numProofs := numProofs) ch poly hblinding).lBlind := by
  rfl

@[simp] theorem constraintModel_l0
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n) :
    (vk.constraintModel (numProofs := numProofs) ch poly hblinding).l0 =
      (canonicalLagrangePolynomials vk.omega hblinding).1 :=
  rfl

@[simp] theorem constraintModel_lLast
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n) :
    (vk.constraintModel (numProofs := numProofs) ch poly hblinding).lLast =
      (canonicalLagrangePolynomials vk.omega hblinding).2.1 :=
  rfl

@[simp] theorem constraintModel_lBlind
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n) :
    (vk.constraintModel (numProofs := numProofs) ch poly hblinding).lBlind =
      (canonicalLagrangePolynomials vk.omega hblinding).2.2 :=
  rfl

/--
The canonical resolver model's fixed selector polynomials evaluate to the
verifier's exact deployed selector triple at every challenge outside the
evaluation domain.
-/
theorem constraintModel_selectorEvaluations
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n)
    (hrows : Function.Injective fun i : Fin vk.n =>
      vk.omega ^ (i : ℕ))
    (hroot : vk.omega ^ vk.n = 1)
    (hnFp : (vk.n : Fp) ≠ 0)
    (hxDomain : ch.x ^ vk.n ≠ 1) :
    let model := vk.constraintModel (numProofs := numProofs) ch poly hblinding
    (model.l0.eval ch.x, model.lLast.eval ch.x,
      model.lBlind.eval ch.x) =
        lagrangeBasis vk.omega vk.n vk.blindingFactors
          (ch.x ^ vk.n) ch.x := by
  simpa [VerifyingKey.constraintModel] using
    canonicalLagrangePolynomials_eval
      hblinding hrows hroot hnFp hxDomain

end VerifyingKey

/--
The canonical model satisfies the generic permutation-domain interface. Its
selector and last-rotation obligations are derived here; callers retain only
the actual VK chunk facts and root-domain facts.
-/
theorem ResolverPermutationDomain.ofCanonicalConstraintModel
    {shape : CircuitShape} {numProofs : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n)
    (hrows : Function.Injective fun i : Fin vk.n =>
      vk.omega ^ (i : ℕ))
    (hroot : vk.omega ^ vk.n = 1)
    (hchunkCount :
      vk.permutationChunks.length = shape.numPermutationSets) :
    let model := vk.constraintModel (numProofs := numProofs) ch poly hblinding
    ResolverPermutationDomain vk model.l0 model.lLast model.lBlind
      vk.n (vk.n - vk.blindingFactors - 1) := by
  have hn : 0 < vk.n := Nat.zero_lt_of_lt hblinding
  have hm : vk.n - vk.blindingFactors - 1 < vk.n := by
    omega
  have hlastRotation :
      vk.omega ^ (vk.n - vk.blindingFactors - 1) =
        vk.omega ^ (-((vk.blindingFactors : ℤ) + 1)) := by
    rw [show vk.n - vk.blindingFactors - 1 =
      vk.n - (vk.blindingFactors + 1) by omega]
    exact domain_pow_sub_eq_zpow_neg
      (t := vk.blindingFactors + 1) (by omega) hroot
  simpa [VerifyingKey.constraintModel,
    canonicalLagrangePolynomials, lastUsableDomainRow] using
      ResolverPermutationDomain.ofCanonicalSelectors vk hn hm hrows
        hchunkCount hlastRotation hroot

/--
The canonical row-selector polynomials satisfy the lookup-domain interface
through every row strictly before its final usable row.
-/
theorem ResolverLookupDomain.ofCanonicalPolynomials
    {shape : CircuitShape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (husable : vk.blindingFactors + 1 < vk.n)
    (hrows : Function.Injective fun i : Fin vk.n =>
      vk.omega ^ (i : ℕ))
    (hroot : vk.omega ^ vk.n = 1) :
    let selectors := canonicalLagrangePolynomials vk.omega
      (Nat.lt_of_succ_lt husable)
    ResolverLookupDomain vk selectors.1 selectors.2.1 selectors.2.2
      vk.n (vk.n - vk.blindingFactors - 2) := by
  let hblinding : vk.blindingFactors < vk.n :=
    Nat.lt_of_succ_lt husable
  have hlast :
      vk.n - vk.blindingFactors - 2 + 1 < vk.n := by
    omega
  have homega : vk.omega ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (by omega)] at hroot
    exact zero_ne_one hroot
  have hlastRow :
      (⟨vk.n - vk.blindingFactors - 2 + 1, hlast⟩ : Fin vk.n) =
        lastUsableDomainRow hblinding := by
    apply Fin.ext
    simp only [lastUsableDomainRow]
    omega
  have hdomain :=
    ResolverLookupDomain.ofCanonicalSelectors vk hlast hrows
      homega hroot
  rw [hlastRow] at hdomain
  simpa [hblinding, canonicalLagrangePolynomials] using hdomain

end Zcash.Snark
