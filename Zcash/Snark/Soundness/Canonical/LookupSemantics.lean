import Zcash.Snark.Soundness.Canonical.LookupInstantiation
import Zcash.Snark.Soundness.GoodChallenge
import Zcash.Snark.Soundness.Canonical.DomainSelectors

/-!
# Semantic endpoint for resolver-backed lookup constraints

`LookupInstantiation` extracts the five polynomial divisibility facts for a selected lookup from
full constraint satisfaction.  This file joins those facts to the evaluation-domain and
good-challenge premises of `deployed_lookup_subset_of_nonzero_challenges`, producing the scalar
row-membership theorem consumed by the operation-level tuple bridge.
-/

namespace Zcash.Snark

open CompPoly.CPolynomial Finset
open scoped ENNReal

set_option maxHeartbeats 20000

/-- Evaluation-domain facts shared by every resolver-backed lookup in one circuit. -/
structure ResolverLookupDomain
    {shape : CircuitShape} {G : Type*}
    (vk : VerifyingKey shape Fp G)
    (l0 lLast lBlind : CPoly) (n u : ℕ) : Prop where
  omegaNonzero : vk.omega ≠ 0
  root : vk.omega ^ n = 1
  active : ∀ i < u + 1,
    1 - (lLast.eval (vk.omega ^ i) + lBlind.eval (vk.omega ^ i)) ≠ 0
  firstSelector : l0.eval (vk.omega ^ 0) ≠ 0
  lastSelector : lLast.eval (vk.omega ^ (u + 1)) ≠ 0

/--
Build the lookup-domain record with the canonical first, last-usable, and
blinding-row selectors. The selector evaluations are independent of the lookup
and of the circuit being instantiated.
-/
theorem ResolverLookupDomain.ofCanonicalSelectors
    {shape : CircuitShape} {G : Type*}
    (vk : VerifyingKey shape Fp G) {n u : ℕ}
    (hlast : u + 1 < n)
    (hrows : Function.Injective fun i : Fin n => vk.omega ^ (i : ℕ))
    (homega : vk.omega ≠ 0)
    (hroot : vk.omega ^ n = 1) :
    ResolverLookupDomain vk
      (rowSelectorPolynomial vk.omega ⟨0, lt_trans (Nat.zero_lt_succ u) hlast⟩)
      (rowSelectorPolynomial vk.omega ⟨u + 1, hlast⟩)
      (blindSelectorPolynomial vk.omega ⟨u + 1, hlast⟩) n u where
  omegaNonzero := homega
  root := hroot
  active i hi := by
    exact last_add_blind_active ⟨u + 1, hlast⟩
      ⟨i, lt_trans hi hlast⟩ hi hrows
  firstSelector :=
    firstSelectorPolynomial_nonzero
      ⟨0, lt_trans (Nat.zero_lt_succ u) hlast⟩ rfl hrows
  lastSelector :=
    lastSelectorPolynomial_nonzero ⟨u + 1, hlast⟩ hrows

/-- The product-difference polynomial whose roots are excluded at the selected lookup's `γ`
squeeze.  It is fixed after `β`. -/
def resolverLookupProductDifference
    {shape : CircuitShape} {k : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (l : Fin shape.numLookups) (u : ℕ) :
    CBiPoly :=
  lookupProdDiff
    (Finset.univ.val.map
      (lookupColumnRows vk.omega (poly (.lookupPermInput p l)) (u + 1)))
    (Finset.univ.val.map
      (lookupColumnRows vk.omega (poly (.lookupPermTable p l)) (u + 1)))
    (Finset.univ.val.map
      (lookupColumnRows vk.omega
        (lookupInputPolyOfResolver vk ch poly p l) (u + 1)))
    (Finset.univ.val.map
      (lookupColumnRows vk.omega
        (lookupTablePolyOfResolver vk ch poly p l) (u + 1)))

/-- The selected lookup difference after fixing `β`, computed without constructing a nested
polynomial. -/
def resolverLookupProductDifferenceGamma
    {shape : CircuitShape} {k : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (l : Fin shape.numLookups) (u : ℕ) : CPoly :=
  lookupProdDiffGamma
    (Finset.univ.val.map
      (lookupColumnRows vk.omega (poly (.lookupPermInput p l)) (u + 1)))
    (Finset.univ.val.map
      (lookupColumnRows vk.omega (poly (.lookupPermTable p l)) (u + 1)))
    (Finset.univ.val.map
      (lookupColumnRows vk.omega
        (lookupInputPolyOfResolver vk ch poly p l) (u + 1)))
    (Finset.univ.val.map
      (lookupColumnRows vk.omega
        (lookupTablePolyOfResolver vk ch poly p l) (u + 1)))
    ch.beta

theorem toPoly_resolverLookupProductDifferenceGamma
    {shape : CircuitShape} {k : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (l : Fin shape.numLookups) (u : ℕ) :
    resolverLookupProductDifferenceGamma vk ch poly p l u =
      CompPoly.CPolynomial.map (evalRingHom ch.beta)
        (resolverLookupProductDifference vk ch poly p l u) := by
  rw [resolverLookupProductDifferenceGamma, resolverLookupProductDifference,
    lookupProdDiffGamma_eq_map]

/-- One `γ` coefficient of the selected lookup difference, computed directly over `Fp`. -/
def resolverLookupProductDifferenceCoeff
    {shape : CircuitShape} {k : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (l : Fin shape.numLookups) (u j : ℕ) : CPoly :=
  lookupProdDiffCoeff
    (Finset.univ.val.map
      (lookupColumnRows vk.omega (poly (.lookupPermInput p l)) (u + 1)))
    (Finset.univ.val.map
      (lookupColumnRows vk.omega (poly (.lookupPermTable p l)) (u + 1)))
    (Finset.univ.val.map
      (lookupColumnRows vk.omega
        (lookupInputPolyOfResolver vk ch poly p l) (u + 1)))
    (Finset.univ.val.map
      (lookupColumnRows vk.omega
        (lookupTablePolyOfResolver vk ch poly p l) (u + 1)))
    j

theorem toPoly_resolverLookupProductDifferenceCoeff
    {shape : CircuitShape} {k : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (l : Fin shape.numLookups) (u j : ℕ) :
    resolverLookupProductDifferenceCoeff vk ch poly p l u j =
      coeff (resolverLookupProductDifference vk ch poly p l u) j := by
  rw [resolverLookupProductDifferenceCoeff, resolverLookupProductDifference]
  apply toPoly_lookupProdDiffCoeff

/-- All separately priced challenges used by the selected lookup endpoint, including the two
row-factor exclusions that eliminate its residual zero-product branch. -/
structure ResolverLookupGoodChallenges
    {shape : CircuitShape} {k : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (p : ℕ) (l : Fin shape.numLookups) (u : ℕ) : Prop where
  gamma : ch.gamma ∉ szBadSet (resolverLookupProductDifferenceGamma vk ch poly p l u)
  beta : ∀ j, ch.beta ∉ szBadSet (resolverLookupProductDifferenceCoeff vk ch poly p l u j)
  inputNonzero : ch.beta ∉ lookupColumnZeroBadSet vk.omega
    (lookupInputPolyOfResolver vk ch poly p l) (u + 1)
  tableNonzero : ch.gamma ∉ lookupColumnZeroBadSet vk.omega
    (lookupTablePolyOfResolver vk ch poly p l) (u + 1)

/-- Resolver-backed full constraint satisfaction enforces scalar membership for every usable row
of a selected compressed lookup.  Tuple recovery is intentionally downstream: it uses the Clean
operation's concrete input/table tuples and the separately priced `θ` collision exclusion. -/
theorem ConstraintSatisfaction.resolverLookupSubset
    {shape : CircuitShape} {numProofs k : ℕ} {G : Type*}
    (vk : VerifyingKey shape Fp G) (ch : Challenges k Fp)
    (poly : CommitmentId → CPoly)
    (sets : Fin numProofs → List (PermSetEval CPoly))
    (chunks : Fin numProofs →
      List (PermSetEval CPoly × List (CPoly × CPoly)))
    (l0 lLast lBlind : CPoly)
    (p : Fin numProofs) (l : Fin shape.numLookups) {n u : ℕ}
    (h : ConstraintSatisfaction
      (constraintModelOfResolver vk ch poly sets chunks l0 lLast lBlind) n)
    (hdom : ResolverLookupDomain vk l0 lLast lBlind n u)
    (hgood : ResolverLookupGoodChallenges vk ch poly p l u) :
    ∀ i : Fin (u + 1), ∃ j : Fin (u + 1),
      lookupColumnRows vk.omega
          (lookupInputPolyOfResolver vk ch poly p l) (u + 1) i =
        lookupColumnRows vk.omega
          (lookupTablePolyOfResolver vk ch poly p l) (u + 1) j := by
  have hdvd := h.lookupConstraintsDvdOfResolver
    vk ch poly sets chunks l0 lLast lBlind p l
  apply deployed_lookup_subset_of_nonzero_challenges
    vk.omega ch.beta ch.gamma
    (poly (.lookupProduct p l))
    (poly (.lookupPermInput p l))
    (poly (.lookupPermTable p l))
    (lookupInputPolyOfResolver vk ch poly p l)
    (lookupTablePolyOfResolver vk ch poly p l)
    l0 lLast lBlind hdvd hdom.omegaNonzero
  · intro i
    rw [← pow_mul, Nat.mul_comm, pow_mul, hdom.root, one_pow]
  · exact hdom.active
  · exact hdom.firstSelector
  · exact hdom.lastSelector
  · simpa [resolverLookupProductDifferenceGamma] using hgood.gamma
  · simpa [resolverLookupProductDifferenceCoeff] using hgood.beta
  · exact hgood.inputNonzero
  · exact hgood.tableNonzero

end Zcash.Snark
