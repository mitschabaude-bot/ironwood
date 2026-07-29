import Zcash.Snark.Soundness.AGM.PinnedRootWitness
import Zcash.Snark.Soundness.Composition.StraightLineDeployed

/-!
# The straight-line deployed family interface is inhabited

`PinnedRootWitness` exhibits `witnessDeployedRootFamily`, an executable inhabitant of the deployed
root interface at the degenerate witness shape.  This module extends it to the two stronger
interfaces layered above it:

* `ComputedDeployedConstraintFSFamily`, by an executable constraint-`x` stage.  The witness data's
  constraint difference is the zero polynomial — the shape has no proofs, so the combined
  constraint list is empty, and `n = 0` collapses the quotient term — so the stage returns the
  empty root set without reading the oracle at all.
* `ComputedStraightLineDeployedFSFamily`, additionally carrying the staged IPA trace.  The witness
  shape has no IPA rounds (`k = 0`), so the per-round trace obligations are vacuous.

That second point is this witness's limit: the interface is consistent and its constraint-`x`
stage concrete, but the IPA-round stages quantify over `Fin 0` and so go unexercised.
`Composition.ZeroStraightLine` is the model with live rounds, instantiated at captured key data by
`Fixtures.MultiAction.CapturedZeroFamily`, and it consumes the zero-coordinate keystone at the end
of this module.
-/

namespace Zcash.Snark

open scoped ENNReal

local instance vestaInhabitedStraightLineWitness : Inhabited VestaG := ⟨0⟩

/-! ## The constraint difference of the zero data vanishes -/

/-- **The witness constraint difference is the zero polynomial.**  The witness shape has no
proofs, so the folded constraint list is empty, and the zero key's `n = 0` collapses the
quotient-side product `q · (X^n - 1)`. -/
theorem deployedConstraintDifferencePreX_witness
    (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG)
    (coins : witnessDeployedRootFamily.toFamily.Coins) :
    deployedConstraintDifferencePreX witnessDeployedRootFamily basis coins = 0 := by
  unfold deployedConstraintDifferencePreX
  rw [committedPreXConstraintDifference_eq]
  have hn : (witnessDeployedRootFamily.vk basis).n = 0 := rfl
  rw [hn]
  simp [combineConstraints, constraintPolys, allConstraints, witnessShape]

/-- The witness family's constraint-`x` root set is empty on every oracle table. -/
theorem deployedConstraintXBadSet_witness
    (basis : AugmentedIndex (2 ^ witnessShape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen witnessShape witnessDeployedRootFamily.init.length 10 +
        3 * witnessShape.k) → Fp) :
    deployedConstraintXBadSet witnessDeployedRootFamily basis O = ∅ := by
  ext x
  simp only [deployedConstraintXBadSet, Set.mem_empty_iff_false, iff_false]
  intro hx
  rw [deployedConstraintDifferencePreX_witness basis O] at hx
  exact (mem_szBadSet.mp hx).1 rfl

/-! ## The executable constraint-`x` stage -/

/-- A fully executable staged constraint-`x` trace for the witness family: the root set is empty,
so the stage returns it without any oracle read — freshness of the `x` squeeze is immediate. -/
def witnessConstraintXTrace :
    DeployedConstraintXOnlineTrace witnessDeployedRootFamily where
  stage := fun _basis => .pure (∅ : Set Fp)
  agrees := fun basis O => by
    rw [OracleComp.run_pure, deployedConstraintXBadSet_witness basis O]
  fresh := fun _basis _O => List.not_mem_nil

/-- **An inhabitant of the deployed constraint family interface.**  The root family's six staged
root computations extend with the executable constraint-`x` stage, so exact `x` pinning is derived
rather than assumed. -/
def witnessDeployedConstraintFamily : ComputedDeployedConstraintFSFamily witnessShape :=
  .ofRoot witnessDeployedRootFamily witnessConstraintXTrace

/-! ## The straight-line family -/

/-- The staged IPA trace of the witness family.  The witness shape has no IPA rounds, so every
obligation quantifies over `Fin 0`. -/
def witnessStraightLineIpaTrace : StraightLineIpaOnlineTrace witnessFamily where
  stage := fun _ j => j.elim0
  agrees := fun _ j => j.elim0
  fresh := fun _ j => j.elim0

/-- **An inhabitant of the straight-line deployed family interface**: the witness root family,
its executable constraint-`x` stage, and the (round-free) staged IPA trace. -/
def witnessStraightLineDeployedFamily : ComputedStraightLineDeployedFSFamily witnessShape where
  toComputedDeployedRootFSFamily := witnessDeployedRootFamily
  ipaTrace := witnessStraightLineIpaTrace
  constraintXTrace := witnessConstraintXTrace

/-! ## Zero-coordinate IPA walks, at any shape

The witness shape has no IPA rounds, so its staged trace is vacuous.  The lemmas below are the
shape-generic keystone a captured-shape constant family will need instead: a proof whose aggregate
and round coordinates vanish walks the zero discrepancy, so every straight-line IPA root
polynomial — at any `k`, for every challenge vector — is the zero polynomial, and
`stage := pure 0` satisfies `agrees` and `fresh` outright.
-/

/-- The discrepancy quadratic of the zero state over a zero round is the zero polynomial. -/
theorem ipaDiscrepancyPolynomial_zero :
    ipaDiscrepancyPolynomial 0 (0, 0) = 0 := by
  simp [ipaDiscrepancyPolynomial]

/-- The zero discrepancy stays zero across a zero round, for every challenge. -/
theorem ipaDiscrepancyStep_zero (c : Fp) : ipaDiscrepancyStep 0 (0, 0) c = 0 := by
  simp [ipaDiscrepancyStep]

/-- Every prefix-selected polynomial of the zero walk over all-zero rounds is zero. -/
theorem ipaDiscrepancyPolynomialAt_zero :
    ∀ (rounds : List (Fp × Fp)) (challenges : List Fp) (j : ℕ),
      (∀ r ∈ rounds, r = (0, 0)) →
      ipaDiscrepancyPolynomialAt 0 rounds challenges j = 0
  | [], challenges, j, _ => by
      cases challenges <;> cases j <;> rfl
  | _round :: _rounds, [], _j, _ => rfl
  | round :: rounds, c :: challenges, 0, h => by
      rw [ipaDiscrepancyPolynomialAt, h round List.mem_cons_self]
      exact ipaDiscrepancyPolynomial_zero
  | round :: rounds, c :: challenges, j + 1, h => by
      rw [ipaDiscrepancyPolynomialAt, h round List.mem_cons_self, ipaDiscrepancyStep_zero]
      exact ipaDiscrepancyPolynomialAt_zero rounds challenges j
        (fun r hr => h r (List.mem_cons_of_mem _ hr))

/-- Any constant survives a zero round, for every challenge. -/
theorem ipaDiscrepancyStep_const (v c : Fp) : ipaDiscrepancyStep v (0, 0) c = v := by
  simp [ipaDiscrepancyStep]

/-- Every in-range prefix-selected polynomial of the constant walk over all-zero rounds is
`C v * X`: the round terms contribute nothing, so only the linear discrepancy term remains. -/
theorem ipaDiscrepancyPolynomialAt_const (v : Fp) :
    ∀ (rounds : List (Fp × Fp)) (challenges : List Fp) (j : ℕ),
      (∀ r ∈ rounds, r = (0, 0)) → j < rounds.length → j < challenges.length →
      ipaDiscrepancyPolynomialAt v rounds challenges j = Polynomial.C v * Polynomial.X
  | [], _, j, _, hj, _ => absurd hj (Nat.not_lt_zero j)
  | _round :: _rounds, [], j, _, _, hj => absurd hj (Nat.not_lt_zero j)
  | round :: _rounds, _c :: _challenges, 0, h, _, _ => by
      rw [ipaDiscrepancyPolynomialAt, h round List.mem_cons_self]
      simp [ipaDiscrepancyPolynomial]
  | round :: rounds, c :: challenges, j + 1, h, hr, hc => by
      rw [ipaDiscrepancyPolynomialAt, h round List.mem_cons_self, ipaDiscrepancyStep_const]
      exact ipaDiscrepancyPolynomialAt_const v rounds challenges j
        (fun r hr' => h r (List.mem_cons_of_mem _ hr'))
        (Nat.lt_of_succ_lt_succ hr) (Nat.lt_of_succ_lt_succ hc)

/-- **A zero-coordinate proof pins the zero polynomial at every IPA round.**  The hypotheses are
exactly the coordinates a constant zero-data prover declares: zero aggregate witness and `U`
components, zero blinding vector, zero multiopen value, and zero round-point coordinates. -/
theorem straightLineIpaRootPolynomial_of_zero_coordinates
    {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → ℕ → VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 → Fp)
    (chi : Fin shape.k → Fp)
    (haMulti : p.aMulti nu = 0) (hmultiU : p.multiU nu = 0)
    (hs : p.s = 0) (hsU : p.sU = 0)
    (hvalue : multiopenValue vk instanceCommitment p.proof.1 (chRecord nu (fun _ => 0)) = 0)
    (hrounds : ∀ j, (p.rounds j).1.gPart = 0 ∧
      (p.rounds j).1.coeffs AugmentedIndex.u = 0 ∧
      (p.rounds j).2.gPart = 0 ∧
      (p.rounds j).2.coeffs AugmentedIndex.u = 0)
    (j : Fin shape.k) :
    p.straightLineIpaRootPolynomial nu chi j = 0 := by
  have hinit : p.straightLineInitialDiscrepancy nu = 0 := by
    rw [p.straightLineInitialDiscrepancy_eq nu, haMulti, hmultiU, hs, hsU, hvalue]
    simp [innerProduct]
  have hdisc : ∀ r ∈ p.straightLineRoundDiscrepancies nu, r = (0, 0) := by
    intro r hr
    unfold AlgebraicWfProof.straightLineRoundDiscrepancies at hr
    obtain ⟨pair, hpair, hrEq⟩ := List.mem_map.mp hr
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hpair
    subst hrEq
    subst hi
    obtain ⟨hg1, hu1, hg2, hu2⟩ := hrounds i
    simp [representedRoundDiscrepancy, representedPointDiscrepancy, hg1, hu1, hg2, hu2,
      innerProduct]
  rw [AlgebraicWfProof.straightLineIpaRootPolynomial, hinit]
  exact ipaDiscrepancyPolynomialAt_zero _ _ _ hdisc

/-- The initial discrepancy of a zero-coordinate prover is `-(ν₁₀ · v)`: only the multiopen
value survives when the aggregate witness, its `U` component, and the blinding vector vanish. -/
theorem straightLineInitialDiscrepancy_of_zero_coordinates
    {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 → Fp)
    (haMulti : p.aMulti nu = 0) (hmultiU : p.multiU nu = 0)
    (hs : p.s = 0) (hsU : p.sU = 0) :
    p.straightLineInitialDiscrepancy nu =
      -(nu 10 * multiopenValue vk instanceCommitment p.proof.1
        (chRecord nu (fun _ => 0))) := by
  rw [p.straightLineInitialDiscrepancy_eq nu, haMulti, hmultiU, hs, hsU]
  simp [innerProduct]

/-- **A zero-group-coordinate proof walks a constant discrepancy.**  With sub-proofs the
multiopen value is not zero, so the zero-coordinate keystone above does not apply; but the
rounds still contribute nothing, and every straight-line IPA root polynomial is the linear
`C (initial discrepancy) * X`.  The `numProofs = 0` keystone is the special case where that
constant vanishes. -/
theorem straightLineIpaRootPolynomial_of_zero_group_coordinates
    {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment) (nu : Fin 11 → Fp)
    (chi : Fin shape.k → Fp)
    (hrounds : ∀ j, (p.rounds j).1.gPart = 0 ∧
      (p.rounds j).1.coeffs AugmentedIndex.u = 0 ∧
      (p.rounds j).2.gPart = 0 ∧
      (p.rounds j).2.coeffs AugmentedIndex.u = 0)
    (j : Fin shape.k) :
    p.straightLineIpaRootPolynomial nu chi j =
      Polynomial.C (p.straightLineInitialDiscrepancy nu) * Polynomial.X := by
  have hdisc : ∀ r ∈ p.straightLineRoundDiscrepancies nu, r = (0, 0) := by
    intro r hr
    unfold AlgebraicWfProof.straightLineRoundDiscrepancies at hr
    obtain ⟨pair, hpair, hrEq⟩ := List.mem_map.mp hr
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hpair
    subst hrEq
    subst hi
    obtain ⟨hg1, hu1, hg2, hu2⟩ := hrounds i
    simp [representedRoundDiscrepancy, representedPointDiscrepancy, hg1, hu1, hg2, hu2,
      innerProduct]
  rw [AlgebraicWfProof.straightLineIpaRootPolynomial]
  refine ipaDiscrepancyPolynomialAt_const _ _ _ _ hdisc ?_ ?_
  · simp [AlgebraicWfProof.straightLineRoundDiscrepancies]
  · simp

end Zcash.Snark
