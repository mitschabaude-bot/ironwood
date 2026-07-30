import Zcash.Snark.Keygen.Certificate
import Zcash.Snark.Keygen.Lagrange
import Zcash.Circuits.Integration.TopLevelInstanceCommitment
import Mathlib.Util.AssertNoSorry

/-!
# The captured instance commitments are the circuit-derived ones

The Action model uses the *circuit-derived* public-instance family
`actionCircuit.instanceCommitment actionProofParams capturedURS inputs` — commitments computed
from the public inputs, as halo2's `verify_proof` computes them from its `instances` argument. The
captured artifacts, meanwhile, are exercised
against the fixture's own family `Fixture.derivedInstanceCommitment` (the Fiat–Shamir fingerprint,
`assemble?`, the negative tests), which `instance_commitments_derived` pins to the captured points
`capturedInstanceCommitments` (ironwood#65/#85).

Nothing joined those two families, so the circuit model could not be instantiated at the captured
proof — the last open seam in sound handling of public instances (ironwood#86). This module closes it.

Two steps, and the first carries the weight:

* **The bases agree.** Halo2 commits public inputs against the Lagrange generators
  (`Fixture.commitLagrange`, `Params::commit_lagrange` under `Blind::default () = 1`), while the
  extractor works against the monomial URS. `commitLagrange_eq_commitInstance` identifies the
  captured computation with the abstract `LagrangeCommitmentKey.commitInstance` at `capturedURS`.
  It needs no new fixture check: the captured Lagrange prefix is already certified against the
  monomial derivation by `derivedUrsGLagrange_prefix_eq`, and `LagrangeCommitmentKey` is a
  subsingleton, so the key a downstream statement names is the key the certificate discharges.
* **The rows agree.** `capturedActionInputs` reads the captured public instances back as the
  circuit's own `PublicInputs` record, and `publicInputRows_capturedActionInputs` checks that the
  circuit's public-input serialization reproduces the captured column. That check is the only
  `native_decide` here, and it is a statement about ten field elements.
-/

namespace Zcash.Snark.Keygen

open Zcash.Arithmetic (derivedUrsGLagrange omegaOf)
open Zcash.Snark
open Zcash.Snark.Fixture
open Halo2
open Zcash.Circuits.Action

set_option maxHeartbeats 400000
set_option maxRecDepth 8000

/-! ## The captured Lagrange prefix as a commitment key -/

/-- **The captured Lagrange generators satisfy the commitment-key setup obligation.** Each exported
generator is the monomial commitment to its Lagrange row, which is exactly
`derivedUrsGLagrange_prefix_eq` (the certificate's prefix cross-check) composed with the closed-form
generator identity. -/
theorem capturedUrsGLagrange_prefix :
    ∀ i : Fin (2 ^ capturedURS.k), (i : ℕ) < capturedUrsGLagrange.length →
      capturedUrsGLagrange.getD (i : ℕ) 0 =
        commit capturedURS (polynomialCoefficients (2 ^ capturedURS.k)
          (rowPolynomial (omegaOf capturedURS.k) (Pi.single i 1))) := by
  intro i hi
  -- The exported prefix is a prefix of the derived basis, so the two agree entry by entry below
  -- its length.
  have hderived :
      capturedUrsGLagrange.getD (i : ℕ) 0
        = (derivedUrsGLagrange capturedURS).getD (i : ℕ) 0 := by
    conv_lhs => rw [← derivedUrsGLagrange_prefix_eq]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
  -- Below the prefix length the derived basis is nonempty there, which is what the closed-form
  -- setup lemma asks for.
  have hlen : (i : ℕ) < (derivedUrsGLagrange capturedURS).length := by
    have hprefix := congrArg List.length derivedUrsGLagrange_prefix_eq
    rw [List.length_take] at hprefix
    omega
  rw [hderived]
  exact ofPrefix_setup_of_closed capturedURS (by decide)
    (fun j => derivedUrsGLagrange_generator_eq capturedURS (by decide) j) i hlen

/-- The captured Lagrange commitment key: the exported prefix, completed by the canonical monomial
commitment beyond it. Every `LagrangeCommitmentKey capturedURS (omegaOf capturedURS.k)` equals this
one (`LagrangeCommitmentKey.instSubsingleton`). -/
noncomputable def capturedLagrangeKey :
    LagrangeCommitmentKey capturedURS (omegaOf capturedURS.k) :=
  LagrangeCommitmentKey.ofPrefix capturedURS (omegaOf capturedURS.k)
    capturedUrsGLagrange capturedUrsGLagrange_prefix

/-- **Halo2's captured `commit_lagrange` is the abstract Lagrange-key instance commitment.** The
captured computation sums canonical representatives against the exported generators and adds the
default blind `w`; the abstract one commits the zero-padded row vector against the key. They agree
for any column that fits inside the exported prefix — which every captured column does
(`capturedPublicInstances_within_lagrange`).

The key is universally quantified because `LagrangeCommitmentKey` records no choice: this discharges
the identity against whichever key a downstream statement names, once its domain generator is
recognised as the captured one. -/
theorem commitLagrange_eq_commitInstance {omega : Fp} (homega : omega = omegaOf capturedURS.k)
    (key : LagrangeCommitmentKey capturedURS omega)
    (values : List Fp) (hfit : values.length ≤ capturedUrsGLagrange.length) :
    commitLagrange values = key.commitInstance values 1 := by
  subst homega
  have hdomain : values.length ≤ 2 ^ capturedURS.k :=
    le_trans hfit (by decide)
  rw [Subsingleton.elim key capturedLagrangeKey, capturedLagrangeKey,
    LagrangeCommitmentKey.ofPrefix_commitInstance_eq capturedURS (omegaOf capturedURS.k)
      capturedUrsGLagrange capturedUrsGLagrange_prefix values 1 hfit hdomain,
    ← LagrangeCommitmentKey.commitPrefixNat_eq_commitPrefix,
    LagrangeCommitmentKey.commitPrefixNat, commitLagrange]
  -- Only the blind differs in spelling: halo2's default blind is `1`, and `(1 : Fp).val • w = w`.
  congr 1
  rw [show ((1 : Fp).val) = 1 from rfl, one_nsmul]

/-- A column whose every row reads zero commits to the blind alone. Used for the instance columns
the Action layout does not populate: the circuit serializes them as zeros, the capture omits them
entirely, and both commit to `w`. -/
theorem commitInstance_of_rows_zero {omega : Fp}
    (key : LagrangeCommitmentKey capturedURS omega)
    {values : List Fp} (hzero : ∀ i, values.getD i 0 = 0) (blind : Fp) :
    key.commitInstance values blind = blind • capturedURS.w := by
  rw [LagrangeCommitmentKey.commitInstance, LagrangeCommitmentKey.commitRows,
    show zeroPaddedRows (n := 2 ^ capturedURS.k) values = 0 from funext fun i => hzero (i : ℕ)]
  rw [show commitGen key.generators (0 : Fin (2 ^ capturedURS.k) → Fp) = 0 by
    simp [commitGen], zero_add]

/-! ## The captured public inputs as the circuit's own record -/

/-- **The captured public inputs, read back as the Action circuit's public-input record.** The
capture stores one flat column of ten field elements per proof
(`capturedPublicInstances`); the circuit's `PublicInputs` names those ten rows. -/
def capturedActionInputs : Fin Fixture.shape.numProofs → PublicInputs Fp := fun proofIndex =>
  let column := capturedPublicInstances.getD (proofIndex.val * capturedNumInstanceColumns) []
  { anchor := column.getD 0 0
    cvX := column.getD 1 0
    cvY := column.getD 2 0
    nfOld := column.getD 3 0
    rkX := column.getD 4 0
    rkY := column.getD 5 0
    cmx := column.getD 6 0
    enableSpend := column.getD 7 0
    enableOutput := column.getD 8 0
    disableCrossAddress := column.getD 9 0 }

/-- **The Action layout serializes its public input as exactly the element vector.** The layout
declares one instance column of ten rows, so `usedRows = 10` and each row index resolves to its own
cell — no zero padding and no reordering. -/
theorem publicInputRows_zero (input : PublicInputs Fp) :
    actionCircuit.publicInputRows input ⟨0⟩ = (toElements input).toList := by
  cases input
  rfl

/-- Every other instance column is serialized as ten zero rows: the layout declares no cell there,
so each row falls off the end of the element vector. -/
theorem publicInputRows_ne_zero (input : PublicInputs Fp) {column : ℕ} (hcolumn : column ≠ 0) :
    ∀ i, (actionCircuit.publicInputRows input ⟨column⟩).getD i 0 = 0 := by
  -- Every serialized entry looks its row up in the cell list, misses, and reads past the end of
  -- the element vector.
  have hzero : ∀ x ∈ actionCircuit.publicInputRows input ⟨column⟩, x = (0 : Fp) := by
    intro x hx
    rw [show actionCircuit.publicInputRows input ⟨column⟩ =
        (List.range PublicInputs.layout.usedRows).map (fun row =>
          (toElements input).toList.getD
            (PublicInputs.layout.cellList.idxOf ((⟨column⟩ : Column .instance), row)) 0) from rfl]
      at hx
    obtain ⟨row, -, rfl⟩ := List.mem_map.mp hx
    rw [List.idxOf_eq_length (by
      simp only [PublicInputs.layout, PublicInputLayout.cellList]
      simp
      intro _ hindex
      exact hcolumn hindex.symm)]
    have hlen : (toElements input).toList.length ≤ PublicInputs.layout.cellList.length := by
      simp only [PublicInputLayout.cellList_length, Vector.length_toList]
      exact le_refl _
    exact List.getD_eq_default _ _ hlen
  intro i
  rcases lt_or_ge i (actionCircuit.publicInputRows input ⟨column⟩).length with h | h
  · rw [List.getD_eq_getElem _ _ h]
    exact hzero _ (List.getElem_mem h)
  · exact List.getD_eq_default _ _ h

/-- **The captured column is the circuit's serialization of the captured record.** Ten field
elements, checked against the capture. -/
theorem publicInputRows_capturedActionInputs (proofIndex : Fin Fixture.shape.numProofs) :
    actionCircuit.publicInputRows (capturedActionInputs proofIndex) ⟨0⟩ =
      capturedPublicInstances.getD (proofIndex.val * capturedNumInstanceColumns) [] := by
  rw [publicInputRows_zero]
  fin_cases proofIndex
  native_decide

/-! ## The seam: the capstone's family is the captured one -/

/-- The keygen domain exponent is the captured URS's `k`, read off the certificate's `Shape`
component rather than by reducing `minimalKForRows`. -/
theorem actionCircuit_domainExponent : actionCircuit.domainExponent = capturedURS.k := by
  have h := congrArg Shape.k shape_eq_mergeDerived
  simp only [ProofParams.mergeDerived] at h
  rw [h]
  decide

/-- The derived verifying key's domain generator is the captured URS's, so a key stated at that key's
`omega` is a key at the captured domain. -/
theorem toVerifierKey_omega_captured :
    (actionCircuit.toVerifierKey actionProofParams capturedURS).omega = omegaOf capturedURS.k := by
  rw [TopLevelCircuit.toVerifierKey_omega, TopLevelCircuit.omega,
    actionCircuit_domainExponent]

/-- **The circuit-derived public-instance family is the fixture's.**
`actionCircuit.instanceCommitment` computes commitments from the public inputs the way halo2's
`verify_proof` computes them from `instances`. At the captured public inputs that family is
`Fixture.derivedInstanceCommitment`, the family the captured artifacts are exercised against.

This is the join that was missing (ironwood#86): the circuit model and capture now speak of the same
group elements. -/
theorem instanceCommitment_capturedActionInputs :
    actionCircuit.instanceCommitment actionProofParams capturedURS capturedActionInputs =
      Fixture.derivedInstanceCommitment := by
  funext proofIndex column
  show (actionCircuit.instanceCommitmentKey actionProofParams capturedURS).commitInstance
      (actionCircuit.publicInputRows (capturedActionInputs proofIndex) ⟨column⟩) 1 =
    commitLagrange
      (capturedPublicInstances.getD
        (proofIndex.val * capturedNumInstanceColumns + column) [])
  rcases eq_or_ne column 0 with rfl | hcolumn
  · -- The single populated column: the circuit's serialization is the captured column itself.
    rw [Nat.add_zero, publicInputRows_capturedActionInputs proofIndex,
      commitLagrange_eq_commitInstance toVerifierKey_omega_captured _ _
        (by fin_cases proofIndex; native_decide)]
  · -- Every other column: the circuit serializes zeros, the capture stores nothing, both give `w`.
    rw [commitInstance_of_rows_zero _ (publicInputRows_ne_zero _ hcolumn),
      List.getD_eq_default _ _ (by
        simp only [capturedPublicInstances, capturedNumInstanceColumns, List.length_cons,
          List.length_nil]
        omega),
      commitLagrange]
    simp

/-- **The circuit model's family is the captured commitment points.** Composing the seam with the
capture's own derivation (`instance_commitments_derived`, ironwood#65/#85): at the captured public
inputs, the circuit-derived commitments are exactly the points the deployed verifier used. -/
theorem instanceCommitment_eq_capturedInstanceCommitments
    (proofIndex : Fin Fixture.shape.numProofs) {column : ℕ}
    (hcolumn : column < capturedNumInstanceColumns) :
    actionCircuit.instanceCommitment actionProofParams capturedURS capturedActionInputs
        proofIndex column =
      capturedInstanceCommitments.getD
        (proofIndex.val * capturedNumInstanceColumns + column) 0 := by
  have hzero : column = 0 := by
    simpa only [capturedNumInstanceColumns, Nat.lt_one_iff] using hcolumn
  subst hzero
  rw [instanceCommitment_capturedActionInputs, ← instance_commitments_derived]
  fin_cases proofIndex
  have hlt : 0 < capturedPublicInstances.length := by
    simp only [capturedPublicInstances, List.length_cons]
    omega
  simp only [Fixture.derivedInstanceCommitment, List.getD_eq_getElem?_getD, List.getElem?_map,
    Nat.zero_mul, Nat.add_zero]
  rw [List.getElem?_eq_getElem hlt]
  rfl

assert_no_sorry commitLagrange_eq_commitInstance
assert_no_sorry publicInputRows_capturedActionInputs
assert_no_sorry instanceCommitment_capturedActionInputs
assert_no_sorry instanceCommitment_eq_capturedInstanceCommitments

end Zcash.Snark.Keygen
