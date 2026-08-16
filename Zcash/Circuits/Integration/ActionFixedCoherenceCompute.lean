import Zcash.Circuits.Action.TopLevel
import Zcash.Circuits.Integration.FixedColumns
import Zcash.Circuits.Integration.ActionConstraintBounds
import Zcash.Snark.Keygen.Lagrange
import Mathlib.Util.AssertNoSorry

/-!
# Interim closed computation for Action fixed-column realization

This certificate unblocks the Action integration while the generic layout compiler
is being equipped with structural consistency theorems. It is deliberately a finite
failure-list check rather than an opaque proof of the final coherence record.

It is **INTERIM**: fixed realization should be decomposed across region cell-disjointness,
  region-local writes, tables, constants, selector packing, and generic
  last-write/dedup/scatter semantics.

Delete this computation once those compiler theorems construct the same fact.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (derivedUrsGLagrange derivedUrsGLagrange_length omegaOf)

open Halo2
open Zcash.Circuits.Action (actionCircuit)

namespace ActionFixedCoherence

open Zcash.Snark.Keygen

/--
**INTERIM:** the final dense Action fixed rows realize every table, region-fixed,
and packed-selector entry consumed by Clean constraint semantics.
-/
theorem realizationFailures_eq_nil :
    interimFixedRealizationFailures actionCircuit = [] := by
  native_decide

/-- Sparse-to-dense realization extracted from the finite interim diagnostic. -/
theorem realizes :
    ∀ column row value,
      (column, row, value) ∈
          topLevelRequiredFixedEntries actionCircuit →
        row < actionCircuit.n ∧
          column <
            actionCircuit.pinnedCS.numFixedColumns ∧
          (actionCircuit.fixedRows.getD column []).getD row 0 =
            value :=
  fixedRowsRealize_of_interimFailures_eq_nil
    actionCircuit realizationFailures_eq_nil

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

/--
Construct the Action fixed-coherence package from generic Lagrange-basis setup facts.
Sparse-to-dense realization is discharged by the interim certificate above; query
coverage, bounds, row shape, commitments, and query counts are generic consequences
of the top-level circuit and `TopLevelCircuit.toVerifierKey`.

The remaining `hgenerators` premise is about the supplied URS, not the Action
circuit layout.
-/
def ofKeygen
    (urs : URS G)
    (hk : actionCircuit.domainExponent = urs.k)
    (hlen : (derivedUrsGLagrange urs).length = 2 ^ urs.k)
    (hgenerators : ∀ i : Fin (2 ^ urs.k),
      (derivedUrsGLagrange urs).getD (i : ℕ) 0 =
        commit urs (polynomialCoefficients (2 ^ urs.k)
          (rowPolynomial
            actionCircuit.omega
            (Pi.single i (1 : Fp))))) :
    TopLevelFixedCoherence actionCircuit urs :=
  TopLevelFixedCoherence.ofKeygen
    actionCircuit urs hk hlen hgenerators
    (by
      intro column row value hentry
      exact realizes column row value hentry)

/--
Construct Action fixed coherence directly from the symbolically proved
Lagrange-basis FFT specification. The only remaining computation is the prominently
interim realization failure list above.
-/
def ofDerived
    (urs : URS G)
    (hk : actionCircuit.domainExponent = urs.k) :
    TopLevelFixedCoherence actionCircuit urs := by
  have hkUrs : urs.k ≤ 32 := by
    rw [← hk]
    exact Nat.le_of_lt_succ ActionConstraintBounds.domainExponent_lt
  have homega :
      actionCircuit.omega = omegaOf urs.k := by
    simp only [TopLevelCircuit.omega, hk]
  apply ofKeygen urs hk (derivedUrsGLagrange_length urs)
  intro i
  simpa only [homega] using
    Keygen.ofPrefix_setup_of_closed urs hkUrs
      (Keygen.derivedUrsGLagrange_generator_eq urs hkUrs) i
      (by
        rw [derivedUrsGLagrange_length]
        exact i.isLt)

assert_no_sorry realizationFailures_eq_nil
assert_no_sorry realizes
assert_no_sorry ofDerived

end ActionFixedCoherence

end Zcash.Snark
