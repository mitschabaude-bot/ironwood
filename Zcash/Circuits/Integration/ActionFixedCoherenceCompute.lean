import Zcash.Circuits.Action.TopLevel
import Zcash.Circuits.Integration.FixedColumns
import Zcash.Circuits.Integration.ActionPermutationDomainCompute
import Zcash.Snark.Keygen.FftSpec

/-!
# Interim closed computations for Action fixed-column coherence

These certificates unblock the Action integration while the generic layout
compiler is being equipped with structural consistency theorems.  They are
deliberately finite failure-list checks rather than opaque proofs of the final
coherence record.

Both checks are **INTERIM**:

* query coverage should follow from query registration;
* fixed realization should be decomposed across region cell-disjointness,
  region-local writes, tables, constants, selector packing, and generic
  last-write/dedup/scatter semantics.

Delete these computations once those compiler theorems construct the same facts.
-/

namespace Zcash.Snark

open Halo2
open Zcash.Circuits.Action (orchardActionTopLevelCircuit)

namespace ActionFixedCoherence

open Zcash.Snark.Keygen Polynomial

/--
**INTERIM:** every Action fixed column currently requested by
`TopLevelFixedCoherence` occurs in its compiler-derived fixed-query layout.
-/
theorem queryCoverageFailures_eq_nil :
    interimFixedQueryCoverageFailures orchardActionTopLevelCircuit = [] := by
  native_decide

/-- Query coverage extracted from the finite interim diagnostic. -/
theorem queryLayout :
    ∀ column,
      column < orchardActionTopLevelCircuit.pinnedCS.numFixedColumns →
        ∃ rotation,
          (column, rotation) ∈
            orchardActionTopLevelCircuit.pinnedCS.fixedQueryLayout :=
  fixedQueryCoverage_of_interimFailures_eq_nil
    orchardActionTopLevelCircuit queryCoverageFailures_eq_nil

/--
**INTERIM:** the final dense Action fixed rows realize every table, region-fixed,
and packed-selector entry consumed by Clean constraint semantics.
-/
theorem realizationFailures_eq_nil :
    interimFixedRealizationFailures orchardActionTopLevelCircuit = [] := by
  native_decide

/-- Sparse-to-dense realization extracted from the finite interim diagnostic. -/
theorem realizes :
    ∀ column row value,
      (column, row, value) ∈
          topLevelRequiredFixedEntries orchardActionTopLevelCircuit →
        row < 2 ^ orchardActionTopLevelCircuit.domainExponent ∧
          column <
            orchardActionTopLevelCircuit.pinnedCS.numFixedColumns ∧
          (orchardActionTopLevelCircuit.fixedRows.getD column []).getD row 0 =
            (value : Fp) :=
  fixedRowsRealize_of_interimFailures_eq_nil
    orchardActionTopLevelCircuit realizationFailures_eq_nil

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

/--
Construct the Action fixed-coherence package from generic Lagrange-basis setup
facts.  Query coverage and sparse-to-dense realization are discharged by the two
interim certificates above; row shape, commitments, and query counts remain
generic consequences of `TopLevelCircuit.toVerifierKey`.

The remaining `hgenerators` premise is about the supplied URS, not the Action
circuit layout.
-/
noncomputable def ofKeygen
    (pp : ProofParams) (urs : URS G)
    (hk : orchardActionTopLevelCircuit.domainExponent = urs.k)
    (hlen : (derivedUrsGLagrange urs).length = 2 ^ urs.k)
    (hgenerators : ∀ i : Fin (2 ^ urs.k),
      (derivedUrsGLagrange urs).getD (i : ℕ) 0 =
        commit urs (polynomialCoefficients (2 ^ urs.k)
          (rowPolynomial
            (orchardActionTopLevelCircuit.toVerifierKey pp urs).omega
            (Pi.single i (1 : Fp))))) :
    TopLevelFixedCoherence orchardActionTopLevelCircuit pp urs :=
  TopLevelFixedCoherence.ofKeygen
    orchardActionTopLevelCircuit pp urs hk hlen hgenerators
    (by
      intro column hcolumn
      rw [orchardActionTopLevelCircuit.toVerifierKey_fixedQueryLayout_derived]
      exact queryLayout column hcolumn)
    (by
      intro column row value hentry
      exact realizes column row value hentry)

/--
Construct Action fixed coherence directly from the symbolically proved
Lagrange-basis FFT specification. The only remaining computations are the
prominently interim layout failure lists above.
-/
noncomputable def ofDerived
    (pp : ProofParams) (urs : URS G)
    (hk : orchardActionTopLevelCircuit.domainExponent = urs.k) :
    TopLevelFixedCoherence orchardActionTopLevelCircuit pp urs := by
  have hkUrs : urs.k ≤ 32 := by
    rw [← hk]
    exact Nat.le_of_lt_succ ActionPermutationDomain.domainExponent_lt
  have homega :
      (orchardActionTopLevelCircuit.toVerifierKey pp urs).omega =
        omegaOf urs.k := by
    change
      omegaOf orchardActionTopLevelCircuit.domainExponent =
        omegaOf urs.k
    rw [hk]
  apply ofKeygen pp urs hk (Keygen.derivedUrsGLagrange_length urs)
  intro i
  simpa only [homega] using
    Keygen.ofPrefix_setup_of_closed urs hkUrs
      (Keygen.derivedUrsGLagrange_generator_eq urs hkUrs) i
      (by
        rw [Keygen.derivedUrsGLagrange_length]
        exact i.isLt)

assert_no_sorry queryCoverageFailures_eq_nil
assert_no_sorry queryLayout
assert_no_sorry realizationFailures_eq_nil
assert_no_sorry realizes
assert_no_sorry ofDerived

end ActionFixedCoherence

end Zcash.Snark
