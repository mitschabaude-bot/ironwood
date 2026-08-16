import Zcash.Circuits.Action.TopLevel
import Zcash.Circuits.Integration.FixedColumns
import Zcash.Circuits.Integration.ActionConstraintBounds
import Zcash.Snark.Keygen.Lagrange

/-!
# Action fixed-column coherence

This module specializes the generic fixed-commitment boundary to the Action circuit.
Sparse-to-dense fixed realization is supplied entirely by the generic compiler.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (derivedUrsGLagrange derivedUrsGLagrange_length omegaOf)

open Halo2
open Zcash.Circuits.Action (actionCircuit)

namespace ActionFixedCoherence

open Zcash.Snark.Keygen

variable {G : Type} [AddCommGroup G] [Module Fp G]
  [DecidableEq G] [Inhabited G]

/--
Construct the Action fixed-coherence package from generic Lagrange-basis setup facts.
Sparse-to-dense realization, query coverage, bounds, row shape, and query counts are
generic consequences
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

/--
Construct Action fixed coherence directly from the symbolically proved
Lagrange-basis FFT specification.
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

end ActionFixedCoherence

end Zcash.Snark
