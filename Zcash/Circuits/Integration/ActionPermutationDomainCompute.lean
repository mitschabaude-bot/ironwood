import Zcash.Snark.Keygen.Derivation
import Zcash.Snark.Soundness.PermutationInstantiation
import Zcash.Circuits.Integration.ActionGateCoherenceCompute

/-!
# Closed computations for the Action permutation layout

This small module isolates the native computation certificates used by the semantic
Action permutation-domain package.  Every statement is against keygen data derived
from `orchardActionTopLevelCircuit`, never the captured verifying-key fixture.
-/

namespace Zcash.Snark

open Zcash.Circuits.Action (orchardActionTopLevelCircuit)

namespace ActionPermutationDomain

/-- The circuit-derived Action domain exponent is within Pasta's supported range. -/
theorem domainExponent_lt :
    orchardActionTopLevelCircuit.domainExponent < 33 :=
  ActionGateCoherence.domainExponent_lt

theorem domainExponent_eq :
    orchardActionTopLevelCircuit.domainExponent = 11 := by
  native_decide

/-- The Action permutation argument has 15 columns and verifier chunk width 7. -/
theorem columnCount_chunkLen_eq :
    (orchardActionTopLevelCircuit.constraintSystem.permutationColumns.length,
        orchardActionTopLevelCircuit.constraintSystem.chunkLen) =
      (15, 7) := by
  native_decide

def ColumnRefCoherent : ColumnRef → Prop
  | .advice i =>
      i < orchardActionTopLevelCircuit.pinnedCS.adviceQueryLayout.length ∧
        (orchardActionTopLevelCircuit.pinnedCS.adviceQueryLayout.getD i (0, 0)).2 = 0
  | .fixed i =>
      i < orchardActionTopLevelCircuit.pinnedCS.fixedQueryLayout.length ∧
        (orchardActionTopLevelCircuit.pinnedCS.fixedQueryLayout.getD i (0, 0)).2 = 0
  | .instance i =>
      i < orchardActionTopLevelCircuit.pinnedCS.instanceQueryLayout.length ∧
        (orchardActionTopLevelCircuit.pinnedCS.instanceQueryLayout.getD i (0, 0)).2 = 0

/-- Executable form of one reference's L-classified routing obligations. -/
def routingCoherentBool (ref : ColumnRef × ℕ) : Bool :=
  match ref.1 with
  | .advice i =>
      decide (i < orchardActionTopLevelCircuit.pinnedCS.adviceQueryLayout.length) &&
      decide
        ((orchardActionTopLevelCircuit.pinnedCS.adviceQueryLayout.getD
          i (0, 0)).2 = 0) &&
      decide
        (ref.2 <
          orchardActionTopLevelCircuit.constraintSystem.permutationColumns.length)
  | .fixed i =>
      decide (i < orchardActionTopLevelCircuit.pinnedCS.fixedQueryLayout.length) &&
      decide
        ((orchardActionTopLevelCircuit.pinnedCS.fixedQueryLayout.getD
          i (0, 0)).2 = 0) &&
      decide
        (ref.2 <
          orchardActionTopLevelCircuit.constraintSystem.permutationColumns.length)
  | .instance i =>
      decide (i < orchardActionTopLevelCircuit.pinnedCS.instanceQueryLayout.length) &&
      decide
        ((orchardActionTopLevelCircuit.pinnedCS.instanceQueryLayout.getD
          i (0, 0)).2 = 0) &&
      decide
        (ref.2 <
          orchardActionTopLevelCircuit.constraintSystem.permutationColumns.length)

theorem routingCoherentBool_eq_true_iff (ref : ColumnRef × ℕ) :
    routingCoherentBool ref = true ↔
      ColumnRefCoherent ref.1 ∧
        ref.2 <
          orchardActionTopLevelCircuit.constraintSystem.permutationColumns.length := by
  rcases ref with ⟨ref, common⟩
  cases ref <;> simp [routingCoherentBool, ColumnRefCoherent]

/-- Compiled Action references that fail either query routing or global-index
bounds. This remains the L-classified routing diagnostic. -/
def routingFailures : List (ColumnRef × ℕ) :=
  (Keygen.permutationChunksOf orchardActionTopLevelCircuit.selectorMap
    orchardActionTopLevelCircuit.constraintSystem).flatten.filter fun ref =>
      !routingCoherentBool ref

theorem routingFailures_eq_nil : routingFailures = [] := by
  native_decide

/-- Every Action permutation reference selects an in-range rotation-zero query and
every accompanying common-permutation index is in range. -/
theorem routingCoherent :
    ∀ chunk ∈
        Keygen.permutationChunksOf orchardActionTopLevelCircuit.selectorMap
          orchardActionTopLevelCircuit.constraintSystem,
      ∀ ref ∈ chunk,
        ColumnRefCoherent ref.1 ∧
          ref.2 <
            orchardActionTopLevelCircuit.constraintSystem.permutationColumns.length := by
  intro chunk hchunk ref href
  by_contra hfailure
  have hmem :
      ref ∈ routingFailures := by
    rw [routingFailures, List.mem_filter]
    refine ⟨List.mem_flatten.mpr ⟨chunk, hchunk, href⟩, ?_⟩
    have hfalse : routingCoherentBool ref = false := by
      apply Bool.eq_false_of_not_eq_true
      exact fun htrue =>
        hfailure ((routingCoherentBool_eq_true_iff ref).mp htrue)
    simp [hfalse]
  rw [routingFailures_eq_nil] at hmem
  simp at hmem

/-- The first 21 powers of Pasta's permutation coset generator are distinct.
Twenty-one is `3 * 7`, the padded Action permutation-column range. -/
theorem deltaPowers_injective :
    Function.Injective fun j : Fin 21 => deltaFp ^ (j : ℕ) := by
  native_decide

assert_no_sorry domainExponent_lt
assert_no_sorry domainExponent_eq
assert_no_sorry columnCount_chunkLen_eq
assert_no_sorry routingFailures_eq_nil
assert_no_sorry routingCoherent
assert_no_sorry deltaPowers_injective

end ActionPermutationDomain

end Zcash.Snark
