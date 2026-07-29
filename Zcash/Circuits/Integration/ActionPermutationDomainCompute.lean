import Zcash.Snark.Keygen.Derivation
import Zcash.Snark.Soundness.Canonical.PermutationInstantiation
import Zcash.Circuits.Integration.ActionGateCoherenceCompute

/-!
# Closed computations for the Action permutation layout

This small module isolates the native computation certificates used by the semantic
Action permutation-domain package.  Every statement is against keygen data derived
from `actionCircuit`, never the captured verifying-key fixture.
-/

namespace Zcash.Snark

open Zcash.Circuits.Action (actionCircuit)

namespace ActionPermutationDomain

/-- The circuit-derived Action domain exponent is within Pasta's supported range. -/
theorem domainExponent_lt :
    actionCircuit.domainExponent < 33 :=
  ActionGateCoherence.domainExponent_lt

def ColumnRefCoherent : ColumnRef → Prop
  | .advice i =>
      i < actionCircuit.pinnedCS.adviceQueryLayout.length ∧
        (actionCircuit.pinnedCS.adviceQueryLayout.getD i (0, 0)).2 = 0
  | .fixed i =>
      i < actionCircuit.pinnedCS.fixedQueryLayout.length ∧
        (actionCircuit.pinnedCS.fixedQueryLayout.getD i (0, 0)).2 = 0
  | .instance i =>
      i < actionCircuit.pinnedCS.instanceQueryLayout.length ∧
        (actionCircuit.pinnedCS.instanceQueryLayout.getD i (0, 0)).2 = 0

/-- Executable form of one reference's L-classified routing obligations. -/
def routingCoherentBool (ref : ColumnRef × ℕ) : Bool :=
  match ref.1 with
  | .advice i =>
      decide (i < actionCircuit.pinnedCS.adviceQueryLayout.length) &&
      decide
        ((actionCircuit.pinnedCS.adviceQueryLayout.getD
          i (0, 0)).2 = 0) &&
      decide
        (ref.2 <
          actionCircuit.constraintSystem.permutationColumns.length)
  | .fixed i =>
      decide (i < actionCircuit.pinnedCS.fixedQueryLayout.length) &&
      decide
        ((actionCircuit.pinnedCS.fixedQueryLayout.getD
          i (0, 0)).2 = 0) &&
      decide
        (ref.2 <
          actionCircuit.constraintSystem.permutationColumns.length)
  | .instance i =>
      decide (i < actionCircuit.pinnedCS.instanceQueryLayout.length) &&
      decide
        ((actionCircuit.pinnedCS.instanceQueryLayout.getD
          i (0, 0)).2 = 0) &&
      decide
        (ref.2 <
          actionCircuit.constraintSystem.permutationColumns.length)

theorem routingCoherentBool_eq_true_iff (ref : ColumnRef × ℕ) :
    routingCoherentBool ref = true ↔
      ColumnRefCoherent ref.1 ∧
        ref.2 <
          actionCircuit.constraintSystem.permutationColumns.length := by
  rcases ref with ⟨ref, common⟩
  cases ref <;> simp [routingCoherentBool, ColumnRefCoherent]

/-- Compiled Action references that fail either query routing or global-index
bounds. This remains the L-classified routing diagnostic. -/
def routingFailures : List (ColumnRef × ℕ) :=
  (Keygen.permutationChunksOf
          actionCircuit.pinnedCS actionCircuit.constraintSystem.chunkLen).flatten.filter fun ref =>
      !routingCoherentBool ref

theorem routingFailures_eq_nil : routingFailures = [] := by
  native_decide

/-- Every Action permutation reference selects an in-range rotation-zero query and
every accompanying common-permutation index is in range. -/
theorem routingCoherent :
    ∀ chunk ∈
        Keygen.permutationChunksOf
          actionCircuit.pinnedCS actionCircuit.constraintSystem.chunkLen,
      ∀ ref ∈ chunk,
        ColumnRefCoherent ref.1 ∧
          ref.2 <
            actionCircuit.constraintSystem.permutationColumns.length := by
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

assert_no_sorry domainExponent_lt
assert_no_sorry routingFailures_eq_nil
assert_no_sorry routingCoherent

end ActionPermutationDomain

end Zcash.Snark
