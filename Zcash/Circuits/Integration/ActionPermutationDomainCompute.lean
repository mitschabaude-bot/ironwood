import Zcash.Snark.Keygen.Pipeline
import Zcash.Circuits.Action.TopLevel
import Zcash.Circuits.Integration.ActionGateCoherenceCompute
import Mathlib.Util.AssertNoSorry
import Zcash.Snark.Soundness.Canonical.PermutationInstantiation

/-!
# Closed computations for the Action permutation layout

This small module isolates the native computation certificates used by the semantic
Action permutation-domain package.  Every statement is against keygen data derived
from `actionCircuit`, never the captured verifying-key fixture.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (deltaFp)

open Zcash.Circuits.Action (actionCircuit)

namespace ActionPermutationDomain

/-- The circuit-derived Action domain exponent is within Pasta's supported range. -/
theorem domainExponent_lt :
    actionCircuit.domainExponent < 33 :=
  ActionGateCoherence.domainExponent_lt

theorem domainExponent_eq :
    actionCircuit.domainExponent = 11 := by
  native_decide

/-- The derived Action permutation columns form two full chunks and one singleton. -/
theorem chunks_eq :
    actionCircuit.verifierCS.permutationChunks =
      [[(.instance 0, 0), (.advice 0, 1), (.advice 1, 2),
          (.advice 2, 3), (.advice 3, 4), (.advice 4, 5),
          (.advice 5, 6)],
        [(.advice 6, 7), (.advice 7, 8), (.advice 8, 9),
          (.advice 9, 10), (.fixed 0, 11), (.fixed 7, 12),
          (.fixed 8, 13)],
        [(.fixed 9, 14)]] := by
  native_decide

/-- The Action permutation argument has 15 columns and verifier chunk width 7. -/
theorem columnCount_chunkLen_eq :
    (actionCircuit.permutationColumnCount,
        actionCircuit.chunkLen) =
      (15, 7) := by
  native_decide

def ColumnRefCoherent : ColumnRef → Prop
  | .advice i =>
      i < actionCircuit.adviceQueryLayout.length ∧
        (actionCircuit.adviceQueryLayout.getD i (0, 0)).2 = 0
  | .fixed i =>
      i < actionCircuit.fixedQueryLayout.length ∧
        (actionCircuit.fixedQueryLayout.getD i (0, 0)).2 = 0
  | .instance i =>
      i < actionCircuit.instanceQueryLayout.length ∧
        (actionCircuit.instanceQueryLayout.getD i (0, 0)).2 = 0

/-- Every Action permutation reference selects an in-range rotation-zero query and
every accompanying common-permutation index is in range. -/
theorem routingCoherent :
    ∀ chunk ∈
        actionCircuit.verifierCS.permutationChunks,
      ∀ ref ∈ chunk,
        ColumnRefCoherent ref.1 ∧
          ref.2 <
            actionCircuit.permutationColumnCount := by
  rw [chunks_eq]
  let chunks : List (List (ColumnRef × ℕ)) :=
    [[(.instance 0, 0), (.advice 0, 1), (.advice 1, 2),
        (.advice 2, 3), (.advice 3, 4), (.advice 4, 5),
        (.advice 5, 6)],
      [(.advice 6, 7), (.advice 7, 8), (.advice 8, 9),
        (.advice 9, 10), (.fixed 0, 11), (.fixed 7, 12),
        (.fixed 8, 13)],
      [(.fixed 9, 14)]]
  have hall :
      chunks.flatten.Forall fun ref =>
        ColumnRefCoherent ref.1 ∧
          ref.2 <
            actionCircuit.permutationColumnCount := by
    simp [chunks, ColumnRefCoherent]
    native_decide
  intro chunk hchunk ref href
  apply List.forall_iff_forall_mem.mp hall
  apply List.mem_flatten.mpr
  exact ⟨chunk, by simpa only [chunks] using hchunk, href⟩

/-- The first 21 powers of Pasta's permutation coset generator are distinct.
Twenty-one is `3 * 7`, the padded Action permutation-column range. -/
theorem deltaPowers_injective :
    Function.Injective fun j : Fin 21 => deltaFp ^ (j : ℕ) := by
  native_decide

assert_no_sorry domainExponent_lt
assert_no_sorry domainExponent_eq
assert_no_sorry chunks_eq
assert_no_sorry columnCount_chunkLen_eq
assert_no_sorry routingCoherent
assert_no_sorry deltaPowers_injective

end ActionPermutationDomain

end Zcash.Snark
