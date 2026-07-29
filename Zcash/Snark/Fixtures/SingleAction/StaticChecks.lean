import Zcash.Snark.Fixtures.SingleAction.Fixture
import Zcash.Snark.Soundness.Composition.DeployedConstraintContainment
import Zcash.Snark.Soundness.DegreeWalk

/-!
# The single-Action captured key's static checks and degree budget

The Action-level capstone lives at the circuit-derived shape — one Action proof — whose captured
twin is this directory's fixture.  The twelve decided facts below mirror
`Fixtures.MultiAction.{StaticChecks, Degree}` at that key: the query layouts cover the shape's
counts, `ω` has order dividing `n`, `n` does not vanish in `𝔽`, and the degree caps that price
the `x`-squeeze schedule at `D = Dq = 20470`.
-/

namespace Zcash.Snark.Fixture

open Zcash.Snark

/-- The captured advice query layout covers the shape's advice query count. -/
theorem vk_advice_layout_length : shape.numAdviceQueries ≤ vk.adviceQueryLayout.length := by
  native_decide

/-- The captured instance query layout covers the shape's instance query count. -/
theorem vk_instance_layout_length :
    shape.numInstanceQueries ≤ vk.instanceQueryLayout.length := by
  native_decide

/-- The captured fixed query layout covers the shape's fixed query count. -/
theorem vk_fixed_layout_length : shape.numFixedQueries ≤ vk.fixedQueryLayout.length := by
  native_decide

/-- The captured `ω` has order dividing `n`. -/
theorem vk_omega_order : vk.omega ^ vk.n = 1 := by
  native_decide

/-- The captured domain size does not vanish in the scalar field. -/
theorem vk_n_cast_ne_zero : ((vk.n : ℕ) : Fp) ≠ 0 := by
  native_decide

/-- Every captured gate clears the degree cap at `B = 2047`. -/
theorem vk_gates_degree_le : ∀ e ∈ vk.gates, e.degreeBound * 2047 ≤ 20470 := by
  native_decide

/-- Every captured permutation chunk has width at most `7`. -/
theorem vk_chunk_width_le : ∀ c ∈ vk.permutationChunks, c.length ≤ 7 := by
  native_decide

/-- Every captured lookup input expression clears the compression cap. -/
theorem vk_lookup_input_degree_le : ∀ l : Fin shape.numLookups,
    ∀ e ∈ vk.lookupInputExprs l, e.degreeBound * 2047 ≤ 8188 := by
  native_decide

/-- Every captured lookup table expression clears the compression cap. -/
theorem vk_lookup_table_degree_le : ∀ l : Fin shape.numLookups,
    ∀ e ∈ vk.lookupTableExprs l, e.degreeBound * 2047 ≤ 8188 := by
  native_decide

/-- The captured quotient tail fits the budget. -/
theorem vk_quotient_tail_le :
    vk.n * shape.numQuotientPieces + (2 ^ shape.k - 1) ≤ 20470 := by
  native_decide

/-- The captured `n − 1` fits the opening degree. -/
theorem vk_n_pred_le : vk.n - 1 ≤ 2047 := by
  native_decide

/-- The captured opening degree: `2^k − 1 ≤ 2047`. -/
theorem shape_k_pred_le : 2 ^ shape.k - 1 ≤ 2047 := by
  native_decide

end Zcash.Snark.Fixture
