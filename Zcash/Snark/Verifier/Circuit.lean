import Zcash.Circuits.Integration.ExprRich
import Zcash.Snark.Verifier.Assemble
import Clean.Halo2.Keygen
import Clean.Halo2.TopLevel

/-!
# Circuit-owned verifier data

`Halo2.TopLevelCircuit.verifierCS` is the single Ironwood-native projection of a
closed Clean circuit. It translates the circuit's pinned expressions and permutation
columns into the types consumed by the verifier, without introducing proof parameters,
commitments, or a second source of circuit configuration.
-/

namespace Zcash.Snark

open Halo2

/-- The Ironwood-native constraint-system data consumed by the verifier. -/
structure VerifierCS (numLookups : ℕ) (F : Type*) where
  gates : List (Expr F)
  permutationChunks : List (List (ColumnRef × ℕ))
  lookupInputExprs : Fin numLookups → List (Expr F)
  lookupTableExprs : Fin numLookups → List (Expr F)

end Zcash.Snark

namespace Halo2.TopLevelCircuit

open Zcash.Snark
open Zcash.Arithmetic (Fp)

variable
    {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap}
    [ProvableType PublicInput]

/--
The circuit-owned verifier constraint system: Clean's pinned circuit data
translated once into Ironwood's expression and column-reference types.
-/
def verifierCS
    (top : TopLevelCircuit F Config PublicInput) :
    VerifierCS top.lookupCount F :=
  let pinned := top.pinnedCS
  let permutationReference : AnyColumn → ColumnRef := fun column =>
    match column.kind with
    | .advice =>
        .advice (pinned.adviceQueryLayout.findIdx
          (· = (column.index, 0)))
    | .fixed =>
        .fixed (pinned.fixedQueryLayout.findIdx
          (· = (column.index, 0)))
    | .instance =>
        .instance (pinned.instanceQueryLayout.findIdx
          (· = (column.index, 0)))
  { gates := pinned.gates.map RichExpression.toExpr
    permutationChunks :=
      ((top.permutationColumns.map
        permutationReference).zipIdx).toChunks top.chunkLen
    lookupInputExprs := fun lookup =>
      (pinned.lookupInputExprs.getD lookup.val []).map
        RichExpression.toExpr
    lookupTableExprs := fun lookup =>
      (pinned.lookupTableExprs.getD lookup.val []).map
        RichExpression.toExpr }

/-- The verifier CS translates the circuit-owned pinned gates. -/
@[simp] theorem verifierCS_gates
    (top : TopLevelCircuit F Config PublicInput) :
  top.verifierCS.gates =
      top.pinnedCS.gates.map RichExpression.toExpr := by
  simp only [verifierCS]

/-- The verifier CS translates one circuit-owned lookup input. -/
@[simp] theorem verifierCS_lookupInputExprs
    (top : TopLevelCircuit F Config PublicInput)
    (lookup : Fin top.lookupCount) :
    top.verifierCS.lookupInputExprs lookup =
      (top.pinnedCS.lookupInputExprs.getD lookup.val []).map
        RichExpression.toExpr := by
  simp only [verifierCS]

/-- The verifier CS translates one circuit-owned lookup table. -/
@[simp] theorem verifierCS_lookupTableExprs
    (top : TopLevelCircuit F Config PublicInput)
    (lookup : Fin top.lookupCount) :
    top.verifierCS.lookupTableExprs lookup =
      (top.pinnedCS.lookupTableExprs.getD lookup.val []).map
        RichExpression.toExpr := by
  simp only [verifierCS]

/--
The translated verifier gates evaluate exactly like the circuit's flattened Clean
gates under the circuit-owned selector map.
-/
theorem verifierCS_gates_eval
    (top : TopLevelCircuit F Config PublicInput)
    (fixed advice instanceFeed : ℕ → F) (valuation : Query → F)
    (hcoverage : ∀ expression ∈ flatGates top.constraintSystem,
      expression.selectorsCovered
        (fun index => (top.selectorMap.lookup index).isSome) = true)
    (hinterprets :
      Interprets top.gateQueryState
        fixed advice instanceFeed valuation)
    (index : ℕ)
    (hverifier : index < top.verifierCS.gates.length)
    (hsource : index < (flatGates top.constraintSystem).length) :
    Expr.eval fixed advice instanceFeed top.verifierCS.gates[index] =
      Expression.eval (substValuation top.selectorMap.lookup valuation)
        (flatGates top.constraintSystem)[index] := by
  have hpinned : index < top.pinnedCS.gates.length := by
    simpa only [top.verifierCS_gates, List.length_map] using hverifier
  have hderived :
      index <
        (PinnedConstraintSystem.derive
          top.constraintSystem top.selectorMap).gates.length := by
    simpa only [TopLevelCircuit.pinnedCS] using hpinned
  have hevaluation :=
    PinnedConstraintSystem.derive_gates_eval
      top.constraintSystem top.selectorMap fixed advice instanceFeed valuation
      hcoverage (by
        simpa only [TopLevelCircuit.gateQueryState] using hinterprets)
      index hderived hsource
  rw [List.getElem_of_eq top.verifierCS_gates hverifier,
    List.getElem_map, RichExpression.eval_toExpr]
  exact hevaluation

/-- Selector compression preserves the number of flattened circuit gates. -/
@[simp] theorem verifierCS_gates_length
    (top : TopLevelCircuit F Config PublicInput) :
    top.verifierCS.gates.length =
      (flatGates top.constraintSystem).length := by
  rw [top.verifierCS_gates, List.length_map]
  simpa only [TopLevelCircuit.pinnedCS] using
    PinnedConstraintSystem.derive_gates_length
      top.constraintSystem top.selectorMap

end Halo2.TopLevelCircuit
