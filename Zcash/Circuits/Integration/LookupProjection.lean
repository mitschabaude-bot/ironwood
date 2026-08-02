import Zcash.Snark.Keygen.Pipeline
import Zcash.Circuits.Integration.OperationLookups
import Zcash.Circuits.Integration.ResolverQueryEnvironment

/-!
# Lookup projection across the Clean boundary

Key generation substitutes the circuit's virtual selectors, then resolves each
configured `LookupArgument` against the authoritative compiler-derived query layout.
This module proves the semantic part of that translation for one selected lookup.

The result deliberately stops at the selector-substitution valuation. A lookup
activation needs the stronger row fact that its complex selectors have their exact
zero/one values; unlike a custom gate, an arbitrary nonzero selector scale is not
enough for tuple membership.
-/

namespace Zcash.Snark

open Halo2

set_option maxHeartbeats 20000

/-- Project one lookup directly through a top-level circuit's owned compilation. -/
theorem _root_.Halo2.TopLevelCircuit.lookup_eval
    {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput)
    (fixed advice instanceFeed : ℕ → F) (valuation : Query → F)
    (lookup : Fin top.lookupCount)
    (hinputCoverage :
      ∀ expression ∈ top.constraintSystem.lookups[lookup.val].inputs,
        expression.selectorsCovered
          (fun selector => (top.selectorMap.lookup selector).isSome) = true)
    (htableCoverage :
      ∀ expression ∈ top.constraintSystem.lookups[lookup.val].tables,
        expression.selectorsCovered
          (fun selector => (top.selectorMap.lookup selector).isSome) = true)
    (hinterprets :
      Interprets (pinnedQueryState top.pinnedCS)
        fixed advice instanceFeed valuation) :
    ((top.pinnedCS.lookupInputExprs.getD lookup.val []).map
        (RichExpression.eval fixed advice instanceFeed) =
      top.constraintSystem.lookups[lookup.val].inputs.map
        (Expression.eval
          (substValuation top.selectorMap.lookup valuation))) ∧
    ((top.pinnedCS.lookupTableExprs.getD lookup.val []).map
        (RichExpression.eval fixed advice instanceFeed) =
      top.constraintSystem.lookups[lookup.val].tables.map
        (Expression.eval
          (substValuation top.selectorMap.lookup valuation))) := by
  let argument := top.constraintSystem.lookups[lookup.val]
  have hargument : argument ∈ top.constraintSystem.lookups :=
    List.getElem_mem lookup.isLt
  have hresolved := top.lookupQueriesResolved argument hargument
  have hinterpretsGate :
      Interprets top.gateQueryState
        fixed advice instanceFeed valuation := by
    rw [← top.pinnedQueryState_eq_gateQueryState]
    exact hinterprets
  have hinputFree :
      ∀ expression ∈ argument.inputs.map
          (substSelectorMap top.selectorMap.lookup),
        expression.SelectorFree := by
    intro expression hexpression
    obtain ⟨source, hsource, hexpression⟩ := List.mem_map.mp hexpression
    subst expression
    exact (substSelectorMap_selectorFree _ source).2
      (hinputCoverage source hsource)
  have htableFree :
      ∀ expression ∈ argument.tables.map
          (substSelectorMap top.selectorMap.lookup),
        expression.SelectorFree := by
    intro expression hexpression
    obtain ⟨source, hsource, hexpression⟩ := List.mem_map.mp hexpression
    subst expression
    exact (substSelectorMap_selectorFree _ source).2
      (htableCoverage source hsource)
  have hinputs := eraseGates_eval fixed advice instanceFeed valuation
    (argument.inputs.map (substSelectorMap top.selectorMap.lookup))
    top.gateQueryState hinputFree
    (List.forall_iff_forall_mem.mp hresolved.1) hinterpretsGate
  have htables := eraseGates_eval fixed advice instanceFeed valuation
    (argument.tables.map (substSelectorMap top.selectorMap.lookup))
    top.gateQueryState htableFree
    (List.forall_iff_forall_mem.mp hresolved.2) hinterpretsGate
  have hpinnedInputs :
      top.pinnedCS.lookupInputExprs.getD lookup.val [] =
        eraseGates
          (argument.inputs.map (substSelectorMap top.selectorMap.lookup))
          top.gateQueryState := by
    simpa only [TopLevelCircuit.pinnedCS, TopLevelCircuit.gateQueryState,
      argument] using
      PinnedConstraintSystem.derive_lookupInputExprs_getD
        top.constraintSystem top.selectorMap lookup.val lookup.isLt
  have hpinnedTables :
      top.pinnedCS.lookupTableExprs.getD lookup.val [] =
        eraseGates
          (argument.tables.map (substSelectorMap top.selectorMap.lookup))
          top.gateQueryState := by
    simpa only [TopLevelCircuit.pinnedCS, TopLevelCircuit.gateQueryState,
      argument] using
      PinnedConstraintSystem.derive_lookupTableExprs_getD
        top.constraintSystem top.selectorMap lookup.val lookup.isLt
  constructor
  · rw [hpinnedInputs]
    apply List.ext_getElem
    · simp only [List.length_map, eraseGates_length, argument]
    · intro index hleft hright
      simp only [List.getElem_map]
      have heval := hinputs index (by simpa using hleft) (by simpa using hright)
      rw [List.getElem_map, substSelectorMap_eval] at heval
      exact heval
  · rw [hpinnedTables]
    apply List.ext_getElem
    · simp only [List.length_map, eraseGates_length, argument]
    · intro index hleft hright
      simp only [List.getElem_map]
      have heval := htables index (by simpa using hleft) (by simpa using hright)
      rw [List.getElem_map, substSelectorMap_eval] at heval
      exact heval

end Zcash.Snark
