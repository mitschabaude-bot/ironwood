import Zcash.Meta.AxiomCheck

/-!
# Regression tests for the environment-level endpoint census

Forged declarations exercising `Zcash.Meta.EndpointCensus`: every endpoint-shaped environment kind
below must be discovered without a census entry, as must every qualified spelling of a semantic
marker, while one that a census entry pinned — or a name in which a marker is merely the prefix of
a longer word — must not be reported.  The declarations are deliberate forgeries, so they live in
this test-only library, out of the production `Zcash` import graph — which is also why
`unpinnedEndpoints` excludes `Zcash.Meta.Tests` by default and the discovery assertion below opts
back in.
-/

namespace Zcash.Meta.Tests.EndpointCensus

/-- A forged endpoint: matches the naming convention, censused nowhere. -/
theorem orchard_action_forged_prob_le : True := trivial

/-- A forged axiom endpoint: declaration kind must not bypass the environment census. -/
axiom orchard_action_forged_axiom_prob_le : True

/-- A forged opaque endpoint: declaration kind must not bypass the environment census. -/
opaque orchard_action_forged_opaque_prob_le : True := trivial

/-- A forged inductive proposition endpoint: its `.inductInfo` must be censused. -/
inductive orchard_action_forged_inductive_prob_le : Prop where
  | intro

/-- A forged structure proposition endpoint: structures are also represented by `.inductInfo`. -/
structure orchard_action_forged_structure_prob_le : Prop where
  proof : True

/-- Carrier whose deliberately endpoint-shaped constructor exercises `.ctorInfo` discovery. -/
inductive CensusConstructorCarrier : Prop where
  | orchard_action_forged_constructor_prob_le

/-- A forged conditional capstone: a premise qualifier after the marker must not retire the
obligation.  This is the spelling the end-anchored rule let escape — the straight-line AGM
capstones are probability bounds *of* textbook-DL hardness. -/
theorem forged_binding_prob_le_of_forgedPremise : True := trivial

/-- A forged instance-qualified bound: `_at_<instance>` after the marker. -/
theorem forged_failure_prob_le_at_forged_instance : True := trivial

/-- A forged primed variant: `'` after the marker. -/
theorem forged_surface_measure_le' : True := trivial

/-- Not an endpoint: `_prob_le` occurs only as the prefix of a longer word, which the marker rule
must leave alone. -/
theorem forged_prob_lemma : True := trivial

/-- A pinned endpoint: the census entry below records it, removing it from the unpinned set. -/
theorem orchard_action_pinned_prob_le : True := trivial

assert_axioms Zcash.Meta.Tests.EndpointCensus.orchard_action_pinned_prob_le

-- The marker rule on base names: a marker is demanded in any position when a qualifier or nothing
-- follows it, and not when it is merely the prefix of a longer word.
#guard Zcash.Meta.isEndpointBaseName "attack_prob_le"
#guard Zcash.Meta.isEndpointBaseName "attack_prob_le'"
#guard Zcash.Meta.isEndpointBaseName "bound_measure_le_for"
#guard Zcash.Meta.isEndpointBaseName "attack_prob_le_of_textbookDL"
#guard Zcash.Meta.isEndpointBaseName "failure_prob_le_at_consensus_max"
#guard Zcash.Meta.isEndpointBaseName "union_probability_bound_of_dlogProfile"
#guard Zcash.Meta.isEndpointBaseName "rootSet_measure_le_shape"
#guard !Zcash.Meta.isEndpointBaseName "attack_prob_lemma"
#guard !Zcash.Meta.isEndpointBaseName "weight_measure_left"
#guard !Zcash.Meta.isEndpointBaseName "pinnedRoots_landing_or_relation"

-- Discovery: with the test exclusion lifted, exactly the forged endpoints are unpinned — the
-- pinned sibling was recorded by its census entry above.  Keeping the expected set explicit makes
-- a declaration-kind regression fail closed.
run_cmd do
  let bad := Zcash.Meta.unpinnedEndpoints (← Lean.getEnv) (excludeTests := false)
  let expected := #[``orchard_action_forged_axiom_prob_le,
    ``CensusConstructorCarrier.orchard_action_forged_constructor_prob_le,
    ``orchard_action_forged_inductive_prob_le, ``orchard_action_forged_opaque_prob_le,
    ``orchard_action_forged_prob_le, ``orchard_action_forged_structure_prob_le,
    ``forged_binding_prob_le_of_forgedPremise, ``forged_failure_prob_le_at_forged_instance,
    ``forged_surface_measure_le'].qsort Lean.Name.lt
  unless bad == expected do
    Lean.throwError m!"expected exactly the forged declaration-kind endpoints unpinned, got \
      {bad.toList}; expected {expected.toList}"

-- The deployed configuration excludes this forged-declaration library, so the command passes
-- even with the forgery in scope.
assert_endpoint_census

end Zcash.Meta.Tests.EndpointCensus
