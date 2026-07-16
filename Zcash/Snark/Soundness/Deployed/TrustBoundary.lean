import Zcash.Snark.Soundness.Vesta
import Mathlib.Util.AssertNoSorry

/-!
# Checked trust boundary of the deployed binding-reduction breaks

This file checks that the binding reductions return computed data. They are plain `def`s, so Lean
rejects noncomputable dependencies. The checks below also reject `sorry` and pin their axiom sets.

`Classical.choice` enters only through erased `Prop` certificate fields; it cannot affect the returned
data because the reductions are computable. The Vesta result also depends on CompElliptic's
`native_decide` proof of the curve-order witness.

The same checks cover the forking reductions `ipa_extractV`, `ipaRelation_extract`, `produceDeployed`,
`deployed_forking_tree`, and `deployed_forking_relation`. Each computes its witness from an explicit
certificate; an existential proof alone cannot produce that data.
-/

open Zcash.Snark

assert_no_sorry NontrivialRelation.ofCombinationCollision
assert_no_sorry NontrivialRelation.ofFoldedGens
assert_no_sorry NontrivialRelation.ofLeafPeel
assert_no_sorry NontrivialRelation.ofDeployedTree
assert_no_sorry NontrivialRelation.ofUnopenedFork
assert_no_sorry NontrivialRelation.ofUnopenedForkVesta

-- The computed-data forking reductions (opening/relation returned as `Σ'` data, not `∃`).
assert_no_sorry ipa_extractV
assert_no_sorry ipaRelation_extract
assert_no_sorry produceDeployed
assert_no_sorry deployed_forking_tree
assert_no_sorry deployed_forking_relation

/-- info: 'Zcash.Snark.NontrivialRelation.ofCombinationCollision' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NontrivialRelation.ofCombinationCollision

/-- info: 'Zcash.Snark.NontrivialRelation.ofFoldedGens' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NontrivialRelation.ofFoldedGens

/-- info: 'Zcash.Snark.NontrivialRelation.ofLeafPeel' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NontrivialRelation.ofLeafPeel

/-- info: 'Zcash.Snark.NontrivialRelation.ofDeployedTree' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NontrivialRelation.ofDeployedTree

/-- info: 'Zcash.Snark.NontrivialRelation.ofUnopenedFork' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NontrivialRelation.ofUnopenedFork

/-- info: 'Zcash.Snark.NontrivialRelation.ofUnopenedForkVesta' depends on axioms: [propext,
Classical.choice,
Quot.sound,
CompElliptic.Curves.Pasta.Vesta.p_nsmul_Gpt._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in
#print axioms NontrivialRelation.ofUnopenedForkVesta

/-- info: 'Zcash.Snark.ipa_extractV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ipa_extractV

/-- info: 'Zcash.Snark.ipaRelation_extract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ipaRelation_extract

/-- info: 'Zcash.Snark.produceDeployed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms produceDeployed

/-- info: 'Zcash.Snark.deployed_forking_tree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployed_forking_tree

/-- info: 'Zcash.Snark.deployed_forking_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms deployed_forking_relation
