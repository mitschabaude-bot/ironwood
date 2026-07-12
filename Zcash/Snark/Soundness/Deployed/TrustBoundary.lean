import Zcash.Snark.Soundness.Vesta
import Mathlib.Util.AssertNoSorry

/-!
# Checked trust boundary of the deployed binding-reduction breaks

Build-time enforcement of the breaks-as-computed-data discipline (see
`Zcash.Security.RandomOracle`), following `Zcash.Security.Ledger.TrustBoundary`. The reductions'
computability is compiler-enforced — they are plain `def`s, so a `noncomputable` dependency
fails the build. What a build does not otherwise pin down is a `sorry` reached through some
dependency, or an unexpected axiom; both checks below follow the elaborated dependency graph.

The pinned sets include `Classical.choice`, entering only through Mathlib lemmas cited by the
erased `Prop` certificate fields (`nontrivial`/`relation`) — harmless per the convention: had
choice touched the break *data*, the definitions could not have compiled as plain `def`s. The
Vesta specialization additionally pins CompElliptic's one `native_decide` fact (the prime-order
witness `p_nsmul_Gpt` behind the curve order), likewise reached only through `Prop` positions.

The same two checks cover the deployed forking reductions that return their result as *computed
data*: `ipa_extractV` (the IPA opening witness), `ipaRelation_extract`, `produceDeployed` and
`deployed_forking_tree` (the root-consistent tree extraction), and `deployed_forking_relation`
(the end-to-end multiopen opening). Their non-vacuity is exactly that they are computable — the
witness cannot be produced without the certificate — so a `sorry` or a `noncomputable` dependency
would defeat them, and the pins freeze that. Their axiom sets are the standard classical trio,
`Classical.choice` again reaching only erased `Prop` positions.
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
