# Action circuit integration roadmap

This note maps the missing semantic last mile between the deployed Halo 2 verifier
model in `Zcash/Snark` and the proved post-NU6.3 Action circuit in
`Zcash/Circuits/Action`.

For each supplied public Action, constructively
extract `ActionData` whose ten public fields equal that Action's instance column, prove
the complete §4.17.4 Action statement, and prove the post-NU6.3 cross-address
condition.

## Consistency proofs should follow the compiler

For consistency, well-formedness, and collision-freedom obligations, first inspect
whether the property follows from the construction that compiled the circuit. Prefer,
in order:

1. a generic invariant of the compiler pipeline that makes the bad state impossible;
2. a compiler decomposition of a large global obligation into small local obligations
   attached to the components that produced the data;
3. small structural proofs or computational certificates for those local obligations;
4. only as a fallback, a full-circuit `native_decide` check over the finished
   artifact.

The second option is important even when the whole property is not true solely by
construction. For example, V1 floor planning should generically prove that distinct
regions never overlap in cells: regions may occupy the same rows, but not the same
column-and-row cells when both use that column. Global fixed-write consistency can
then be decomposed into tractable statements about writes within one region and the
other compiler stages that produce fixed cells—table layout, constant allocation,
and selector packing—plus composition theorems showing that those stages do not
collide. Tables are not conceptual exceptions to this approach merely because they
are outside region placement; they are another part of the broader layout/compiler
pipeline whose construction should expose the relevant invariant or decomposition.
The same principle applies to advice assignment, copy-cell resolution, selector
activation, lookup layout, and future consistency requirements.

A whole-circuit native check is therefore a deliberately bad fallback, not the
default proof architecture. If such a check temporarily stands in for a compiler
argument that appears possible but is too large for the current milestone, label it
prominently as an **interim solution**, state the intended structural replacement,
and keep it out of foundational interfaces where it could silently become permanent.

The follow-on design for eliminating the Action-specific certificates is
[`lawfulness-and-certificate-elimination.md`](../../../Zcash/Circuits/Integration/lawfulness-and-certificate-elimination.md).
It includes correctness obligations currently hidden by `closeWithOperations`: the
canonical keygen pipeline should reject configure/synthesis mismatch rather than
repair it and rely on the concrete VK comparison to make the repair appear harmless.

## Upstream PR landscape

The verifier foundations on which this integration was originally stacked are now
merged:

- [#30, Bind IPA witness to verifier columns](https://github.com/zcash/ironwood/pull/30),
  implements the deployed `x₄` and `x₁` decode, member-commitment and
  claimed-evaluation binding, and decoded-column capstone foundations.
- [#91, Permutation and lookup arguments](https://github.com/zcash/ironwood/pull/91)
  extends #30's polynomial constraint model with the verifier's permutation and lookup
  expressions, splits the combined constraint check, reads the arguments row by row,
  telescopes their running products, and reaches copy-equality and lookup-inclusion
  endpoints.

- [#89, Add Ironwood circuit formalization](https://github.com/zcash/ironwood/pull/89)
  supplies the Action circuit, `soundnessPost`, and the executable Rust/Clean CS and
  layout comparisons. It was the original base of this integration.
- [#85, Derive instance commitments](https://github.com/zcash/ironwood/pull/85),
  removes statement-derived instance commitments from the circuit-fixed VK, derives
  them from public inputs, and exercises the result with single- and multi-Action
  fixtures.
- [#79](https://github.com/zcash/ironwood/pull/79) consolidates the checked
  trust-boundary census into `Zcash/TrustBoundary.lean` and enforces explicit axiom
  tiers through the `AxiomCheck` macros.

The still-open [#82](https://github.com/zcash/ironwood/pull/82) makes the proof map
point at the current computed capstone; it does not prove a semantic bridge.

Three draft PRs now divide the active work:

- [#99](https://github.com/zcash/ironwood/pull/99) is this deterministic
  verifier-to-Clean integration. Its concrete completion criterion is elimination of
  the live capstone's free `S`/`hencodes` by constructing the Action bundle statement
  from accepted, decoded verifier data.
- [#96](https://github.com/zcash/ironwood/pull/96) composes the forking/extraction
  layer with the deployed constraint-soundness capstone. It can remain parallel until
  #99 supplies the concrete encoding theorem at its abstract statement boundary.
- [#98](https://github.com/zcash/ironwood/pull/98) refines the circuit-exported
  `SpecPost` to the games-facing ledger statement, including the concrete handling of
  Sinsemilla exceptional cases. It is downstream of circuit satisfaction and can
  proceed independently; the final #99 adapter should target or compose with its
  refined statement rather than grow a competing ledger semantics.

#99 combines the merged APIs while preserving #85's architectural split: the
verifying key contains circuit-fixed data, and statement-derived instance commitments
remain explicit inputs to the verifier and soundness stack.

## Stable semantic endpoint

`Action.Circuit.soundnessPost` already proves

```text
Clean environment assumptions
  + exact constraints of the closed, unit-input synthesis
  -> SpecPost realGenerators realBases extractedActionData.
```

Both proof-carrying Action circuits now expose `unit` input. Their prover choices are
the fixed `Action.Circuit.hintWitnesses` program: field, point, scalar, and Merkle-path
values are read from the runtime `ProverHint` through `hintGet` (the existing native
Merkle-swap function reads the same hint environment). The raw
`synthesizeBase ... W` function remains useful for internal circuit lemmas, but neither
the base nor post-Ironwood `FormalCircuit` lets its caller select `W`.

Correspondingly, `Bridge.actionOperations` is synthesized from the real
`orchardActionCircuit` at unit input. The separate synthetic
`Bridge.keygenWitnesses` value has been removed.

The final adapter is now:

```text
placed Clean environment satisfying `mainPost`
  -> TopLevelCircuit.Spec extractedPublic extractedPrivate
  -> Action.actionCircuit.Statement extractedPublic.
```

`TopLevelCircuit` owns the public/private boundary. It declares the instance cells
encoding its public input, derives environment extraction from that layout, separately
extracts the private witness, and proves that recombining the two agrees with the
formal circuit's native extractor. The Action instance specializes this interface with
ten public field elements and a private witness containing only the remaining
`ActionData` fields.

### 1. Recover the committed columns from multiopen

**Status: substantially implemented by
[#30](https://github.com/zcash/ironwood/pull/30), with
[#85](https://github.com/zcash/ironwood/pull/85)'s statement-derived instance
commitments threaded through the combined stack.**

The `a` in the current `SnarkRelation` is an opening of the final `x₄`-collapsed,
`x₁`-compressed multiopen commitment. It is not an advice-column vector and cannot be
read directly as an Action witness.

#30 now connects the Vandermonde-style recovery to the deployed
`assembleOpening`/`constructIntermediateSets` shape. Its `x4BatchCommitments`,
`x4BatchEvals`, `decodedCols`, `x1DecodeCols`, `deployed_witness_member_binding`, and
budgeted node-binding results recover the point-set aggregates, unbatch their member
columns, and bind those members to the routed commitments and claimed evaluations.
The transcript-prefix and multiopen-challenge rewinds are modeled as well.

The remaining work is:

1. produce #30's batch/member-decode data from the live computed experiment without
   the remaining family-wide `hExtract`/adaptive-coupling supply premise;
2. route the recovered members into the full constraint model from #91 and then into
   the Clean Action assignment described below.

### 2. Replace the free column decoders

**Status: polynomial/query-level decoding is implemented by
[#30](https://github.com/zcash/ironwood/pull/30); the generic Clean row decoder and
the concrete Action public-instance commitment provenance are now implemented on this
branch.**

The deployed/member capstones use canonical decoding through `coeffsToPoly`,
`decodedCols`, `x1DecodeCols`, query-layout member selection, and `rotatedFeed`. The
extracted opening and the polynomials consumed by those capstones are therefore not
independent.

`PolynomialEnvironment` is the canonical decoder from those polynomials to values on
the size-`2^k` evaluation domain. It evaluates column `c` at row `r` as
`c(ω^r)` and proves that Clean's rotated advice, fixed, and instance queries agree
with the verifier's rotated polynomials. `resolverEnvironment` remains the
verifier-side polynomial interpretation. At the top-level circuit boundary,
`resolverAssignment` retains only per-proof advice and instance columns, while
`TopLevelCircuit.environment` supplies circuit-compiled fixed columns and usable
rows. `TopLevelAssignment.FixedColumnEncoding` is the named representation fact
that proves these two environments equal.

Public-instance row provenance now has a canonical target as well.
`instanceRowPolynomial` Lagrange-interpolates a zero-padded list of public values over
the `ω` domain, `instanceRowPolynomial_eval` proves that it reads those rows back, and
`resolverEnvironment_instance_of_rowPolynomial` transports a decoded-polynomial
identity directly to the corresponding Clean instance reads.

The generic cryptographic step is now complete in `InstanceCommitment`.
`LagrangeCommitmentKey` states the circuit-independent setup relation between each
Lagrange generator and the monomial URS. `commitRows_eq` proves that Halo 2's
Lagrange-basis public-instance commitment is the monomial commitment of the
interpolated coefficient vector. Consequently,
`coeffsToPoly_eq_instanceRowPolynomial_or_relation` proves that any augmented
`(g, U, W)` opening of that commitment is the canonical zero-padded row polynomial,
or computes the existing nontrivial-relation branch. At the deployed endpoint,
`OpenedMemberDecode.commitment` supplies that opening for the routed instance member.
The verifier grouping now preserves enough indexed provenance to close the intervening
step generically: `constructIntermediateSets_member_provenance` shows that a grouped
commitment and its retained identity arise from the same assembled query,
`assembleQueries_instance_commitment` identifies every `.instanceCol p column` query
with the statement-derived commitment, and
`deployedMemberRef_eq_instanceCommitment` composes those facts for any deployed
member slot. None of these theorems mentions Action placement or operations.

`TopLevelAssignment.PublicInputEncoding` now expresses this row mapping generically
through the cells declared by `TopLevelCircuit.publicInputLayout`.
`publicInputEncoding_of_rowPolynomials` derives it from canonical per-column row
polynomials, and `extractPublicInput_eq` identifies the extracted public input.
The Action specialization supplies only the intrinsic facts that its layout is the
primary column at rows 0–9 and that `PublicInputs.rows` is its `ProvableType`
serialization; the former `Integration/ActionStatement.lean` side layer has been
deleted.
`CanonicalMemberConstraintRelation.instanceColumn_eq_rowPolynomial_or_relation`
now performs the deployed representation step generically. It follows an assembled
instance query through the canonical grouped-member route, identifies that member's
commitment with the verifier-supplied instance commitment, and concludes that the
decoded polynomial is the canonical row polynomial or computes the shared nontrivial
relation. The binding-aware Action endpoint invokes this theorem internally; it no
longer accepts the decoded-polynomial equality as a premise.
`ActionInstanceCommitment.action_bundleStatement_or_relation_of_accepted_topLevelBundleStatement`
constructs the Lagrange key from the monomial URS, derives the commitment from the
ten supplied rows, and binds the verifier-supplied instance polynomial to the
generic top-level statement. The generic query compiler proves that
configure-registered layouts survive
packed-selector insertion and the gate/lookup erasure walks, and then the generic
layout-to-assembly lemma supplies the actual proof- and challenge-dependent query.
The endpoint also derives evaluation-domain injectivity and size equalities from
`TopLevelCircuit` plus the existing supported-`k` bound.

The exported fixture contains only the ten Lagrange generators reachable by Action
public rows, rather than the whole 2048-row domain. `LagrangeCommitmentKey.ofPrefix`
matches that representation: it turns a certified exported prefix into a full key by
using canonical monomial-URS commitments beyond the prefix. Thus the concrete setup
certificate needs ten generator equations, not 2048; zero padding ensures the
synthetic suffix cannot affect the instance commitment.
`ofPrefix_commitInstance_eq` proves this last step generically and matches the
fixture's finite-prefix commitment computation directly.
`commitPrefixNat_eq_commitPrefix` additionally discharges the representational
difference between the fixture's executable `c.val • point` natural-scalar sums and
the abstract `Fp`-module commitment, leaving only the ten actual generator equations
as concrete setup data.

The concrete Action construction is now closed in
`ActionInstanceCommitment`. `instanceKey` derives the compatible Lagrange key from
the monomial URS, `commitment` computes the verifier's instance commitment from each
Action's ten public rows, and `commitment_primary_eq_commit` identifies it with the
zero-padded row polynomial plus Halo 2's default blind. The Action endpoint constructs
this key and commitment internally, discharges primary-query registration and the
Action domain bounds, and no longer accepts an instance key, commitment equation, or
registration premise from its caller. A commitment mismatch remains visible only as
the shared `HasNontrivialRelation` exceptional branch.

Then expose the result as the row-indexed Clean `Environment` used by
`Action.Circuit.soundnessPost`. The remaining gap is not the old free-polynomial
decoder; it is the polynomial/query representation to Clean row/placement
representation.

### 3. Prove reusable VK correctness

**Status: executable coverage in
[#89](https://github.com/zcash/ironwood/pull/89) and public-instance provenance in
[#85](https://github.com/zcash/ironwood/pull/85); the projection's *semantics* are now
proven on this branch, but the fixture-equality side still has no reusable theorem.**

`Zcash.Circuits.Fixtures.ProjectSemantics` proves that the VK-match projection
preserves meaning: selector compression is evaluation under the root-finding
replacement valuation (`substSelectorMap_eval`, with the packed-column case algebra
`selReplacement_eval_of_root`/`_of_other`/`_of_zero`), and the query-index erasure walk
evaluates to the original gate expression whenever the evaluation families interpret
the walk's final query layout (`eraseExpr_eval`; composed per gate as
`eraseExpr_substSelectorMap_eval`). The projection now targets the verifier's own gate
AST (the shared `Zcash/Common/Expr.lean`), so no translation layer separates the two
sides. What remains here is the *syntactic* linking:

The circuit subtree already contains strong executable checks:

- `TestVkMatchAction` compares the projected Clean `ConstraintSystem` with the Rust
  pre- and post-selector-compression dumps;
- `TestVkLayoutAction` compares placements, ordered copies, permutation σ, and fixed
  columns with the Rust layout dump.

They are build-time `IO` Boolean checks over JSON fixtures, not propositions reusable
by soundness. Refactor the projections and fixture values so kernel-checked theorems
state that the actual `VerifyingKey` fields used by `Zcash.Snark` correspond to:

- **done on this branch**: `Zcash.Circuits.Fixtures.PartialPinnedConstraintSystem`
  models the sub-record of halo2's `PinnedConstraintSystem` the capture certifies, and
  its derivation from a Clean constraint system (`derive`, taking the two keygen
  witnesses — registration seed and selector-compression map — as explicit inputs
  until the keygen ports compute them); `Fixtures.SingleAction.PinnedCsMatch`/
  `VkMatch` compute the captured VK's pinned CS equal to the derived Action circuit
  (per-field `native_decide` on the fast CS-data dump, `capturedPinnedCs_eq_derived`
  over the full record — counts, constants, and minimum degree included — with
  `VkMatch` exporting the per-field verifying-key links), and `derive_gates_eval`
  hands every VK gate's evaluation to the Clean gate expressions. The
  selector-compression map is now *derived* from the circuit
  (`deriveSelCompressMap`, the `compress_selectors` port, checked equal to the Rust
  dump by `TestSelMapDerivation`); pending: the floor-planner placement port (making
  the derivation's activation input circuit-side) and the permutation columns (with
  the commitment-matching phase);
- `Action.Circuit.configure orchardGenerators` after selector compression;
- the closed post-NU6.3 `mainPost` layout at `orchardBases`, whose operation stream is
  now derived directly from `orchardActionCircuit`;
- the fixed commitments, permutation commitments, and query/chunk ordering produced
  by key generation.

#85 makes the correct architectural split: `VerifyingKey` contains circuit-fixed data,
while `assembleQueries` receives per-proof instance commitments derived by
`commitLagrange` from public inputs. Its captured-fixture theorem proves that derivation
for the fixtures. The generic basis-conversion and binding theorem is now reusable;
the concrete setup certificate still has to identify the exported Lagrange generators
with the monomial URS relation. The remaining VK fields still need to be connected to
#89's Clean configuration and layout.

#30 currently carries `hadviceLayout`, `hinstanceLayout`, quotient routing, and related
facts as capstone hypotheses. The VK theorem should discharge those facts rather than
merely restating fixture equality.

### 4. Strengthen circuit satisfaction beyond custom gates

**Status: the protocol mathematics and generic Clean-operation adapters are
implemented. Action fixed/table coherence and copy replay are now constructed
internally. The synthesis-side lookup-selector law is now proved for the complete
Action circuit; concrete deterministic closure is down to transporting those exact
activations through V1 placement and packed fixed columns. Lookup and permutation
challenge exclusions are priced and packaged, but must still be supplied at their
transcript squeezes.**

#30's decoded capstones record only the combined custom-gate quotient identity. #91
defines the full gate/permutation/lookup constraint list over polynomials, proves that
evaluation commutes with its builders, and identifies its `y` fold with the verifier's
own `allExpressions`/`expected_h_eval` fold. This removes the former permutation/lookup
fingerprint premise at the quotient check. Its latest stack additionally proves:

- a good `y` splits the combined check into divisibility of every individual
  constraint;
- the permutation row equations telescope through each chunk and across chunks;
- the resulting multiset identity gives equal values on each permutation cycle;
- the lookup row equations and product identity imply every input value occurs in the
  table.

This integration branch now packages the deployed flat list as
`ConstraintPolyModel.constraints`, turns the split theorem into the family-separated
`ConstraintSatisfaction` record, and exposes named membership/divisibility facts for
each selected lookup's five constraints. `LookupRows` reads those five polynomial
constraints over the evaluation domain and closes the lookup endpoint, including the
explicit zero-factor branch when the running product ends at zero.
`ConstraintSatisfaction.of_circuitSatViaConstraints` now also connects the capstone
identity directly to that record: a good folding challenge splits
`circuitSatViaConstraints` into divisibility of every modeled constraint. This is the
generic deterministic seam at which [#96](https://github.com/zcash/ironwood/pull/96)'s
extraction/probability result can hand its witness to this PR. #96 deliberately keeps
the final encoding relation abstract; this PR's completion criterion is to eliminate
those free `hencodes`/statement parameters by deriving the concrete Action bundle
statement.

That endpoint now has a canonical, bundle-wide type.
`CanonicalMemberConstraintRelation` derives its commitment-ID polynomial resolver
from the decoded members and the deployed assembled-query route, then constructs the
entire constraint model from the accepted VK. Fixed columns, permutation sets/chunks,
lookups, and selector polynomials are no longer free relation parameters.
`actionTopLevelCircuitCorrectness` packages the Action circuit's gate, fixed, copy,
lookup, and query-representation laws as a generic `TopLevelCircuitCorrectness`
record. The generic
`topLevelBundleStatement_or_bad_of_constraintSatisfaction` theorem consumes that
record and concludes the top-level circuit statement, with no abstract `S` or
`hencodes` premise and with the key locked to
`actionCircuit.toVerifierKey`. The binding-aware Action endpoint
constructs `TopLevelFixedCoherence` from the Action circuit, its derived key, and the
symbolic Lagrange-basis theorem, then derives the selector-activation and fixed/table
families.
It also constructs copy replay from the canonical permutation semantics, preserving
the commitment-relation branch, and derives lookup satisfaction from exact
packed-selector values and one
`TopLevelLookupChallengeExclusions` record, and derives the public-instance
polynomial from the routed member and supplied Lagrange commitment data. A fixed- or
instance-column mismatch returns the shared augmented commitment-relation event
instead of becoming a silent binding assumption.
`LookupInstantiation` now constructs those coherent lookup entries from an arbitrary
VK and a `CommitmentId`-keyed polynomial resolver, proves that openings for the actual
assembled lookup queries give the verifier's five claimed evaluations, and specializes
`ConstraintSatisfaction` to the compact five-constraint record consumed by that
endpoint. `Multiopen.ConstraintResolver` now constructs that resolver from
`OpenedMemberDecode` columns and a partial commitment-ID-to-member routing, and turns
the existing member-node binding into uniform query openings or the existing
nontrivial-relation branch. It feeds the clean branch directly into the lookup
instantiation theorem. The grouping layer now proves claimed-value faithfulness on
the verifier's non-duplicate path, constructs the commitment-ID route automatically,
and derives its coverage and non-duplication premises from a successful `assemble?`.
The Clean-facing representation step is now generic as well.
`LookupProjection` proves that the circuit-derived VK's selected input and table
expressions evaluate like their configured Clean expressions.
`TopLevelLookups` routes every synthesis-enabled lookup to that configured index,
projects its exact selector-substituted tuples into the resolver's compressed
input/table polynomials, and constructs both one `EnabledLookup.DeployedWitness` and
the complete witness family consumed by `FullCircuitBridge`.
Lookup configure lawfulness is now correct by construction. Clean's `LookupArgument`
carries selector-free tables and matching tuple arity, while `closeWithOperations`
raises `numSelectors` to cover every selector appearing in lookup inputs.
`TopLevelCircuit.lookupInputsAllocated` exposes that closure invariant and
`TopLevelLookupCoherence.ofTopLevel` converts it to compression-map coverage. The
former `LookupArgumentWellFormed`/`ConstraintSystemLookupsWellFormed` sidecar has been
deleted; no Action configure proof remains.

`InputSelectorValuesRealized` now states exactly the expression-level equality needed
by projection. Its former all-selectors formulation was false: an unrelated simple
gate selector can legitimately be active on the same absolute row. The generic
`LookupSelectorRows` bridge restricts the dense-row obligation to selector leaves that
actually occur in each lookup input and transports it through fixed-column binding.
Table projection follows generically from selector freedom. Activation-row fit is now
generic too: extracted lookup membership
identifies the raw `.enableLookup` operation, Clean bounds its row by the measured
region extent and `usedRows`, and the top-level fit certificate bounds `usedRows` by
the usable-row prefix. `TopLevelLookupWitnessConditions` therefore retains only exact
packed selector values and the `β`/`γ`/`θ` exclusions; row fit is no longer supplied
by a caller. The same activation-row fact also proves that a nonempty lookup family
has at least one usable row, so deployed lookup construction no longer asks every
caller for a separate blinding-row arithmetic premise.
`lookup_gamma_failure_measure_le` and
`lookup_beta_failure_measure_le` now price the two lookup-product root surfaces
generically from their column lengths, while
`uniformChallenge_enabledLookupThetaBadSet` prices one enabled tuple-compression
surface. The family aggregation is complete as well:
`allResolverLookupBetaBadSet` and `allResolverLookupGammaBadSet` combine every
proof/lookup pair and construct all of their `ResolverLookupGoodChallenges` records
from two shared exclusions; `enabledLookupThetaBadSetFamily` does the analogous job
for an arbitrary finite family of placed Clean activations. Their measure bounds
multiply or sum the individual row/arity budgets explicitly. Only placement of these
already-priced events at the corresponding transcript squeezes remains in the
probability layer.
`TopLevelLookupChallengeExclusions` now specializes those three events to the exact
circuit-derived key, all bundle proof indices, and all enabled operation activations.
Its `θ` field uses `allTopLevelLookupThetaBadSet`, whose reusable measure theorem is
the sum of `usableRows × tupleArity` over that complete bundle family.
`TopLevelLookupWitnessConditions.ofChallengeExclusions` turns one such bundle record
and the fixed stream's exact selector values into the per-proof conditions consumed
by `deployedWitnesses`; callers no longer distribute `β`/`γ`/`θ` facts manually.
`PermutationInstantiation` now supplies the analogous permutation layer. It maps
running products through `permProduct`, maps each chunk's value-side `ColumnRef`
through the corresponding VK query-layout entry, maps its σ-side through
`permCommon`, and proves that evaluating the resulting polynomial records reproduces
`subProofPermSets` and `subProofPermChunks`. The decoded-member specialization retains
the nontrivial-relation branch. Its resolver-backed constraint model and
`ResolverPermutationConstraints` package extract the exact step, inter-set chain,
start, and end divisibility facts consumed by
`deployed_perm_copy_constraints_all_chunks`. `PermutationSemantics` now completes the
generic semantic call: `ResolverPermutationDomain` isolates the concrete VK/domain
facts, `ResolverPermutationCycle` carries the replayed global cell permutation and
the common-polynomial naming equation, and
`ResolverPermutationGoodChallenges` carries the separately priced `β`/`γ`
exclusions. Given those records,
`ConstraintSatisfaction.resolverPermutationCopyConstraints` yields equality on every
keygen permutation cycle (or the theorem's explicit zero-factor branch). The same
module flattens variable-width chunks to global columns and derives chunk-name
injectivity from the standard root-of-unity/coset hypotheses. The generic keygen
construction is now present as well: `replayKeygenPermutation` performs the
source-ordered cycle merges and proves that its cycles are exactly the copy-equivalence
classes; `chunkPermutationOfFlat` conjugates that flat permutation through an
arbitrary concrete chunk layout; and
`keygenSigmaColumn` interpolates the permuted cell names over the evaluation domain.
Its node-evaluation and degree-bound theorems prove that these are exactly the
degree-`< n` common permutation polynomials required by Halo2.
`ResolverPermutationCycle.ofKeygenColumns` then restricts the full-domain keygen
permutation to the active rows and constructs the semantic cycle record; its only
polynomial-identification premise says that each resolver-selected common polynomial
equals the corresponding generated σ column. Keeping the full `n`-row interpolation
separate from the `m` active-row copy theorem is essential: the VK commits to the
former even though soundness reads only the latter.

The current item-4 sequence is:

1. **complete:** route every assembled query through the canonical decoded-member
   resolver and instantiate the full deployed constraint model;
2. **complete, including Action:** derive the complete gate family from
   circuit-derived query layouts, selector compression, and canonical constraint
   satisfaction; `ActionGateCoherence.topLevelGateCoherence` supplies the deployed
   circuit's static package;
3. **generic layer complete:** route every enabled lookup to its configured argument,
   project its input/table tuples into the resolver polynomials, and construct the
   complete `EnabledLookup.DeployedWitness` family;
4. **complete, including Action:** generic replay/value transport and the concrete
   copy adapter:
   every resolvable declared non-constant copy occurs in the V1 copy list, and
   `chunkRowValue_eq_of_mem_copies` transports that membership through replay,
   conjugation, active-row restriction, and the resolver copy theorem to endpoint
   value equality. `CopyReplayWitness.ofLinkedPairs` packages the complete witness.
   The Action adapter now proves every declared endpoint's permutation-cell address
   roundtrip, connects every constant declaration positionally to its V1 allocation
   and raw copy tuple, realizes both the positional and canonical same-value constant
   cells through fixed coherence, and constructs the complete witness from pairwise
   σ-copy values alone. The permutation compiler round trip is now generic:
   `topLevelPermutationColumnAddresses_eq` proves that flattening and decoding the
   derived chunks recovers the circuit's declared permutation-column order, with no
   concrete computation certificate. The Action `[7,7,1]` specialization uses only
   its three prefix lengths to prove that `actionCopyValue` is exactly the resolver's
   `chunkRowValue` at the inverse-flattened active cell.
   `actionResolverPermutationCycle_or_relation` now identifies every routed common
   polynomial with its generated Action σ column and constructs the exact active
   resolver cycle, or returns the shared augmented-commitment relation. The symbolic
   `bestFftG` correctness theorem supplies the Lagrange-basis setup generically; no
   concrete setup certificate remains. `actionCopyReplayWitness_or_relation` combines
   that cycle, canonical constraint satisfaction, bundle-wide permutation challenge
   exclusions, and fixed reads to construct the complete `CopyReplayWitness`;
5. instantiate `TopLevelFixedCoherence`, use it to realize packed selectors and fixed
   tables, and discharge the lookup selector-projection fields; bundle-wide lookup
   challenge exclusions are already packaged by
   `TopLevelLookupWitnessConditions.ofChallengeExclusions`;
6. combine gate, copy, lookup, and fixed results in `FullCircuitBridge`.

The permutation side has moved past the former “Action permutation data” placeholder.
The Action chunk/domain certificates, decoded σ-column identification, and executable
assembly simulation are present. `runAssembly_getPair` proves that the final assembly
mapping is exactly the action of `replayKeygenPermutation` over the same ordered
copies. `CopyReplayWitness.ofPairCycles` and `.ofPairValues` perform the generic
packaging. `mem_V1_copyList_of_declared` now sends every resolvable cell/cell or
cell/instance declaration into that replay, and `chunkRowValue_eq_of_mem_copies`
proves the resulting committed endpoint values equal. The Action representation
adapter's coordinate/value side is now closed.
`actionActiveChunkCell_columnAddress` uses the generic permutation-compiler round
trip to identify the verifier query reference with the corresponding Clean
`actionPermCols` entry, and `actionCopyValue_eq_activeChunkRowValue` identifies the
resulting environment read with the verifier-native chunk-row value.
`actionResolverPermutationCycle_or_relation` closes the remaining σ leaf from the
keygen-generated rows and commitments. Finally,
`actionCopyPairValue_of_resolverPermutation` applies the generic cycle theorem to
every decoded keygen copy, and `actionCopyReplayWitness_or_relation` packages those
equalities together with constant allocations and fixed-row reads.
`actionCopyAddressFailures_eq_nil` certifies the finite endpoint address law;
`mem_operationConstSites_of_declared_constant`, `V1_go_snd_eq`, and
`actionConstantRawPair` follow constant declarations through the positional compiler
stream into the raw keygen copy list. Fixed coherence now includes allocated constants
as required compiler output. Consequently
`actionCopyReplayWitness_ofPairValues_or_bad` derives constant-copy equality and all
declared endpoint reads internally; its only semantic premise is value agreement on
each decoded `actionCopies` pair. That premise is now constructed internally at the
binding-aware Action endpoint; the terminal API no longer accepts a caller-supplied
copy witness.

The `β`/`γ` exclusions remain with explicit bad-set accounting rather than becoming
circuit assumptions. `ChallengePricing`'s resolver-permutation section now packages
their union across every proof in a bundle. Avoiding
`allResolverPermutationGammaBadSet` and `allResolverPermutationBetaBadSet`
constructs every `ResolverPermutationGoodChallenges`; the corresponding measure
theorems bound the γ surface by the sum of `2·activeCells` and the β surface by the
sum of `(activeCells+1)·activeCells`.

The residual zero-factor branch is now closed generically as well.
`additiveZeroBadSet` observes that, after `β` and the committed cell values are fixed,
each factor `value + β·name + γ` excludes exactly one value of the later `γ`
challenge. `resolverPermutationZeroFactorBadSet` collects those exclusions,
`uniformChallenge_resolverPermutationGammaBadSet` combines their active-cell count
with the existing Schwartz–Zippel root budget, and
`resolverPermutationCopyConstraints` now concludes cycle equality directly under the
combined good-`γ` condition. Thus concrete Action work need not propagate a
zero-product disjunction; it only supplies the already explicit challenge-avoidance
premise at the correct transcript squeeze.

The evaluation-domain selector side is now generic too.
`rowSelectorPolynomial` and `blindSelectorPolynomial` define the canonical `l₀`,
`l_last`, and `l_blind` row polynomials. Their evaluation theorems discharge the
first-row, last-row, and active-row selector premises shared by
`ResolverPermutationDomain` and `ResolverLookupDomain`. The remaining provenance step
is to identify the verifier-side Lagrange polynomials with these canonical
polynomials; it does not depend on Action placement or operations.
`ResolverPermutationDomain.ofCanonicalSelectors` and
`ResolverLookupDomain.ofCanonicalSelectors` now perform this generic discharge:
their callers retain only the actual domain bounds, root facts, and the
permutation-specific chunk/last-rotation facts.

The transcript-side provenance is now explicit rather than assumed.
`domainNodal_eq_vanishing` identifies the interpolation nodes' nodal polynomial
with `X^n - 1`, `domainNodalWeight_eq` computes the corresponding barycentric
weight, and
`rowSelectorPolynomial_eval_eq_lagrangeBasisValue_of_rotation` proves that the
fixed row-selector polynomial evaluates to the verifier's deployed
`lagrangeBasisValue` formula at any rotation naming that row. The blinding
selector is separately identified as the sum of all row selectors after the
last usable row. `blindingDomainRowEquiv` performs the generic finite reindexing
between those rows and the verifier's negative blinding rotations, and
`canonicalLagrangePolynomials_eval` packages the result: away from the
evaluation domain, evaluating the fixed canonical polynomial triple is exactly
the deployed `lagrangeBasis` computation. No Action-specific selector
provenance remains.

`canonicalConstraintModelOfPermutationResolver` now installs that fixed triple
directly into the generic commitment-ID resolver model, eliminating the option
for a downstream caller to pair accepted verifier evaluations with unrelated
selector polynomials. Its selector-evaluation theorem supplies all three
deployed matching equations together.
`ResolverPermutationDomain.ofCanonicalConstraintModel` additionally derives
the last-row rotation, while
`ResolverLookupDomain.ofCanonicalConstraintModel` derives the lookup active-row
boundary. Concrete instantiation retains only the genuine VK chunk counts and
the generic root/domain facts.

Those remaining domain facts are now exposed directly from every fitting
`TopLevelCircuit`. `TopLevelAssignment.domainRoot`,
`domainRowsInjective`, and `domainSizeCastNeZero` provide the root, row
injectivity, and nonzero field-size premises at the circuit-derived exponent.
The two `blindingFactors_*_domainSize` theorems derive the selector and
active-prefix bounds from keygen's existing `FitsAt` certificate (with a
nonempty-operation premise only for the stronger lookup bound).
`TopLevelCircuit.toVerifierKey` now constructs the verifier key from exactly this
circuit-owned keygen data, so no Action arithmetic or separately supplied key is
needed to instantiate the canonical resolver model.

After that, translate the endpoints to the exact relations that Clean's
`Halo2.Constraints` requires: declared `constrainEqual`/`constrainInstance` copies,
`RegionOperation.enableLookup` membership with the exact loaded tables, fixed
assignments and selector activations, and all synthesized regions under their actual
placement. Replace the gate-only circuit predicate with a full satisfaction record;
custom gates alone still cannot imply the Action operation trace.

The generic target and copy half of that translation are now in place.
`FullCircuitSatisfaction` splits the authoritative `Halo2.Constraints` predicate into
gate, copy, lookup, and fixed/table fields and proves exact equivalence in both
directions. `operationDeclaredCopies` extracts equality, instance, and constant copies from the
complete operation stream; `copy_constraints_iff_declaredCopies` proves that their
satisfaction is exactly the full record's copy field. Finally,
`copy_constraints_or_bad_of_replay` transports equality from the generic keygen
permutation cycles to every declared copy while preserving the caller's shared
exceptional event (for example commitment binding). Permutation zero factors
themselves are already eliminated by the priced `γ` exclusion above. The concrete
layout instantiation only has to encode endpoints as keygen cells (including
constants-column allocations) and identify their environment reads.

The generic lookup and reassembly halves are now present too.
`operationEnabledLookups` extracts every placed `enableLookup` activation and
`lookup_constraints_iff_enabledLookups` proves that their tuple membership is exactly
the full record's lookup field. `resolverLookupSubset` joins the five resolver-backed
constraint families to the deployed row theorem. Its `β`/`γ` zero-product branch is
eliminated by `lookupColumnZeroBadSet`, at one excluded challenge value per usable
row. `foldPoly_injective_of_length_eq` then proves the separate `θ` step:
equal-length tuples with equal compressions are equal outside their explicit
compression-difference root set. `EnabledLookup.thetaBadSet` unions those roots over
the usable table rows and bounds the event by
`usableRows × tupleArity / |Fp|`.

`EnabledLookup.DeployedWitness` packages the remaining representation facts for one
activation: the matching resolver input/table polynomials, row-evaluation coherence,
usable-row count, tuple arity, scalar subset, and good `θ`. Finally,
`FullCircuitBridge` combines those lookup witnesses with gate/fixed satisfaction and
the copy-replay witness. Its `satisfaction_or_bad` theorem returns the exact
`FullCircuitSatisfaction` record, and `constraints_or_bad` returns Clean's single
ground-truth `Halo2.Constraints`. The remaining Action-specific work is therefore
construction of these records, not another semantic proof.
`FullCircuitBridge.ofTopLevelCanonical` is now the circuit-integration join for one
proof: from the circuit-derived canonical constraint model it constructs the gate
and lookup fields itself, then combines them with fixed/table satisfaction and the
copy-replay witness. `bundleTopLevelSoundness_or_bad` lifts any such family to all
proof indices while preserving one shared exceptional event. Thus neither the
one-proof nor bundle join needs an Action-specific gate/lookup reassembly theorem.

The lookup representation boundary is now generic.
`LookupProjection` follows the actual threaded `eraseLookups` compiler walk, selects
the configured argument corresponding to any lookup index, and proves that both
derived pinned tuples evaluate like their selector-substituted Clean source
expressions under the final resolver query layouts. `TopLevelLookups` then routes an
enabled operation through configure/synthesis closure, proves that its compressed
resolver input and table polynomials evaluate to the concrete Clean tuples, and
constructs the one-lookup and whole-operation-stream deployed witness families.
The remaining concrete selector fact is intentionally stronger than the gate
analogue: lookup selectors must have their exact zero/one activation values, not
merely a nonzero scale. Orchard's lookup selectors are complex/lookup-only selectors,
so the fixed-layout constructor should derive that exact projection from their packed
columns rather than expose it as an Action assumption.
The generic boundary now quantifies only selector leaves that actually occur in the
selected lookup's input expressions; unrelated gate selectors may legitimately be
active at the same absolute row. `LookupSelectorRows` transports exact dense packed
rows through fixed-polynomial binding into that expression-level projection.
`TopLevelCircuit` briefly carried two generic operation-stream laws for this seam:
`lookupRelevantSelectorActivationsExact`, saying that every selector leaf used by a
lookup input is activated at the lookup row exactly when it appears in that
operation's enabled-selector list, and `lookupInputsNoSimpleSelectors`, ruling out
the simple-selector overlap case that selector packing cannot represent exactly.
Neither field was ever read by a keygen or verifier theorem — lookup projection
coverage is obtained by counting selector indices instead — so both fields and the
compositional Action proofs that discharged them have been withdrawn. Halo 2's
rejection of simple selectors in lookup arguments is consequently not modelled; see
`Zcash/Circuits/Integration/lawfulness-and-certificate-elimination.md` for the shape
a future keygen-fidelity theorem would need to restore.

The remaining placement half is deliberately narrower: transport this exact
operation-level accounting through V1's concrete region starts and the derived
selector-compression map. The short-term path is a guarded V1 selector-placement
certificate specialized only at this compiler seam. This is an explicit unblocker,
not a claim that the allocator's full cell-disjointness theorem has been proved.
The preferred structural replacement remains the generic compiler invariant that
distinct regions never overlap in cells; once available, it should make the guard
fall out compositionally and remove the finite certificate.

That guarded path is now implemented in Clean. `V1.planOperations` first tries the
ordinary shared-column placement, but accepts it only when
`PlacedLookupSelectorRowsExact` directly checks the semantic seam: for every selector
leaf of every placed lookup input, membership in the global activation table at that
row is equivalent to membership in the operation's enabled-selector list. If the
candidate fails, V1 falls back to a globally separated placement. The generic
`PlacedLookupSelectorRowsExact.placed` theorem combines this guard with the
region-local `TopLevelCircuit` law; it does not assume a stronger, unproved allocator
theorem. The Action candidate passes this guard and retains its fixture-compatible
placement.

`LookupSelectorRows.inputSelectorLeafRowsExact_of_realizes` now performs the next
generic step. The interim required-entry list emits the expected zero/one cell for a
singleton root-one packed selector, and deliberately emits an out-of-bounds sentinel
if a relevant leaf is missing from the map or has any other packing. Consequently a
proof of the shared fixed realization boundary both rules out the malformed cases and
supplies the exact lookup valuation. `ActionLookupSelectorRows` merely instantiates
this generic theorem with the shared `TopLevelFixedCoherence`; it carries no
Action-specific selector law. The binding-aware Action encoding endpoint then derives
`InputSelectorValuesRealized` internally for every proof and lookup; the former free
`lookupSelectorValues` premise has been removed from the canonical,
accepted-circuit-satisfaction, and accepted-node-binding APIs.

The generic gate and fixed/table operation layers are now implemented as well.
`operationEnabledGates` extracts every placed activation and
`gate_constraints_iff_enabledGates` proves exact equivalence with the gate family.
`EnabledGate.PolynomialWitness` identifies each enabled Clean constraint with one
member of #91's selected polynomial gate family and transports verifier-side
vanishing to Clean's enabled-gate semantics. Selector compression still supplies a
nonzero packed-selector value, but the bridge needs only the one-sided vanishing
implication rather than an exact scaling equation.
`operationFixedRequirements` similarly extracts fixed assignments and table loads,
with `fixed_constraints_iff_requirements` proving exact equivalence to the fixed
family. `FullCircuitBridge.ofPolynomialWitnesses` assembles these gate/fixed witnesses
with the existing copy and lookup witnesses.

Configure/synthesis registration coherence is now enforced at the generic keygen
boundary rather than certified by each concrete circuit. `ConstraintSystem.closeWithOperations`
preserves the raw configure order and appends the first occurrence of every gate or
lookup enabled only by synthesis, including the query registrations that affect
blinding factors. `FormalCircuit.toConstraintSystem` exposes that closed system and
`toPinnedCS` uses it consistently for domain sizing, selector compression, and
projection. For faithful circuits such as Action the closure is inert, as checked by
the existing VK/layout fixtures. `OperationsKeygenCoherent.closeWithOperations` proves
the former registration premise once by construction, and `TopLevelCircuit.keygenCoherent`
instantiates it without an Action certificate. `OperationsKeygenCoherent.gate` and
.lookup` still provide the convenient transport from an extracted activation to
membership in the closed CS. Every `Gate` now carries its own `Gate.WellFormed` law,
so no completed-circuit sidecar is needed.

The selector-compression bridge is proved in `GateProjection`.
`eval_substSelectorMap_zero_imp_queryEval_zero` proves that a compressed verifier
gate's vanishing implies Clean enabled-gate vanishing whenever the ordinary query
valuations agree, the packed selector is nonzero, and the gate's intrinsic
well-formedness law holds. `Gate.withSelector` derives that law automatically from
selector-free ungated bodies; the witness-point gate supplies the only custom proof.

The resolver representation now follows Halo2's query indexing exactly. An `Expr`
leaf indexes a VK query-layout entry `(column, rotation)`, so
`constraintModelOfResolver` feeds it the decoded base column composed with
`ω^rotation · X`, rather than incorrectly treating the query index as a column index.
`resolverQueryFeeds_interpret` proves that these three rotated feeds interpret Clean's
row environment on every domain row. `enabledGatePolynomialWitnessOfResolver` then
combines that interpretation, pinned-CS gate equality, configure coherence, and
selector compression into the `EnabledGate.PolynomialWitness` consumed by the generic
gate-satisfaction bridge.

Gate well-formedness is now correct by construction. All ordinary circuit gates use
`Gate.withSelector`, whose default `selector_free` proof produces the intrinsic
one-sided law without changing call-site syntax. The custom witness-point gate proves
the same law directly. This removes the former 1,285-line Action gate-coherence
sidecar and the generic configure-state preservation machinery it depended on.

The selector compiler layer is now generic as well. The greedy packing proof shows
that every compression-map entry has a positive assigned root, that the root is at
most its combination length, and—more tightly—that every combination length is
bounded by the constraint system's compression degree. Consequently
`selectorRootsWellFormed_deriveSelCompressMap` proves `SelectorRootsWellFormed` from
the minimal field-size condition `csDegree cs < scalarFieldOrder`, independent of the
total selector count. This avoids normalizing the Action configure program merely to
discover that it has 56 selectors; the required bound is the ordinary generic
keygen-degree bound instead, not an Action-specific fact or fixture computation.
The complementary coverage theorem
`deriveSelCompressMap_lookup_isSome_of_lt` proves that this same generic compiler
produces a compression-map entry for every allocated selector index
`selector < cs.numSelectors`: the greedy partition may regroup selectors into packed
columns, but cannot drop one. This closes map coverage independently of Action. A
distinct configure-side obligation still has to show that selector atoms occurring
syntactically in configured gate expressions are allocated indices; semantic
`Gate.WellFormed` alone intentionally does not imply that stronger syntactic fact.
`ConstraintSystem.GateSelectorsAllocated` now states that obligation precisely:
each gate's distinguished selector and every selector atom in every constraint are
below `cs.numSelectors`. The monotonicity lemma for `selectorsCovered` and
`gateSelectorsCovered_deriveSelCompressMap` then turn that single configure
certificate into the exact projection-coverage premise. There is no Action-specific
compression-map computation or selector-count proof left.
For lookup-only selectors, `process_lookup_degreeZero_of_mem` proves structurally that
degree-zero descriptions are packed alone with combination length and assigned root
both equal to one. `deriveSelCompressMap_lookup_degreeZero_of_lt` carries that result
through the circuit-derived fixed-column offset and proves that the packed column lies
in the newly appended selector-column suffix.

For activations, `mem_selectorFixed_of_activation` proves that every synthesized
`(selector, row)` with a compression-map entry is emitted by the generic
`Fixtures.Layout.selectorFixed` compiler as the expected packed fixed assignment.
`selectorActivationsRealized_of_selectorFixed` then reduces
`SelectorActivationsRealized` to one precise downstream obligation: the environment's
fixed-column reads realize those emitted assignments. The incoming circuit-owned VK
construction can discharge that obligation by identifying its fixed polynomials with
the layout compiler output; no Action-specific activation-placement argument remains.
The polynomial side of that connection is already generic:
`selectorActivationsRealized_of_fixedRowPolynomials` takes dense fixed-row lists,
their common domain length, valid selector roots, and the expected sparse-to-dense
cell equalities, then uses canonical Lagrange interpolation to prove that the
resulting polynomial environment realizes every selector activation. It needs no
separate placement-bound premise: an out-of-domain dense-list read would be zero,
contradicting the valid selector root's proved nonzeroness. Its converse compiler
lemma establishes independently that an emitted selector assignment cannot invent a
row absent from the source activation list. Thus the circuit-owned VK need only
expose its dense fixed rows and prove the ordinary layout/scatter equations; selector
semantics does not enter VK assembly.

The same polynomial-to-layout step now covers the complete fixed family, not only
selector activations. `FixedLayout.constraints_of_fixedRowPolynomials` proves that
canonical row interpolation satisfies every table load and placed fixed assignment
emitted by the layout compiler, provided the dense rows contain those sparse entries
and the emitted rows fit the domain. The remaining fixed-side work is therefore to
derive those two compiler facts from `TopLevelCircuit` keygen data and feed this
theorem to `FullCircuitBridge.ofPolynomialWitnesses`.

The commitment-provenance half of that work is now generic too.
`assembleQueries_fixed_commitment` proves that an assembled `.fixedCol` query carries
the corresponding commitment from the accepted VK, and the canonical member route
retains that identity at the decoded member position.
`fixedColumn_eq_rowPolynomial_or_relation` compares the member's augmented opening
with the Lagrange commitment to the keygen row vector. It returns either equality
with the canonical interpolated row polynomial or a computed nontrivial relation
among `(g, U, W)`. Consequently fixed and selector satisfaction will not silently
assume commitment binding: the integration theorem exposes the same exceptional
branch that the deployed probability layer must price.
`TopLevelFixedCoherence` packages the proof-independent keygen data—dense rows,
their Lagrange commitments, static fixed-query-layout coverage, and sparse-to-dense
layout correctness. Generic layout-to-assembly routing turns that static coverage
into the actual verifier query for any proof string and challenges.
`topLevelFixedConstraints_or_relation` uses that package to discharge
both selector activations and all fixed/table operations for a resolver assignment.
The constructor is now instantiated through the
`TopLevelCircuit.toVerifierKey` pipeline:

- the generic keygen half is complete on this branch: `denseColumns` is rectangular,
  each entry of `fixedCommitmentsOf` is the Lagrange commitment of the corresponding
  dense row, and `TopLevelFixedCoherence.ofKeygen` derives the rows, key,
  commitments, and fixed-query count;
- `ActionFixedCoherence.ofKeygen` supplies the Action layout premises and leaves only
  the URS's generic Lagrange-basis setup equations to its caller.

The commitment proof is factored through a small one-row Lagrange-MSM theorem and
explicit projection simp lemmas for `ofOperations`, `verifierKeyAt`, and
`toVerifierKey`; downstream proofs do not unfold the VK constructor. Fixed keygen uses
the complete executable derived Lagrange list through
`LagrangeCommitmentKey.ofFullList`, so this constructor has no noncomputable
interpolation fallback.

The concrete sparse-to-dense and query-coverage premises are currently closed through
prominently **interim** finite diagnostics.
`interimFixedRealizationFailures` lists required fixed/table/selector writes whose
final dense cell has the wrong bounds or value, and its generic soundness theorem
turns an empty list into the exact realization fact.
`ActionFixedCoherence.realizationFailures_eq_nil` certifies the Action list is empty.
The companion query diagnostic closes both directions of the current
all-fixed-columns boundary: every allocated fixed column is queried and every queried
fixed column is allocated. The latter makes out-of-range commitment identities
provably absent from the verifier resolver. Both directions remain interim compiler
lawfulness debt.

For the current lookup-selector milestone, the required set also contains the exact
singleton packed-selector cell at every lookup input leaf: the assigned root when the
operation enables that selector and zero otherwise. This deliberately reuses the
existing, prominently interim sparse-to-dense certificate instead of introducing a
second Action-specific computation. It is an unblocker, not the intended final
layout proof.

The generic scatter semantics no longer needs computation:
`denseColumns_getD_getD_eq_zero_of_no_target` proves that an unwritten in-domain cell
retains the zero initializer, while
`denseColumns_getD_getD_eq_of_last_write` proves that the final sparse write to a cell
determines its dense value. These are the assembly lemmas for both disabled selector
rows and ordinary fixed realization; the remaining work is to prove the required
no-later-collision facts from the producers of the sparse stream.

Their intended replacement follows the compiler pipeline: prove that V1 regions are
disjoint in cells, prove small region-local write obligations, establish the
table/constant/selector-packing collision and composition laws, and assemble them
through generic last-write/dedup/scatter semantics. Query coverage should likewise
follow query registration, preferably after weakening the coherence interface to
request commitments only for columns actually consumed by the semantic bridge.

The structural replacement has been narrowed to concrete generic lemmas. The sorter
and last-write HashMap pass must prove that every final sparse entry originates in
the raw table/constant/selector/region stream; the synthesis-closed constraint system
must close `numFixedColumns` over every configured constant, loaded table, and
region-local fixed assignment; and degree-zero selector packing must prove singleton
column ownership. Together with the direct V1 guard, those facts prove disabled
lookup-selector cells remain zero without inspecting the full Action artifact.
To derive degree zero from the existing no-simple-selector synthesis law, the
compiler should additionally carry selector-kind consistency by allocated index:
two selectors with the same index must agree on the `simple` flag. This property is
not implied by the current interface because `selectorMaxDegrees` keys only by the
numeric index.

The generic operation walk already proves that every extracted enabled gate occurs in
the floor-planner activation table, and `selectorScale_ne_zero_of_enabledGate` turns
the two contracts into the required nonzero scale. The remaining gate work is now to
connect circuit-derived fixed rows and polynomials to the emitted layout assignments,
with only the generic degree-below-field-order condition. The evaluation and
resolver-membership algebra is no longer circuit-specific.

`TopLevelCircuit.selectorActivations` and `.selectorMap` now expose those two keygen
objects directly, and `pinnedCS_eq_derive` identifies the circuit's existing pinned
constraint system with that exact map. The final pinned query state is also proved to
extend the intermediate gate-erasure state (`derive_queryState_extends_gates`), so
lookup projection may append query entries without forcing a false equality between
the VK's final layouts and the earlier gate state.

`TopLevelGateCoherence` is the generic static boundary to the circuit-owned verifying
key. It is now parameterized by proof parameters and a URS, and all of its
verifier-side objects use `top.toVerifierKey pp urs`; an arbitrary key cannot be paired
with a circuit. Gate expressions and query layouts are therefore obtained in keygen's
construction direction rather than restated as caller hypotheses. Its
`polynomialWitness` theorem derives the resolver witness for every enabled constraint
using only the top-level circuit's own operations, placement, selector map, pinned
projection, and the decoded fixed-polynomial realization.
`TopLevelGateCoherence.constraints` then supplies the complete gate field of Clean's
constraint satisfaction. Gate well-formedness is read directly from each selected
gate rather than supplied by this package. The concrete Action constructor is complete; the
remaining gate-adjacent work belongs to the fixed stream, which connects the derived
VK's dense fixed rows to `SelectorActivationsRealized`.

The configure proof for `GateSelectorsAllocated` now has a reusable local interface.
`Gate.SelectorsOwned` says a gate mentions no selector other than its distinguished
one, and `Gate.selectorsOwned_of_withSelector` derives it structurally from the same
selector-free bodies already used by the semantic gate-shape proof. Allocation is
monotone as selector counters increase. `PreservesGateSelectorsAllocated` supplies
the ordinary state-monad preservation rules and direct certificates for the common
simple- or complex-selector/create-gate leaf patterns. Generic relational rules retain
fresh-index facts across multi-selector gate groups, mixed selector/lookup programs,
and child programs that consume a selector allocated by their parent. The
continuation form of the selector/create-gate rule also avoids elaborating a large
reassociated state-monad term while keeping the 20,000-heartbeat debugging bound.

`Action.SelectorCoherence` now completes the circuit instantiation without touching
the VK path. It proves ownership and configure preservation for the ordinary leaves,
LookupRangeCheck, variable- and fixed-base ECC (including the parent-allocated
running-sum selector), Poseidon, NoteCommit, both Sinsemilla gate forms, and Merkle,
then composes them in the exact `Action.Circuit.configure` registration order. Thus
`Action.Circuit.configure_preservesGateSelectorsAllocated` is the compact
circuit-derived certificate required by `TopLevelGateCoherence`. Together with the
intrinsic well-formedness of every `Gate`, it feeds
`ActionGateCoherence.topLevelGateCoherence`, which also discharges the three query
counts and the domain/degree bounds for the derived Action key. A sealed,
equality-pinned configure handle keeps the `fromEmpty` proof structural without
normalizing the full configure monad. This closes the configure-side gate/selector
obligation. It does not claim the separate lookup-expression selector-coverage
property required by `TopLevelLookupCoherence`; that property and exact packed-selector
realization remain part of the lookup/fixed compiler boundary.

The `Fixtures.Layout` reconstruction is generic over operations, and σ-cycle
correctness of its replayed keygen merge is now proved once and for all:
`runAssembly_getPair` identifies the executable assembly mapping with
`replayKeygenPermutation`.

### 5. Construct the Clean assignment

**Status: the generic VK-free assignment shell and a circuit-derived Action
decoded-member constructor are implemented. The merged
[#89](https://github.com/zcash/ironwood/pull/89) supplies the target semantics, while
[#30](https://github.com/zcash/ironwood/pull/30) and
[#91](https://github.com/zcash/ironwood/pull/91) supply most of the prospective source
data.**

From the recovered per-column row values, build:

- a `ProofAssignment` containing only advice and instance reads;
- the circuit-owned environment, which compiles fixed rows and usable rows;
- the circuit-owned post-NU6.3 floor-planner placement and configuration;
- the unit input of the closed Action circuit.

The generic top-level boundary and the Action-side closure are now implemented.
`TopLevelCircuit` holds a `FormalCircuit` with unit configuration input, synthesis
input, and output; requires its public `Assumptions` predicate to be exactly `True`;
and provides verifier- and prover-side theorems with no exposed `EnvAssumptions`
premise. Its single `closesEnvironment` law states only the residual environment
facts that cannot be derived from both constraints and witness extension.
`TopLevelCircuit.Statement` receives the circuit's explicit public-input value and
existentially hides only its private witness. The generic SNARK bridge extracts that
public value through the circuit-declared instance-cell layout; the Action adapter
then identifies it with the ten values committed by the verifier.

The generic keygen layer now derives from the top-level circuit itself:

- `TopLevelCircuit.pinnedCS` runs `FormalCircuit.toPinnedCS` on the circuit's fixed
  configuration input and unit synthesis input;
- `regionStarts` and `placement` run the V1 floor planner over the circuit's own
  operation stream;
- `domainExponent` runs `minimalK` on the same configured CS and operation stream;
  `usedRows`, `blindingFactors`, `usableRowsAt`, and `FitsAt` state the keygen domain
fit entirely in circuit-owned terms;
- `TopLevelCircuit.environment` combines the compiled fixed rows and usable-row
  bound with a proof-varying advice/instance assignment.

The fixed-data bridge now reaches the keygen layout compiler as well.
`FixedLayout.mem_tableFixed_of_loadTable_of_lt` and `_of_fill` cover both the explicit
table block and Halo 2's default-filled tail, while
`mem_regionAssignFixed_of_requirement` connects each extracted region requirement to
its V1 absolute row. Consequently `FixedLayout.constraints_of_entries` proves the
entire Clean `.fixed` family from realization of the raw sparse entries emitted by
`Layout.tableFixed ++ Layout.regionAssignFixed`. The remaining representation step is
intentionally narrow: the circuit-owned key builder must show that its
deduplicated/scattered dense fixed rows, and then their interpolated polynomials,
realize those raw entries. No Action operation-list proof remains.

The domain algebra is kernel-reusable as well. `Bridge.powFast_eq_pow` connects the
executable binary exponentiation to ordinary powers, and
`omegaOf_isPrimitiveRoot`, `omegaOf_domain`, and `omegaOf_powers_injective` derive the
size-`2^k` root, vanishing-domain equation, and distinct row nodes from CompElliptic's
certified Pasta `2^32` root for every supported `k`. A single native-tier equality
connects the executable generator spelling to that certified root; `omegaOf` itself
remains pure, so generic assignment and Action semantic theorems retain their standard
axiom tier. Concrete Action proofs no longer need fixture-specific hypotheses for
these domain facts.

`TopLevelAssignment` is the corresponding verifier-to-Clean assignment shell. It is
indexed by a bundle proof index and stores only the commitment-ID polynomial resolver;
a family `∀ p, TopLevelAssignment top numProofs p` therefore cannot silently read a
different member's advice or instance columns. The top-level circuit supplies its
operations, V1 placement, derived domain exponent, blinding rows, and usable-row fit;
`Bridge.omegaOf top.domainExponent` supplies the protocol domain root. Consequently
the type has neither an arbitrary domain nor a `VerifyingKey` argument, and
`TopLevelAssignment.proofAssignment` exposes only the proof-varying advice and
instance reads. `TopLevelCircuit.environment` adds the circuit-derived fixed rows and
usable-row bound.

The deployed capstone constructs this shell internally through the canonical
accepted-member route, so the decoder never accepts an arbitrary verifying key: it
uses `actionCircuit.toVerifierKey pp urs`, whose shape, scalar, gates,
query layouts, fixed commitments, permutation commitments and lookup data are all
derived from the configured Action circuit and supplied URS, with no separate shape
or shape/domain coherence premise. (The former standalone constructor,
`TopLevelAssignment.ofActionDecodedMembers`, was deleted once the capstone chain left
it without a consumer.) The reusable derivation remains independent of the captured
fixture; the deliberately expensive `Keygen.Certificate` separately proves that the
captured deployed key equals that derived key.

On the SNARK side, `FullCircuitSatisfaction.topLevelSoundness` composes exact
gate/copy/lookup/fixed satisfaction with that generic top-level endpoint.
`FullCircuitBridge.topLevelSoundness_or_bad` performs the same composition while
preserving the bridge's shared exceptional event. Neither theorem mentions the
Action circuit, an Action-specific placement, or Action-specific operations.

The Action-specific public boundary is intentionally small.
`Action.PublicInputs` names the ten instance-column rows in protocol order, and the
single concrete `Action.actionCircuit` owns the complete post-NU6.3 specification at
the real generators and bases. There is no separate Action statement wrapper:
capstones conclude `actionCircuit.Statement` directly, while
`Action.BundleStatement` merely quantifies that statement over every proof index.
The remaining public-input obligation is to identify each decoded instance
polynomial with the values supplied to the verifier.

That row-identification lemma now consumes `TopLevelAssignment` directly. Its domain
root is `Bridge.omegaOf k`, its instance column is selected by the assignment's proof
index, and it no longer accepts an arbitrary verifier key. This is the intentionally
small Action-specific part: it only maps the first ten rows into `Action.PublicInputs`;
assignment construction and domain/layout choices remain generic.

`Action.actionCircuit` instantiates that boundary. It projects the initial
Sinsemilla generator-table load from the real `mainPost` operation stream and derives:

- exact generator-table contents and all four shared Sinsemilla table-loaded facts;
- the shared 10-bit range table from the generator table's index column;
- the fixed-base configuration equalities and lookup-selector distinctness produced
  by `Action.Circuit.configure`.

The prover-side closure projects the same load from `ExtendsWitnesses` and converts
its fixed-table clauses to the corresponding constraints. The deployed
`actionCircuit` specializes this generic Action construction to the
real generators and certified bases. Clean constraints remain on the generic
integration side of the boundary: the security-layer bridge begins with the
Action-native `SpecPost` and refines it to the ledger statement, rather than
repeating the generic constraint-to-specification argument.

The legacy `ActionAssignment` has been deleted. Its decoded constructor now returns
the generic `TopLevelAssignment` indexed by `actionCircuit`, so
placement, operations, domain exponent, blinding factors, and usable rows all come
from the top-level circuit. The only Action-specific work left in this layer is the
deployed decoder routing; the verifier key itself is now obtained generically from
the top-level circuit.

The compositional base and post-Ironwood `FormalCircuit`s intentionally retain their
`EnvAssumptions`: child circuits may state contracts that a parent fulfills.
`TopLevelCircuit` is the separate deployment boundary that closes those contracts.
The full-satisfaction-to-statement step now consumes the canonical
`top.environment assignment`. Fixed-column commitment binding proves
`FixedColumnEncoding`, which identifies the verifier resolver environment with that
canonical environment before the generic soundness terminal is invoked. Gate,
fixed, copy, lookup, and public-instance reconstruction are all instantiated in the
Action endpoint.

After #79's merge, the generic circuit-integration declarations are checked in the
single `Zcash/TrustBoundary.lean` census with explicit standard or Vesta-native axiom
budgets. The concrete Action adapter is not independently claimed at the standard
SNARK tier: mentioning the Action `FormalCircuit` intentionally reaches the circuit
formalization's existing Pallas/native facts. The eventual end-to-end Action capstone
must price that concrete circuit trust once, at the final boundary, rather than
smuggling it into a supposedly generic adapter.

The Action top-level closure obtains its substantive `EnvAssumptions` from the
transported `Constraints` rather than separate VK-fixed-data facts:
`GeneratorTableExact` is defined as the `Constraints` of the generator-table load,
and the Action circuit's own operations contain the `loadTable`/`assignFixed` steps
whose transported clauses pin the same fixed cells the table-loaded and fixed-base
assumptions read.

### 6. Generalize from one Action to an Orchard bundle

**Status: verifier-side substrate is generic in #30/#91 and exercised by the merged
[#85](https://github.com/zcash/ironwood/pull/85). The assignment, external statement,
canonical relation, public-instance commitment, Action endpoint, lookup challenge
packaging, generic full-bridge join, concrete copy replay, and fixed-row lookup
selector realization are bundle-indexed.**

A deployed proof covers `shape.numProofs` Actions. Generalize the public-input family,
`TopLevelAssignment`, and `Action.BundleStatement` to a `Fin shape.numProofs` family
and decode one Clean assignment per sub-proof. The shared fixed columns and VK are
common, while advice/instance columns and protocol statements are per Action. The
final conclusion should quantify over or return the high-level statement for every
supplied Action.

`TopLevelAssignment.Bundle top numProofs` is the dependent family
`∀ p, TopLevelAssignment top numProofs p`, so each member is forced to resolve the
columns named by its own index. `Action.BundleStatement inputs` is the matching
external conclusion `∀ p, Action.actionCircuit.Statement (inputs p)`. No separate
monolithic bundle witness is required: fixed columns and the circuit-derived VK
remain shared, while decoded advice/instance polynomials and extracted `ActionData`
remain per-member.

#85's multi-Action fixture derives each proof's instance commitment and proves that
sub-proof commitment slots remain disjoint. The accepted-route selector and Vesta
terminal now reconstruct advice and instance feeds separately for every
`Fin shape.numProofs`; there is no distinguished proof index or singleton-shape
premise. `action_bundleStatement_or_relation_of_deployedAccepts` exposes that fact at
the public API over arbitrary `ProofParams` and returns the bundle-wide Action
statement.

### 7. Thread the bridge into the live capstone

**Status: complete at the deterministic Vesta terminal. The canonical relation now
reaches a concrete bundle-wide Action theorem, and
the circuit-generic
`topLevelBundleStatement_or_relation_of_deployedAccepts` now performs the core join
for an arbitrary `TopLevelCircuit`. `TopLevelCircuitCorrectness` exposes the named
gate, fixed/selector, copy, and lookup representation boundaries and deliberately
contains neither the desired statement nor an opaque encoding implication.
`action_bundleStatement_or_relation_of_deployedAccepts` specializes that theorem with
the Action correctness constructor, then identifies the primary instance
polynomial and presents the circuit-owned statement as `Action.BundleStatement`.
Both the generic and Action theorems quantify over arbitrary proof parameters and
reconstruct accepted member selections proof-by-proof. Their public signatures have
no free `S`, `hencodes`, member decoder, or independently selected advice/instance
feeds. The captured-VK theorem is only a deployment corollary in
`Soundness/Deployed/ActionVesta`; it is not imported by the normal `Zcash` target.
The remaining quantitative Fiat–Shamir/adaptive-coupling work is a separate
probability-layer composition. Substantial foundations are in
[#30](https://github.com/zcash/ironwood/pull/30),
[#91](https://github.com/zcash/ironwood/pull/91), and
the merged [#85](https://github.com/zcash/ironwood/pull/85).**

Once the direct semantic bridge exists, instantiate the Vesta constraint capstones
with the concrete high-level Action statement. Then thread that same concrete
statement through the computed Fiat–Shamir/AGM endpoint.

#30 adds `orchard_verifier_sound_vesta_computed`, whose original circuit predicate was
the concrete gate check over decoded member columns rather than a free decoder. This
branch now strengthens that endpoint's extracted relation with exact
`FullCircuitSatisfaction` of the same witness and carries both facts in
`circuitSatViaGatesAndOperations`. This is type-level plumbing, not yet the final
derivation: the endpoint currently receives the full-satisfaction proof and decoded
environment as inputs. Supplying them from the deployed constraint split and the
Action records is the next representation step.

The computed endpoint still receives batch/decode/gate/layout data by hand, and its
quantitative endpoint remains conditional on the family-wide
`hExtract`/adaptive-coupling data-supply premise. The merged #85 threads
statement-derived instance commitments through the live verifier. #82 documents the computed capstone
and #79 provides the eventual trust-boundary census location.

At the deterministic seam,
`canonicalRoutingConditions_of_accepts` now obtains the grouped-set count and
duplicate-query rejection directly from `DeployedAccepts`.
`CanonicalMemberConstraintRelation.ofAcceptedCircuitSat` uses those facts to turn
satisfaction of the accepted run's canonical decoded-member model into the exact
relation consumed by circuit integration.
`Soundness/Deployed/ActionVesta` carries the transport ingredients for the deployed
seam — the fixture `k`-match and blinding-factor facts (`shape_k_eq_capturedURS_k`,
`vk_blindingFactors_lt`); the public-instance commitment is the circuit-native
`ActionInstanceCommitment.commitment`, used directly at the captured shape. They carry
the generic Action/Vesta statements to the captured artifacts along
the keygen certificate. The deployed capstone in `Soundness/Deployed/ActionVesta`
consumes satisfaction of the canonical accepted model through that transport.
`AcceptedModelClaimedEvaluations` is the corresponding verifier-native node-binding
fingerprint: it states once that the canonical model's fixed/advice/instance,
permutation, lookup, and row-selector polynomials evaluate to the accepted proof
claims at `x`.
`AcceptedModelClaimedEvaluations.ofOpenings` now constructs that fingerprint rather
than asking a terminal caller to restate its nine component families. Its uniform
opening premise ranges over the actual `assembleQueries` result and uses the accepted
member decoder's canonical `CommitmentId` resolver. From that one premise it derives
the fixed, advice, instance, permutation-set, permutation-chunk, and lookup
evaluations; the canonical Lagrange-polynomial theorem derives `l₀`, `l_last`, and
`l_blind`. The three query-layout count equalities replace the former three arbitrary
column-feed equations.
`CanonicalMemberConstraintRelation.acceptedPolynomial_opens_or_relation` then derives
the uniform opening family itself from acceptance and decoded member-node binding.
`AcceptedModelClaimedEvaluations.ofNodeBinding_or_relation` packages the complete
result, retaining the same augmented commitment-relation branch if a node fails to
bind. Thus the remaining direct input from the decoded-column layer is its actual
node-binding property, not a free decoder or a restated family of query equations.
`acceptedModel_circuitSat_or_relation` feeds the resulting package to the deployed
quotient-member theorem and returns satisfaction of the same canonical model, or the
shared augmented commitment relation. The terminal no longer needs to choose
unrelated advice and instance decoder functions or independently supply the derived
permutation/lookup/selector evaluations.
`ActionInstanceCommitment.action_bundleStatement_or_relation_of_acceptedModel_circuitSat`
then constructs the concrete Action bundle statement from that satisfaction result,
with no free `S`, `hencodes`, relation, or operation-constraint family. Fixed/table
coherence, exact packed lookup-selector realization, and the complete copy replay
witness are now constructed internally. The permutation and lookup challenge
exclusions remain explicit because they are probability-layer events. This theorem
is the function to substitute at the live constraint terminal's `hencodes` argument.

That substitution is now expressed directly, without preserving the abstract
argument.
`ActionInstanceCommitment.action_bundleStatement_or_relation_of_decodedMemberPolynomial_eq`
specializes the canonical terminal to
`actionCircuit.toVerifierKey`, derives all query-layout, permutation,
and domain facts from that circuit-owned key, and feeds canonical satisfaction into
the Action endpoint. Its conclusion is exactly the concrete `Action.BundleStatement`
or the shared augmented-basis relation. The theorem has no arbitrary key, decoder,
constraint model, `S`, or `hencodes`; only explicitly priced good-challenge facts
remain.

At the captured artifacts, the deployed capstone is the corresponding direct
receiver for a `CircuitSat` proof over the canonical accepted model, obtained by
transporting the generic Action/Vesta capstone.
`Soundness/Multiopen/CanonicalSelection` now constructs the advice and
instance slots forced by `CanonicalMemberConstraintRelation.acceptedRoute` and proves
that their full polynomial feeds equal the canonical accepted model's feeds.
`Soundness/Canonical/Vesta` specializes the verifier-native terminal's former free
callback to `CircuitSat` for that model and derives the accepted selections for every
proof index. `Snark/Soundness/TopLevelTerminal` generically turns the resulting
canonical constraint satisfaction and the circuit's component correctness package
into `TopLevelBundleStatement`; `Snark/Soundness/TopLevelVesta` is the corresponding
circuit-generic Vesta capstone. `Snark/Soundness/ActionVesta` supplies the Action
package, derived shape, VK, and public-instance commitments, and performs only the
final Action statement presentation. `Snark/Soundness/Deployed/ActionVesta` only
transports the captured single-Action artifacts to that result. These route
equalities are generic multiopen facts, not Action synthesis or floor-planner
obligations. The recent tail of #96 exposes complementary
slot-to-commitment provenance for the quantitative reroute; it is adjacent to, but
not needed for, this exact deterministic member-route identification.

The final theorem should say, modulo the explicitly priced Fiat–Shamir, polynomial
identity, and discrete-log failure events, that acceptance by the modeled deployed
verifier with the post-NU6.3 Action VK yields the high-level statement for every Action
whose public inputs were committed by the verifier.

## Suggested implementation order

0. **Complete:** close both Action circuit inputs to `unit`, instantiate prover choices
   through the hint-backed witness program, and derive the operation stream from the
   real proof-carrying circuit.
1. **Complete:** instantiate the full constraint split at the canonical deployed
   resolver, including the domain-selector, permutation, and lookup semantic
   endpoints.
2. **Complete generically:** derive the pinned CS, V1 placement, domain, verifying key,
   polynomial row environment, gate witnesses, and lookup witnesses from
   `TopLevelCircuit`. The executable permutation assembly is now proved equal to the
   abstract copy replay, and the concrete Action gate-coherence package is complete.
3. **Complete:** derive exact packed-selector projection for lookups from the
   circuit-owned fixed rows. `ActionFixedCoherence.ofDerived` now obtains the complete
   Lagrange setup from the symbolic FFT theorem and the Action endpoint constructs it
   internally. The σ cycle, pairwise value transport, constants, endpoint reads, and
   complete `CopyReplayWitness` are also constructed internally. The two Action fixed
   diagnostics remain explicitly interim pending their structural compiler
   replacements. Lookup configure lawfulness, activation-row fit, bundle-wide
   challenge packaging, and public-instance provenance are complete. The configured
   top-level synthesis boundary now carries exact lookup-activation and
   no-simple-selector laws. Generic `foldOps`/`foldCall` theorems reduce either law
   over a serial circuit fold to one symbolic round, with a state-independent
   interface that keeps the potentially large closed-form accumulator opaque.
   `CalculateRoot.circuit_synthesize_operations` exposes its 16-layer Merkle folds at
   precisely that boundary rather than reducing the concrete fold. The guarded V1
   packing rule and generic exact-row theorem now construct the required selector
   values inside the Action endpoint.
4. **Generic join complete:** `FullCircuitBridge.ofTopLevelCanonical` assembles one
   proof index and `bundleTopLevelSoundness_or_bad` quantifies it over every
   `Fin shape.numProofs`. Instantiate those constructors with the incoming
   fixed-selector and copy records. The external `Action.BundleStatement` endpoint
   is already implemented directly over `Action.actionCircuit.Statement`.
5. **Complete:** construct
   `AcceptedModelClaimedEvaluations` from accepted decoded-member node binding, the
   circuit-derived query-layout counts, and standard permutation/domain facts; then
   obtain canonical model satisfaction or the shared relation and compose it with
   `action_bundleStatement_or_relation_of_acceptedModel_circuitSat` in the Action-owned
   integration boundary. The resulting accepted-node-binding theorem constructs
   fixed coherence, selector realization, and copy replay internally.
6. **Complete:** replace the live constraint terminal's free `S`/`hencodes`
   argument with the concrete Action composition. The generic selected-member
   theorems identify every proof's advice and instance feeds with the accepted
   `CommitmentId` route; the circuit-derived Vesta capstone fixes the decoder and
   returns `Action.BundleStatement` or the standard nontrivial-relation alternative.
   The family-wide adaptive-coupling/`hExtract` supply problem is a distinct
   probability-layer task and may remain an explicitly conditional or residual term
   in the subsequent quantitative theorem.

## Current execution dashboard

The ownership labels below are coordination hints, not architectural boundaries.
Each work package should remain independently mergeable through the branch's
append-only merge flow.

| Marker | Work package | Current state | Delivers / unblocks |
|---|---|---|---|
| **[DONE: ProofAssignment]** | Separate proof-varying advice/instance data from circuit-derived placement, fixed rows, and usable rows. | `TopLevelAssignment.proofAssignment` uses `resolverAssignment`; `TopLevelCircuit.environment` supplies the circuit-fixed data. `FixedColumnEncoding` derives exact equality with the verifier polynomial environment, and the generic terminal now invokes top-level soundness only in that canonical environment. | Removes arbitrary synthesis environments and obsolete `SynthesisWellFormed` premises from the final semantic path. |
| **[ME] fixed compiler** | Replace the interim Action fixed-write and query-coverage diagnostics with compiler-derived laws: use region cell-disjointness to remove cross-region collisions, decompose the remainder across region-local writes, tables, constants, and selector packing, finish generic last-write/dedup/scatter semantics, and minimize query coverage to consumed columns. | Dense-row shape, full-list Lagrange commitment provenance, fixed-query count, and `TopLevelFixedCoherence.ofKeygen` are generic. Two prominently interim finite failure lists now certify Action sparse-to-dense realization and query coverage; `ActionFixedCoherence.ofKeygen` assembles them with the generic constructor. | A usable Action fixed-coherence constructor now; ultimately a compiler-derived replacement for its two interim certificates. |
| **[DONE: FFT correctness]** | Prove `bestFftG`'s DFT specification symbolically — `output[i] = Σ_k ω^{i·k} • input[k]`, by induction over the butterfly rounds (invariant: after round `r`, each `2^r` block holds the DFT of its stride-subsampled slice). | `Keygen/FftSpec.lean` proves `bestFftG_dft`, `derivedUrsGLagrange_generator_eq`, and `derivedUrsGLagrange_length`. `ActionFixedCoherence.ofDerived` now consumes those results through `ofPrefix_setup_of_closed`; no Lagrange setup premise reaches the Action endpoint. | The URS setup equations consumed by both fixed and σ commitment identification, for every supported URS. |
| **[DONE: lookup join]** | Derive exact packed-selector zero/one values for only the selector leaves occurring in each lookup input. | The guarded V1 packing path emits either the exact singleton selector row or an out-of-bounds sentinel. Shared fixed realization rules out the sentinel, and `EnabledLookup.inputSelectorLeafRowsExact_of_realizes` supplies the generic exact-row result. `ActionLookupSelectorRows` is only the thin circuit instantiation; no Action-specific planner theorem or free selector-value premise remains. | The lookup field of `FullCircuitBridge` for every Action proof index is internal to the terminal. |
| **[DONE: copy]** | Instantiate pairwise value agreement on decoded `actionCopies` from σ semantics. | `actionResolverPermutationCycle_or_relation` constructs the exact Action cycle; `actionCopyPairValue_of_resolverPermutation` proves each pair's value equality; `actionCopyReplayWitness_or_relation` packages all copies, constants, and endpoint reads. The terminal no longer accepts a copy witness. | The copy field is internal to the Action endpoint. |
| **[DONE: Action fixed/VK]** | Supply the generic Lagrange-basis setup equations to `ActionFixedCoherence.ofKeygen` and feed the resulting record into the terminal. | `ActionFixedCoherence.ofDerived` constructs the record from the circuit-owned key and symbolic FFT result. Action query coverage and sparse-to-dense realization remain closed by two explicitly interim diagnostics, but no fixed-coherence premise reaches the terminal. | The fixed/table family and its exact lookup-selector projection are internal. |
| **[DONE: instance]** | No independent work remains in the deterministic instance stream. | `ActionInstanceCommitment.instanceKey` and `.commitment` derive the key and public commitment from the URS and ten Action rows; the binding-aware bundle endpoint consumes them internally and preserves only the shared nontrivial-relation branch. | Public-instance provenance is ready for the one-proof/bundle join. |
| **[DONE: terminal API]** | Keep the canonical quotient terminal in polynomial language and perform the concrete join in `Circuits/Integration`. | `acceptedModel_circuitSat_or_relation_of_decodedMemberPolynomial_eq` reconstructs the complete accepted model and `action_bundleStatement_or_relation_of_decodedMemberPolynomial_eq` specializes it to the circuit-derived Action key and concrete bundle statement. Its signature has no free `S`/`hencodes`, fixed record, copy record, or selector-value premise. The deployed accepted-`CircuitSat` endpoint is also exported. | The deterministic semantic function is ready for invocation by the live probability capstone. |
| **[SEPARATE: ledger]** | Continue [#98](https://github.com/zcash/ironwood/pull/98)'s `SpecPost`-to-ledger refinement. | Independent of polynomial reconstruction and Clean constraint satisfaction. | The games-facing conclusion that should follow after the circuit statement is recovered. |
| **[SEPARATE: probability]** | Connect [#96](https://github.com/zcash/ironwood/pull/96)'s extraction/coupling result to the deterministic terminal and place the already-priced lookup/permutation exclusions at their transcript squeezes. | The deterministic terminal consumes decoded openings and explicit good-challenge facts; it does not solve the family-wide adaptive `hExtract` supply problem. | A quantitative live theorem around the deterministic #99 result, without reintroducing a free semantic encoding. |
| **[DONE: bundle]** | Apply the internal gate/fixed/copy/instance/lookup adapters to every accepted canonical model in the proof bundle. | The Action canonical endpoint constructs fixed coherence, exact selector projection, and copy replay per proof index. Only explicitly priced exclusions remain. | A concrete `Action.BundleStatement` over every `Fin numProofs`, with only explicitly priced exceptional events. |
| **[DONE: Vesta join]** | Invoke the accepted-`CircuitSat` Action endpoint from the live Vesta constraint theorem. | `acceptedModel_circuitSat_or_relation_of_acceptedSelections` constructs canonical advice/instance slots for every proof index. `action_bundleStatement_or_relation_of_deployedAccepts` composes the resulting `CircuitSat` fact with the circuit-derived Action theorem for arbitrary `ProofParams`; the captured theorem is only a deployed corollary. The public signature contains no free `S`/`hencodes`, decoder, selected-member feeds, separate VK, or singleton-proof premise. #96 remains adjacent quantitative work rather than a dependency of this deterministic theorem. | #99's deterministic completion criterion is met for single- and multi-proof shapes. |

The shortest dependency chain to removing `hencodes` is therefore:

```text
canonical selected-member equality (done) ─────┐
deterministic Action terminal (done) ──────────┼─> deployed Vesta join (done)
priced exclusions (explicit) ─────────────────┘      ─> no live hencodes
```

The family-wide `hExtract`/adaptive-coupling premise is deliberately absent from this
chain. It controls how the decoded data is obtained with the claimed probability; it
does not prevent #99 from proving what that data encodes.
