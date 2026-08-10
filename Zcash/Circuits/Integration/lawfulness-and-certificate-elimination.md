# Halo2 lawfulness and certificate elimination

## Status and scope

This document tracks the integration arc replacing concrete, whole-Action
computational certificates with reusable Halo2-Clean lawfulness and compiler
theorems.

The deployed verifying-key equality is intentionally **not** part of this cleanup.
Checking that the circuit-derived key equals the deployed Orchard key is a legitimate
concrete trust-boundary check. It must not, however, double as evidence that the Clean
formal circuit is internally lawful.

There are currently 22 Action-specific computations on the live integration path.
That number understates the architectural debt:

* `ActionGateCoherence.gateData_eq` bundles two independent facts;
* the original VK-match bundle contained two further non-capture wellformedness checks; and
* `ConstraintSystem.closeWithOperations` silently repairs one further missing
  configure/synthesis fact without proving that the repair is inactive.

The cleanup backlog therefore contains **26 atomic lawfulness obligations**. The
tables below keep the original 22 rows recognizable, then list the four extra atomic
obligations. The count excludes the intentional deployed-VK equality and does not
double-count the bundle's `K = 11`, which is already represented by
`domainExponent_eq`.

Two further synthesis laws, `LookupRelevantSelectorActivationsExact` and
`LookupInputsNoSimpleSelectors`, were once proved here at the wrong abstraction
layer, backed by a roughly 3,000-line Action/NoteCommit proof stack. The former was
withdrawn as consumerless. The latter is now enforced directly by lookup
registration and is therefore no longer a top-level synthesis obligation. Neither
was included in the count of 26.

The guiding rule is:

> A concrete VK comparison may establish deployment identity. It must not establish
> that a formal circuit is well formed.

## How configure/synthesis closure was eliminated

The original Clean pipeline took the raw result of `configure` and applied
`ConstraintSystem.closeWithOperations` to the synthesis stream. Closure:

1. appends gates enabled by synthesis but absent from `configure`;
2. appends lookups enabled by synthesis but absent from `configure`;
3. registers queries for those appended arguments; and
4. increases `numSelectors` when lookup expressions use selectors beyond the bound
   allocated by `configure`.

That produced a self-consistent internal object, but it was not Halo2's algorithm:
synthesis may enable only gates and lookups established by configuration.

The problem is not cured by comparing the resulting pinned CS with a captured VK.
Such a comparison says that the *repaired derivation* matches the deployed data; it
does not say that the repair was inactive. In particular, semantically redundant or
projection-equivalent repairs need not be observable in every downstream pinned
field.

Clean now packages this invariant as `FormalCircuit.KeygenLawful`. Its compositional
proofs establish gate and lookup registration for every circuit bundle, while
selector-allocation lawfulness establishes both gate-selector ownership and lookup
input bounds. Consequently the canonical top-level constraint system is the raw
configure result:

```text
rawCS := (c.configure ci {}).2
ops   := c.toOperations ci input

FormalCircuit lawfulness proves:
  every enabled gate is in rawCS.gates
  every enabled lookup is in rawCS.lookups
  every lookup selector is below rawCS.numSelectors

c.toConstraintSystem ci input = rawCS
c.toPinnedCS ci input = PinnedConstraintSystem.derive rawCS selectorMap
```

Ironwood consumes `top.keygenCoherent`, `top.gateSelectorsAllocated`, and
`top.lookupInputsAllocated` directly. The Action selector-coherence sidecar and the
closure-based repair path have been deleted.

## Classification

Each obligation receives one primary classification:

* **G — generic now:** follows from existing `FormalCircuit`, `TopLevelCircuit`, or
  compiler guarantees, with additional generic reasoning only.
* **L — local law needed:** requires a new lawfulness fact attached to the gate,
  lookup, configure program, region, circuit bundle, or operation stream that creates
  the relevant data.
* **R — remove the demand:** the concrete fact exists only because downstream code is
  specialized to Action constants; make that code consume circuit-derived data
  generically.

“Local law needed” does not mean adding a sidecar theorem next to every concrete
circuit. Laws belong in the formal-circuit package or in the object being constructed,
and should normally be discharged by default tactics and compositional theorems.

## The original 22 capstone-facing computations

| # | Current computation | Class | Structural replacement | Expected difficulty |
|---:|---|:---:|---|---|
| 1 | `queryCoverageFailures_eq_nil` | L | Gate and lookup query-support laws, plus generic registration/projection theorems. The current diagnostic checks both that every allocated fixed column is queried and that every queried column is allocated; replace both directions structurally, while narrowing coverage to semantically consumed columns. | Medium |
| 2 | `realizationFailures_eq_nil` | L | Region-local fixed-write consistency, table-load consistency, constant-allocation consistency, and selector-packing consistency; compose them using V1 shared-column non-overlap. | Hard |
| 3 | `actionNumPermCols_pos` (eliminated as a certificate) | G | Action's configured primary column witnesses nonemptiness; no exact column-count computation is needed. | Done |
| 4 | `actionCopyColumnBounds` (eliminated as a certificate) | G | Generic operation-stream traversal shows that both endpoints use registered permutation columns; finite-index bounds follow from membership. | Done |
| 5 | `actionCopyActiveRowFailures_eq_nil` (eliminated) | G | `usedRows` includes operation copy endpoints and V1 deferred-constant allocations; structural traversal of the V1 copy stream transfers those bounds to every decoded copy. | Done |
| 6 | `actionNumPermCols_eq` (eliminated) | R | Replay now uses the circuit-derived permutation family directly; the literal `15` is absent from the semantic path. | Done |
| 7 | `actionCopyAddressFailures_eq_nil` (eliminated) | G | Generic endpoint registration and row-footprint theorems reduce encoding to the permutation-index round trip. | Done |
| 8 | `actionMissingConstantAllocations_eq_nil` (eliminated) | G | Keygen lawfulness supplies enough equality-enabled constant capacity; generic V1 stream correspondence supplies each declared constant's allocation. | Done |
| 9 | `actionConstantSites_fit` (eliminated as a certificate) | G | The compositional constant-capacity law directly bounds the operation stream by V1's assignments. | Done |
| 10 | `actionConstantValueFailures_eq_nil` (eliminated) | G | Generic ordered-stream and positional-zip theorems preserve every allocated constant value. | Done |
| 11 | `actionConstantCellAddressFailures_eq_nil` (eliminated) | G | Keygen registration places constant columns in the permutation family; generic row bounds and permutation-index inversion give the address round trip. | Done |
| 12a | `gateData_eq`, gate component | L | Raw configure/synthesis registration: every synthesis-enabled gate was registered by `configure`. This must make gate closure inactive. | Medium |
| 12b | `gateData_eq`, selector-count component | L | Every selector used by a configured or enabled lookup is below raw `numSelectors`. This must make the closure maximum inactive. | Medium |
| 13 | `selectorDegree` | L | Compositional gate/lookup degree bounds, then a generic `ConstraintSystem` degree theorem. | Medium |
| 14 | gate `domainExponent_lt` | L | A supported-domain property on `TopLevelCircuit`, preferably derived compositionally from region/bundle footprint bounds. | Medium–hard |
| 15 | permutation `domainExponent_lt` | R | Share the generic top-level supported-domain fact; remove the duplicate Action computation. | Easy |
| 16 | `domainExponent_eq` | R | Reason over the abstract derived exponent. Keep exact `K = 11` only as part of deployment identity. | Medium |
| 17 | `chunks_eq` | R | Prove generic chunking order/index facts over the derived permutation columns; remove literal `[7, 7, 1]`. | Medium |
| 18 | `permutationColumnCount_eq` (eliminated) | G | Configure interpretation deduplicates equality requests and every request lies in the configured column space; Action's small advice/fixed/instance counts bound that space without fixing the permutation family to `15`. | Done |
| 19 | `queryLayouts_eq` | G | Both sides project the same pinned CS. Prove the projection equality with behavioral simp lemmas, not reduction through the concrete circuit. | Medium |
| 20 | `routingCoherent` | L | Configure permutation law: every permutation column has the required zero-rotation query; derive routing from generic chunk indices. | Medium |
| 21 | `deltaPowers_injective` | G | Pure field/group-order argument for the supported permutation-column range. | Medium |
| 22 | `primaryRegistered` | L | Every `constrainInstance` target column is equality-enabled, plus the generic permutation-query law. | Medium |

The split of row 12 makes this table contain 23 atomic obligations even though it
still corresponds to the original 22 theorem rows.

## Elimination progress

The `certificate-elimination-rg` branch currently closes eight R/G rows without changing any L-classified interface or premise:

* **#10 (G), constant values:** generic traversal lemmas prove that the semantic constant-site collector and V1 planner collect the same ordered value stream, and that positional allocation preserves those values whenever the existing allocation-completeness premise holds. The Action-wide failure list and its `native_decide` theorem have been deleted. Rows 8 and 9 remain deliberately untouched.
* **#15 (R), duplicate domain bound:** the permutation bridge now reuses the gate bridge's existing supported-domain fact instead of evaluating the same Action property a second time. The underlying supported-domain law remains row 14 (L).
* **#6 (R), literal permutation-column count:** replay, chunk flattening, and cycle reconstruction now use the circuit-derived permutation-column list and its length. The theorem fixing that length to `15` has been deleted.
* **#17 (R), literal chunk family:** generic list-chunking lemmas establish the compiler's chunk count, per-chunk width, complete flattening, and full-width prefix. The Action replay/cycle argument now consumes those theorems and no longer proves or case-splits on `[7, 7, 1]`.
* **#19 (G), query layouts:** `mergeDerived` and `toVerifierKey` now expose the `TopLevelCircuit`'s own `pinnedCS` layouts directly. The separate Action projection, whole-circuit comparison, three projection corollaries, and `native_decide` theorem have been deleted. A small generic `Fp` instance-irrelevance lemma connects legacy projection call sites without computing Action.
* **#16 (R), exact domain exponent:** the permutation coset argument now quantifies over the circuit-derived exponent and uses only the existing supported-domain bound. The public-row adapter derives its ten-row capacity from keygen's generic fit theorem and Action's structurally present 1024-row generator-table load. The standalone `K = 11` computation has been deleted.
* **#21 (G), delta powers:** the Pasta Pratt witness proves that `5` generates `Fpˣ`; consequently `deltaFp = 5^(2^32)` has the full odd order and its powers are injective on every supported prefix. The first-21-powers `native_decide` theorem has been deleted, and the coset theorem is generic in both domain exponent and prefix length.
* **#3 (R), nonempty permutation family:** the generic permutation semantics handles an empty derived chunk family and proves any attempted cell consumption impossible from its `Fin 0` index. The Action-only total coordinate encoder derives positivity from the one remaining column-count fact instead of carrying an independent whole-circuit computation.

Row **#18 (R)** is partially closed: all replay and cycle consumers use the derived chunk width, and name injectivity now ranges over the actual variable-width chunks instead of the padded `numSets * chunkLen` rectangle. The remaining exact computation supplies only `permutationColumns.length = 15`, used to show that the circuit's column-name prefix fits inside the certified order of `deltaFp` and, transitively, that Action's total endpoint encoder has an inhabitant. The current circuit interfaces do not bound `permutationColumns.length`: columns carry unbounded `Nat` indices and `Configure` is an arbitrary state function. Eliminating this final fact therefore needs either a configure law ensuring a duplicate-free in-range column list or an explicit supported-column-count law on the top-level keygen interface. That is a new design decision and is not being smuggled into this R/G-only branch.

The only remaining R/G work is this law-dependent tail of row #18. All listed L rows remain design inputs rather than implementation targets on this branch.

The subsequent keygen-lawfulness work also closes **#12a**, **#12b**, **#25**, and **#26**. These were L-classified because they required new packaged laws rather than because they required Action-specific proofs: `FormalCircuit.KeygenLawful` and the selector-allocation interface now supply them generically. The former `TopLevelGateCoherence` record has accordingly been reduced to numerical domain and degree facts and renamed `TopLevelConstraintBounds`.

The query-correctness slice closes **#1** and **#24** as well. Gates and lookup
arguments now carry local query-declaration laws, configure composition preserves
them, and the read-only pinned-CS projection resolves expressions against the one
authoritative compiler-derived query state. Generic top-level theorems derive valid
query atoms, advice/instance layout bounds, and fixed-query bounds. Fixed-column
coverage is the only circuit-specific remainder: Action proves it compositionally
from the gates and generator-table lookup that consume its 14 allocated fixed
columns. The former Action advice-bound, fixed-query-coverage, and queried-cell
`native_decide` certificates have all been deleted.

The permutation-routing slice closes **#20**. The existing configure query-lawfulness
package now proves that every `enableEquality` request also registers the column's
rotation-zero query. A generic top-level theorem transports this through selector
compression, `findIdx`, global `zipIdx` numbering, and chunking, proving every derived
permutation reference coherent for every `TopLevelCircuit`. The Action failure list,
its `native_decide` proof, and the obsolete routing diagnostics have been deleted. The
same compute module retains only the separate residual certificate that the Action
circuit has 15 permutation columns.

## Additional correctness obligations

| # | Current location or hidden behavior | Class | Structural replacement | Expected difficulty |
|---:|---|:---:|---|---|
| 24 | `action_queriedCells_wellFormed` in the VK-match bundle | L | Gate/lookup query declarations consist only of valid query atoms and match expression support. This belongs in argument lawfulness, not in a concrete capture. | Easy–medium |
| 25 | `action_gates_selectorsCovered` in the VK-match bundle, formerly replaced by the Action-specific `Action/SelectorCoherence.lean` sidecar | L | Move gate-selector allocation into the `FormalCircuit` lawfulness package or enforce it through the configure API. The existing compositional proof can discharge that packaged law during migration; selector-compression coverage then follows from a generic compiler theorem. | Medium |
| 26 | lookup component of closure inactivity | L | Every synthesis-enabled lookup is present in the raw configure lookup list. This is currently repaired by `closeWithOperations` and is not directly proved for Action. | Medium |

Together with rows 12a and 12b, these bring the inventory to 26 atomic obligations.
The VK bundle's `actionK_eq` is not another item because row 16 already covers it.

The old `invalidQueriedCells = []` check was previously easy to dismiss because it
was not imported by the capstone. It is now a generic theorem of every lawful
`TopLevelCircuit`, derived from the packaged configure query laws rather than checked
on Action.

The former `Action/SelectorCoherence.lean` sidecar has been deleted. Its 1,448 lines
and the duplicate `action_gates_selectorsCovered` computation in the VK-match bundle
were replaced by the packaged selector-allocation law and compositional proofs carried
by the formal circuits themselves.

## Lookup selector fidelity

`TopLevelCircuit` once carried two static synthesis obligations:

* `LookupRelevantSelectorActivationsExact`: every lookup operation's recorded enabled
  selectors exactly match the relevant selectors activated in its complete region at
  that row; and
* `LookupInputsNoSimpleSelectors`: lookup input expressions contain no simple
  selectors.

Both fields, together with the sidecars that discharged them for Action
(`Action/SynthesisLaws.lean`, `NoteCommit/SynthesisLaws.lean`, and
`Action/TopLevelSynthesisLaws.lean`, which retraced the entire Action and NoteCommit
synthesis call graphs because circuit and subcircuit constructors do not preserve
this evidence), were withdrawn. Lookup projection coverage is established
independently, by counting selector indices rather than by appealing to a
region-local activation law.

The no-simple-selector condition has since been restored at its natural boundary.
`LookupArgument` proves that every input contains no simple selector, `lookup`
requires that proof when registering the argument, and complex selectors have a
distinct type. The configure elaboration additionally tracks the exact selector
usage of gates and lookups, including which uses were inherited from a parent
program. Circuit owners reduce that provenance to compact summaries, so cross-child
compatibility composes without reopening the full Action configure tree.

`LookupRelevantSelectorActivationsExact` remains withdrawn. If a future theorem
needs its region-local synthesis claim, the evidence should be packaged on the
lookup-emitting circuit bundles and preserved by circuit composition rather than
reattached as a whole-Action sidecar.

## Current compile-cost baseline

The following measurements were taken on one development machine before the most
recent keygen performance work. They are order-of-magnitude costs for compiling the
containing module, not isolated timings for one `native_decide`: module elaboration,
shared concrete-circuit evaluation, and proof checking are included.

| Certificate group | Containing module | Approximate compile time | Approximate peak memory |
|---|---|---:|---:|
| Constraint degree and domain | `ActionConstraintBoundsCompute.lean` | 10 s | 7.0 GB |
| Primary-instance registration | `ActionInstanceCommitmentCompute.lean` | 4 s | 3.8 GB |
| Permutation column count | `ActionPermutationDomainCompute.lean` | 3 s | not remeasured |
| Copy bounds, addresses, constants | `ActionCopyWitness.lean` | 30–40 s | 7.7 GB |
| Fixed realization | `ActionFixedCoherenceCompute.lean` | 30 s | 7.0 GB |

The serial total was roughly 2 minutes 40 seconds. These numbers should guide
iteration priorities, not be treated as stable benchmarks: several facts share one
large circuit evaluation, and moving or bundling a theorem can shift the apparent
cost. The closure-inertness obligations are also entangled with circuit derivation and
the VK match rather than timed as a clean standalone group.

## Query-lawfulness interfaces

### 1. Exact gate query support

For a gate, the list supplied as `queriedCells` records Rust closure-call order, while
expression traversal records syntactic use order and may repeat atoms differently.
The implemented law uses support inclusion rather than list equality:

```text
Gate.WellFormed.constraintQueriesDeclared gate :=
  every query atom used by gate.constraints occurs in gate.queriedCells
```

This is the exact direction required by soundness and remains Halo2-faithful when a
closure queries a cell that its returned constraints do not ultimately use. Selector
ownership remains the separate `Gate.WellFormed` law.

The query-declaration law and the existing selector discipline are both packaged in
`Gate.WellFormed`. Construction retains the existing call syntax through default
proof arguments and tactics.

Consequences should include:

* no invalid `queriedCells`;
* every expression query receives the intended registered query index;
* query coverage for every semantically consumed gate fixed column;
* expression projection is independent of an unrelated concrete VK check.

### 2. Lookup query support

Lookups carry the analogous input/table registration laws:

```text
LookupQueriesDeclared queriedCells tableMap :=
  every queriedCells entry is a query atom
  ∧ every query atom used by the input expressions occurs in queriedCells
```

It composes with the existing lookup properties: table expressions are selector-free,
input selectors are disciplined, tuple arities match, and activation rows are exact.
The declaration reflects the actual configure closure-call order when that order
affects query indices. Configure is append-only, so these local laws compose into the
top-level layouts without replaying the concrete Action circuit.

### 3. Configure/synthesis registration

The raw configure result and synthesis stream need a packaged law such as:

```text
FormalCircuit.RegisteredIn :=
  let rawCS := (configure configInput {}).2
  let ops := toOperations configInput input
  OperationsKeygenCoherent rawCS ops
  ∧ LookupSelectorsAllocated rawCS
```

The name and exact factorization can change, but the property must live on
`FormalCircuit` (or a construction it contains), not beside each Action subcircuit.
As with Clean's other lawfulness fields, primitives should prove it once and
combinators should preserve it. A default tactic should solve ordinary bundles from
those compositional lemmas.

This law gives:

* `missingEnabledGates rawCS ops = []`;
* `missingEnabledLookups rawCS ops = []`;
* the closure selector maximum equals `rawCS.numSelectors`;
* `rawCS.closeWithOperations ops = rawCS`; and
* canonical `toConstraintSystem` and `toPinnedCS` can use `rawCS` directly.

This is stricter and more faithful than merely baking synthesis-enabled arguments into
the derived CS.

### 4. Configure permutation and constant laws

Configure should also expose:

* every equality-enabled column has the zero-rotation query required by permutation
  routing;
* every constant column is equality-enabled;
* every instance column targeted by synthesis is equality-enabled; and
* allocated column/selector counters are monotone and references are in range.

These are good candidates for proof-by-construction in a restricted append-only
configure monad. Until then, they should be fields preserved by configure primitives
and discharged compositionally.

### 5. Region-operation lawfulness

Each region should certify locally:

* every referenced cell was allocated in that region;
* referenced offsets are below the measured region extent;
* repeated writes to the same local fixed cell agree; and
* copy endpoints use equality-enabled columns.

The V1 planner already proves that regions sharing a measured column receive
non-overlapping column-and-row intervals. That generic theorem turns local fixed-write
consistency into cross-region consistency. Regions may share row numbers; what cannot
overlap is a cell in a shared column.

Tables, constant allocation, and selector packing are separate compiler stages, not
exceptions. Each stage needs a small consistency theorem and a composition theorem
showing that its writes do not conflict with region writes or with the other stages.

### 6. Operation-stream lawfulness

Move the two existing lookup synthesis laws from `TopLevelCircuit` to
`FormalCircuit`, with compositional support in circuit and subcircuit constructors.
The same formal-circuit lawfulness package should grow to cover:

* table loads for the same destination are consistent;
* constants are allocatable;
* instance constraints target enabled columns; and
* region-local laws hold for every synthesized region.

These should compose through operation-list append and circuit calls, so a top-level
circuit inherits them without enumerating every Action subcircuit in one theorem.

### 7. Supported domain

`TopLevelCircuit` should expose a supported-domain fact:

```text
∃ k ≤ fieldTwoAdicity, top.FitsAt k
```

Ideally this follows from per-region or per-bundle footprint bounds and generic
planner bounds. If the complete structural proof is too large initially, a concrete
domain check may remain only as a prominently marked interim certificate with this
replacement named.

## Generic compiler proofs still required

Even a fully lawful circuit does not eliminate all work. The compiler needs reusable
proofs that:

1. the pinned query layouts are exactly the final query-registration state;
2. constant collection and allocation preserve the ordered value stream;
3. permutation column lookup, chunking, and address encoding round-trip;
4. replay handles the empty permutation family and arbitrary derived widths;
5. V1 placement transports region-local bounds and consistency to placed cells;
6. selector compression covers every selector of a lawful gate or lookup; and
7. the required delta powers are injective within the field-supported column range.

These are generic algorithms over small abstract inputs. They should be proved with
behavioral simp lemmas and induction, not `rfl`/`whnf` through a concrete Action
definition.

## Recommended implementation sequence

### Phase A — make raw configure authoritative

1. Define the configure/synthesis registration and selector-allocation laws.
2. Prove closure is inactive for lawful circuits.
3. Put the law on `FormalCircuit` with compositional primitive/bundle support.
4. Change canonical `toConstraintSystem`/`toPinnedCS` to use raw configure output.
5. Retain `closeWithOperations` only as a migration/diagnostic helper.

This phase replaces gate closure, lookup closure, and selector-bound closure and
prevents the VK capture from hiding a modeling error.

### Phase B — remove concrete downstream demands

Generalize permutation replay and domain consumers to remove rows 3, 6, 15, 16, 17,
and 18. Exact deployed constants remain visible only in the VK identity check.

### Phase C — gate, lookup, and configure lawfulness

Add exact query support, degree bounds, permutation-column registration, constant
column laws, and instance registration. This addresses query coverage, constant-cell
routing, degree safety, permutation routing, primary-instance registration, invalid
query declarations, and the local premise of selector-compression coverage.

### Phase D — generic projection and algebra

Prove query-layout projection, constant-stream value preservation,
selector-compression coverage, and delta-power injectivity.

### Phase E — region, copy, constants, and fixed realization

Build region-local allocation/write laws and generic placement transfer, then compose
the fixed-producing stages. This addresses rows 2, 4, 5, 7, 8, 9, and the remaining
part of 11.

### Phase F — supported domain

Derive the top-level domain bound compositionally and remove row 14. This can proceed
in parallel with much of Phase E once the footprint interface is settled.

## Completion criteria

This arc is complete when:

* the canonical Clean keygen pipeline does not repair configure/synthesis mismatch;
* all 26 lawfulness obligations are discharged generically or compositionally;
* lookup synthesis laws are carried by every `FormalCircuit`, rather than proved by
  Action/NoteCommit sidecars and attached only at `TopLevelCircuit`;
* the Action integration capstone imports none of the listed concrete certificate
  theorems;
* no whole-Action `native_decide` remains for circuit correctness, layout
  consistency, query registration, routing, or domain safety;
* any retained concrete computation checks only deployment identity or fixture data;
  and
* adding another lawful top-level Halo2 circuit requires no analogous hand-written
  certificate module.

## Non-goals

This work does not remove the deployed Action VK capture, prove fixture provenance,
or change verifier/soundness semantics to speak in Clean-native terms. It strengthens
the Clean-to-Ironwood boundary so that the circuit interface arrives with the
Ironwood-facing properties that soundness needs.
