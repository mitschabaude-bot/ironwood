import Zcash.Snark.Fixtures.MultiAction.Honest.Fixture
import Zcash.Snark.Keygen.Certificate

/-!
# Shape and VK faithfulness checks for the multi-action capture

For the single-action capture, Lean re-derives the key: `Keygen/Certificate.lean` proves the
dumped VK equals the one derived from the ported `configure`/keygen, with per-field checks in
`Fixtures/SingleAction/Honest/VkMatch.lean`. That certificate transports to this multi-action key in
`Fixtures/MultiAction/Honest/VkCertificate.lean`, along the cross-capture point equalities of
`Fixtures/PostNu63.lean`, so the checks here are drift-naming diagnostics rather than the boundary.
The Orchard capture re-runs key generation, compares that exact key against the checked-in
canonical Post-NU6.3 `PinnedVerificationKey`, and passes the same key to verification and the fixture
dumper; `Fixtures.PostNu63` pins the emitted transcript representation in Lean. These checks verify
that the named captured lists, typed accessors, query layouts, and expression indices agree with
the generated `shape`; `FiatShamir.lean` pins the captured transcript prefix to
`initialTranscript` outright.

In particular this catches the totalization hazards called out in `Verifier.Assemble`: an
out-of-range query index would otherwise route through `finFn`/`finFnG` and alias `0`/`default`.

Counts and per-entry ranges are not enough for the permutation argument, whose chunk *layout* also
carries meaning: `permutation_chunk_layout_regular` adds the width and index-coverage conditions
`permChunkExpression`'s coset offset depends on, and `vk_chunkLen_and_chunks_derived` pins the chunk
width and the chunking to `actionCircuit` rather than to the capture's own numbers — the multi-action
analog of `Fixtures.SingleAction.Honest.VkMatch.vk_permutationChunks_derived`, which reaches the capture
here via the circuit-derived layout instead of a second keygen certificate. Both are kernel-checked
over the literal layout; only the circuit side they compare against carries `native_decide`, so
neither widens this module's compiler trust.
-/

namespace Zcash.Snark.Fixture2

open Zcash.Snark
open Zcash.Circuits.Action (actionCircuit)

/-- Permutation-chunk projection commutes with transport between circuit shapes. -/
private theorem castVk_permutationChunks
    {s₁ s₂ : CircuitShape} (h : s₁ = s₂)
    (key : VerifyingKey s₁ Fp G) :
    key.permutationChunks =
      (h ▸ key : VerifyingKey s₂ Fp G).permutationChunks := by
  cases h
  rfl

/-- Chunk-width projection commutes with transport between circuit shapes. -/
private theorem castVk_chunkLen
    {s₁ s₂ : CircuitShape} (h : s₁ = s₂)
    (key : VerifyingKey s₁ Fp G) :
    key.chunkLen = (h ▸ key : VerifyingKey s₂ Fp G).chunkLen := by
  cases h
  rfl

theorem captured_list_lengths_match_shape :
    -- Fixed commitments are per *column* and fixed evals per *query*; the counts coincide (29) for
    -- this Orchard VK because every fixed column is queried exactly once. The load-bearing guard for
    -- out-of-range columns is `query_layout_columns_in_range` below.
    capturedFixedCommitments.length = capturedFixedEvals.length
      ∧ capturedInstanceCommitments.length = shape.numProofs * capturedNumInstanceColumns
      ∧ capturedPermutationCommonCommitments.length = shape.numPermutationColumns
      ∧ capturedPermutationCommonEvals.length = shape.numPermutationColumns
      ∧ capturedAdviceCommitments.length = shape.numProofs * shape.numAdviceColumns
      ∧ capturedLookupPermutedInput.length = shape.numProofs * shape.numLookups
      ∧ capturedLookupPermutedTable.length = shape.numProofs * shape.numLookups
      ∧ capturedPermutationProducts.length = shape.numProofs * shape.numPermutationSets
      ∧ capturedLookupProducts.length = shape.numProofs * shape.numLookups
      ∧ capturedHPieces.length = shape.numQuotientPieces
      ∧ capturedInstanceEvals.length = shape.numProofs * shape.numInstanceQueries
      ∧ capturedAdviceEvals.length = shape.numProofs * shape.numAdviceQueries
      ∧ capturedFixedEvals.length = shape.numFixedQueries
      ∧ capturedPermutationSetEvals.length = shape.numProofs * shape.numPermutationSets
      ∧ capturedLookupEvals.length = shape.numProofs * shape.numLookups
      ∧ capturedMultiopenU.length = shape.numPointSets
      ∧ capturedIpaRounds.length = shape.k := by
  native_decide

def layoutColumnsInRange (bound : ℕ) (layout : List (ℕ × ℤ)) : Bool :=
  layout.all fun entry => decide (entry.1 < bound)

theorem query_layout_columns_in_range :
    layoutColumnsInRange capturedNumInstanceColumns vk.instanceQueryLayout = true
      ∧ layoutColumnsInRange shape.numAdviceColumns vk.adviceQueryLayout = true
      ∧ layoutColumnsInRange capturedFixedCommitments.length vk.fixedQueryLayout = true := by
  native_decide

def columnRefInRange : ColumnRef → Bool
  | .advice i => decide (i < shape.numAdviceQueries)
  | .fixed i => decide (i < shape.numFixedQueries)
  | .instance i => decide (i < shape.numInstanceQueries)

def exprRefsInRange : Expr Fp → Bool
  | .constant _ => true
  | .fixed i => decide (i < shape.numFixedQueries)
  | .advice i => decide (i < shape.numAdviceQueries)
  | .instance i => decide (i < shape.numInstanceQueries)
  | .negated e => exprRefsInRange e
  | .sum a b => exprRefsInRange a && exprRefsInRange b
  | .product a b => exprRefsInRange a && exprRefsInRange b
  | .scaled e _ => exprRefsInRange e

def exprListRefsInRange (xs : List (Expr Fp)) : Bool :=
  xs.all exprRefsInRange

def lookupExprRefsInRange (exprs : Fin shape.numLookups → List (Expr Fp)) : Bool :=
  (List.ofFn (fun l : Fin shape.numLookups => exprListRefsInRange (exprs l))).all fun b => b

def permutationChunksRefsInRange : Bool :=
  vk.permutationChunks.all fun chunk =>
    chunk.all fun cr => columnRefInRange cr.1 && decide (cr.2 < shape.numPermutationColumns)

theorem vk_expression_refs_in_range :
    exprListRefsInRange vk.gates = true
      ∧ lookupExprRefsInRange vk.lookupInputExprs = true
      ∧ lookupExprRefsInRange vk.lookupTableExprs = true
      ∧ permutationChunksRefsInRange = true := by
  native_decide

theorem permutation_chunks_match_shape :
    vk.permutationChunks.length = shape.numPermutationSets
      ∧ (vk.permutationChunks.map List.length).sum = shape.numPermutationColumns := by
  native_decide

/-- The chunking is *regular*: every chunk but the last is exactly `vk.chunkLen` columns wide, the
last is a nonempty remainder, the chunk count is the induced `⌈columns / chunkLen⌉`, and the
flattened common-eval indices are `0, 1, …, numPermutationColumns - 1` in order.

This is what `permChunkExpression`'s coset offset needs. That offset is `β·x·δ^(c · chunkLen)` and
the `j`-th factor within chunk `c` multiplies it by `δ^j`, so chunk `c` continues its predecessors'
coset only when chunk `c` really does start at column `c · chunkLen` — i.e. only when every earlier
chunk is exactly `chunkLen` wide. Independently, `cr.2` selects which `permutationCommonEvals` (the
σ evaluations) enters each column's factor, so a duplicated or omitted index would silently rewire
the argument. Neither `permutation_chunks_match_shape` (count and total) nor
`permutationChunksRefsInRange` (per-entry range) excludes uneven widths or a non-bijective index
assignment; this does, and together the four conjuncts leave the layout no freedom beyond
`vk.chunkLen` itself, which `vk_chunkLen_and_chunks_derived` pins to the circuit. -/
theorem permutation_chunk_layout_regular :
    (∀ chunk ∈ vk.permutationChunks.dropLast, chunk.length = vk.chunkLen)
      ∧ (∀ chunk ∈ vk.permutationChunks, 0 < chunk.length ∧ chunk.length ≤ vk.chunkLen)
      ∧ vk.permutationChunks.length
          = (shape.numPermutationColumns + vk.chunkLen - 1) / vk.chunkLen
      ∧ vk.permutationChunks.flatten.map Prod.snd
          = List.range shape.numPermutationColumns := by
  decide

/-- The chunk width and the chunking itself are the *circuit's*, not free parameters of the capture.
The derived chunks are the recorded permutation columns paired with their σ index by `zipIdx` and
cut by `List.toChunks chunkLen`. A regeneration that changed either fails here instead of passing
the shape counts above. -/
theorem vk_chunkLen_and_chunks_derived :
    vk.chunkLen = actionCircuit.chunkLen
      ∧ vk.permutationChunks = actionCircuit.verifierCS.permutationChunks := by
  refine ⟨?_, ?_⟩
  · have hchunkLen := congrArg VerifyingKey.chunkLen
        Zcash.Snark.Keygen.vk_eq_toVerifierKey
    have hcast := castVk_chunkLen
      Zcash.Snark.Keygen.actionCircuitShape_eq_fixtureCircuitShape
      (actionCircuit.toVerifierKey Zcash.Snark.Fixture.capturedURS)
    have hsingle :
        Zcash.Snark.Fixture.vk.chunkLen = actionCircuit.chunkLen := by
      simpa only [actionCircuit.toVerifierKey_chunkLen] using
        hchunkLen.trans hcast.symm
    have hfixtures : vk.chunkLen = Zcash.Snark.Fixture.vk.chunkLen := by
      decide
    exact hfixtures.trans hsingle
  · have hchunks := congrArg VerifyingKey.permutationChunks
        Zcash.Snark.Keygen.vk_eq_toVerifierKey
    have hcast := castVk_permutationChunks
      Zcash.Snark.Keygen.actionCircuitShape_eq_fixtureCircuitShape
      (actionCircuit.toVerifierKey Zcash.Snark.Fixture.capturedURS)
    have hsingle :
        Zcash.Snark.Fixture.vk.permutationChunks =
          actionCircuit.verifierCS.permutationChunks := by
      simpa only [actionCircuit.toVerifierKey_permutationChunks] using
        hchunks.trans hcast.symm
    have hfixtures :
        vk.permutationChunks =
          Zcash.Snark.Fixture.vk.permutationChunks := by
      decide
    exact hfixtures.trans hsingle

theorem vk_domain_size_matches_shape :
    vk.n = 2 ^ shape.k := by
  native_decide

end Zcash.Snark.Fixture2
