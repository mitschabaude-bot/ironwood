import Zcash.Snark.Verifier.FiatShamir

/-!
# Parametric verifier schedule obligations

The generated fingerprint fixtures remain concrete empirical checks (`numProofs = 1` and `numProofs = 2`,
plus any future selected captures). This module records the complementary generic obligation: the Lean verifier
traverses every sub-proof by a `Fin shape.numProofs` fold, for arbitrary `shape.numProofs`.
This is stronger than the Orchard consensus-scoped need: every consensus-valid action count
`N ≤ 2^16 - 1` is one instantiation of the same `shape.numProofs` parameter.

These theorems do not prove byte-for-byte Rust faithfulness; that boundary is still supplied by the
capture/dumper plus selected fixtures. They make explicit that the Lean-side assembly and Fiat–Shamir
schedule are not specialized to the current concrete fixtures.

Most obligations here are definitional pins — `rfl`-provable restatements that fail loudly if a
definition drifts. Two carry content beyond a pin: `subProofBlocks_length_const` (the flattened
schedule carries exactly one block per sub-proof — none dropped, none duplicated) and
`subProofOpeningQueries_commId_disjoint` (distinct sub-proofs' opening queries occupy disjoint
commitment slots, so the multiopen grouping can never merge commitments across sub-proofs).
-/

namespace Zcash.Snark

/-- Orchard's consensus maximum number of actions, hence the maximum `numProofs` for the Orchard
bundle proof verified by this model.

The bound is a consensus rule, not an encoding artifact: `nActionsOrchard` is a `compactSize` (which
admits values up to `2^64 - 1`), but the Zcash Protocol Specification §7.1.2 "Transaction Consensus
Rules" requires `nActionsOrchard < 2^16` (NU5 onward), so `nActionsOrchard ≤ 2^16 - 1 = 65535`. The v5
transaction format carrying it is defined by ZIP 225. -/
def orchardConsensusMaxProofs : ℕ := 2^16 - 1

/-- The consensus-scoped subcase of the stronger parametric theorems below. Only the upper bound is
load-bearing: a consensus-valid transaction verifies an Orchard proof only when it has at least one
action (`proofsOrchard` is present iff `nActionsOrchard > 0`, ZIP 225), so `numProofs = 0` never
reaches the deployed verifier and is not excluded here. -/
def Shape.hasConsensusNumProofs (shape : Shape) : Prop :=
  shape.numProofs ≤ orchardConsensusMaxProofs

/-- Flatten one list-producing block over all sub-proofs. This is the parametric shape shared by the
assembly and Fiat–Shamir schedules: the number of blocks is exactly the ambient `numProofs`. (The
restatements below also reuse it for the inner per-lookup / per-permutation-set folds, where the index
runs over lookups or sets rather than sub-proofs.) -/
def subProofBlocks {α : Type*} {numProofs : ℕ} (block : Fin numProofs → List α) : List α :=
  (List.ofFn block).flatten

/-- The flattened schedule's length is the sum of the per-sub-proof block lengths. -/
theorem subProofBlocks_length {α : Type*} {numProofs : ℕ} (block : Fin numProofs → List α) :
    (subProofBlocks block).length = ∑ p, (block p).length := by
  simp [subProofBlocks, List.length_flatten, List.map_ofFn, List.sum_ofFn]

/-- With equal-length blocks, the flattened schedule carries exactly `numProofs` blocks — no
sub-proof's block is dropped or duplicated by the fold. -/
theorem subProofBlocks_length_const {α : Type*} {numProofs L : ℕ}
    (block : Fin numProofs → List α) (h : ∀ p, (block p).length = L) :
    (subProofBlocks block).length = numProofs * L := by
  simp [subProofBlocks_length, h, Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- The constraint-expression fold is generic over all `shape.numProofs`; it is not specialized to the
single-action fixture. -/
theorem allExpressions_parametric_numProofs {shape : Shape} {F G : Type*} [Field F]
    (vk : VerifyingKey shape F G) (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (l0 lLast lBlind : F) :
    allExpressions vk ps ch l0 lLast lBlind =
      subProofBlocks (fun p : Fin shape.numProofs =>
        subProofExpressions vk ps ch l0 lLast lBlind p) :=
  rfl

/-- The proof-commitment Fiat–Shamir absorb for a per-sub-proof matrix is generic in the outer
`numProofs` index. -/
theorem absorbPoints2_parametric_numProofs {F G : Type*} {numProofs cols : ℕ}
    (f : Fin numProofs → Fin cols → G) :
    absorbPoints2 (F := F) f =
      subProofBlocks (fun p : Fin numProofs => absorbPoints (f p)) :=
  rfl

/-- The proof-scalar Fiat–Shamir absorb for a per-sub-proof matrix is generic in the outer `numProofs`
index. -/
theorem absorbScalars2_parametric_numProofs {F G : Type*} {numProofs cols : ℕ}
    (f : Fin numProofs → Fin cols → F) :
    absorbScalars2 (G := G) f =
      subProofBlocks (fun p : Fin numProofs => absorbScalars (f p)) :=
  rfl

/-- Lookup-permuted commitments are absorbed per proof, then per lookup, for arbitrary `numProofs`. -/
theorem absorbLookupPermuted_parametric_numProofs {F G : Type*} {numProofs lookups : ℕ}
    (input table : Fin numProofs → Fin lookups → G) :
    absorbLookupPermuted (F := F) input table =
      subProofBlocks (fun p : Fin numProofs =>
        subProofBlocks (fun l : Fin lookups =>
          [TranscriptElt.point (input p l), TranscriptElt.point (table p l)])) :=
  rfl

/-- The per-sub-proof opening-query block used by `assembleQueries`. -/
def subProofOpeningQueries {shape : Shape} {F G : Type*} [Field F] [Inhabited G]
    (vk : VerifyingKey shape F G) (ps : ProofString shape F G) (x xInv xNext xLast : F)
    (p : Fin shape.numProofs) : List (VerifierQuery shape.k F G) :=
  columnQueries vk.omega x (vk.instanceCommitment p) (CommitmentId.instanceCol p)
      vk.instanceQueryLayout (List.ofFn (ps.instanceEvals p))
  ++ columnQueries vk.omega x (finFnG (ps.adviceCommitments p)) (CommitmentId.adviceCol p)
      vk.adviceQueryLayout (List.ofFn (ps.adviceEvals p))
  ++ permutationQueries x xNext xLast (CommitmentId.permProduct p)
      (List.ofFn (fun s => (ps.permutationProduct p s, ps.permutationSetEvals p s)))
  ++ lookupQueries x xInv xNext (CommitmentId.lookupProduct p) (CommitmentId.lookupPermInput p)
      (CommitmentId.lookupPermTable p) (List.ofFn (fun l =>
      ({ product := ps.lookupProduct p l, permutedInput := ps.lookupPermutedInput p l,
         permutedTable := ps.lookupPermutedTable p l }, ps.lookupEvals p l)))

/-- The sub-proof index carried by a commitment slot, when the slot is per-sub-proof. Shared slots
(fixed columns, common permutation, vanishing `h`, random poly) carry none. -/
def CommitmentId.subProofIdx? : CommitmentId → Option ℕ
  | .instanceCol p _ => some p
  | .adviceCol p _ => some p
  | .permProduct p _ => some p
  | .lookupProduct p _ => some p
  | .lookupPermInput p _ => some p
  | .lookupPermTable p _ => some p
  | .fixedCol _ => none
  | .permCommon _ => none
  | .vanishingH => none
  | .randomPoly => none

/-- Every opening query in sub-proof `p`'s block carries a commitment slot tagged with `p`. -/
theorem commId_subProofIdx_of_mem_subProofOpeningQueries {shape : Shape} {F G : Type*} [Field F]
    [Inhabited G] (vk : VerifyingKey shape F G) (ps : ProofString shape F G)
    (x xInv xNext xLast : F) (p : Fin shape.numProofs) :
    ∀ q ∈ subProofOpeningQueries vk ps x xInv xNext xLast p,
      q.commId.subProofIdx? = some p.val := by
  intro q hq
  simp only [subProofOpeningQueries, columnQueries, permutationQueries, lookupQueries,
    List.mem_append] at hq
  rcases hq with ((hq | hq) | hq) | hq
  · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hq
    rfl
  · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hq
    rfl
  · rcases hq with hq | hq
    · obtain ⟨s, -, hs⟩ := List.mem_flatMap.mp hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;> rfl
    · obtain ⟨s, -, hs⟩ := List.mem_filterMap.mp hq
      cases hle : s.1.2.lastEval with
      | none => simp [hle] at hs
      | some le =>
          rw [hle, Option.map_some] at hs
          obtain rfl := Option.some.inj hs
          rfl
  · obtain ⟨l, -, hl⟩ := List.mem_flatMap.mp hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Distinct sub-proofs' opening queries occupy disjoint commitment slots. `constructIntermediateSets`
groups queries by `commId` (the Lean image of halo2 `construct_intermediate_sets`' pointer-identity
keying), so the multiopen grouping can never merge commitments across sub-proofs — for any
`numProofs`, not just the captured fixtures. -/
theorem subProofOpeningQueries_commId_disjoint {shape : Shape} {F G : Type*} [Field F]
    [Inhabited G] (vk : VerifyingKey shape F G) (ps : ProofString shape F G)
    (x xInv xNext xLast : F) {p p' : Fin shape.numProofs} (hpp : p ≠ p') :
    ∀ q ∈ subProofOpeningQueries vk ps x xInv xNext xLast p,
      ∀ q' ∈ subProofOpeningQueries vk ps x xInv xNext xLast p',
        q.commId ≠ q'.commId := by
  intro q hq q' hq' heq
  apply hpp
  apply Fin.val_injective
  have h1 := commId_subProofIdx_of_mem_subProofOpeningQueries vk ps x xInv xNext xLast p q hq
  have h2 := commId_subProofIdx_of_mem_subProofOpeningQueries vk ps x xInv xNext xLast p' q' hq'
  rw [heq, h2] at h1
  exact (Option.some.inj h1).symm

/-- `assembleQueries` builds all per-sub-proof opening-query blocks by folding over
`Fin shape.numProofs`, then appends the shared fixed, permutation-common, and vanishing queries. -/
theorem assembleQueries_parametric_numProofs {shape : Shape} {F G : Type*} [Field F] [Inhabited G]
    (vk : VerifyingKey shape F G) (ps : ProofString shape F G) (ch : Challenges shape.k F) :
    assembleQueries vk ps ch =
      let x := ch.x
      let xn := x ^ vk.n
      let xNext := rotateOmega vk.omega x 1
      let xInv := rotateOmega vk.omega x (-1)
      let xLast := rotateOmega vk.omega x (-((vk.blindingFactors : ℤ) + 1))
      let lb := lagrangeBasis vk.omega vk.n vk.blindingFactors xn x
      let exprs := allExpressions vk ps ch lb.1 lb.2.1 lb.2.2
      let eHEval := expectedHEval exprs ch.y xn
      let hComm := vanishingHCommitment shape.k xn (List.ofFn ps.hPieces)
      let perProof := subProofBlocks (fun p : Fin shape.numProofs =>
        subProofOpeningQueries vk ps x xInv xNext xLast p)
      let fixedQ := columnQueries vk.omega x vk.fixedCommitment CommitmentId.fixedCol
        vk.fixedQueryLayout (List.ofFn ps.fixedEvals)
      let permCommonQ := permutationCommonQueries x CommitmentId.permCommon
        (List.ofFn (fun c => (vk.permutationCommonCommitment c, ps.permutationCommonEvals c)))
      let vanishingQ := vanishingQueries x hComm eHEval ps.vanishingRandom ps.vanishingRandomEval
      perProof ++ fixedQ ++ permCommonQ ++ vanishingQ :=
  rfl

/-- The Fiat–Shamir challenge schedule is generic in `shape.numProofs`. The per-proof absorbs in this
schedule are the generic folds exposed by `absorbPoints2_parametric_numProofs`,
`absorbScalars2_parametric_numProofs`, and `absorbLookupPermuted_parametric_numProofs`.
The hash output is intentionally outside these parametric lemmas: Blake2b is taken at the
random-oracle boundary, while the concrete fixtures use a fixture oracle over the captured transcript
events (`Zcash.Snark.Fixtures.SingleAction.FiatShamir`, `Zcash.Snark.Fixtures.MultiAction.FiatShamir`). -/
theorem deriveChallenges_parametric_numProofs {shape : Shape} {F G : Type*} [Zero F]
    (fs : FiatShamir F G) (init : List (TranscriptElt F G)) (ps : ProofString shape F G) :
    deriveChallenges fs init ps =
      let t := init ++ subProofBlocks (fun p : Fin shape.numProofs =>
        absorbPoints (ps.adviceCommitments p)) ++ [.challenge]
      let theta := fs.squeeze t
      let t := t ++ subProofBlocks (fun p : Fin shape.numProofs =>
        subProofBlocks (fun l : Fin shape.numLookups =>
          [TranscriptElt.point (ps.lookupPermutedInput p l),
           TranscriptElt.point (ps.lookupPermutedTable p l)])) ++ [.challenge]
      let beta := fs.squeeze t
      let t := t ++ [.challenge]
      let gamma := fs.squeeze t
      let t := t
        ++ subProofBlocks (fun p : Fin shape.numProofs => absorbPoints (ps.permutationProduct p))
        ++ subProofBlocks (fun p : Fin shape.numProofs => absorbPoints (ps.lookupProduct p))
        ++ [TranscriptElt.point ps.vanishingRandom] ++ [.challenge]
      let y := fs.squeeze t
      let t := t ++ absorbPoints ps.hPieces ++ [.challenge]
      let x := fs.squeeze t
      let evalElts := subProofBlocks (fun p : Fin shape.numProofs =>
        absorbScalars (ps.instanceEvals p))
        ++ subProofBlocks (fun p : Fin shape.numProofs => absorbScalars (ps.adviceEvals p))
        ++ absorbScalars ps.fixedEvals ++ [TranscriptElt.scalar ps.vanishingRandomEval]
        ++ absorbScalars ps.permutationCommonEvals
        ++ subProofBlocks (fun p : Fin shape.numProofs =>
          subProofBlocks (fun s : Fin shape.numPermutationSets =>
            absorbPermSet (ps.permutationSetEvals p s)))
        ++ subProofBlocks (fun p : Fin shape.numProofs =>
          subProofBlocks (fun l : Fin shape.numLookups => absorbLookup (ps.lookupEvals p l)))
      let t := t ++ evalElts ++ [.challenge]
      let x1 := fs.squeeze t
      let t := t ++ [.challenge]
      let x2 := fs.squeeze t
      let t := t ++ [TranscriptElt.point ps.multiopenQPrime] ++ [.challenge]
      let x3 := fs.squeeze t
      let t := t ++ absorbScalars ps.multiopenU ++ [.challenge]
      let x4 := fs.squeeze t
      let t := t ++ [TranscriptElt.point ps.ipaS] ++ [.challenge]
      let xi := fs.squeeze t
      let t := t ++ [.challenge]
      let z := fs.squeeze t
      let ipaRes := (List.finRange shape.k).foldl
        (fun (st : List (TranscriptElt F G) × List F) j =>
          let t := st.1 ++ [TranscriptElt.point (ps.ipaRounds j).1,
            TranscriptElt.point (ps.ipaRounds j).2, TranscriptElt.challenge]
          let uj := fs.squeeze t
          (t, st.2 ++ [uj])) (t, [])
      { theta := theta, beta := beta, gamma := gamma, y := y, x := x,
        x1 := x1, x2 := x2, x3 := x3, x4 := x4, xi := xi, z := z,
        ipaRound := fun j => ipaRes.2.getD j.val 0 } := by
  simp [deriveChallenges, absorbPoints2, absorbScalars2, absorbLookupPermuted, subProofBlocks]

end Zcash.Snark
