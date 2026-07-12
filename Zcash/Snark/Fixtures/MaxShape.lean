import Zcash.Snark

/-!
# Verifier-shape fixture: the captured Orchard shape at any action count

The parametric verifier obligations of `Zcash.Snark.Verifier.Parametric`, specialized to the captured
Orchard verifier shape (`Fixture`/`Fixture2`) with the action count `numProofs` a free parameter `n`. The
verifying key, proof string, and challenges stay universally quantified — nothing is evaluated at a
concrete `n`. What is pinned: the per-sub-proof folds elaborate at the captured Orchard column/query
dimensions for every `n`, so drift in a parametric statement fails to elaborate here.

Not a Rust/Halo2 capture, and no Rust/Lean MSM match: a real max-action fixture would need a
65,535-action Rust capture, and the single- and multi-action captures remain the empirical regressions for
that boundary.

Every consensus-valid bundle has `n ≤ orchardConsensusMaxProofs` (see that definition for the protocol
spec §7.1.2 rule); `shape_hasConsensusNumProofs` records that each such `n` — the maximum included —
instantiates this shape, and the folds hold for arbitrary `n` regardless.
-/

namespace Zcash.Snark.FixtureMax

open Zcash.Snark

abbrev G := ℕ

/-- The captured Orchard verifier shape (`Fixture`/`Fixture2`), with the action count `numProofs` left
as the parameter `n`. Every other dimension is the captured Orchard column/query layout. -/
def shape (n : ℕ) : Shape := {
  k := 11,
  numProofs := n,
  numAdviceColumns := 10,
  numLookups := 3,
  numPermutationSets := 3,
  numPermutationColumns := 15,
  numQuotientPieces := 8,
  numInstanceQueries := 1,
  numAdviceQueries := 25,
  numFixedQueries := 29,
  numPointSets := 5
}

theorem shape_numProofs (n : ℕ) : (shape n).numProofs = n :=
  rfl

/-- `n ≤ orchardConsensusMaxProofs` gives `(shape n).hasConsensusNumProofs`, so every consensus-valid
action count instantiates the captured shape. (The bound is the protocol-spec consensus rule; see
`orchardConsensusMaxProofs`.) -/
theorem shape_hasConsensusNumProofs {n : ℕ} (hn : n ≤ orchardConsensusMaxProofs) :
    (shape n).hasConsensusNumProofs :=
  hn

/-- The consensus maximum `numProofs = 2^16 - 1` is itself in range, so the pinned obligations below
cover the largest deployable Orchard bundle. -/
theorem consensus_max_hasConsensusNumProofs :
    (shape orchardConsensusMaxProofs).hasConsensusNumProofs :=
  shape_hasConsensusNumProofs (Nat.le_refl _)

/-- `allExpressions_parametric_numProofs` at the captured Orchard shape, for every consensus-valid action count `n`,
verifying key, proof string, and challenge assignment. -/
theorem allExpressions_at_captured_shape (n : ℕ) (vk : VerifyingKey (shape n) Fp G)
    (ps : ProofString (shape n) Fp G) (ch : Challenges (shape n).k Fp) (l0 lLast lBlind : Fp) :
    allExpressions vk ps ch l0 lLast lBlind =
      subProofBlocks (fun p : Fin (shape n).numProofs =>
        subProofExpressions vk ps ch l0 lLast lBlind p) :=
  allExpressions_parametric_numProofs vk ps ch l0 lLast lBlind

/-- `assembleQueries_parametric_numProofs` at the captured Orchard shape, for every consensus-valid action count `n`,
verifying key, proof string, and challenge assignment. -/
theorem assembleQueries_at_captured_shape (n : ℕ) (vk : VerifyingKey (shape n) Fp G)
    (ps : ProofString (shape n) Fp G) (ch : Challenges (shape n).k Fp) :
    assembleQueries vk ps ch =
      let x := ch.x
      let xn := x ^ vk.n
      let xNext := rotateOmega vk.omega x 1
      let xInv := rotateOmega vk.omega x (-1)
      let xLast := rotateOmega vk.omega x (-((vk.blindingFactors : ℤ) + 1))
      let lb := lagrangeBasis vk.omega vk.n vk.blindingFactors xn x
      let exprs := allExpressions vk ps ch lb.1 lb.2.1 lb.2.2
      let eHEval := expectedHEval exprs ch.y xn
      let hComm := vanishingHCommitment (shape n).k xn (List.ofFn ps.hPieces)
      let perProof := subProofBlocks (fun p : Fin (shape n).numProofs =>
        subProofOpeningQueries vk ps x xInv xNext xLast p)
      let fixedQ := columnQueries vk.omega x vk.fixedCommitment CommitmentId.fixedCol
        vk.fixedQueryLayout (List.ofFn ps.fixedEvals)
      let permCommonQ := permutationCommonQueries x CommitmentId.permCommon
        (List.ofFn (fun c => (vk.permutationCommonCommitment c, ps.permutationCommonEvals c)))
      let vanishingQ := vanishingQueries x hComm eHEval ps.vanishingRandom ps.vanishingRandomEval
      perProof ++ fixedQ ++ permCommonQ ++ vanishingQ :=
  assembleQueries_parametric_numProofs vk ps ch

/-- `deriveChallenges_parametric_numProofs` at the captured Orchard shape, for every consensus-valid action count `n`
and proof string. -/
theorem deriveChallenges_at_captured_shape (n : ℕ) (fs : FiatShamir Fp G)
    (init : List (TranscriptElt Fp G)) (ps : ProofString (shape n) Fp G) :
    deriveChallenges fs init ps =
      let t := init ++ subProofBlocks (fun p : Fin (shape n).numProofs =>
        absorbPoints (ps.adviceCommitments p)) ++ [.challenge]
      let theta := fs.squeeze t
      let t := t ++ subProofBlocks (fun p : Fin (shape n).numProofs =>
        subProofBlocks (fun l : Fin (shape n).numLookups =>
          [TranscriptElt.point (ps.lookupPermutedInput p l),
           TranscriptElt.point (ps.lookupPermutedTable p l)])) ++ [.challenge]
      let beta := fs.squeeze t
      let t := t ++ [.challenge]
      let gamma := fs.squeeze t
      let t := t
        ++ subProofBlocks (fun p : Fin (shape n).numProofs => absorbPoints (ps.permutationProduct p))
        ++ subProofBlocks (fun p : Fin (shape n).numProofs => absorbPoints (ps.lookupProduct p))
        ++ [TranscriptElt.point ps.vanishingRandom] ++ [.challenge]
      let y := fs.squeeze t
      let t := t ++ absorbPoints ps.hPieces ++ [.challenge]
      let x := fs.squeeze t
      let evalElts := subProofBlocks (fun p : Fin (shape n).numProofs =>
        absorbScalars (ps.instanceEvals p))
        ++ subProofBlocks (fun p : Fin (shape n).numProofs => absorbScalars (ps.adviceEvals p))
        ++ absorbScalars ps.fixedEvals ++ [TranscriptElt.scalar ps.vanishingRandomEval]
        ++ absorbScalars ps.permutationCommonEvals
        ++ subProofBlocks (fun p : Fin (shape n).numProofs =>
          subProofBlocks (fun s : Fin (shape n).numPermutationSets =>
            absorbPermSet (ps.permutationSetEvals p s)))
        ++ subProofBlocks (fun p : Fin (shape n).numProofs =>
          subProofBlocks (fun l : Fin (shape n).numLookups => absorbLookup (ps.lookupEvals p l)))
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
      let ipaRes := (List.finRange (shape n).k).foldl
        (fun (st : List (TranscriptElt Fp G) × List Fp) j =>
          let t := st.1 ++ [TranscriptElt.point (ps.ipaRounds j).1,
            TranscriptElt.point (ps.ipaRounds j).2, TranscriptElt.challenge]
          let uj := fs.squeeze t
          (t, st.2 ++ [uj])) (t, [])
      { theta := theta, beta := beta, gamma := gamma, y := y, x := x,
        x1 := x1, x2 := x2, x3 := x3, x4 := x4, xi := xi, z := z,
        ipaRound := fun j => ipaRes.2.getD j.val 0 } :=
  deriveChallenges_parametric_numProofs fs init ps

/-- `subProofOpeningQueries_commId_disjoint` at the captured Orchard shape: for every consensus-valid action count `n`,
no two distinct sub-proofs' opening queries share a commitment slot, so the multiopen grouping cannot
merge across sub-proofs. -/
theorem commId_disjoint_at_captured_shape (n : ℕ) (vk : VerifyingKey (shape n) Fp G)
    (ps : ProofString (shape n) Fp G) (x xInv xNext xLast : Fp) {p p' : Fin (shape n).numProofs}
    (hpp : p ≠ p') :
    ∀ q ∈ subProofOpeningQueries vk ps x xInv xNext xLast p,
      ∀ q' ∈ subProofOpeningQueries vk ps x xInv xNext xLast p',
        q.commId ≠ q'.commId :=
  subProofOpeningQueries_commId_disjoint vk ps x xInv xNext xLast hpp

end Zcash.Snark.FixtureMax
