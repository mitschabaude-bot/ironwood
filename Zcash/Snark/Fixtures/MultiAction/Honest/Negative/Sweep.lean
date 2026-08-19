import Zcash.Snark.Fixtures.MultiAction.Honest.FiatShamir
import Zcash.Snark.Fixtures.Shared.TamperSweep

/-!
# Tamper sensitivity sweep for the multi-action capture

A systematic per-slot negative suite for the fingerprint match, complete **by construction**
rather than curated: the tamper list is generated from the `ProofString` declaration
(`Core/ProofString.lean`) and the `Challenges` declaration (`Core/Challenges.lean`) by the fixed
rule below, so a reviewer checks coverage against those declarations, not against a hand-picked
list. A failing theorem names the broken slot. The wholesale-swap and rejection-path negatives,
the schedule-sensitivity negatives, and the paired `assembles` forms of the blind slots stay in
`Negative.lean`; this sweep re-covers their slots under the systematic rule rather than curating
them out.

**Construction rule.** For each of the 20 `ProofString` fields, in declaration order: one tamper
at the all-first index; for each axis of the field, one tamper at that axis's last index with
every other axis at its first index. An axis of length 1 contributes no last-index tamper (it
would restate the first-index theorem verbatim). Nested records (`PermSetEval`, `LookupEval`,
and the `G × G` IPA round pairs, whose components are halo2's round commitments `L`/`R`) get the
index rule on their first subfield (`eval` / `productEval` / `L`) plus one all-first tamper for
each remaining subfield; axis-last coverage of nested records therefore runs through the first
subfield only. Scalar tampers are `+ 1`; group-element tampers substitute `capturedPoint 0` (a
URS generator, distinct from every commitment in the capture); `lastEval` tampers use
`Option.map (· + 1)`, staying inside `some` so the tamper is an MSM-level negative rather than a
read-schedule rejection. Then: each of the 22 challenges (the 11 named challenges in squeeze
order, plus the 11 `ipaRound` slots individually), and one public-input tamper routed through
`commitLagrange`. If a `+ 1` delta or a point substitution ever accidentally cancels, the
`native_decide` fails at build time and the delta is changed (and documented at the slot).

**Every proof-string and public-input tamper is stated at the captured `ch`.** All fields except
`ipaC` and `ipaF` are absorbed by `deriveChallenges`, so a tamper routed through the composed
statement would trivially derail into a Fiat–Shamir oracle miss; holding `ch` fixed makes
each theorem witness MSM sensitivity, not schedule derailment. The challenge family is the
complement: it tampers `ch` and holds `ps` fixed. `x` and `x3` — the only challenges the
rejection set reads (`xⁿ = 1`; `x₃` hitting an opened point; the duplicate-query points are
rotations `ωʳ·x` and `x₃`) — carry paired `assembles` theorems certifying their sweep tampers
land on the MSM side rather than a rejection path, where `¬ MsmMatch` would hold vacuously via
the zero-MSM fallback.
-/

namespace Zcash.Snark.Fixture2

open Zcash.Snark

/-! ## The 20 `ProofString` fields, in declaration order -/

/-! ### `adviceCommitments` (proof × column, `G`) -/

def psSweepAdviceCommitmentsFirst : ProofString shape Fp G :=
  { ps with adviceCommitments := mapAt2 0 0 (fun _ => capturedPoint 0) ps.adviceCommitments }

theorem sweep_advice_commitments_first_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepAdviceCommitmentsFirst ch) capturedMsm := by
  native_decide

def psSweepAdviceCommitmentsLastProof : ProofString shape Fp G :=
  { ps with adviceCommitments := mapAt2 1 0 (fun _ => capturedPoint 0) ps.adviceCommitments }

theorem sweep_advice_commitments_last_proof_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepAdviceCommitmentsLastProof ch) capturedMsm := by
  native_decide

def psSweepAdviceCommitmentsLastColumn : ProofString shape Fp G :=
  { ps with adviceCommitments := mapAt2 0 9 (fun _ => capturedPoint 0) ps.adviceCommitments }

theorem sweep_advice_commitments_last_column_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepAdviceCommitmentsLastColumn ch) capturedMsm := by
  native_decide

/-! ### `lookupPermutedInput` (proof × lookup, `G`) -/

def psSweepLookupPermutedInputFirst : ProofString shape Fp G :=
  { ps with lookupPermutedInput := mapAt2 0 0 (fun _ => capturedPoint 0) ps.lookupPermutedInput }

theorem sweep_lookup_permuted_input_first_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepLookupPermutedInputFirst ch) capturedMsm := by
  native_decide

def psSweepLookupPermutedInputLastProof : ProofString shape Fp G :=
  { ps with lookupPermutedInput := mapAt2 1 0 (fun _ => capturedPoint 0) ps.lookupPermutedInput }

theorem sweep_lookup_permuted_input_last_proof_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepLookupPermutedInputLastProof ch) capturedMsm := by
  native_decide

def psSweepLookupPermutedInputLastLookup : ProofString shape Fp G :=
  { ps with lookupPermutedInput := mapAt2 0 2 (fun _ => capturedPoint 0) ps.lookupPermutedInput }

theorem sweep_lookup_permuted_input_last_lookup_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepLookupPermutedInputLastLookup ch) capturedMsm := by
  native_decide

/-! ### `lookupPermutedTable` (proof × lookup, `G`) -/

def psSweepLookupPermutedTableFirst : ProofString shape Fp G :=
  { ps with lookupPermutedTable := mapAt2 0 0 (fun _ => capturedPoint 0) ps.lookupPermutedTable }

theorem sweep_lookup_permuted_table_first_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepLookupPermutedTableFirst ch) capturedMsm := by
  native_decide

def psSweepLookupPermutedTableLastProof : ProofString shape Fp G :=
  { ps with lookupPermutedTable := mapAt2 1 0 (fun _ => capturedPoint 0) ps.lookupPermutedTable }

theorem sweep_lookup_permuted_table_last_proof_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepLookupPermutedTableLastProof ch) capturedMsm := by
  native_decide

def psSweepLookupPermutedTableLastLookup : ProofString shape Fp G :=
  { ps with lookupPermutedTable := mapAt2 0 2 (fun _ => capturedPoint 0) ps.lookupPermutedTable }

theorem sweep_lookup_permuted_table_last_lookup_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepLookupPermutedTableLastLookup ch) capturedMsm := by
  native_decide

/-! ### `permutationProduct` (proof × set, `G`) -/

def psSweepPermutationProductFirst : ProofString shape Fp G :=
  { ps with permutationProduct := mapAt2 0 0 (fun _ => capturedPoint 0) ps.permutationProduct }

theorem sweep_permutation_product_first_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepPermutationProductFirst ch) capturedMsm := by
  native_decide

def psSweepPermutationProductLastProof : ProofString shape Fp G :=
  { ps with permutationProduct := mapAt2 1 0 (fun _ => capturedPoint 0) ps.permutationProduct }

theorem sweep_permutation_product_last_proof_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepPermutationProductLastProof ch) capturedMsm := by
  native_decide

def psSweepPermutationProductLastSet : ProofString shape Fp G :=
  { ps with permutationProduct := mapAt2 0 2 (fun _ => capturedPoint 0) ps.permutationProduct }

theorem sweep_permutation_product_last_set_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepPermutationProductLastSet ch) capturedMsm := by
  native_decide

/-! ### `lookupProduct` (proof × lookup, `G`) -/

def psSweepLookupProductFirst : ProofString shape Fp G :=
  { ps with lookupProduct := mapAt2 0 0 (fun _ => capturedPoint 0) ps.lookupProduct }

theorem sweep_lookup_product_first_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepLookupProductFirst ch) capturedMsm := by
  native_decide

def psSweepLookupProductLastProof : ProofString shape Fp G :=
  { ps with lookupProduct := mapAt2 1 0 (fun _ => capturedPoint 0) ps.lookupProduct }

theorem sweep_lookup_product_last_proof_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepLookupProductLastProof ch) capturedMsm := by
  native_decide

def psSweepLookupProductLastLookup : ProofString shape Fp G :=
  { ps with lookupProduct := mapAt2 0 2 (fun _ => capturedPoint 0) ps.lookupProduct }

theorem sweep_lookup_product_last_lookup_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepLookupProductLastLookup ch) capturedMsm := by
  native_decide

/-! ### `vanishingRandom` (single, `G`) -/

def psSweepVanishingRandom : ProofString shape Fp G :=
  { ps with vanishingRandom := capturedPoint 0 }

theorem sweep_vanishing_random_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepVanishingRandom ch) capturedMsm := by
  native_decide

/-! ### `hPieces` (piece, `G`) -/

def psSweepHPiecesFirst : ProofString shape Fp G :=
  { ps with hPieces := mapAt 0 (fun _ => capturedPoint 0) ps.hPieces }

theorem sweep_h_pieces_first_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepHPiecesFirst ch) capturedMsm := by
  native_decide

def psSweepHPiecesLastPiece : ProofString shape Fp G :=
  { ps with hPieces := mapAt 7 (fun _ => capturedPoint 0) ps.hPieces }

theorem sweep_h_pieces_last_piece_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepHPiecesLastPiece ch) capturedMsm := by
  native_decide

/-! ### `instanceEvals` (proof × query, `F`; the query axis has length 1) -/

def psSweepInstanceEvalsFirst : ProofString shape Fp G :=
  { ps with instanceEvals := mapAt2 0 0 (· + 1) ps.instanceEvals }

theorem sweep_instance_evals_first_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepInstanceEvalsFirst ch) capturedMsm := by
  native_decide

def psSweepInstanceEvalsLastProof : ProofString shape Fp G :=
  { ps with instanceEvals := mapAt2 1 0 (· + 1) ps.instanceEvals }

theorem sweep_instance_evals_last_proof_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepInstanceEvalsLastProof ch) capturedMsm := by
  native_decide

/-! ### `adviceEvals` (proof × query, `F`) -/

def psSweepAdviceEvalsFirst : ProofString shape Fp G :=
  { ps with adviceEvals := mapAt2 0 0 (· + 1) ps.adviceEvals }

theorem sweep_advice_evals_first_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepAdviceEvalsFirst ch) capturedMsm := by
  native_decide

def psSweepAdviceEvalsLastProof : ProofString shape Fp G :=
  { ps with adviceEvals := mapAt2 1 0 (· + 1) ps.adviceEvals }

theorem sweep_advice_evals_last_proof_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepAdviceEvalsLastProof ch) capturedMsm := by
  native_decide

def psSweepAdviceEvalsLastQuery : ProofString shape Fp G :=
  { ps with adviceEvals := mapAt2 0 24 (· + 1) ps.adviceEvals }

theorem sweep_advice_evals_last_query_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepAdviceEvalsLastQuery ch) capturedMsm := by
  native_decide

/-! ### `fixedEvals` (query, `F`) -/

def psSweepFixedEvalsFirst : ProofString shape Fp G :=
  { ps with fixedEvals := mapAt 0 (· + 1) ps.fixedEvals }

theorem sweep_fixed_evals_first_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepFixedEvalsFirst ch) capturedMsm := by
  native_decide

def psSweepFixedEvalsLastQuery : ProofString shape Fp G :=
  { ps with fixedEvals := mapAt 28 (· + 1) ps.fixedEvals }

theorem sweep_fixed_evals_last_query_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepFixedEvalsLastQuery ch) capturedMsm := by
  native_decide

/-! ### `vanishingRandomEval` (single, `F`) -/

def psSweepVanishingRandomEval : ProofString shape Fp G :=
  { ps with vanishingRandomEval := ps.vanishingRandomEval + 1 }

theorem sweep_vanishing_random_eval_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepVanishingRandomEval ch) capturedMsm := by
  native_decide

/-! ### `permutationCommonEvals` (column, `F`) -/

def psSweepPermutationCommonEvalsFirst : ProofString shape Fp G :=
  { ps with permutationCommonEvals := mapAt 0 (· + 1) ps.permutationCommonEvals }

theorem sweep_permutation_common_evals_first_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepPermutationCommonEvalsFirst ch) capturedMsm := by
  native_decide

def psSweepPermutationCommonEvalsLastColumn : ProofString shape Fp G :=
  { ps with permutationCommonEvals := mapAt 14 (· + 1) ps.permutationCommonEvals }

theorem sweep_permutation_common_evals_last_column_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepPermutationCommonEvalsLastColumn ch) capturedMsm := by
  native_decide

/-! ### `permutationSetEvals` (proof × set × `PermSetEval`) -/

def psSweepPermutationSetEvalsEvalFirst : ProofString shape Fp G :=
  { ps with permutationSetEvals :=
      mapAt2 0 0 (fun e => { e with eval := e.eval + 1 }) ps.permutationSetEvals }

theorem sweep_permutation_set_evals_eval_first_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepPermutationSetEvalsEvalFirst ch) capturedMsm := by
  native_decide

def psSweepPermutationSetEvalsEvalLastProof : ProofString shape Fp G :=
  { ps with permutationSetEvals :=
      mapAt2 1 0 (fun e => { e with eval := e.eval + 1 }) ps.permutationSetEvals }

theorem sweep_permutation_set_evals_eval_last_proof_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepPermutationSetEvalsEvalLastProof ch) capturedMsm := by
  native_decide

def psSweepPermutationSetEvalsEvalLastSet : ProofString shape Fp G :=
  { ps with permutationSetEvals :=
      mapAt2 0 2 (fun e => { e with eval := e.eval + 1 }) ps.permutationSetEvals }

theorem sweep_permutation_set_evals_eval_last_set_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepPermutationSetEvalsEvalLastSet ch) capturedMsm := by
  native_decide

def psSweepPermutationSetEvalsNextEvalFirst : ProofString shape Fp G :=
  { ps with permutationSetEvals :=
      mapAt2 0 0 (fun e => { e with nextEval := e.nextEval + 1 }) ps.permutationSetEvals }

theorem sweep_permutation_set_evals_next_eval_first_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepPermutationSetEvalsNextEvalFirst ch) capturedMsm := by
  native_decide

/-- Set `(0, 0)` is a non-last set, so its `lastEval` is `some` (`permutationLastEvalsWellFormed`)
and `Option.map` tampers the value while keeping the read-schedule shape intact. -/
def psSweepPermutationSetEvalsLastEvalFirst : ProofString shape Fp G :=
  { ps with permutationSetEvals :=
      mapAt2 0 0 (fun e => { e with lastEval := e.lastEval.map (· + 1) }) ps.permutationSetEvals }

theorem sweep_permutation_set_evals_last_eval_first_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepPermutationSetEvalsLastEvalFirst ch) capturedMsm := by
  native_decide

/-! ### `lookupEvals` (proof × lookup × `LookupEval`) -/

def psSweepLookupEvalsProductEvalFirst : ProofString shape Fp G :=
  { ps with lookupEvals :=
      mapAt2 0 0 (fun e => { e with productEval := e.productEval + 1 }) ps.lookupEvals }

theorem sweep_lookup_evals_product_eval_first_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepLookupEvalsProductEvalFirst ch) capturedMsm := by
  native_decide

def psSweepLookupEvalsProductEvalLastProof : ProofString shape Fp G :=
  { ps with lookupEvals :=
      mapAt2 1 0 (fun e => { e with productEval := e.productEval + 1 }) ps.lookupEvals }

theorem sweep_lookup_evals_product_eval_last_proof_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepLookupEvalsProductEvalLastProof ch) capturedMsm := by
  native_decide

def psSweepLookupEvalsProductEvalLastLookup : ProofString shape Fp G :=
  { ps with lookupEvals :=
      mapAt2 0 2 (fun e => { e with productEval := e.productEval + 1 }) ps.lookupEvals }

theorem sweep_lookup_evals_product_eval_last_lookup_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepLookupEvalsProductEvalLastLookup ch) capturedMsm := by
  native_decide

def psSweepLookupEvalsProductNextEvalFirst : ProofString shape Fp G :=
  { ps with lookupEvals :=
      mapAt2 0 0 (fun e => { e with productNextEval := e.productNextEval + 1 }) ps.lookupEvals }

theorem sweep_lookup_evals_product_next_eval_first_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepLookupEvalsProductNextEvalFirst ch) capturedMsm := by
  native_decide

def psSweepLookupEvalsPermutedInputEvalFirst : ProofString shape Fp G :=
  { ps with lookupEvals :=
      mapAt2 0 0 (fun e => { e with permutedInputEval := e.permutedInputEval + 1 }) ps.lookupEvals }

theorem sweep_lookup_evals_permuted_input_eval_first_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepLookupEvalsPermutedInputEvalFirst ch) capturedMsm := by
  native_decide

def psSweepLookupEvalsPermutedInputInvEvalFirst : ProofString shape Fp G :=
  { ps with lookupEvals :=
      mapAt2 0 0 (fun e => { e with permutedInputInvEval := e.permutedInputInvEval + 1 }) ps.lookupEvals }

theorem sweep_lookup_evals_permuted_input_inv_eval_first_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepLookupEvalsPermutedInputInvEvalFirst ch) capturedMsm := by
  native_decide

def psSweepLookupEvalsPermutedTableEvalFirst : ProofString shape Fp G :=
  { ps with lookupEvals :=
      mapAt2 0 0 (fun e => { e with permutedTableEval := e.permutedTableEval + 1 }) ps.lookupEvals }

theorem sweep_lookup_evals_permuted_table_eval_first_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepLookupEvalsPermutedTableEvalFirst ch) capturedMsm := by
  native_decide

/-! ### `multiopenQPrime` (single, `G`) -/

def psSweepMultiopenQPrime : ProofString shape Fp G :=
  { ps with multiopenQPrime := capturedPoint 0 }

theorem sweep_multiopen_q_prime_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepMultiopenQPrime ch) capturedMsm := by
  native_decide

/-! ### `multiopenU` (point set, `F`) -/

def psSweepMultiopenUFirst : ProofString shape Fp G :=
  { ps with multiopenU := mapAt 0 (· + 1) ps.multiopenU }

theorem sweep_multiopen_u_first_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepMultiopenUFirst ch) capturedMsm := by
  native_decide

def psSweepMultiopenULastPointSet : ProofString shape Fp G :=
  { ps with multiopenU := mapAt 4 (· + 1) ps.multiopenU }

theorem sweep_multiopen_u_last_point_set_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepMultiopenULastPointSet ch) capturedMsm := by
  native_decide

/-! ### `ipaS` (single, `G`) -/

def psSweepIpaS : ProofString shape Fp G :=
  { ps with ipaS := capturedPoint 0 }

theorem sweep_ipa_s_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepIpaS ch) capturedMsm := by
  native_decide

/-! ### `ipaRounds` (round × `L`/`R`, `G × G`) -/

def psSweepIpaRoundsLFirst : ProofString shape Fp G :=
  { ps with ipaRounds := mapAt 0 (fun lr => (capturedPoint 0, lr.2)) ps.ipaRounds }

theorem sweep_ipa_rounds_l_first_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepIpaRoundsLFirst ch) capturedMsm := by
  native_decide

def psSweepIpaRoundsLLastRound : ProofString shape Fp G :=
  { ps with ipaRounds := mapAt 10 (fun lr => (capturedPoint 0, lr.2)) ps.ipaRounds }

theorem sweep_ipa_rounds_l_last_round_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepIpaRoundsLLastRound ch) capturedMsm := by
  native_decide

def psSweepIpaRoundsRFirst : ProofString shape Fp G :=
  { ps with ipaRounds := mapAt 0 (fun lr => (lr.1, capturedPoint 0)) ps.ipaRounds }

theorem sweep_ipa_rounds_r_first_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepIpaRoundsRFirst ch) capturedMsm := by
  native_decide

/-! ### `ipaC`, `ipaF` (single, `F`) — never absorbed by `deriveChallenges`; this MSM comparison
is their only detector -/

def psSweepIpaC : ProofString shape Fp G :=
  { ps with ipaC := ps.ipaC + 1 }

theorem sweep_ipa_c_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepIpaC ch) capturedMsm := by
  native_decide

def psSweepIpaF : ProofString shape Fp G :=
  { ps with ipaF := ps.ipaF + 1 }

theorem sweep_ipa_f_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment psSweepIpaF ch) capturedMsm := by
  native_decide

/-! ## The 22 challenges, in squeeze order (tampering `ch`, holding `ps` fixed) -/

def chSweepTheta : Challenges shape.k Fp := { ch with theta := ch.theta + 1 }

theorem sweep_theta_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment ps chSweepTheta) capturedMsm := by
  native_decide

def chSweepBeta : Challenges shape.k Fp := { ch with beta := ch.beta + 1 }

theorem sweep_beta_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment ps chSweepBeta) capturedMsm := by
  native_decide

def chSweepGamma : Challenges shape.k Fp := { ch with gamma := ch.gamma + 1 }

theorem sweep_gamma_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment ps chSweepGamma) capturedMsm := by
  native_decide

def chSweepY : Challenges shape.k Fp := { ch with y := ch.y + 1 }

theorem sweep_y_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment ps chSweepY) capturedMsm := by
  native_decide

def chSweepX : Challenges shape.k Fp := { ch with x := ch.x + 1 }

/-- `x` is one of the two challenges the rejection set reads (`xⁿ = 1`, and the multiopen
duplicate/collision points are rotations of `x`): this certifies the `+ 1` tamper lands on the
MSM-sensitivity side, so `sweep_x_mismatch` is not vacuously true via the zero-MSM rejection
fallback. -/
theorem sweep_x_assembles : (assemble? vk derivedInstanceCommitment ps chSweepX).isSome = true := by
  native_decide

theorem sweep_x_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment ps chSweepX) capturedMsm := by
  native_decide

def chSweepX1 : Challenges shape.k Fp := { ch with x1 := ch.x1 + 1 }

theorem sweep_x1_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment ps chSweepX1) capturedMsm := by
  native_decide

def chSweepX2 : Challenges shape.k Fp := { ch with x2 := ch.x2 + 1 }

theorem sweep_x2_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment ps chSweepX2) capturedMsm := by
  native_decide

def chSweepX3 : Challenges shape.k Fp := { ch with x3 := ch.x3 + 1 }

/-- `x3` is the other rejection-relevant challenge (`x₃` colliding with an opened point): as
`sweep_x_assembles`, this pins its sweep tamper to the MSM side. -/
theorem sweep_x3_assembles : (assemble? vk derivedInstanceCommitment ps chSweepX3).isSome = true := by
  native_decide

theorem sweep_x3_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment ps chSweepX3) capturedMsm := by
  native_decide

def chSweepX4 : Challenges shape.k Fp := { ch with x4 := ch.x4 + 1 }

theorem sweep_x4_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment ps chSweepX4) capturedMsm := by
  native_decide

def chSweepXi : Challenges shape.k Fp := { ch with xi := ch.xi + 1 }

theorem sweep_xi_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment ps chSweepXi) capturedMsm := by
  native_decide

def chSweepZ : Challenges shape.k Fp := { ch with z := ch.z + 1 }

theorem sweep_z_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment ps chSweepZ) capturedMsm := by
  native_decide

def chSweepIpaRound (j : ℕ) : Challenges shape.k Fp :=
  { ch with ipaRound := mapAt j (· + 1) ch.ipaRound }

theorem sweep_ipa_round_0_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment ps (chSweepIpaRound 0)) capturedMsm := by
  native_decide

theorem sweep_ipa_round_1_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment ps (chSweepIpaRound 1)) capturedMsm := by
  native_decide

theorem sweep_ipa_round_2_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment ps (chSweepIpaRound 2)) capturedMsm := by
  native_decide

theorem sweep_ipa_round_3_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment ps (chSweepIpaRound 3)) capturedMsm := by
  native_decide

theorem sweep_ipa_round_4_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment ps (chSweepIpaRound 4)) capturedMsm := by
  native_decide

theorem sweep_ipa_round_5_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment ps (chSweepIpaRound 5)) capturedMsm := by
  native_decide

theorem sweep_ipa_round_6_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment ps (chSweepIpaRound 6)) capturedMsm := by
  native_decide

theorem sweep_ipa_round_7_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment ps (chSweepIpaRound 7)) capturedMsm := by
  native_decide

theorem sweep_ipa_round_8_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment ps (chSweepIpaRound 8)) capturedMsm := by
  native_decide

theorem sweep_ipa_round_9_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment ps (chSweepIpaRound 9)) capturedMsm := by
  native_decide

theorem sweep_ipa_round_10_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitment ps (chSweepIpaRound 10)) capturedMsm := by
  native_decide

/-! ## Public inputs -/

/-- The captured public inputs with the first entry of the first instance column bumped. -/
def capturedPublicInstancesTampered : List (List Fp) :=
  match capturedPublicInstances with
  | [] => []
  | c :: cs =>
      (match c with
       | [] => [1]
       | v :: vs => (v + 1) :: vs) :: cs

/-- `derivedInstanceCommitment` recomputed from the tampered public inputs through the same
`commitLagrange` derivation (`Fixture.lean`): the tamper moves a commitment *base* of the
assembled MSM, so the match must fail on a point, not a coefficient. -/
def derivedInstanceCommitmentTampered (p : Fin shape.numProofs) (i : ℕ) : G :=
  commitLagrange (capturedPublicInstancesTampered.getD (p.val * capturedNumInstanceColumns + i) [])

theorem sweep_public_input_mismatch :
    ¬ MsmMatch (assemble vk derivedInstanceCommitmentTampered ps ch) capturedMsm := by
  native_decide

end Zcash.Snark.Fixture2
