import Zcash.Snark.Fixtures.MultiAction.Fixture
import Zcash.Snark.Fixtures.ScheduleMarker

/-!
# Fiat–Shamir schedule check for the multi-action capture

Checks the deployed Fiat–Shamir absorb/squeeze order against the multi-action Rust capture, then connects
the resulting FS-derived fingerprint (`nonInteractiveFingerprint`, i.e. `assemble` at `deriveChallenges`)
to the captured multi-action MSM. The multi-action analog of `Zcash.Snark.Fixtures.SingleAction.FiatShamir`,
with the challenge schedule made concrete for this capture: Blake2b is taken at the random-oracle boundary,
and `capturedFs` acts as a fixture oracle over Rust-captured transcript events, returning each captured
challenge only when `deriveChallenges` presents the captured prefix (re-encoded to the challenge-marker
transcript by `markerSchedule`).

With `numProofs = 2` this check reaches the schedule's *per-sub-proof absorb interleavings* — all
proofs' advice commitments before `θ`, per-proof-per-lookup permuted pairs before `β`/`γ`, per-proof
evaluation blocks before `x₁`, and so on — which the single-action fixture exercises only at length 1.
A mis-ordered multi-proof absorb changes the transcript prefix presented to `capturedFs`, so the
`deriveChallenges_matches_captured_schedule` check fails.

This remains a fixture-oracle check over typed transcript events: generated `capturedInit` contains the
verifier-key transcript scalar and instance commitment events before the first proof-derived read, and
generated `capturedScheduleEntries` records the Rust verifier prefixes, including that captured prefix.

As with the generated fingerprint fixtures, the Rust capture/dumper boundary is trusted to emit the
typed proof fields, verifier-key transcript scalar, instance commitments, transcript-event trace, and
captured challenges corresponding to the deployed transcript; this file does not replay transcript
bytes.

TODO: once a general transcript-ordering theorem lands, either point this oracle at it or keep it as
a concrete regression for the captured proof.
-/

namespace Zcash.Snark.Fixture2

open Zcash.Snark

/-- The challenge values as emitted by the Rust transcript-event capture. -/
def capturedChallengeValues : List Fp :=
  capturedScheduleEntries.map Prod.snd

/-- The same challenge values, projected through the generated `ch` record. -/
def expectedChallengeValues : List Fp :=
  [ch.theta, ch.beta, ch.gamma, ch.y, ch.x, ch.x1, ch.x2, ch.x3, ch.x4, ch.xi, ch.z]
    ++ List.ofFn (fun j : Fin shape.k => ch.ipaRound j)

/-- The generated schedule carries the same challenge sequence as the generated `ch` record. -/
theorem capturedChallengeValues_eq_expected : capturedChallengeValues = expectedChallengeValues := by
  native_decide

/-- The fallback value used when `deriveChallenges` presents an unexpected transcript prefix. -/
def missingChallenge : Fp := 0

theorem missingChallenge_not_captured : missingChallenge ∉ capturedChallengeValues := by
  native_decide

/-- The captured challenges are pairwise distinct, so the schedule check's record equality also detects
output-field wiring mistakes in `deriveChallenges`: swapping two challenge assignments would equate two
distinct captured values. (Without this, a swap between two accidentally-equal captured challenges
would pass silently.) -/
theorem capturedChallengeValues_nodup : capturedChallengeValues.Nodup := by
  native_decide

/-- Every captured squeeze prefix starts with the generated pre-proof verifier transcript prefix. -/
def capturedScheduleIncludesInit : Bool :=
  capturedScheduleEntries.all fun e => decide (e.1.take capturedInit.length = capturedInit)

theorem capturedScheduleIncludesInit_eq_true : capturedScheduleIncludesInit = true := by
  native_decide

/-- The captured schedule re-encoded to `deriveChallenges`'s challenge-marker transcript
(`markerSchedule`): the capture records re-absorption prefixes, the model writes a `challenge` marker
per squeeze and never feeds the challenge back — same absorb events, same challenge values. -/
def markerScheduleEntries : List (List (TranscriptElt Fp G) × Fp) :=
  markerSchedule capturedScheduleEntries

/-- Fixture Fiat–Shamir oracle: returns a captured challenge only at a Rust-captured transcript prefix,
re-encoded to the challenge-marker transcript (`markerScheduleEntries`). Unknown prefixes return
`missingChallenge`, which is checked above not to be one of the captured challenges. -/
def capturedFs : FiatShamir Fp G := {
  squeeze := fun t =>
    match markerScheduleEntries.find? (fun e => decide (e.1 = t)) with
    | some e => e.2
    | none => missingChallenge
}

/-- Concrete check that the Lean Fiat–Shamir schedule reaches the captured challenges in the captured
multi-action proof. This is the theorem that fails if a proof-derived absorb is reordered or omitted. -/
theorem deriveChallenges_matches_captured_schedule :
    deriveChallenges capturedFs capturedInit ps = ch := by native_decide

/-- The Fiat–Shamir-derived fingerprint matches the captured multi-action MSM under the concrete captured
schedule oracle above. -/
theorem nonInteractiveFingerprint_matches :
    MsmMatch (nonInteractiveFingerprint capturedFs capturedInit vk ps) capturedMsm := by
  unfold nonInteractiveFingerprint
  rw [deriveChallenges_matches_captured_schedule]
  exact fingerprint_matches

end Zcash.Snark.Fixture2
