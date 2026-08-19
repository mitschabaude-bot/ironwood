import Zcash.Snark.Fixtures.MultiAction.Random.Fixture
import Zcash.Snark.Fixtures.Shared.ScheduleMarker

/-!
# Fiat–Shamir schedule check for the random two-action capture

The schedule checks of the honest families, restated at the random two-action capture: the
deployed verifier ran to completion on a random proof string (match-only — the capture is
deliberately non-accepting), and its replay recorded the schedule consumed here. `capturedFs`
returns a captured challenge only at its captured transcript prefix, converted by
`markerSchedule` to the model's marker encoding. `deriveChallenges_matches_captured_schedule`
pins the Lean schedule model — including the per-proof absorb interleaving — at this generic
input, and `nonInteractiveFingerprint_matches` folds the schedule into the MSM match;
`Boundary.lean` restates that match at the Lean-derived verifying key as the family's statement
of record.
-/

namespace Zcash.Snark.FixtureRandom2

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

/-- The captured challenges are distinct, so record equality also detects swapped output fields. -/
theorem capturedChallengeValues_nodup : capturedChallengeValues.Nodup := by
  native_decide

/-- Every captured squeeze prefix starts with the generated pre-proof verifier transcript prefix. -/
def capturedScheduleIncludesInit : Bool :=
  capturedScheduleEntries.all fun e => decide (e.1.take capturedInit.length = capturedInit)

theorem capturedScheduleIncludesInit_eq_true : capturedScheduleIncludesInit = true := by
  native_decide

/-- The captured schedule converted from challenge re-absorption to challenge-marker encoding. -/
def markerScheduleEntries : List (List (TranscriptElt Fp G) × Fp) :=
  markerSchedule capturedScheduleEntries

/-- Return a captured challenge at its recorded prefix and `missingChallenge` elsewhere. -/
def capturedFs : FiatShamir Fp G := {
  squeeze := fun t =>
    match markerScheduleEntries.find? (fun e => decide (e.1 = t)) with
    | some e => e.2
    | none => missingChallenge
}

/-- The Lean schedule reaches every captured challenge for the random two-action proof. -/
theorem deriveChallenges_matches_captured_schedule :
    deriveChallenges capturedFs capturedInit ps = ch := by native_decide

/-- The captured verifier prefix is exactly the canonical VK-and-instance prefix. -/
theorem capturedInit_eq_initialTranscript :
    capturedInit =
      initialTranscript capturedVkTranscriptRepr derivedInstanceCommitment := by
  change
    TranscriptElt.scalar capturedVkTranscriptRepr ::
        List.map (TranscriptElt.point (F := Fp)) capturedInstanceCommitments =
      TranscriptElt.scalar capturedVkTranscriptRepr ::
        absorbInstanceCommitments derivedInstanceCommitment
  apply congrArg (fun tail => TranscriptElt.scalar capturedVkTranscriptRepr :: tail)
  rw [← instance_commitments_derived]
  rfl

/-- The statement-bound entry point reaches the captured challenge schedule. -/
theorem deriveChallengesForStatement_matches_captured_schedule :
    deriveChallengesForStatement capturedFs capturedVkTranscriptRepr
      derivedInstanceCommitment ps = ch := by
  rw [deriveChallengesForStatement, ← capturedInit_eq_initialTranscript]
  exact deriveChallenges_matches_captured_schedule

/-- The Fiat–Shamir-derived fingerprint matches the captured random two-action MSM, with the VK
and public statement bound into Fiat–Shamir as the honest families state it. -/
theorem nonInteractiveFingerprint_matches :
    MsmMatch (nonInteractiveFingerprintForStatement capturedFs capturedVkTranscriptRepr
      vk derivedInstanceCommitment ps) capturedMsm := by
  unfold nonInteractiveFingerprintForStatement
  rw [deriveChallengesForStatement_matches_captured_schedule]
  exact fingerprint_matches

end Zcash.Snark.FixtureRandom2
