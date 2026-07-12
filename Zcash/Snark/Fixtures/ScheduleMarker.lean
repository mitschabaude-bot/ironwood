import Zcash.Snark.Verifier.FiatShamir

/-!
# Captured Fiat–Shamir schedules, re-encoded to the challenge-marker transcript

The Rust `ChallengeRecorder` captures record each squeeze's transcript prefix in the *re-absorption*
encoding: after a squeeze, the challenge value is fed back into the running transcript as a `.scalar`,
and no marker is written. `deriveChallenges` instead models the deployed transcript with the
`TranscriptElt.challenge` domain marker — halo2 writes the `BLAKE2B_PREFIX_CHALLENGE` byte before each
squeeze and never feeds the challenge value back (`Zcash.Snark.Verifier.FiatShamir`).

The two encodings record the same absorb events, so they are interconvertible: `markerSchedule`
re-encodes a captured schedule into the marker form, and the per-capture schedule checks
(`deriveChallenges_matches_captured_schedule`) re-verify the converted schedule against
`deriveChallenges` by `native_decide` — a conversion mistake surfaces there, not silently.
-/

namespace Zcash.Snark

variable {F G : Type*}

/-- The fold behind `markerSchedule`: `prev` is the previous entry already re-encoded (its prefix ends
with the `challenge` marker), `oldLen` the previous entry's prefix length in the captured encoding.
Each step drops the one re-absorbed challenge that opens every post-squeeze block of the captured
encoding, keeps the block's absorbs, and appends the marker. -/
def markerSchedule.go (prev : List (TranscriptElt F G) × F) (oldLen : ℕ) :
    List (List (TranscriptElt F G) × F) → List (List (TranscriptElt F G) × F)
  | [] => [prev]
  | e :: es =>
      prev :: markerSchedule.go (prev.1 ++ e.1.drop (oldLen + 1) ++ [.challenge], e.2) e.1.length es

/-- Re-encode a captured Fiat–Shamir schedule from the capture's re-absorption encoding (each squeezed
challenge fed back as a `.scalar`, no marker) to `deriveChallenges`'s challenge-marker encoding: entry
`i`'s prefix becomes entry `i−1`'s re-encoded prefix, then entry `i`'s new absorbs — its captured
prefix past entry `i−1`'s, minus the single re-absorbed challenge — then the `challenge` marker. The
challenge values are unchanged. -/
def markerSchedule : List (List (TranscriptElt F G) × F) → List (List (TranscriptElt F G) × F)
  | [] => []
  | e :: es => markerSchedule.go (e.1 ++ [.challenge], e.2) e.1.length es

end Zcash.Snark
