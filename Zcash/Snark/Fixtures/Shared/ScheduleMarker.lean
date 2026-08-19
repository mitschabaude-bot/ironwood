import Zcash.Snark.Verifier.FiatShamir

/-!
# Re-encode captured Fiat–Shamir schedules

Rust captures a squeezed challenge by feeding its value back as `.scalar`. `deriveChallenges`
instead records halo2's challenge-domain marker before the squeeze.

`markerSchedule` converts the captured form to the marker form. Fixture checks then compare the
result with `deriveChallenges` using `native_decide`.
-/

namespace Zcash.Snark

variable {F G : Type*}

/-- Convert one captured schedule step by dropping the reabsorbed challenge and appending its marker. -/
def markerSchedule.go (prev : List (TranscriptElt F G) × F) (oldLen : ℕ) :
    List (List (TranscriptElt F G) × F) → List (List (TranscriptElt F G) × F)
  | [] => [prev]
  | e :: es =>
      prev :: markerSchedule.go (prev.1 ++ e.1.drop (oldLen + 1) ++ [.challenge], e.2) e.1.length es

/-- Convert a captured reabsorption schedule to `deriveChallenges`'s marker encoding. -/
def markerSchedule : List (List (TranscriptElt F G) × F) → List (List (TranscriptElt F G) × F)
  | [] => []
  | e :: es => markerSchedule.go (e.1 ++ [.challenge], e.2) e.1.length es

end Zcash.Snark
