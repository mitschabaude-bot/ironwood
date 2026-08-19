import Zcash.Snark.Fixtures.MultiAction.Honest.FiatShamir
import Zcash.Snark.Fixtures.MultiAction.Honest.VkCertificate
import Mathlib.Util.AssertNoSorry

/-!
# The trust boundary at the Lean-derived key (multi-action)

The statement of record for the multi-action capture: the deployed verifier's fingerprint
— `assemble` at the challenges Lean's Fiat–Shamir schedule model derives from the captured
oracle — matches the captured MSM, with the verifying key spelled as its end-to-end
derivation from the ported `configure`/keygen at the captured URS
(`VkCertificate.lean`). The dumped verifying-key record no longer enters the comparison,
and the captured challenges are derived rather than taken as given.

The instance side stays `derivedInstanceCommitment` — already a derivation, the Lagrange
commitment of the captured public inputs, pinned to the captured points by
`instance_commitments_derived` — since the multi-action capture has no
`Keygen/InstanceCapture.lean` analogue.
-/

namespace Zcash.Snark.Fixture2

open Zcash.Snark

/-- **The fingerprint match at the derived verifying key.** The transported certificate
(`vk_eq_derived`) rewrites the dumped key out of `nonInteractiveFingerprint_matches`. -/
theorem nonInteractiveFingerprint_matches_derived :
    MsmMatch
      (nonInteractiveFingerprintForStatement capturedFs capturedVkTranscriptRepr
        derivedVk derivedInstanceCommitment ps)
      capturedMsm := by
  have h : vk = derivedVk := vk_eq_derived
  rw [← h]
  exact nonInteractiveFingerprint_matches

assert_no_sorry nonInteractiveFingerprint_matches_derived

end Zcash.Snark.Fixture2
