import Zcash.Snark.Fixtures.SingleAction.Honest.FiatShamir
import Zcash.Snark.Keygen.InstanceCapture
import Mathlib.Util.AssertNoSorry

/-!
# The trust boundary at the Lean-derived key

The statement of record for the single-action capture: the deployed verifier's fingerprint
— `assemble` at the challenges Lean's Fiat–Shamir schedule model derives from the captured
oracle — matches the captured MSM, with the verifying key spelled as its end-to-end
derivation from the ported `configure`/keygen at the captured URS, and, in the strongest
form, the instance commitments spelled as the circuit's commitment of the captured public
inputs. The dumped verifying-key record no longer enters the comparison, and the captured
challenges are derived rather than taken as given.

Both theorems rewrite certificate equalities into the captured match — stating the boundary
at derived artifacts costs no new evaluation.
-/

namespace Zcash.Snark.Fixture

open Zcash.Snark
open Zcash.Circuits.Action (actionCircuit)

/-- The Action circuit's derived key at the captured URS, transported to the fixture shape. -/
def derivedVk : VerifyingKey shape Fp G :=
  Keygen.actionCircuitShape_eq_fixtureCircuitShape ▸ actionCircuit.toVerifierKey capturedURS

/-- **The fingerprint match at the derived verifying key.** The keygen certificate
(`Keygen.vk_eq_toVerifierKey`) rewrites the dumped key out of
`nonInteractiveFingerprint_matches`. -/
theorem nonInteractiveFingerprint_matches_derived :
    MsmMatch
      (nonInteractiveFingerprintForStatement capturedFs capturedVkTranscriptRepr
        derivedVk derivedInstanceCommitment ps)
      capturedMsm := by
  unfold derivedVk
  have h := Keygen.vk_eq_toVerifierKey
  rw [← h]
  exact nonInteractiveFingerprint_matches

/-- **The fingerprint match with the instance side also derived**: the commitments are the
circuit's commitment of the captured public inputs (`Keygen.instanceCommitment_capturedActionInputs`),
so both group-element families on the Lean side are derivations, not dump entries. -/
theorem nonInteractiveFingerprint_matches_derived_inputs :
    MsmMatch
      (nonInteractiveFingerprintForStatement capturedFs capturedVkTranscriptRepr
        derivedVk
        (actionCircuit.instanceCommitment capturedURS Keygen.capturedActionInputs) ps)
      capturedMsm := by
  rw [Keygen.instanceCommitment_capturedActionInputs]
  exact nonInteractiveFingerprint_matches_derived

assert_no_sorry nonInteractiveFingerprint_matches_derived
assert_no_sorry nonInteractiveFingerprint_matches_derived_inputs

end Zcash.Snark.Fixture
