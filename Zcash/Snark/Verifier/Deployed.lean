import Zcash.Snark.Verifier.FiatShamir
import Zcash.Snark.Verifier.Instances

/-!
# Halo2-faithful non-interactive verifier entry

This module composes the raw-instance rejection path with the statement-bound Fiat–Shamir
schedule.  Raw public columns are checked before they are committed.  The VK transcript
representation and every resulting instance commitment are then absorbed before proof-controlled
advice commitments and the first challenge. Binding the key here means binding its opaque transcript
representation; this model does not connect `vkTranscriptRepr` to the fields of `vk`. Halo2's
Blake2b hash of the pinned key and its collision resistance remain below this abstraction boundary.

The column commitment operation remains a parameter here.  For Orchard it is instantiated by the
existing Lagrange-basis commitment model; this entry point controls when it may run and how its
outputs enter both the transcript and opening-query assembly. Binding is therefore at commitment
level: Halo2's Lagrange commitment zero-pads columns to the usable length, so raw columns that differ
only by trailing zeros commit and verify identically.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm)

/-- Checked non-interactive MSM assembly from raw public-instance columns.

This is the generic verifier entry corresponding to Halo2's `verify_proof` control flow: reject
malformed instance shapes, derive their commitments, bind the VK and all instance commitments into
Fiat–Shamir, derive challenges, and finally run the checked MSM assembler. -/
def assembleNonInteractiveInstances? {shape : Shape} {F G : Type*}
    [Field F] [DecidableEq F] [DecidableEq G] [Inhabited G]
    (fs : FiatShamir F G) (vkTranscriptRepr : F) (vk : VerifyingKey shape F G)
    (instances : RawInstances shape F) (commitColumn : List F → G)
    (ps : ProofString shape F G) : Option (Msm shape.k F G) :=
  match validateInstances? vk instances with
  | none => none
  | some valid =>
      let instanceCommitment := valid.commitments commitColumn
      assemble? vk instanceCommitment ps
        (deriveChallengesForStatement fs vkTranscriptRepr instanceCommitment ps)

theorem assembleNonInteractiveInstances?_eq_none_of_wrong_column_count
    {shape : Shape} {F G : Type*}
    [Field F] [DecidableEq F] [DecidableEq G] [Inhabited G]
    (fs : FiatShamir F G) (vkTranscriptRepr : F) (vk : VerifyingKey shape F G)
    (instances : RawInstances shape F) (commitColumn : List F → G)
    (ps : ProofString shape F G)
    (hcount : ¬ InstancesHaveExpectedColumnCount instances) :
    assembleNonInteractiveInstances? fs vkTranscriptRepr vk instances commitColumn ps = none := by
  simp [assembleNonInteractiveInstances?, validateInstances?, hcount]

theorem assembleNonInteractiveInstances?_eq_none_of_oversized_column
    {shape : Shape} {F G : Type*}
    [Field F] [DecidableEq F] [DecidableEq G] [Inhabited G]
    (fs : FiatShamir F G) (vkTranscriptRepr : F) (vk : VerifyingKey shape F G)
    (instances : RawInstances shape F) (commitColumn : List F → G)
    (ps : ProofString shape F G)
    (hcount : InstancesHaveExpectedColumnCount instances)
    (hfit : ¬ InstanceColumnsFit vk instances) :
    assembleNonInteractiveInstances? fs vkTranscriptRepr vk instances commitColumn ps = none := by
  simp [assembleNonInteractiveInstances?, validateInstances?, hcount, hfit]

end Zcash.Snark
