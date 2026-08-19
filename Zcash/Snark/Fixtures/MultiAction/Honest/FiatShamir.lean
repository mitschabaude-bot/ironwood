import Zcash.Snark.Fixtures.MultiAction.Honest.Fixture
import Zcash.Snark.Fixtures.Shared.ScheduleMarker
import Zcash.Snark.Verifier.Deployed

/-!
# Fiat–Shamir schedule check for the multi-action capture

This file checks the deployed absorb/squeeze order against a multi-action Rust capture and then
matches `nonInteractiveFingerprint` to the captured MSM; `Boundary.lean` restates that match at the
Lean-derived verifying key as the statement of record. `capturedFs` returns a captured challenge
only at its captured transcript prefix, converted by `markerSchedule` to the model's marker encoding.

With `numProofs = 2`, the check covers the per-proof absorb order that the single-action fixture cannot
distinguish. The Rust capture is trusted to provide the typed proof data, transcript events, and
challenges, not transcript bytes. General IPA ordering and sub-proof traversal are proved elsewhere;
this remains a concrete full-schedule regression.
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

/-- The Lean schedule reaches every captured challenge for the multi-action proof. -/
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

/-- The captured flattened public columns, restored to the verifier's proof/column nesting. -/
def capturedRawInstances : RawInstances shape Fp :=
  fun p => List.ofFn fun column : Fin shape.numInstanceColumns =>
    capturedPublicInstances.getD
      (p.val * capturedNumInstanceColumns + column.val) []

/-- The captured raw instance family has the circuit-pinned column count. -/
theorem capturedRawInstances_have_expected_column_count :
    InstancesHaveExpectedColumnCount capturedRawInstances := by
  intro p
  simp [capturedRawInstances]

/-- Every captured public-instance column fits in the verifier's usable row prefix. -/
theorem capturedRawInstances_columns_fit :
    InstanceColumnsFit vk capturedRawInstances := by
  intro p column
  fin_cases p <;> fin_cases column <;>
    norm_num [capturedRawInstances, instanceUsableRows, vk, shape, capturedNumInstanceColumns,
      capturedPublicInstances]

/-- Committing the validated raw columns recovers every configured captured commitment. -/
theorem capturedRawInstances_commitments_eq
    (p : Fin shape.numProofs) (column : Fin shape.numInstanceColumns) :
    commitLagrange ((capturedRawInstances p).getD column []) =
      derivedInstanceCommitment p column := by
  fin_cases p <;> fin_cases column <;>
    simp [capturedRawInstances, derivedInstanceCommitment, shape, capturedNumInstanceColumns]

/-- The captured VK opens only the configured instance column. -/
theorem capturedInstanceQueryLayout_eq : vk.instanceQueryLayout = [(0, 0)] := by
  rfl

/-- The validated and captured commitment families agree everywhere the captured VK reads them. -/
theorem capturedRawInstances_commitments_eq_on_layout :
    ∀ p column rotation, (column, rotation) ∈ vk.instanceQueryLayout →
      commitLagrange ((capturedRawInstances p).getD column []) =
        derivedInstanceCommitment p column := by
  intro p column rotation hmem
  rw [capturedInstanceQueryLayout_eq, List.mem_singleton] at hmem
  injection hmem with hcolumn _
  subst column
  exact capturedRawInstances_commitments_eq p ⟨0, by simp [shape]⟩

/-- The composed rejecting verifier reproduces checked assembly at the captured challenges. -/
theorem assembleNonInteractiveInstances?_matches_captured :
    assembleNonInteractiveInstances? capturedFs capturedVkTranscriptRepr vk
      capturedRawInstances commitLagrange ps =
        assemble? vk derivedInstanceCommitment ps ch := by
  simp only [assembleNonInteractiveInstances?, validateInstances?,
    capturedRawInstances_have_expected_column_count, capturedRawInstances_columns_fit,
    ↓reduceDIte]
  change
    assemble? vk
        (fun p column => commitLagrange ((capturedRawInstances p).getD column [])) ps
        (deriveChallengesForStatement capturedFs capturedVkTranscriptRepr
          (fun p column => commitLagrange ((capturedRawInstances p).getD column [])) ps) =
      assemble? vk derivedInstanceCommitment ps ch
  rw [deriveChallengesForStatement_congr capturedFs capturedVkTranscriptRepr
      (fun p column => commitLagrange ((capturedRawInstances p).getD column []))
      derivedInstanceCommitment ps capturedRawInstances_commitments_eq,
    deriveChallengesForStatement_matches_captured_schedule]
  exact assemble?_congr_instanceCommitment vk _ _ ps ch
    capturedRawInstances_commitments_eq_on_layout

/-- The Fiat–Shamir-derived fingerprint matches the captured multi-action MSM under the concrete captured
schedule oracle above. -/
theorem nonInteractiveFingerprint_matches :
    MsmMatch (nonInteractiveFingerprintForStatement capturedFs capturedVkTranscriptRepr
      vk derivedInstanceCommitment ps) capturedMsm := by
  unfold nonInteractiveFingerprintForStatement
  rw [deriveChallengesForStatement_matches_captured_schedule]
  exact fingerprint_matches

end Zcash.Snark.Fixture2
