import Zcash.Snark.Verifier.Assemble

/-!
# Public-instance validation

Halo2 validates the public-instance shape before committing columns or reading proof data.  Each
proof must supply exactly the instance-column count pinned by the verifying key, and each column
must fit in the usable prefix of the evaluation domain.  This module models those rejection paths
without conflating the raw public rows with their derived commitments.
-/

namespace Zcash.Snark

open Zcash.Arithmetic

/-- Raw public-instance columns, grouped by proof.  The outer proof count is already fixed by the
typed `ProofString`; each proof's column list remains raw so a wrong column count is representable
and rejectable. -/
abbrev RawInstances (shape : Shape) (F : Type*) :=
  Fin shape.numProofs → List (List F)

/-- Halo2's usable instance-row prefix: the domain excluding the blinding suffix and terminal row. -/
def instanceUsableRows {shape : Shape} {F G : Type*}
    (vk : VerifyingKey shape F G) : ℕ :=
  vk.n - (vk.blindingFactors + 1)

/-- Every proof supplies exactly the number of instance columns pinned by the proof shape. -/
def InstancesHaveExpectedColumnCount {shape : Shape} {F : Type*}
    (instances : RawInstances shape F) : Prop :=
  ∀ p, (instances p).length = shape.numInstanceColumns

instance {shape : Shape} {F : Type*} (instances : RawInstances shape F) :
    Decidable (InstancesHaveExpectedColumnCount instances) := by
  unfold InstancesHaveExpectedColumnCount
  infer_instance

/-- Every supplied instance column fits in Halo2's usable row prefix. -/
def InstanceColumnsFit {shape : Shape} {F G : Type*}
    (vk : VerifyingKey shape F G) (instances : RawInstances shape F) : Prop :=
  ∀ p (column : Fin (instances p).length),
    ((instances p).get column).length ≤ instanceUsableRows vk

instance {shape : Shape} {F G : Type*} (vk : VerifyingKey shape F G)
    (instances : RawInstances shape F) : Decidable (InstanceColumnsFit vk instances) := by
  unfold InstanceColumnsFit
  infer_instance

/-- Raw instances after the two deployed pre-commitment checks have succeeded. -/
structure ValidatedInstances {shape : Shape} {F G : Type*}
    (vk : VerifyingKey shape F G) where
  columns : RawInstances shape F
  columnCount : InstancesHaveExpectedColumnCount columns
  columnsFit : InstanceColumnsFit vk columns

/-- Perform Halo2's instance-column count and usable-row checks. -/
def validateInstances? {shape : Shape} {F G : Type*}
    (vk : VerifyingKey shape F G) (instances : RawInstances shape F) :
    Option (ValidatedInstances vk) :=
  if hcount : InstancesHaveExpectedColumnCount instances then
    if hfit : InstanceColumnsFit vk instances then
      some ⟨instances, hcount, hfit⟩
    else none
  else none

/-- Derive the total commitment family consumed by the existing query assembler.  Only indices
below `shape.numInstanceColumns` are reachable from a faithful VK; `getD` keeps the legacy total
function representation at that internal boundary. -/
def ValidatedInstances.commitments {shape : Shape} {F G : Type*}
    {vk : VerifyingKey shape F G} (instances : ValidatedInstances vk)
    (commitColumn : List F → G) : Fin shape.numProofs → ℕ → G :=
  fun p column => commitColumn ((instances.columns p).getD column [])

/-- The rejecting verifier entry point for raw public instances.  Validation precedes commitment
derivation and MSM assembly, matching `halo2_proofs::plonk::verify_proof`. -/
def assembleInstances? {shape : Shape} {F G : Type*}
    [Field F] [DecidableEq F] [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape F G) (instances : RawInstances shape F)
    (commitColumn : List F → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F) : Option (Msm shape.k F G) :=
  match validateInstances? vk instances with
  | none => none
  | some valid => assemble? vk (valid.commitments commitColumn) ps ch

theorem validateInstances?_eq_none_of_wrong_column_count
    {shape : Shape} {F G : Type*} (vk : VerifyingKey shape F G)
    (instances : RawInstances shape F)
    (hcount : ¬ InstancesHaveExpectedColumnCount instances) :
    validateInstances? vk instances = none := by
  simp [validateInstances?, hcount]

theorem validateInstances?_eq_none_of_oversized_column
    {shape : Shape} {F G : Type*} (vk : VerifyingKey shape F G)
    (instances : RawInstances shape F)
    (hcount : InstancesHaveExpectedColumnCount instances)
    (hfit : ¬ InstanceColumnsFit vk instances) :
    validateInstances? vk instances = none := by
  simp [validateInstances?, hcount, hfit]

theorem validateInstances?_isSome_of_valid
    {shape : Shape} {F G : Type*} (vk : VerifyingKey shape F G)
    (instances : RawInstances shape F)
    (hcount : InstancesHaveExpectedColumnCount instances)
    (hfit : InstanceColumnsFit vk instances) :
    (validateInstances? vk instances).isSome = true := by
  simp [validateInstances?, hcount, hfit]

theorem assembleInstances?_eq_none_of_wrong_column_count
    {shape : Shape} {F G : Type*}
    [Field F] [DecidableEq F] [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape F G) (instances : RawInstances shape F)
    (commitColumn : List F → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F)
    (hcount : ¬ InstancesHaveExpectedColumnCount instances) :
    assembleInstances? vk instances commitColumn ps ch = none := by
  simp [assembleInstances?, validateInstances?, hcount]

theorem assembleInstances?_eq_none_of_oversized_column
    {shape : Shape} {F G : Type*}
    [Field F] [DecidableEq F] [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape F G) (instances : RawInstances shape F)
    (commitColumn : List F → G) (ps : ProofString shape F G)
    (ch : Challenges shape.k F)
    (hcount : InstancesHaveExpectedColumnCount instances)
    (hfit : ¬ InstanceColumnsFit vk instances) :
    assembleInstances? vk instances commitColumn ps ch = none := by
  simp [assembleInstances?, validateInstances?, hcount, hfit]

end Zcash.Snark
