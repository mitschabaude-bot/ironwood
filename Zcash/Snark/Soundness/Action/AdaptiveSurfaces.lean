import Zcash.Snark.Soundness.Action.AdaptiveTerminal
import Zcash.Snark.Soundness.Action.StraightLineBudgets
import Zcash.Snark.Soundness.AGM.AdaptiveSurfaces

/-!
# Action semantic surfaces for arbitrary adaptive online-AGM adversaries

The first five deployed squeezes are `theta`, `beta`, `gamma`, `y`, and `x`.  At each point an
online-AGM annotation fixes exactly the prover commitments already absorbed into that prefix.
This file records those stage-local representation lists before constructing the corresponding
finite bad sets.
-/

namespace Zcash.Snark

open Classical
open Halo2 CompPoly CompPoly.CPolynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open scoped ENNReal

variable {shape : Shape}

local instance vestaInhabitedAdaptiveActionSurfaces : Inhabited VestaG := ⟨0⟩

set_option maxRecDepth 10000

/-- Prover-emitted AGM representations available at one of the five Action semantic squeezes.
The definition follows the deployed transcript order literally. -/
def AlgebraicProofString.actionRepresentationsBefore
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 5) :
    List (AlgebraicPoint (F := Fp) basis) :=
  let advice :=
    (List.ofFn fun p => List.ofFn fun i => aps.adviceCommitments p i).flatten
  let lookupPermuted :=
    (List.ofFn fun p => List.ofFn fun i => aps.lookupPermutedInput p i).flatten ++
      (List.ofFn fun p => List.ofFn fun i => aps.lookupPermutedTable p i).flatten
  let products :=
    (List.ofFn fun p => List.ofFn fun i => aps.permutationProduct p i).flatten ++
      (List.ofFn fun p => List.ofFn fun i => aps.lookupProduct p i).flatten ++
      [aps.vanishingRandom]
  if (n : Nat) = 0 then advice
  else if (n : Nat) < 3 then advice ++ lookupPermuted
  else if (n : Nat) = 3 then advice ++ lookupPermuted ++ products
  else advice ++ lookupPermuted ++ products ++ List.ofFn aps.hPieces

theorem AlgebraicProofString.adviceCommitment_mem_actionRepresentationsBefore
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 5)
    (p : Fin shape.numProofs) (i : Fin shape.numAdviceColumns) :
    aps.adviceCommitments p i ∈ aps.actionRepresentationsBefore n := by
  have hadvice : aps.adviceCommitments p i ∈
      (List.ofFn fun p => List.ofFn fun i => aps.adviceCommitments p i).flatten :=
    List.mem_flatten.mpr
      ⟨_, List.mem_ofFn.mpr ⟨p, rfl⟩, List.mem_ofFn.mpr ⟨i, rfl⟩⟩
  unfold AlgebraicProofString.actionRepresentationsBefore
  split
  · exact hadvice
  · split
    · simp only [List.mem_append]
      tauto
    · split <;> simp only [List.mem_append] <;> tauto

theorem AlgebraicProofString.lookupPermutedInput_mem_actionRepresentationsBefore
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 5)
    (p : Fin shape.numProofs) (i : Fin shape.numLookups)
    (hn : 1 ≤ (n : Nat)) :
    aps.lookupPermutedInput p i ∈ aps.actionRepresentationsBefore n := by
  have hinput : aps.lookupPermutedInput p i ∈
      (List.ofFn fun p => List.ofFn fun i => aps.lookupPermutedInput p i).flatten :=
    List.mem_flatten.mpr
      ⟨_, List.mem_ofFn.mpr ⟨p, rfl⟩, List.mem_ofFn.mpr ⟨i, rfl⟩⟩
  unfold AlgebraicProofString.actionRepresentationsBefore
  split
  · omega
  · split
    · simp only [List.mem_append]
      tauto
    · split <;> simp only [List.mem_append] <;> tauto

theorem AlgebraicProofString.lookupPermutedTable_mem_actionRepresentationsBefore
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 5)
    (p : Fin shape.numProofs) (i : Fin shape.numLookups)
    (hn : 1 ≤ (n : Nat)) :
    aps.lookupPermutedTable p i ∈ aps.actionRepresentationsBefore n := by
  have htable : aps.lookupPermutedTable p i ∈
      (List.ofFn fun p => List.ofFn fun i => aps.lookupPermutedTable p i).flatten :=
    List.mem_flatten.mpr
      ⟨_, List.mem_ofFn.mpr ⟨p, rfl⟩, List.mem_ofFn.mpr ⟨i, rfl⟩⟩
  unfold AlgebraicProofString.actionRepresentationsBefore
  split
  · omega
  · split
    · simp only [List.mem_append]
      tauto
    · split <;> simp only [List.mem_append] <;> tauto

theorem AlgebraicProofString.permutationProduct_mem_actionRepresentationsBefore
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 5)
    (p : Fin shape.numProofs) (i : Fin shape.numPermutationSets)
    (hn : 3 ≤ (n : Nat)) :
    aps.permutationProduct p i ∈ aps.actionRepresentationsBefore n := by
  have hproduct : aps.permutationProduct p i ∈
      (List.ofFn fun p => List.ofFn fun i => aps.permutationProduct p i).flatten :=
    List.mem_flatten.mpr
      ⟨_, List.mem_ofFn.mpr ⟨p, rfl⟩, List.mem_ofFn.mpr ⟨i, rfl⟩⟩
  unfold AlgebraicProofString.actionRepresentationsBefore
  split
  · omega
  · split
    · omega
    · split <;> simp only [List.mem_append, List.mem_singleton] <;> tauto

theorem AlgebraicProofString.lookupProduct_mem_actionRepresentationsBefore
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 5)
    (p : Fin shape.numProofs) (i : Fin shape.numLookups)
    (hn : 3 ≤ (n : Nat)) :
    aps.lookupProduct p i ∈ aps.actionRepresentationsBefore n := by
  have hproduct : aps.lookupProduct p i ∈
      (List.ofFn fun p => List.ofFn fun i => aps.lookupProduct p i).flatten :=
    List.mem_flatten.mpr
      ⟨_, List.mem_ofFn.mpr ⟨p, rfl⟩, List.mem_ofFn.mpr ⟨i, rfl⟩⟩
  unfold AlgebraicProofString.actionRepresentationsBefore
  split
  · omega
  · split
    · omega
    · split <;> simp only [List.mem_append, List.mem_singleton] <;> tauto

/-- Coordinate-free counterpart of `actionRepresentationsBefore`. -/
def ProofString.actionCommitmentPointsBefore {G : Type*}
    (ps : ProofString shape Fp G) (n : Fin 5) : List G :=
  let advice :=
    (List.ofFn fun p => List.ofFn fun i => ps.adviceCommitments p i).flatten
  let lookupPermuted :=
    (List.ofFn fun p => List.ofFn fun i => ps.lookupPermutedInput p i).flatten ++
      (List.ofFn fun p => List.ofFn fun i => ps.lookupPermutedTable p i).flatten
  let products :=
    (List.ofFn fun p => List.ofFn fun i => ps.permutationProduct p i).flatten ++
      (List.ofFn fun p => List.ofFn fun i => ps.lookupProduct p i).flatten ++
      [ps.vanishingRandom]
  if (n : Nat) = 0 then advice
  else if (n : Nat) < 3 then advice ++ lookupPermuted
  else if (n : Nat) = 3 then advice ++ lookupPermuted ++ products
  else advice ++ lookupPermuted ++ products ++ List.ofFn ps.hPieces

@[simp] theorem AlgebraicProofString.actionRepresentationsBefore_points
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 5) :
    (aps.actionRepresentationsBefore n).map AlgebraicPoint.point =
      aps.erase.actionCommitmentPointsBefore n := by
  fin_cases n <;>
    simp [AlgebraicProofString.actionRepresentationsBefore,
      ProofString.actionCommitmentPointsBefore, AlgebraicProofString.erase,
      Function.comp_def, List.map_flatten]

/-- At the final Action squeeze, the stage source is the complete pre-`x1` assembly source. -/
theorem AlgebraicProofString.actionRepresentationsBefore_four_append
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis)
    (fixed : List (AlgebraicPoint (F := Fp) basis)) :
    aps.actionRepresentationsBefore (4 : Fin 5) ++ fixed =
      aps.preX1AssemblySource fixed := by
  simp [AlgebraicProofString.actionRepresentationsBefore,
    AlgebraicProofString.preX1AssemblySource, AlgebraicProofString.preX1Points,
    List.append_assoc]

/-- Every representation used by an Action semantic surface occurs in the complete pre-`x`
online source. -/
theorem AlgebraicProofString.actionRepresentationsBefore_mem_preX1Points
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 5)
    (ap : AlgebraicPoint (F := Fp) basis)
    (hap : ap ∈ aps.actionRepresentationsBefore n) :
    ap ∈ aps.preX1Points := by
  fin_cases n <;>
    simp [AlgebraicProofString.actionRepresentationsBefore,
      AlgebraicProofString.preX1Points] at hap ⊢ <;> aesop

/-- Appending verifier-fixed representations preserves inclusion in the complete pre-`x`
assembly source. -/
theorem AlgebraicProofString.actionStageSource_subset_preX1AssemblySource
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis)
    (fixed : List (AlgebraicPoint (F := Fp) basis)) (n : Fin 5)
    (ap : AlgebraicPoint (F := Fp) basis)
    (hap : ap ∈ aps.actionRepresentationsBefore n ++ fixed) :
    ap ∈ aps.preX1AssemblySource fixed := by
  unfold AlgebraicProofString.preX1AssemblySource
  rw [List.mem_append] at hap ⊢
  exact hap.imp (aps.actionRepresentationsBefore_mem_preX1Points n ap) id

/-- Every stage-local prover representation is already present in that stage's actual query
transcript. -/
theorem AlgebraicProofString.actionRepresentationsBefore_covered
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (init : List (TranscriptElt Fp VestaG))
    (aps : AlgebraicProofString shape basis) (hwf : PsWellFormed aps.erase) (n : Fin 5)
    (ap : AlgebraicPoint (F := Fp) basis)
    (hap : ap ∈ aps.actionRepresentationsBefore n) :
    ap.point ∈ transcriptGroupPoints
      (preIpaSqueezePoints init aps.erase (Fin.castLE (by omega) n)) := by
  have lift {P : VestaG} {i j : Fin 11} (hij : (i : Nat) ≤ (j : Nat))
      (hmem : TranscriptElt.point P ∈ preIpaSqueezePoints init aps.erase i) :
      P ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase j) := by
    apply (transcriptGroupPoints_prefix
      (preIpaSqueezePoints_prefix_of_le init aps.erase hwf i j hij)).mem
    exact mem_transcriptGroupPoints_of_mem_point hmem
  fin_cases n
  · change ap.point ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase 0)
    simp [AlgebraicProofString.actionRepresentationsBefore] at hap
    obtain ⟨p, i, h⟩ := hap
    rw [← h]
    exact mem_transcriptGroupPoints_of_mem_point
      (adviceCommitment_mem_preIpaSqueezePoints_zero init aps.erase p i)
  · change ap.point ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase 1)
    simp [AlgebraicProofString.actionRepresentationsBefore] at hap
    rcases hap with hadvice | hinput | htable
    · obtain ⟨p, i, h⟩ := hadvice
      rw [← h]
      exact lift (i := 0) (j := 1) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hinput
      rw [← h]
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := htable
      rw [← h]
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init aps.erase p i)
  · change ap.point ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase 2)
    simp [AlgebraicProofString.actionRepresentationsBefore] at hap
    rcases hap with hadvice | hinput | htable
    · obtain ⟨p, i, h⟩ := hadvice
      rw [← h]
      exact lift (i := 0) (j := 2) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hinput
      rw [← h]
      exact lift (i := 1) (j := 2) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := htable
      rw [← h]
      exact lift (i := 1) (j := 2) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init aps.erase p i)
  · change ap.point ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase 3)
    simp [AlgebraicProofString.actionRepresentationsBefore] at hap
    rcases hap with hadvice | hinput | htable | hperm | hlookup | hrandom
    · obtain ⟨p, i, h⟩ := hadvice
      rw [← h]
      exact lift (i := 0) (j := 3) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hinput
      rw [← h]
      exact lift (i := 1) (j := 3) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := htable
      rw [← h]
      exact lift (i := 1) (j := 3) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hperm
      rw [← h]
      exact mem_transcriptGroupPoints_of_mem_point
        (permutationProduct_mem_preIpaSqueezePoints_three init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hlookup
      rw [← h]
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupProduct_mem_preIpaSqueezePoints_three init aps.erase p i)
    · rw [hrandom]
      exact mem_transcriptGroupPoints_of_mem_point
        (vanishingRandom_mem_preIpaSqueezePoints_three init aps.erase)
  · change ap.point ∈ transcriptGroupPoints (preIpaSqueezePoints init aps.erase 4)
    simp [AlgebraicProofString.actionRepresentationsBefore] at hap
    rcases hap with hadvice | hinput | htable | hperm | hlookup | hrandom | hpiece
    · obtain ⟨p, i, h⟩ := hadvice
      rw [← h]
      exact lift (i := 0) (j := 4) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hinput
      rw [← h]
      exact lift (i := 1) (j := 4) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := htable
      rw [← h]
      exact lift (i := 1) (j := 4) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hperm
      rw [← h]
      exact lift (i := 3) (j := 4) (by omega)
        (permutationProduct_mem_preIpaSqueezePoints_three init aps.erase p i)
    · obtain ⟨p, i, h⟩ := hlookup
      rw [← h]
      exact lift (i := 3) (j := 4) (by omega)
        (lookupProduct_mem_preIpaSqueezePoints_three init aps.erase p i)
    · rw [hrandom]
      exact lift (i := 3) (j := 4) (by omega)
        (vanishingRandom_mem_preIpaSqueezePoints_three init aps.erase)
    · obtain ⟨i, h⟩ := hpiece
      rw [← h]
      exact mem_transcriptGroupPoints_of_mem_point
        (hPiece_mem_preIpaSqueezePoints_four init aps.erase i)

/-- Ordinary commitment points in the stage view are covered by the same exact prefix. -/
theorem ProofString.actionCommitmentPointsBefore_covered
    (init : List (TranscriptElt Fp VestaG))
    (ps : ProofString shape Fp VestaG) (hwf : PsWellFormed ps) (n : Fin 5)
    (P : VestaG) (hP : P ∈ ps.actionCommitmentPointsBefore n) :
    P ∈ transcriptGroupPoints
      (preIpaSqueezePoints init ps (Fin.castLE (by omega) n)) := by
  have lift {P : VestaG} {i j : Fin 11} (hij : (i : Nat) ≤ (j : Nat))
      (hmem : TranscriptElt.point P ∈ preIpaSqueezePoints init ps i) :
      P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps j) := by
    apply (transcriptGroupPoints_prefix
      (preIpaSqueezePoints_prefix_of_le init ps hwf i j hij)).mem
    exact mem_transcriptGroupPoints_of_mem_point hmem
  fin_cases n
  · change P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps 0)
    simp [ProofString.actionCommitmentPointsBefore] at hP
    obtain ⟨p, i, rfl⟩ := hP
    exact mem_transcriptGroupPoints_of_mem_point
      (adviceCommitment_mem_preIpaSqueezePoints_zero init ps p i)
  · change P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps 1)
    simp [ProofString.actionCommitmentPointsBefore] at hP
    rcases hP with hadvice | hinput | htable
    · obtain ⟨p, i, rfl⟩ := hadvice
      exact lift (i := 0) (j := 1) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init ps p i)
    · obtain ⟨p, i, rfl⟩ := hinput
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := htable
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init ps p i)
  · change P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps 2)
    simp [ProofString.actionCommitmentPointsBefore] at hP
    rcases hP with hadvice | hinput | htable
    · obtain ⟨p, i, rfl⟩ := hadvice
      exact lift (i := 0) (j := 2) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init ps p i)
    · obtain ⟨p, i, rfl⟩ := hinput
      exact lift (i := 1) (j := 2) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := htable
      exact lift (i := 1) (j := 2) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init ps p i)
  · change P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps 3)
    simp [ProofString.actionCommitmentPointsBefore] at hP
    rcases hP with hadvice | hinput | htable | hperm | hlookup | hrandom
    · obtain ⟨p, i, rfl⟩ := hadvice
      exact lift (i := 0) (j := 3) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init ps p i)
    · obtain ⟨p, i, rfl⟩ := hinput
      exact lift (i := 1) (j := 3) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := htable
      exact lift (i := 1) (j := 3) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := hperm
      exact mem_transcriptGroupPoints_of_mem_point
        (permutationProduct_mem_preIpaSqueezePoints_three init ps p i)
    · obtain ⟨p, i, rfl⟩ := hlookup
      exact mem_transcriptGroupPoints_of_mem_point
        (lookupProduct_mem_preIpaSqueezePoints_three init ps p i)
    · subst P
      exact mem_transcriptGroupPoints_of_mem_point
        (vanishingRandom_mem_preIpaSqueezePoints_three init ps)
  · change P ∈ transcriptGroupPoints (preIpaSqueezePoints init ps 4)
    simp [ProofString.actionCommitmentPointsBefore] at hP
    rcases hP with hadvice | hinput | htable | hperm | hlookup | hrandom | hpiece
    · obtain ⟨p, i, rfl⟩ := hadvice
      exact lift (i := 0) (j := 4) (by omega)
        (adviceCommitment_mem_preIpaSqueezePoints_zero init ps p i)
    · obtain ⟨p, i, rfl⟩ := hinput
      exact lift (i := 1) (j := 4) (by omega)
        (lookupPermutedInput_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := htable
      exact lift (i := 1) (j := 4) (by omega)
        (lookupPermutedTable_mem_preIpaSqueezePoints_one init ps p i)
    · obtain ⟨p, i, rfl⟩ := hperm
      exact lift (i := 3) (j := 4) (by omega)
        (permutationProduct_mem_preIpaSqueezePoints_three init ps p i)
    · obtain ⟨p, i, rfl⟩ := hlookup
      exact lift (i := 3) (j := 4) (by omega)
        (lookupProduct_mem_preIpaSqueezePoints_three init ps p i)
    · subst P
      exact lift (i := 3) (j := 4) (by omega)
        (vanishingRandom_mem_preIpaSqueezePoints_three init ps)
    · obtain ⟨i, rfl⟩ := hpiece
      exact mem_transcriptGroupPoints_of_mem_point
        (hPiece_mem_preIpaSqueezePoints_four init ps i)

/-- Query-local stage source: first pre-answer representations of exactly the Action commitments
already absorbed at this squeeze, followed by verifier-fixed representations. -/
def adaptiveActionQuerySource
    (init : List (TranscriptElt Fp VestaG))
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (n : Fin 5)
    {t : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)}
    (decoded : DecodedPreIpaPrefix (shape := shape) init (Fin.castLE (by omega) n) t)
    (query : AlgebraicTranscriptQuery (F := Fp) basis t)
    (fixed : List (AlgebraicPoint (F := Fp) basis)) :
    List (AlgebraicPoint (F := Fp) basis) :=
  query.representationsForPoints
      (decoded.proof.1.actionCommitmentPointsBefore n) (by
        intro P hP
        rw [← decoded.point_eq]
        exact decoded.proof.1.actionCommitmentPointsBefore_covered
          init decoded.proof.2 n P hP) ++ fixed

/-- Canonical polynomial carried by a stage-local AGM source. -/
def adaptiveActionPointPolynomial
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (source : List (AlgebraicPoint (F := Fp) basis)) :
    VestaG → CPoly :=
  onlinePointPolynomial source

/-- Commitment slots actually consumed by the constraint model.  Returning zero outside this
finite layout makes the stage resolver agree with canonical routing on absent identities. -/
def adaptiveActionCommitmentActive
    (proofShape : Shape) {G : Type*}
    (vk : VerifyingKey proofShape Fp G) : CommitmentId → Prop
  | .instanceCol p i => p < proofShape.numProofs ∧
      ∃ rotation, (i, rotation) ∈ vk.instanceQueryLayout
  | .adviceCol p i => p < proofShape.numProofs ∧ i < proofShape.numAdviceColumns ∧
      ∃ rotation, (i, rotation) ∈ vk.adviceQueryLayout
  | .fixedCol i => ∃ rotation, (i, rotation) ∈ vk.fixedQueryLayout
  | .permProduct p s => p < proofShape.numProofs ∧ s < proofShape.numPermutationSets
  | .lookupProduct p l | .lookupPermInput p l | .lookupPermTable p l =>
      p < proofShape.numProofs ∧ l < proofShape.numLookups
  | .permCommon c => c < proofShape.numPermutationColumns
  | .vanishingH | .randomPoly => False

/-- Executable finite-list check for whether a query layout names a column. -/
def adaptiveActionLayoutContainsColumn
    (layout : List (Nat × Int)) (column : Nat) : Bool :=
  layout.any fun entry => entry.1 == column

theorem adaptiveActionLayoutContainsColumn_iff
    (layout : List (Nat × Int)) (column : Nat) :
    adaptiveActionLayoutContainsColumn layout column = true ↔
      ∃ rotation, (column, rotation) ∈ layout := by
  simp only [adaptiveActionLayoutContainsColumn, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨candidate, rotation⟩, hmem, heq⟩
    dsimp only at heq
    subst candidate
    exact ⟨rotation, hmem⟩
  · rintro ⟨rotation, hmem⟩
    exact ⟨(column, rotation), hmem, rfl⟩

instance adaptiveActionLayoutColumnMem_decidable
    (layout : List (Nat × Int)) (column : Nat) :
    Decidable (∃ rotation, (column, rotation) ∈ layout) :=
  decidable_of_iff (adaptiveActionLayoutContainsColumn layout column = true)
    (adaptiveActionLayoutContainsColumn_iff layout column)

instance adaptiveActionCommitmentActive_decidable
    (proofShape : Shape) {G : Type*}
    (vk : VerifyingKey proofShape Fp G) (id : CommitmentId) :
    Decidable (adaptiveActionCommitmentActive proofShape vk id) := by
  cases id <;> simp only [adaptiveActionCommitmentActive] <;> infer_instance

/-- The derived Action advice layout never names an out-of-range advice column. -/
theorem adaptiveActionAdviceLayout_column_lt
    (basis : AugmentedIndex (2 ^ actionCircuit.shape.k) → VestaG)
    (column : ℕ) (rotation : ℤ)
    (hmem : (column, rotation) ∈ (ActionTerminal.vkAt basis).adviceQueryLayout) :
    column < actionCircuit.adviceColumnCount := by
  apply ActionGateCoherence.adviceQueryColumnsAllocated (column, rotation)
  simpa only [ActionTerminal.vkAt,
    actionCircuit.toVerifierKey_adviceQueryLayout] using hmem

/-- Every active Action commitment identity has a concrete query in the deployed assembly. -/
theorem adaptiveActionActive_query
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (id : CommitmentId)
    (hactive : adaptiveActionCommitmentActive (actionCircuit.shape.withProofParams pp)
      (ActionTerminal.vkAt basis) id) :
    ∃ q ∈ assembleQueries (ActionTerminal.vkAt basis)
        (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs) ps ch,
      q.commId = id := by
  let vk := ActionTerminal.vkAt basis
  let ic := actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs
  have hadviceCount :=
    actionCircuit.toVerifierKey_adviceQueryCount
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
  have hinstanceCount :=
    actionCircuit.toVerifierKey_instanceQueryCount
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
  have hfixedCount :=
    actionCircuit.toVerifierKey_fixedQueryCount
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
  cases id with
  | instanceCol p column =>
      rcases hactive with ⟨hp, rotation, hlayout⟩
      obtain ⟨q, hq, hqid⟩ := instanceQuery_of_layout vk ic ps ch
        ⟨p, hp⟩ column rotation hinstanceCount hlayout
      exact ⟨q, hq, hqid⟩
  | adviceCol p column =>
      rcases hactive with ⟨hp, hcolumn, rotation, hlayout⟩
      obtain ⟨j, hj, hentry⟩ := List.mem_iff_getElem.mp hlayout
      have hje : j < actionCircuit.adviceQueryCount := by
        simpa only [← hadviceCount] using hj
      obtain ⟨q, hq, hqid, -⟩ := advice_query_mem_assembleQueries_eval
        vk ic ps ch ⟨p, hp⟩ hj hje
      refine ⟨q, hq, ?_⟩
      rw [List.getD_eq_getElem _ _ hj, hentry] at hqid
      exact hqid
  | fixedCol column =>
      rcases hactive with ⟨rotation, hlayout⟩
      obtain ⟨q, hq, hqid⟩ := fixedQuery_of_layout vk ic ps ch
        column rotation hfixedCount hlayout
      exact ⟨q, hq, hqid⟩
  | permProduct p s =>
      rcases hactive with ⟨hp, hs⟩
      obtain ⟨q, hq, hqid, -⟩ := perm_product_query_mem_assembleQueries
        vk ic ps ch ⟨p, hp⟩ ⟨s, hs⟩
      exact ⟨q, hq, hqid⟩
  | lookupProduct p l =>
      rcases hactive with ⟨hp, hl⟩
      obtain ⟨q, hq, hqid, -⟩ := lookup_product_query_mem_assembleQueries
        vk ic ps ch ⟨p, hp⟩ ⟨l, hl⟩
      exact ⟨q, hq, hqid⟩
  | lookupPermInput p l =>
      rcases hactive with ⟨hp, hl⟩
      obtain ⟨q, hq, hqid, -⟩ := lookup_permInput_query_mem_assembleQueries
        vk ic ps ch ⟨p, hp⟩ ⟨l, hl⟩
      exact ⟨q, hq, hqid⟩
  | lookupPermTable p l =>
      rcases hactive with ⟨hp, hl⟩
      obtain ⟨q, hq, hqid, -⟩ := lookup_permTable_query_mem_assembleQueries
        vk ic ps ch ⟨p, hp⟩ ⟨l, hl⟩
      exact ⟨q, hq, hqid⟩
  | permCommon c =>
      have hc : c < actionCircuit.permutationColumnCount := hactive
      obtain ⟨q, hq, hqid, -⟩ := permCommon_query_mem_assembleQueries
        vk ic ps ch ⟨c, hc⟩
      exact ⟨q, hq, hqid⟩
  | vanishingH => exact False.elim hactive
  | randomPoly => exact False.elim hactive

/-- Every non-terminal identity emitted by the deployed query assembler is one of the active
Action commitment slots. -/
theorem adaptiveActionQuery_active_or_terminal
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (q : VerifierQuery (actionCircuit.shape.withProofParams pp).k Fp VestaG)
    (hq : q ∈ assembleQueries (ActionTerminal.vkAt basis)
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs) ps ch) :
    adaptiveActionCommitmentActive (actionCircuit.shape.withProofParams pp)
      (ActionTerminal.vkAt basis) q.commId ∨
      q.commId = .vanishingH ∨ q.commId = .randomPoly := by
  simp only [assembleQueries, List.mem_append] at hq
  rcases hq with (((hperProof | hfixed) | hcommon) | hvanishing)
  · obtain ⟨proofQueries, hproofQueries, hq⟩ := List.mem_flatten.mp hperProof
    obtain ⟨proofIndex, hproofQueries⟩ := List.mem_ofFn.mp hproofQueries
    rw [← hproofQueries] at hq
    simp only [List.mem_append] at hq
    rcases hq with ((hinstance | hadvice) | hpermutation) | hlookup
    · rw [columnQueries, List.mem_map] at hinstance
      obtain ⟨entry, hentry, rfl⟩ := hinstance
      left
      exact ⟨proofIndex.isLt, entry.1.2, (List.of_mem_zip hentry).1⟩
    · rw [columnQueries, List.mem_map] at hadvice
      obtain ⟨entry, hentry, rfl⟩ := hadvice
      have hlayout : entry.1 ∈ (ActionTerminal.vkAt basis).adviceQueryLayout :=
        (List.of_mem_zip hentry).1
      left
      exact ⟨proofIndex.isLt,
        adaptiveActionAdviceLayout_column_lt basis entry.1.1 entry.1.2 hlayout,
        entry.1.2, hlayout⟩
    · simp only [permutationQueries, List.mem_append] at hpermutation
      rcases hpermutation with hregular | hlast
      · simp only [List.mem_flatMap, List.mem_cons, List.mem_nil_iff, or_false] at hregular
        obtain ⟨entry, hentry, hq | hq⟩ := hregular <;> subst q <;> left
        all_goals
          exact ⟨proofIndex.isLt, by
            have := (List.of_mem_zip hentry).2
            simpa using this⟩
      · rw [List.mem_filterMap] at hlast
        obtain ⟨entry, hentry, hentryMap⟩ := hlast
        cases hlastEval : entry.1.2.lastEval with
        | none => simp [hlastEval] at hentryMap
        | some lastEval =>
            simp [hlastEval] at hentryMap
            subst q
            left
            refine ⟨proofIndex.isLt, ?_⟩
            have hindexed : entry ∈
                (List.ofFn (fun s =>
                  (ps.permutationProduct proofIndex s,
                    ps.permutationSetEvals proofIndex s))).zip
                  (List.range (List.ofFn (fun s =>
                    (ps.permutationProduct proofIndex s,
                      ps.permutationSetEvals proofIndex s))).length) := by
              exact List.mem_reverse.mp (List.mem_of_mem_drop hentry)
            have := (List.of_mem_zip hindexed).2
            simpa using this
    · simp only [lookupQueries, List.mem_flatMap, List.mem_cons,
        List.mem_nil_iff, or_false] at hlookup
      obtain ⟨entry, hentry, hq | hq | hq | hq | hq⟩ := hlookup <;> subst q <;> left
      all_goals
        exact ⟨proofIndex.isLt, by
          have := (List.of_mem_zip hentry).2
          simpa using this⟩
  · rw [columnQueries, List.mem_map] at hfixed
    obtain ⟨entry, hentry, rfl⟩ := hfixed
    left
    exact ⟨entry.1.2, (List.of_mem_zip hentry).1⟩
  · rw [permutationCommonQueries, List.mem_map] at hcommon
    obtain ⟨entry, hentry, rfl⟩ := hcommon
    left
    have := (List.of_mem_zip hentry).2
    simpa using this
  · simp [vanishingQueries] at hvanishing
    rcases hvanishing with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

/-- Whether a commitment class has already been absorbed at an Action semantic squeeze. -/
def adaptiveActionCommitmentAvailable (n : Fin 5) : CommitmentId → Prop
  | .instanceCol _ _ | .adviceCol _ _ | .fixedCol _ | .permCommon _ => True
  | .lookupPermInput _ _ | .lookupPermTable _ _ => 1 ≤ (n : Nat)
  | .permProduct _ _ | .lookupProduct _ _ => 3 ≤ (n : Nat)
  | .vanishingH | .randomPoly => False

/-- An active identity available at stage `n` has an explicit point representation in that
stage's source. -/
theorem adaptiveActionActive_point_mem_stage
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10 +
        3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (n : Fin 5) (id : CommitmentId)
    (hactive : adaptiveActionCommitmentActive (actionCircuit.shape.withProofParams pp)
      (ActionTerminal.vkAt basis) id)
    (havailable : adaptiveActionCommitmentAvailable n id) :
    let data := (family.adversary basis).run O
    let ch := ActionTerminal.adaptiveActionRunRecord family basis O
    ∃ P,
      assembledCommitment (ActionTerminal.vkAt basis)
          (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
          data.algebraicProof.erase ch id = .point P ∧
        ∃ ap ∈ data.algebraicProof.actionRepresentationsBefore n ++
            family.fixedRepresentations basis,
          ap.point = P := by
  simp only
  let data := (family.adversary basis).run O
  let urs := ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis
  let ic := actionCircuit.instanceCommitment urs inputs
  have hvkAt : family.vk basis = ActionTerminal.vkAt basis := by
    simpa only [ActionTerminal.vkAt, CircuitShape.withProofParams_k] using hvk basis
  cases id with
  | instanceCol p column =>
      rcases hactive with ⟨hp, rotation, hlayout⟩
      have hlayout' : ∃ rotation,
          (column, rotation) ∈ (family.vk basis).instanceQueryLayout := by
        rw [hvk basis]
        exact ⟨rotation, hlayout⟩
      obtain ⟨ap, hap, hpoint⟩ := family.instanceRepresented basis ⟨p, hp⟩ column
        hlayout'
      refine ⟨ic ⟨p, hp⟩ column, ?_, ap, ?_, ?_⟩
      · rw [assembledCommitment, dif_pos hp]
        apply congrArg CommitmentRef.point
        apply congrArg (fun proof : Fin pp.numProofs => ic proof column)
        exact Fin.ext rfl
      · exact List.mem_append.mpr (Or.inr hap)
      · change ap.point = actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs ⟨p, hp⟩ column
        rw [← hI basis]
        exact hpoint
  | adviceCol p column =>
      rcases hactive with ⟨hp, hcolumn, rotation, hlayout⟩
      have hcolumn' : column < actionCircuit.adviceColumnCount := by
        simpa only [actionCircuit.shape_numAdviceColumns] using hcolumn
      let ap := data.algebraicProof.adviceCommitments ⟨p, hp⟩ ⟨column, hcolumn⟩
      refine ⟨ap.point, ?_, ap, ?_, rfl⟩
      · rw [assembledCommitment, dif_pos hp]
        rw [finFnG, dif_pos hcolumn]
        simp only [ap, data, AlgebraicProofString.erase]
      · apply List.mem_append.mpr
        apply Or.inl
        simpa only [ap] using
          data.algebraicProof.adviceCommitment_mem_actionRepresentationsBefore
            n ⟨p, hp⟩ ⟨column, hcolumn⟩
  | fixedCol column =>
      rcases hactive with ⟨rotation, hlayout⟩
      have hlayout' : ∃ rotation,
          (column, rotation) ∈ (family.vk basis).fixedQueryLayout := by
        rw [hvk basis]
        exact ⟨rotation, hlayout⟩
      obtain ⟨ap, hap, hpoint⟩ := family.fixedRepresented basis column
        hlayout'
      refine ⟨(ActionTerminal.vkAt basis).fixedCommitment column, rfl,
        ap, List.mem_append.mpr (Or.inr hap), ?_⟩
      rw [← hvkAt]
      exact hpoint
  | permProduct p s =>
      rcases hactive with ⟨hp, hs⟩
      let ap := data.algebraicProof.permutationProduct ⟨p, hp⟩ ⟨s, hs⟩
      refine ⟨ap.point, ?_, ap, ?_, rfl⟩
      · rw [assembledCommitment, dif_pos hp]
        rw [finFnG, dif_pos hs]
        simp only [ap, data, AlgebraicProofString.erase]
      · apply List.mem_append.mpr
        apply Or.inl
        have hn : 3 ≤ (n : Nat) := by
          simpa only [adaptiveActionCommitmentAvailable] using havailable
        simpa only [ap] using
          data.algebraicProof.permutationProduct_mem_actionRepresentationsBefore
            n ⟨p, hp⟩ ⟨s, hs⟩ hn
  | lookupProduct p l =>
      rcases hactive with ⟨hp, hl⟩
      let ap := data.algebraicProof.lookupProduct ⟨p, hp⟩ ⟨l, hl⟩
      refine ⟨ap.point, ?_, ap, ?_, rfl⟩
      · rw [assembledCommitment, dif_pos hp]
        rw [finFnG, dif_pos hl]
        simp only [ap, data, AlgebraicProofString.erase]
      · apply List.mem_append.mpr
        apply Or.inl
        have hn : 3 ≤ (n : Nat) := by
          simpa only [adaptiveActionCommitmentAvailable] using havailable
        simpa only [ap] using
          data.algebraicProof.lookupProduct_mem_actionRepresentationsBefore
            n ⟨p, hp⟩ ⟨l, hl⟩ hn
  | lookupPermInput p l =>
      rcases hactive with ⟨hp, hl⟩
      let ap := data.algebraicProof.lookupPermutedInput ⟨p, hp⟩ ⟨l, hl⟩
      refine ⟨ap.point, ?_, ap, ?_, rfl⟩
      · rw [assembledCommitment, dif_pos hp]
        rw [finFnG, dif_pos hl]
        simp only [ap, data, AlgebraicProofString.erase]
      · apply List.mem_append.mpr
        apply Or.inl
        have hn : 1 ≤ (n : Nat) := by
          simpa only [adaptiveActionCommitmentAvailable] using havailable
        simpa only [ap] using
          data.algebraicProof.lookupPermutedInput_mem_actionRepresentationsBefore
            n ⟨p, hp⟩ ⟨l, hl⟩ hn
  | lookupPermTable p l =>
      rcases hactive with ⟨hp, hl⟩
      let ap := data.algebraicProof.lookupPermutedTable ⟨p, hp⟩ ⟨l, hl⟩
      refine ⟨ap.point, ?_, ap, ?_, rfl⟩
      · rw [assembledCommitment, dif_pos hp]
        rw [finFnG, dif_pos hl]
        simp only [ap, data, AlgebraicProofString.erase]
      · apply List.mem_append.mpr
        apply Or.inl
        have hn : 1 ≤ (n : Nat) := by
          simpa only [adaptiveActionCommitmentAvailable] using havailable
        simpa only [ap] using
          data.algebraicProof.lookupPermutedTable_mem_actionRepresentationsBefore
            n ⟨p, hp⟩ ⟨l, hl⟩ hn
  | permCommon c =>
      have hc : c < actionCircuit.permutationColumnCount := hactive
      obtain ⟨ap, hap, hpoint⟩ := family.permutationCommonRepresented basis ⟨c, hc⟩
      refine ⟨(ActionTerminal.vkAt basis).permutationCommonCommitment ⟨c, hc⟩,
        ?_, ap, List.mem_append.mpr (Or.inr hap), ?_⟩
      · simp [assembledCommitment, finFnG, hc]
        congr 2
      · rw [← hvkAt]
        exact hpoint
  | vanishingH => exact False.elim hactive
  | randomPoly => exact False.elim hactive

/-- Executable commitment-ID resolver induced by stage-local point coordinates and explicit
verifier data.  Passing the key and instance commitment as data keeps the terminal finder free of
the noncomputable key-generation wrapper. -/
def adaptiveActionCommitmentPolynomialOf
    {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (ic : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges shape.k Fp) :
    CommitmentId → CPoly :=
  let pointPoly := adaptiveActionPointPolynomial source
  fun id =>
    if adaptiveActionCommitmentActive shape vk id then
        match assembledCommitment vk ic ps ch id with
        | .point P => pointPoly P
        | .msm _ => 0
    else 0

/-- Action specialization of the executable commitment resolver. -/
def adaptiveActionCommitmentPolynomial
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp) :
    CommitmentId → CPoly :=
  adaptiveActionCommitmentPolynomialOf (ActionTerminal.vkAt basis)
    (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    ps source ch

/-- Supplying the deployed Action key and instance commitment to the executable commitment
resolver recovers the Action-specialized resolver. -/
theorem adaptiveActionCommitmentPolynomialOf_action
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (vk : VerifyingKey actionCircuit.shape Fp VestaG)
    (ic : Fin pp.numProofs → Nat → VestaG)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (hvk : vk = ActionTerminal.vkAt basis)
    (hI : ic = actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs) :
    adaptiveActionCommitmentPolynomialOf vk ic ps source ch =
      adaptiveActionCommitmentPolynomial pp basis inputs ps source ch := by
  subst vk
  subst ic
  simp only [adaptiveActionCommitmentPolynomialOf, adaptiveActionCommitmentPolynomial]
  congr

/-- Every nonterminal commitment resolver is independent of the challenge record; only the
separately handled reassembled quotient slot can depend on `x`. -/
theorem adaptiveActionCommitmentPolynomial_challenge_congr
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch₁ ch₂ : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (id : CommitmentId) (hvanishing : id ≠ .vanishingH) :
    adaptiveActionCommitmentPolynomial pp basis inputs ps source ch₁ id =
      adaptiveActionCommitmentPolynomial pp basis inputs ps source ch₂ id := by
  cases id <;>
    simp_all only [adaptiveActionCommitmentPolynomial, adaptiveActionCommitmentPolynomialOf,
      adaptiveActionCommitmentActive,
      adaptiveActionPointPolynomial, assembledCommitment, ne_eq, not_true_eq_false]

/-- The constraint model determined before `y`/`x` by the commitments already in the transcript. -/
def adaptiveActionCommittedModelOf
    {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (ic : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges shape.k Fp)
    (hblinding : vk.blindingFactors < vk.n) :
    ConstraintPolyModel shape.numProofs :=
  vk.constraintModel ch
    (adaptiveActionCommitmentPolynomialOf vk ic ps source ch) hblinding

def adaptiveActionCommittedModel
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp) :
    ConstraintPolyModel (actionCircuit.shape.withProofParams pp).numProofs :=
  adaptiveActionCommittedModelOf (ActionTerminal.vkAt basis)
    (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    ps source ch (actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))

/-- Executable fixed pre-`x` constraint difference.  Every coefficient is computed from the
explicit key, instance commitment, proof, and online AGM coordinate source supplied as data. -/
def adaptiveActionPreXDifferenceOf
    {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (ic : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges shape.k Fp)
    (hblinding : vk.blindingFactors < vk.n) : CPoly :=
  let model := adaptiveActionCommittedModelOf vk ic ps source ch hblinding
  combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
      model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta ch.y
      model.chunkLen model.l0 model.lLast model.lBlind
    - committedPreXQuotient vk (fun i => onlinePointPolynomial source (ps.hPieces i))
        * (X ^ vk.n - 1)

/-- Action specialization of the executable fixed pre-`x` difference. -/
def adaptiveActionPreXDifference
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp) : CPoly :=
  adaptiveActionPreXDifferenceOf (ActionTerminal.vkAt basis)
    (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    ps source ch (actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))

/-- Supplying the deployed Action key and instance commitment to the executable resolver recovers
the Action-specialized pre-`x` difference. -/
theorem adaptiveActionPreXDifferenceOf_action
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (vk : VerifyingKey (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (ic : Fin pp.numProofs → Nat → VestaG)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (hblinding : vk.blindingFactors < vk.n)
    (hvk : vk = ActionTerminal.vkAt basis)
    (hI : ic = actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs) :
    adaptiveActionPreXDifferenceOf vk ic ps source ch hblinding =
      adaptiveActionPreXDifference pp basis inputs ps source ch := by
  subst vk
  subst ic
  rfl

theorem adaptiveActionPreXDifferenceOf_eq
    {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (ic : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges shape.k Fp)
    (hblinding : vk.blindingFactors < vk.n) :
    let model := adaptiveActionCommittedModelOf vk ic ps source ch hblinding
    adaptiveActionPreXDifferenceOf vk ic ps source ch hblinding =
      combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
          model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
          ch.y model.chunkLen model.l0 model.lLast model.lBlind -
        committedPreXQuotient vk (fun i => onlinePointPolynomial source (ps.hPieces i)) *
          (X ^ vk.n - 1) := rfl

/-- The stage-`x` difference is exactly the constraint difference of the stage-local canonical
model with the genuinely pre-`x` quotient polynomial. -/
theorem adaptiveActionPreXDifference_eq
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp) :
    let vk := ActionTerminal.vkAt basis
    let model := adaptiveActionCommittedModel pp basis inputs ps source ch
    adaptiveActionPreXDifference pp basis inputs ps source ch =
      combineConstraints model.fixedCols model.adviceCols model.instanceCols model.gates
          model.sets model.chunks model.lookups model.beta model.gamma model.delta model.theta
          ch.y model.chunkLen model.l0 model.lLast model.lBlind -
        committedPreXQuotient vk (fun i => onlinePointPolynomial source (ps.hPieces i)) *
          (X ^ vk.n - 1) := by
  exact adaptiveActionPreXDifferenceOf_eq (shape := actionCircuit.shape.withProofParams pp)
    (ActionTerminal.vkAt basis)
    (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    ps source ch (actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))

/-- The stage-local model reads only `theta`, `beta`, and `gamma`; later challenge fields do not
affect its constraint polynomials. -/
theorem adaptiveActionCommittedModel_challenge_congr
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch₁ ch₂ : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (htheta : ch₁.theta = ch₂.theta) (hbeta : ch₁.beta = ch₂.beta)
    (hgamma : ch₁.gamma = ch₂.gamma) :
    adaptiveActionCommittedModel pp basis inputs ps source ch₁ =
      adaptiveActionCommittedModel pp basis inputs ps source ch₂ := by
  unfold adaptiveActionCommittedModel adaptiveActionCommittedModelOf
  have hpoly : adaptiveActionCommitmentPolynomialOf (ActionTerminal.vkAt basis)
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      ps source ch₁ =
    adaptiveActionCommitmentPolynomialOf (ActionTerminal.vkAt basis)
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      ps source ch₂ := by
    funext id
    by_cases hvanishing : id = .vanishingH
    · subst id
      simp [adaptiveActionCommitmentPolynomialOf,
        adaptiveActionCommitmentActive]
    · exact adaptiveActionCommitmentPolynomial_challenge_congr
        pp basis inputs ps source ch₁ ch₂ id hvanishing
  unfold VerifyingKey.constraintModel constraintModelOfResolver
  dsimp only
  rw [hpoly, htheta, hbeta, hgamma]

/-- The canonical constraint model never reads the quotient or random-polynomial terminal slots,
so pointwise agreement on every other identity determines the whole model. -/
theorem VerifyingKey.constraintModel_congr_nonterminal
    {shape : CircuitShape} {G : Type*}
    (numProofs : ℕ)
    (vk : VerifyingKey shape Fp G) (ch : Challenges shape.k Fp)
    (poly₁ poly₂ : CommitmentId → CPoly)
    (hblinding : vk.blindingFactors < vk.n)
    (hpoly : ∀ id, id ≠ .vanishingH → id ≠ .randomPoly →
      poly₁ id = poly₂ id) :
    vk.constraintModel (numProofs := numProofs) ch poly₁ hblinding =
      vk.constraintModel (numProofs := numProofs) ch poly₂ hblinding := by
  have hcolumn : ∀ id, id.isColumnInput → poly₁ id = poly₂ id := by
    intro id hid
    apply hpoly id <;> cases id <;> simp_all [CommitmentId.isColumnInput]
  have hpermutation : ∀ id, id.isPermutationInput → poly₁ id = poly₂ id := by
    intro id hid
    apply hpoly id <;> cases id <;> simp_all [CommitmentId.isPermutationInput]
  have hfixed : fixedQueryFeedOfResolver vk poly₁ =
      fixedQueryFeedOfResolver vk poly₂ :=
    fixedQueryFeedOfResolver_congr vk hcolumn
  have hadvice : adviceQueryFeedOfResolver vk poly₁ =
      adviceQueryFeedOfResolver vk poly₂ := by
    funext p
    exact adviceQueryFeedOfResolver_congr vk p hcolumn
  have hinstance : instanceQueryFeedOfResolver vk poly₁ =
      instanceQueryFeedOfResolver vk poly₂ := by
    funext p
    exact instanceQueryFeedOfResolver_congr vk p hcolumn
  have hsets : permutationSetsOfResolver (numProofs := numProofs) vk poly₁ =
      permutationSetsOfResolver (numProofs := numProofs) vk poly₂ := by
    funext p
    unfold permutationSetsOfResolver
    apply congrArg List.ofFn
    funext s
    unfold permutationSetOfResolver
    rw [hpoly (.permProduct p s) (by simp) (by simp)]
  have hchunks : permutationChunksOfResolver (numProofs := numProofs) vk poly₁ =
      permutationChunksOfResolver (numProofs := numProofs) vk poly₂ := by
    funext p
    unfold permutationChunksOfResolver
    rw [hsets]
    apply List.map_congr_left
    intro sc hsc
    apply Prod.ext
    · rfl
    · apply List.map_congr_left
      intro cr hcr
      exact Prod.ext
        (permutationColumnPolynomialOfResolver_congr vk p
          (fun id hid => hpermutation id hid.toPermutation) cr.1)
        (hpoly (.permCommon cr.2) (by simp) (by simp))
  have hlookups : lookupEntriesOfResolver vk poly₁ =
      lookupEntriesOfResolver vk poly₂ := by
    funext p
    unfold lookupEntriesOfResolver
    apply congrArg List.ofFn
    funext l
    rw [hpoly (.lookupProduct p l) (by simp) (by simp),
      hpoly (.lookupPermInput p l) (by simp) (by simp),
      hpoly (.lookupPermTable p l) (by simp) (by simp)]
  unfold VerifyingKey.constraintModel constraintModelOfResolver
  dsimp only
  rw [hfixed, hadvice, hinstance, hsets, hchunks, hlookups]

/-- A plain commitment routed by an accepting adaptive decode carries the polynomial fixed by
the run's online pre-`x` AGM source. -/
theorem adaptiveAcceptedPolynomial_eq_online_of_query
    (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (pnu : WrappedAlgebraicOutput family basis)
    (rounds : Fin shape.k → Fp)
    (fixed : List (AlgebraicPoint (F := Fp) basis))
    (witness : DeployedBatchWitness family basis pnu)
    (hsrc : witness.fixedRepresentations = fixed)
    (decode : DeployedAlgebraicDecode shape (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (wrappedPreIpaRecord pnu)
      (pnu.1.aMulti (wrappedPreIpaReads pnu))
      (pnu.1.multiU (wrappedPreIpaReads pnu))
      (pnu.1.multiBlind (wrappedPreIpaReads pnu)))
    (hbatches : decode.batches = witness.batches)
    (hchar : deployedX4PairCount (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) rounds) < Zcash.Arithmetic.scalarFieldOrder)
    (haccepts : DeployedAccepts shape (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (chRecord (wrappedPreIpaReads pnu) rounds))
    (id : CommitmentId) (q : VerifierQuery shape.k Fp VestaG)
    (hq : q ∈ assembleQueries (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) rounds))
    (hqid : q.commId = id) (P : VestaG)
    (hpoint : assembledCommitment (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) rounds) id = .point P) :
    CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => (decode.reRound rounds).toMemberDecode hchar i hi)
        haccepts id =
      onlinePointPolynomial (pnu.1.algebraicProof.preX1AssemblySource fixed) P := by
  let routing := canonicalRoutingConditions_of_accepts
    (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
    (family.instanceCommitment basis)
    pnu.1.proof.1 (chRecord (wrappedPreIpaReads pnu) rounds) haccepts
  have routed := assembledQueryMemberRoute_faithful
    (instanceCommitment := family.instanceCommitment basis)
    (family.vk basis) pnu.1.proof.1
    (chRecord (wrappedPreIpaReads pnu) rounds) routing.1 routing.2 q hq
  have hmemberPoint : ((deployedSetQueries (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) rounds) routed.slot.setIndex).getD
        (routed.slot.memberIndex : Nat) (.point 0, [])).1 = .point P := by
    rw [deployed_member_commitment_eq_assembled
        (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
        (chRecord (wrappedPreIpaReads pnu) rounds) routed.slot.setIndex
        routed.slot.memberIndex CommitmentId.vanishingH
        (assembledQueryMemberRoute_id
          (instanceCommitment := family.instanceCommitment basis)
          (family.vk basis) pnu.1.proof.1
          (chRecord (wrappedPreIpaReads pnu) rounds)
          routing.1 routing.2 id routed.slot
          (by simpa only [CanonicalMemberConstraintRelation.acceptedRoute, routing, ← hqid]
            using routed.route_eq)) (.point 0, [])]
    exact hpoint
  have hmember : (decode.reRound rounds).memberPoly
        routed.slot.setIndex routed.slot.setIndex_lt
        routed.slot.memberIndex =
      onlinePointPolynomial (pnu.1.algebraicProof.preX1AssemblySource fixed) P := by
    change decode.memberPoly routed.slot.setIndex routed.slot.setIndex_lt
      routed.slot.memberIndex = _
    unfold DeployedAlgebraicDecode.memberPoly onlinePointPolynomial
    rw [hbatches, ← hsrc]
    rw [congrFun (witness.memberCoeffs routed.slot.setIndex routed.slot.setIndex_lt)
      routed.slot.memberIndex]
    exact congrArg coeffsToPoly
      (deployedMemberRepresentationsOfCovered_coeffs_point
        pnu.1
        witness.fixedRepresentations witness.membersCovered
        (wrappedPreIpaReads pnu)
        routed.slot.setIndex routed.slot.setIndex_lt routed.slot.memberIndex P hmemberPoint)
  have hroute : CanonicalMemberConstraintRelation.acceptedRoute haccepts id =
      some routed.slot := by
    simpa only [CanonicalMemberConstraintRelation.acceptedRoute, routing, ← hqid] using
      routed.route_eq
  unfold CanonicalMemberConstraintRelation.acceptedPolynomial decodedPolynomialResolver
  rw [hroute]
  exact hmember

/-- Compare one stage-local representation with the deterministic first representation of the
same point in the complete pre-`x` source. -/
def representationAgainstSourceMismatch?
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ap : AlgebraicPoint (F := Fp) basis) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  match hfound : source.find? (fun candidate => candidate.point = ap.point) with
  | none => none
  | some first => representationMismatchRelation? first ap (by
      simpa using List.find?_some hfound)

/-- Return the first mismatch between a stage source and the complete pre-`x` source. -/
def representationSourceMismatchFinder
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (source target : List (AlgebraicPoint (F := Fp) basis)) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?
    (target.map (representationAgainstSourceMismatch? source))

/-- With no source-collision relation, deterministic point lookup gives the same polynomial in
the stage source and the complete pre-`x` source. -/
theorem onlinePointPolynomial_eq_of_sourceMismatch_none
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (source target : List (AlgebraicPoint (F := Fp) basis))
    (hsub : ∀ ap ∈ target, ap ∈ source)
    (hnone : representationSourceMismatchFinder source target = none)
    (P : VestaG) (hP : ∃ ap ∈ target, ap.point = P) :
    onlinePointPolynomial source P = onlinePointPolynomial target P := by
  obtain ⟨ap, hap, rfl⟩ := hP
  have htargetSome : (target.find? (fun candidate => candidate.point = ap.point)).isSome := by
    rw [List.find?_isSome]
    exact ⟨ap, hap, by simp⟩
  obtain ⟨stage, hstage⟩ := Option.isSome_iff_exists.mp htargetSome
  have hstageMem : stage ∈ target := List.mem_of_find?_eq_some hstage
  have hstagePoint : stage.point = ap.point := by
    simpa using List.find?_some hstage
  have hsourceSome : (source.find? (fun candidate => candidate.point = ap.point)).isSome := by
    rw [List.find?_isSome]
    exact ⟨stage, hsub stage hstageMem, by simp [hstagePoint]⟩
  obtain ⟨first, hfirst⟩ := Option.isSome_iff_exists.mp hsourceSome
  have hall := (ComputedAdaptiveOnlineAGMFSFamily.firstAdaptiveRelation?_eq_none_iff _).1 hnone
  have hmismatch : representationAgainstSourceMismatch? source stage = none := by
    apply hall
    exact List.mem_map.mpr ⟨stage, hstageMem, rfl⟩
  have hfirstStage : source.find? (fun candidate => candidate.point = stage.point) =
      some first := by
    simpa only [hstagePoint] using hfirst
  have hcoeff : first.coeffs = stage.coeffs := by
    unfold representationAgainstSourceMismatch? at hmismatch
    split at hmismatch
    · rename_i hnone
      rw [hfirstStage] at hnone
      contradiction
    · rename_i found hfound
      have hfoundEq : found = first := Option.some.inj (hfound.symm.trans hfirstStage)
      subst found
      exact (representationMismatchRelation?_eq_none_iff first stage (by
        simpa using List.find?_some hfirstStage)).1 hmismatch
  unfold onlinePointPolynomial onlinePointCoordinates
  rw [hfirst, hstage]
  apply congrArg coeffsToPoly
  funext i
  exact congrFun hcoeff (AugmentedIndex.gen i)

/-- One of the five exact Action semantic bad sets, reconstructed only from the stage prefix,
earlier oracle answers, and stage-local AGM coordinates. -/
def adaptiveActionSurfaceAt
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (n : Fin 5)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (earlier : Fin (n : Nat) → Fp) : Set Fp :=
  let nu : Fin 11 → Fp := fun i =>
    if h : (i : Nat) < (n : Nat) then earlier ⟨i, h⟩ else 0
  let ch := chRecord nu (fun _ => 0)
  let urs := ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis
  let vk := ActionTerminal.vkAt basis
  let poly := adaptiveActionCommitmentPolynomial pp basis inputs ps source ch
  if _h0 : (n : Nat) = 0 then
    ↑(TopLevelLookup.thetaBadSet
      actionCircuit pp urs poly)
  else if _h1 : (n : Nat) = 1 then
    ↑(allResolverPermutationBetaBadSet pp.numProofs vk poly actionActiveRows) ∪
      ↑(allResolverLookupBetaBadSet pp.numProofs vk
        (ActionTerminal.semanticChRecord ch.theta 0
          (k := (actionCircuit.shape.withProofParams pp).k)) poly
        (actionCircuit.n - actionCircuit.blindingFactors - 2))
  else if _h2 : (n : Nat) = 2 then
    ↑(allResolverPermutationGammaBadSet pp.numProofs vk
        (ActionTerminal.semanticChRecord ch.theta ch.beta
          (k := (actionCircuit.shape.withProofParams pp).k)) poly actionActiveRows) ∪
      ↑(allResolverLookupGammaBadSet pp.numProofs vk
        (ActionTerminal.semanticChRecord ch.theta ch.beta
          (k := (actionCircuit.shape.withProofParams pp).k)) poly
          (actionCircuit.n - actionCircuit.blindingFactors - 2))
  else if _h3 : (n : Nat) = 3 then
    let model := adaptiveActionCommittedModel pp basis inputs ps source ch
    ⋃ j, ↑(szBadSet (foldSplitWitness model.constraints actionCircuit.n j))
  else
    ↑(szBadSet (adaptiveActionPreXDifference pp basis inputs ps source ch))

/-- Equality of one exact semantic prefix pins precisely the ordinary commitment list used by
that stage. -/
theorem actionCommitmentPointsBefore_eq_of_prefix
    (init : List (TranscriptElt Fp VestaG)) (n : Fin 5)
    (ps ps' : ProofString shape Fp VestaG)
    (hprefix : preIpaSqueezePoints init ps (Fin.castLE (by omega) n) =
      preIpaSqueezePoints init ps' (Fin.castLE (by omega) n)) :
    ps.actionCommitmentPointsBefore n = ps'.actionCommitmentPointsBefore n := by
  fin_cases n
  · have h := preThetaSqueezePoint_inj init hprefix
    simp [ProofString.actionCommitmentPointsBefore, h]
  · obtain ⟨ha, hi, ht⟩ := preBetaSqueezePoint_inj init hprefix
    simp [ProofString.actionCommitmentPointsBefore, ha, hi, ht]
  · obtain ⟨ha, hi, ht⟩ := preGammaSqueezePoint_inj init hprefix
    simp [ProofString.actionCommitmentPointsBefore, ha, hi, ht]
  · obtain ⟨ha, hi, ht, hp, hl, hr⟩ := preYSqueezePoint_inj init hprefix
    simp [ProofString.actionCommitmentPointsBefore, ha, hi, ht, hp, hl, hr]
  · obtain ⟨ha, hi, ht, hp, hl, hr, hh⟩ := preXSqueezePoint_inj init hprefix
    simp [ProofString.actionCommitmentPointsBefore, ha, hi, ht, hp, hl, hr, hh]

theorem adaptiveActionCommitmentPolynomial_column_eq
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps ps' : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source source' : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (hsource : source = source') (hadvice : ps.adviceCommitments = ps'.adviceCommitments) :
    ∀ id, id.isColumnInput →
      adaptiveActionCommitmentPolynomial pp basis inputs ps source ch id =
        adaptiveActionCommitmentPolynomial pp basis inputs ps' source' ch id := by
  intro id hid
  subst source'
  cases id <;>
    simp_all [CommitmentId.isColumnInput, adaptiveActionCommitmentPolynomial,
      adaptiveActionCommitmentPolynomialOf,
      adaptiveActionPointPolynomial, assembledCommitment]

theorem adaptiveActionCommitmentPolynomial_lookup_eq
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps ps' : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source source' : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (hsource : source = source') (hadvice : ps.adviceCommitments = ps'.adviceCommitments)
    (hinput : ps.lookupPermutedInput = ps'.lookupPermutedInput)
    (htable : ps.lookupPermutedTable = ps'.lookupPermutedTable) :
    ∀ id, id.isLookupInput →
      adaptiveActionCommitmentPolynomial pp basis inputs ps source ch id =
        adaptiveActionCommitmentPolynomial pp basis inputs ps' source' ch id := by
  intro id hid
  subst source'
  cases id <;>
    simp_all [CommitmentId.isLookupInput, adaptiveActionCommitmentPolynomial,
      adaptiveActionCommitmentPolynomialOf,
      adaptiveActionPointPolynomial, assembledCommitment]

theorem adaptiveActionCommitmentPolynomial_permutation_eq
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps ps' : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source source' : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (hsource : source = source') (hadvice : ps.adviceCommitments = ps'.adviceCommitments) :
    ∀ id, id.isPermutationInput →
      adaptiveActionCommitmentPolynomial pp basis inputs ps source ch id =
        adaptiveActionCommitmentPolynomial pp basis inputs ps' source' ch id := by
  intro id hid
  subst source'
  cases id <;>
    simp_all [CommitmentId.isPermutationInput, adaptiveActionCommitmentPolynomial,
      adaptiveActionCommitmentPolynomialOf,
      adaptiveActionPointPolynomial, assembledCommitment]

theorem adaptiveActionCommitmentPolynomial_eq_of_preY_fields
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps ps' : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source source' : List (AlgebraicPoint (F := Fp) basis))
    (ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (hsource : source = source')
    (hadvice : ps.adviceCommitments = ps'.adviceCommitments)
    (hinput : ps.lookupPermutedInput = ps'.lookupPermutedInput)
    (htable : ps.lookupPermutedTable = ps'.lookupPermutedTable)
    (hperm : ps.permutationProduct = ps'.permutationProduct)
    (hlookup : ps.lookupProduct = ps'.lookupProduct)
    (hrandom : ps.vanishingRandom = ps'.vanishingRandom) :
    adaptiveActionCommitmentPolynomial pp basis inputs ps source ch =
      adaptiveActionCommitmentPolynomial pp basis inputs ps' source' ch := by
  funext id
  subst source'
  cases id <;>
    simp [adaptiveActionCommitmentPolynomial, adaptiveActionCommitmentPolynomialOf,
      adaptiveActionPointPolynomial,
      assembledCommitment, hadvice, hinput, htable, hperm, hlookup, hrandom]

/-- Equal exact prefixes and equal stage-local coordinates define the same semantic bad set. -/
theorem adaptiveActionSurfaceAt_congr
    (pp : ProofParams)
    (init : List (TranscriptElt Fp VestaG))
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (n : Fin 5)
    (ps ps' : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (_hwf : PsWellFormed ps) (_hwf' : PsWellFormed ps')
    (source source' : List (AlgebraicPoint (F := Fp) basis))
    (earlier : Fin (n : Nat) → Fp)
    (hprefix : preIpaSqueezePoints init ps
        (Fin.castLE (by omega) n) =
      preIpaSqueezePoints init ps' (Fin.castLE (by omega) n))
    (hsource : source = source') :
    adaptiveActionSurfaceAt pp basis inputs n ps source earlier =
      adaptiveActionSurfaceAt pp basis inputs n ps' source' earlier := by
  subst source'
  let nu : Fin 11 → Fp := fun i =>
    if h : (i : Nat) < (n : Nat) then earlier ⟨i, h⟩ else 0
  let ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp :=
    chRecord nu (fun _ => 0)
  fin_cases n
  · have ha := preThetaSqueezePoint_inj init hprefix
    have hp := adaptiveActionCommitmentPolynomial_column_eq
      pp basis inputs ps ps' source source ch rfl ha
    have hs := congrArg (fun s : Finset Fp => (↑s : Set Fp))
      (TopLevelLookup.thetaBadSet_congr
        actionCircuit pp
          (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) hp)
    simpa [adaptiveActionSurfaceAt, nu, ch] using hs
  · obtain ⟨ha, hi, ht⟩ := preBetaSqueezePoint_inj init hprefix
    have hpPerm := adaptiveActionCommitmentPolynomial_permutation_eq
      pp basis inputs ps ps' source source ch rfl ha
    have hpLookup := adaptiveActionCommitmentPolynomial_lookup_eq
      pp basis inputs ps ps' source source ch rfl ha hi ht
    have hsPerm := congrArg (fun s : Finset Fp => (↑s : Set Fp))
      (allResolverPermutationBetaBadSet_congr
        pp.numProofs (ActionTerminal.vkAt basis) actionActiveRows hpPerm)
    have hsLookup := congrArg (fun s : Finset Fp => (↑s : Set Fp))
      (allResolverLookupBetaBadSet_congr
        pp.numProofs (ActionTerminal.vkAt basis)
        (actionCircuit.n -
          actionCircuit.blindingFactors - 2)
        (ch₁ := ActionTerminal.semanticChRecord ch.theta 0
          (k := (actionCircuit.shape.withProofParams pp).k))
        (ch₂ := ActionTerminal.semanticChRecord ch.theta 0
          (k := (actionCircuit.shape.withProofParams pp).k)) rfl hpLookup)
    simpa [adaptiveActionSurfaceAt, nu, ch] using
      congrArg₂ (fun a b : Set Fp => a ∪ b) hsPerm hsLookup
  · obtain ⟨ha, hi, ht⟩ := preGammaSqueezePoint_inj init hprefix
    have hpPerm := adaptiveActionCommitmentPolynomial_permutation_eq
      pp basis inputs ps ps' source source ch rfl ha
    have hpLookup := adaptiveActionCommitmentPolynomial_lookup_eq
      pp basis inputs ps ps' source source ch rfl ha hi ht
    have hsPerm := congrArg (fun s : Finset Fp => (↑s : Set Fp))
      (allResolverPermutationGammaBadSet_congr
        pp.numProofs (ActionTerminal.vkAt basis) actionActiveRows
        (ch₁ := ActionTerminal.semanticChRecord ch.theta ch.beta
          (k := (actionCircuit.shape.withProofParams pp).k))
        (ch₂ := ActionTerminal.semanticChRecord ch.theta ch.beta
          (k := (actionCircuit.shape.withProofParams pp).k)) rfl hpPerm)
    have hsLookup := congrArg (fun s : Finset Fp => (↑s : Set Fp))
      (allResolverLookupGammaBadSet_congr
        pp.numProofs (ActionTerminal.vkAt basis)
        (actionCircuit.n -
          actionCircuit.blindingFactors - 2)
        (ch₁ := ActionTerminal.semanticChRecord ch.theta ch.beta
          (k := (actionCircuit.shape.withProofParams pp).k))
        (ch₂ := ActionTerminal.semanticChRecord ch.theta ch.beta
          (k := (actionCircuit.shape.withProofParams pp).k)) rfl rfl hpLookup)
    simpa [adaptiveActionSurfaceAt, nu, ch] using
      congrArg₂ (fun a b : Set Fp => a ∪ b) hsPerm hsLookup
  · obtain ⟨ha, hi, ht, hp, hl, hr⟩ := preYSqueezePoint_inj init hprefix
    have hpoly := adaptiveActionCommitmentPolynomial_eq_of_preY_fields
      pp basis inputs ps ps' source source ch rfl ha hi ht hp hl hr
    have hmodel :
        adaptiveActionCommittedModel pp basis inputs ps source ch =
          adaptiveActionCommittedModel pp basis inputs ps' source ch := by
      change adaptiveActionCommitmentPolynomialOf (ActionTerminal.vkAt basis)
          (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
          ps source ch =
        adaptiveActionCommitmentPolynomialOf (ActionTerminal.vkAt basis)
          (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
          ps' source ch at hpoly
      unfold adaptiveActionCommittedModel adaptiveActionCommittedModelOf
      rw [hpoly]
    have hs := congrArg (fun model : ConstraintPolyModel
        pp.numProofs =>
      ⋃ j, (↑(szBadSet (foldSplitWitness model.constraints
        actionCircuit.n j)) : Set Fp)) hmodel
    simpa [adaptiveActionSurfaceAt, nu, ch] using hs
  · obtain ⟨ha, hi, ht, hp, hl, _hr, hh⟩ := preXSqueezePoint_inj init hprefix
    have hpoly := adaptiveActionCommitmentPolynomial_eq_of_preY_fields
      pp basis inputs ps ps' source source ch rfl ha hi ht hp hl _hr
    have hmodel :
        adaptiveActionCommittedModel pp basis inputs ps source ch =
          adaptiveActionCommittedModel pp basis inputs ps' source ch := by
      change adaptiveActionCommitmentPolynomialOf (ActionTerminal.vkAt basis)
          (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
          ps source ch =
        adaptiveActionCommitmentPolynomialOf (ActionTerminal.vkAt basis)
          (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
          ps' source ch at hpoly
      unfold adaptiveActionCommittedModel adaptiveActionCommittedModelOf
      rw [hpoly]
    have hdifference :
        adaptiveActionPreXDifference pp basis inputs ps source ch =
          adaptiveActionPreXDifference pp basis inputs ps' source ch := by
      rw [adaptiveActionPreXDifference_eq, adaptiveActionPreXDifference_eq]
      rw [hmodel, hh]
    have hs := congrArg
      (fun polynomial : CPoly => (↑(szBadSet polynomial) : Set Fp)) hdifference
    simpa [adaptiveActionSurfaceAt, nu, ch] using hs

/-! ## Pointwise prices of the five Action surfaces -/

/-- The adaptive `theta` surface has the ordinary top-level lookup budget. -/
theorem adaptiveActionThetaSurface_measure_le
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis)) (earlier : Fin 0 → Fp) :
    uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAt pp basis inputs 0 ps source earlier) ≤
      (TopLevelLookup.thetaBudget actionCircuit pp
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
        (adaptiveActionCommitmentPolynomial pp basis inputs ps source
          (chRecord (fun _ => 0) (fun _ => 0))) : ENNReal) /
        Fintype.card Fp := by
  simpa [adaptiveActionSurfaceAt] using
    (ActionTerminal.actionThetaBadSet_measure_le pp basis
      (adaptiveActionCommitmentPolynomial pp basis inputs ps source
        (chRecord (fun _ => 0) (fun _ => 0))))

/-- The adaptive `beta` surface is priced by the same permutation/lookup counts as the staged
Action remainder. -/
theorem adaptiveActionBetaSurface_measure_le
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis)) (earlier : Fin 1 → Fp) :
    let ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp :=
      chRecord (fun i => if h : (i : Nat) < 1 then earlier ⟨i, h⟩ else 0) (fun _ => 0)
    let poly := adaptiveActionCommitmentPolynomial pp basis inputs ps source ch
    uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAt pp basis inputs 1 ps source earlier) ≤
      ((∑ p : Fin pp.numProofs,
        (Fintype.card (ResolverPermutationCell (ActionTerminal.vkAt basis) poly p
          actionActiveRows) + 1) *
          Fintype.card (ResolverPermutationCell (ActionTerminal.vkAt basis) poly p
            actionActiveRows) : Nat) : ENNReal) / Fintype.card Fp +
      ((pp.numProofs * actionCircuit.lookupCount *
        ((actionCircuit.n -
            actionCircuit.blindingFactors - 2 + 2) *
          (actionCircuit.n -
            actionCircuit.blindingFactors - 2 + 1) +
          (actionCircuit.n -
            actionCircuit.blindingFactors - 2 + 1)) : Nat) : ENNReal) /
        Fintype.card Fp := by
  dsimp only
  simpa [adaptiveActionSurfaceAt, actionActiveRows] using
    (ActionTerminal.actionBetaBadSets_measure_le pp basis (earlier 0)
      (adaptiveActionCommitmentPolynomial pp basis inputs ps source
        (chRecord (fun i => if h : (i : Nat) < 1 then earlier ⟨i, h⟩ else 0)
          (fun _ => 0))))

/-- The adaptive `gamma` surface is priced by the same doubled permutation/lookup count. -/
theorem adaptiveActionGammaSurface_measure_le
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis)) (earlier : Fin 2 → Fp) :
    let ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp :=
      chRecord (fun i => if h : (i : Nat) < 2 then earlier ⟨i, h⟩ else 0) (fun _ => 0)
    let poly := adaptiveActionCommitmentPolynomial pp basis inputs ps source ch
    uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAt pp basis inputs 2 ps source earlier) ≤
      ((∑ p : Fin pp.numProofs,
        2 * Fintype.card (ResolverPermutationCell (ActionTerminal.vkAt basis) poly p
          actionActiveRows) : Nat) : ENNReal) / Fintype.card Fp +
      ((pp.numProofs * actionCircuit.lookupCount *
        (2 * (actionCircuit.n -
          actionCircuit.blindingFactors - 2 + 1)) : Nat) : ENNReal) /
        Fintype.card Fp := by
  dsimp only
  simpa [adaptiveActionSurfaceAt, actionActiveRows] using
    (ActionTerminal.actionGammaBadSets_measure_le pp basis (earlier 0) (earlier ⟨1, by omega⟩)
      (adaptiveActionCommitmentPolynomial pp basis inputs ps source
        (chRecord (fun i => if h : (i : Nat) < 2 then earlier ⟨i, h⟩ else 0)
          (fun _ => 0))))

/-- The adaptive `y` surface is the standard fold-split union. -/
theorem adaptiveActionYSurface_measure_le
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis)) (earlier : Fin 3 → Fp)
    (hn : actionCircuit.n ≠ 0) :
    let ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp :=
      chRecord (fun i => if h : (i : Nat) < 3 then earlier ⟨i, h⟩ else 0) (fun _ => 0)
    let model := adaptiveActionCommittedModel pp basis inputs ps source ch
    uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAt pp basis inputs 3 ps source earlier) ≤
      ((actionCircuit.n * model.constraints.length : Nat) : ENNReal) /
        Fintype.card Fp := by
  dsimp only
  simpa [adaptiveActionSurfaceAt] using
    (ActionTerminal.actionYBadSet_measure_le
      (adaptiveActionCommittedModel pp basis inputs ps source
        (chRecord (fun i => if h : (i : Nat) < 3 then earlier ⟨i, h⟩ else 0)
          (fun _ => 0))).constraints hn)

/-- The adaptive `x` surface is one Schwartz--Zippel set at the explicit canonical pre-`x`
constraint difference. -/
theorem adaptiveActionXSurface_measure_le
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis)) (earlier : Fin 4 → Fp) :
    let ch : Challenges (actionCircuit.shape.withProofParams pp).k Fp :=
      chRecord (fun i => if h : (i : Nat) < 4 then earlier ⟨i, h⟩ else 0) (fun _ => 0)
    let difference := adaptiveActionPreXDifference pp basis inputs ps source ch
    uniformChallenge.toOuterMeasure
        (adaptiveActionSurfaceAt pp basis inputs 4 ps source earlier) ≤
      (difference.natDegree : ENNReal) / Fintype.card Fp := by
  dsimp only
  simpa [adaptiveActionSurfaceAt] using
    (uniformChallenge_szBadSet
      (adaptiveActionPreXDifference pp basis inputs ps source
        (chRecord (fun i => if h : (i : Nat) < 4 then earlier ⟨i, h⟩ else 0)
          (fun _ => 0))))

theorem adaptiveActionPreXDifference_challenge_congr
    (pp : ProofParams)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (ch₁ ch₂ : Challenges (actionCircuit.shape.withProofParams pp).k Fp)
    (htheta : ch₁.theta = ch₂.theta) (hbeta : ch₁.beta = ch₂.beta)
    (hgamma : ch₁.gamma = ch₂.gamma) (hy : ch₁.y = ch₂.y) :
    adaptiveActionPreXDifference pp basis inputs ps source ch₁ =
      adaptiveActionPreXDifference pp basis inputs ps source ch₂ := by
  have hmodel := adaptiveActionCommittedModel_challenge_congr
    pp basis inputs ps source ch₁ ch₂ htheta hbeta hgamma
  rw [adaptiveActionPreXDifference_eq, adaptiveActionPreXDifference_eq]
  rw [hmodel, hy]

/-- On a queried prefix with no provenance relation, the query-time stage source is literally
the final stage source. -/
theorem adaptiveActionQuerySource_eq_of_pinned
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (n : Fin 5)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (decoded : DecodedPreIpaPrefix (shape := shape) family.init
      (Fin.castLE (by omega) n)
      (algebraicFullPrefixesPre family.init
        ((family.adversary basis).run O).toAlgebraicWfProof (Fin.castLE (by omega) n)))
    (pinned : SelectedQueryRepresentationPinned
      (algebraicFullPrefixesPre family.init
        ((family.adversary basis).run O).toAlgebraicWfProof (Fin.castLE (by omega) n))
      (family.adversary basis) O
      (((family.adversary basis).run O).algebraicProof.actionRepresentationsBefore n)) :
    adaptiveActionQuerySource family.init basis n decoded pinned.query
        (family.fixedRepresentations basis) =
      ((family.adversary basis).run O).algebraicProof.actionRepresentationsBefore n ++
        family.fixedRepresentations basis := by
  let data := (family.adversary basis).run O
  let final := data.algebraicProof.actionRepresentationsBefore n
  have hprefixBounded : fullPrefixesPre family.init decoded.proof (Fin.castLE (by omega) n) =
      fullPrefixesPre family.init data.toAlgebraicWfProof.proof
        (Fin.castLE (by omega) n) := decoded.point_eq
  have hprefix : preIpaSqueezePoints family.init decoded.proof.1
      (Fin.castLE (by omega) n) =
      preIpaSqueezePoints family.init data.algebraicProof.erase
        (Fin.castLE (by omega) n) := congrArg Subtype.val hprefixBounded
  have hordinary : decoded.proof.1.actionCommitmentPointsBefore n =
      data.algebraicProof.erase.actionCommitmentPointsBefore n :=
    actionCommitmentPointsBefore_eq_of_prefix family.init n _ _ hprefix
  have hselected : pinned.query.representationsFor final pinned.covered = final :=
    algebraicPointList_eq_of_maps_eq
      (pinned.query.representationsFor_points final pinned.covered)
      pinned.coefficients_eq
  let decodedCovered : ∀ P ∈ decoded.proof.1.actionCommitmentPointsBefore n,
      P ∈ transcriptGroupPoints
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof
          (Fin.castLE (by omega) n)).val := by
    intro P hP
    rw [← decoded.point_eq]
    exact decoded.proof.1.actionCommitmentPointsBefore_covered family.init
      decoded.proof.2 n P hP
  unfold adaptiveActionQuerySource
  change pinned.query.representationsForPoints
      (decoded.proof.1.actionCommitmentPointsBefore n) decodedCovered ++
        family.fixedRepresentations basis = _
  have hordinaryFinal : decoded.proof.1.actionCommitmentPointsBefore n =
      final.map AlgebraicPoint.point :=
    hordinary.trans (data.algebraicProof.actionRepresentationsBefore_points n).symm
  let finalCoveredPoints : ∀ P ∈ final.map AlgebraicPoint.point,
      P ∈ transcriptGroupPoints
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof
          (Fin.castLE (by omega) n)).val := by
    intro P hP
    obtain ⟨ap, hap, rfl⟩ := List.mem_map.mp hP
    exact pinned.covered ap hap
  have representationsForPoints_congr
      (points points' : List VestaG)
      (hcovered : ∀ P ∈ points, P ∈ transcriptGroupPoints
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof
          (Fin.castLE (by omega) n)).val)
      (hcovered' : ∀ P ∈ points', P ∈ transcriptGroupPoints
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof
          (Fin.castLE (by omega) n)).val)
      (hpoints : points = points') :
      pinned.query.representationsForPoints points hcovered =
        pinned.query.representationsForPoints points' hcovered' := by
    subst points'
    rfl
  have hqueryPoints : pinned.query.representationsForPoints
      (decoded.proof.1.actionCommitmentPointsBefore n) decodedCovered =
      pinned.query.representationsForPoints
        (final.map AlgebraicPoint.point) finalCoveredPoints := by
    exact representationsForPoints_congr _ _ decodedCovered finalCoveredPoints hordinaryFinal
  rw [hqueryPoints,
    ← pinned.query.representationsFor_eq_representationsForPoints final pinned.covered]
  exact congrArg (fun source => source ++ family.fixedRepresentations basis) hselected

/-- Query-time Action surface reconstructed from the exact ordinary prefix and its pre-answer AGM
annotation. -/
def adaptiveQueriedActionSurface
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (n : Fin 5)
    (t : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10 +
        3 * (actionCircuit.shape.withProofParams pp).k))
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (earlier : Fin (n : Nat) → Fp) : Set Fp :=
  let n11 : Fin 11 := ⟨n, by omega⟩
  match decodePreIpaPrefix? (shape := actionCircuit.shape.withProofParams pp) family.init n11 t with
  | none => ∅
  | some decoded =>
      adaptiveActionSurfaceAt pp basis inputs n decoded.proof.1
        (adaptiveActionQuerySource family.init basis n decoded label
          (family.fixedRepresentations basis)) earlier

/-- Fresh-prefix fallback reconstructed from the final output's own stage-local AGM
representations. -/
def adaptiveFallbackActionSurface
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (n : Fin 5)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (_t : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10 +
        3 * (actionCircuit.shape.withProofParams pp).k))
    (earlier : Fin (n : Nat) → Fp) : Set Fp :=
  adaptiveActionSurfaceAt pp basis inputs n data.algebraicProof.erase
    (data.algebraicProof.actionRepresentationsBefore n ++ family.fixedRepresentations basis)
    earlier

namespace ComputedAdaptiveOnlineAGMFSFamily

/-- Compare the final stage-local Action commitments with the first online-AGM annotation at the
actual semantic squeeze.  Any coefficient mismatch is returned as explicit relation data. -/
def adaptiveActionRepresentationRelationAt?
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (n : Fin 5) : Option (AlgebraicRelationWitness (F := Fp) basis) :=
  let p := data.toAlgebraicWfProof
  let n11 : Fin 11 := Fin.castLE (by omega) n
  let t := algebraicFullPrefixesPre family.init p n11
  selectedQueryRepresentationRelation? t (family.adversary basis) O
    (data.algebraicProof.actionRepresentationsBefore n) (by
      intro ap hap
      change ap.point ∈ transcriptGroupPoints
        (preIpaSqueezePoints family.init data.algebraicProof.erase n11)
      exact data.algebraicProof.actionRepresentationsBefore_covered
        family.init data.wellFormed n ap hap)

/-- Cached-log form of one Action semantic-squeeze provenance comparison. -/
def adaptiveActionRepresentationRelationAtFromAnnotations?
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (annotations : AdaptiveOnlineAGMAnnotationLog family.init basis)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (n : Fin 5) : Option (AlgebraicRelationWitness (F := Fp) basis) :=
  let p := data.toAlgebraicWfProof
  let n11 : Fin 11 := Fin.castLE (by omega) n
  let t := algebraicFullPrefixesPre family.init p n11
  selectedQueryRepresentationRelationFromAnnotations? t annotations
    (data.algebraicProof.actionRepresentationsBefore n) (by
      intro ap hap
      change ap.point ∈ transcriptGroupPoints
        (preIpaSqueezePoints family.init data.algebraicProof.erase n11)
      exact data.algebraicProof.actionRepresentationsBefore_covered
        family.init data.wellFormed n ap hap)

@[simp] theorem adaptiveActionRepresentationRelationAtFromAnnotations?_annotations
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (n : Fin 5) :
    family.adaptiveActionRepresentationRelationAtFromAnnotations? basis
        ((family.adversary basis).annotations O) data n =
      family.adaptiveActionRepresentationRelationAt? basis O data n := by
  unfold adaptiveActionRepresentationRelationAtFromAnnotations?
    adaptiveActionRepresentationRelationAt?
  exact selectedQueryRepresentationRelationFromAnnotations?_eq _ _ _ _ _

/-- Compare the polynomial source visible at one semantic squeeze with the complete pre-`x`
source used by the executable decoder.  A collision with different coordinates is an explicit
relation rather than an unpriced future dependency. -/
def adaptiveActionSourceMismatchAt?
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (n : Fin 5) : Option (AlgebraicRelationWitness (F := Fp) basis) :=
  representationSourceMismatchFinder
    (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
    (data.algebraicProof.actionRepresentationsBefore n ++
      family.fixedRepresentations basis)

/-- Compare the online coordinate vector of the quotient MSM with the explicit quotient-piece
power sum.  Both sides are computed from the bare adaptive run's retained pre-`x` source. -/
def adaptiveActionQuotientAgreementOrRelation
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    let pnu := ActionTerminal.adaptiveActionRunOutput family basis O
    let source := pnu.1.algebraicProof.preX1AssemblySource
      (family.fixedRepresentations basis)
    let xn := (wrappedPreIpaRecord pnu).x ^ (family.vk basis).n
    let msm := vanishingHCommitment shape.k xn (List.ofFn pnu.1.proof.1.hPieces)
    let hcovered : CommitmentRefCovered source (.msm msm) := by
      intro pr hpr
      have hpoint : pr.2 ∈ msm.otherPoints := by
        rw [Zcash.Arithmetic.Msm.otherPoints]
        exact List.mem_map.mpr ⟨pr, hpr, rfl⟩
      have hpiece := mem_otherPoints_vanishingHCommitment xn
        (List.ofFn pnu.1.proof.1.hPieces) pr.2 hpoint
      obtain ⟨i, hi⟩ := List.mem_ofFn.mp hpiece
      refine ⟨pnu.1.algebraicProof.hPieces i,
        pnu.1.algebraicProof.hPiece_mem_preX1AssemblySource
          (family.fixedRepresentations basis) i, ?_⟩
      change (pnu.1.algebraicProof.hPieces i).point = pr.2 at hi
      exact hi
    let represented := coveredCommitmentRepresentation source (.msm msm) hcovered
    let pieces : AlgebraicColumnRepresentations
        (ursOfAugmentedBasis shape.k basis) pnu.1.proof.1.hPieces :=
      { coeffs := fun i => (onlinePointCoordinates source
            (pnu.1.algebraicProof.hPieces i).point).1
        uComp := fun i => (onlinePointCoordinates source
            (pnu.1.algebraicProof.hPieces i).point).2.1
        wComp := fun i => (onlinePointCoordinates source
            (pnu.1.algebraicProof.hPieces i).point).2.2
        commitment := fun i => by
          simpa using onlinePointCoordinates_commitment source
            (pnu.1.algebraicProof.hPieces i).point
            ⟨pnu.1.algebraicProof.hPieces i,
              pnu.1.algebraicProof.hPiece_mem_preX1AssemblySource
                (family.fixedRepresentations basis) i, rfl⟩ }
    (represented.coeffs = ∑ i : Fin shape.numQuotientPieces,
        xn ^ (i : Nat) • pieces.coeffs i ∧
      represented.uComp = ∑ i : Fin shape.numQuotientPieces,
        xn ^ (i : Nat) * pieces.uComp i ∧
      represented.wComp = ∑ i : Fin shape.numQuotientPieces,
        xn ^ (i : Nat) * pieces.wComp i) ⊕'
      AugmentedRelationWitness (F := Fp)
        (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u
        (ursOfAugmentedBasis shape.k basis).w := by
  dsimp only
  let pnu := ActionTerminal.adaptiveActionRunOutput family basis O
  let source := pnu.1.algebraicProof.preX1AssemblySource
    (family.fixedRepresentations basis)
  let xn := (wrappedPreIpaRecord pnu).x ^ (family.vk basis).n
  let msm := vanishingHCommitment shape.k xn (List.ofFn pnu.1.proof.1.hPieces)
  let hcovered : CommitmentRefCovered source (.msm msm) := by
    intro pr hpr
    have hpoint : pr.2 ∈ msm.otherPoints := by
      rw [Zcash.Arithmetic.Msm.otherPoints]
      exact List.mem_map.mpr ⟨pr, hpr, rfl⟩
    have hpiece := mem_otherPoints_vanishingHCommitment xn
      (List.ofFn pnu.1.proof.1.hPieces) pr.2 hpoint
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hpiece
    refine ⟨pnu.1.algebraicProof.hPieces i,
      pnu.1.algebraicProof.hPiece_mem_preX1AssemblySource
        (family.fixedRepresentations basis) i, ?_⟩
    change (pnu.1.algebraicProof.hPieces i).point = pr.2 at hi
    exact hi
  let represented := coveredCommitmentRepresentation source (.msm msm) hcovered
  let pieces : AlgebraicColumnRepresentations
      (ursOfAugmentedBasis shape.k basis) pnu.1.proof.1.hPieces :=
    { coeffs := fun i => (onlinePointCoordinates source
          (pnu.1.algebraicProof.hPieces i).point).1
      uComp := fun i => (onlinePointCoordinates source
          (pnu.1.algebraicProof.hPieces i).point).2.1
      wComp := fun i => (onlinePointCoordinates source
          (pnu.1.algebraicProof.hPieces i).point).2.2
      commitment := fun i => by
        simpa using onlinePointCoordinates_commitment source
          (pnu.1.algebraicProof.hPieces i).point
          ⟨pnu.1.algebraicProof.hPieces i,
            pnu.1.algebraicProof.hPiece_mem_preX1AssemblySource
              (family.fixedRepresentations basis) i, rfl⟩ }
  let pieceCoeffs := ∑ i : Fin shape.numQuotientPieces,
    xn ^ (i : Nat) • pieces.coeffs i
  let pieceU := ∑ i : Fin shape.numQuotientPieces,
    xn ^ (i : Nat) * pieces.uComp i
  let pieceW := ∑ i : Fin shape.numQuotientPieces,
    xn ^ (i : Nat) * pieces.wComp i
  have hvanishing : msm.eval (ursOfAugmentedBasis shape.k basis) =
      ∑ i : Fin shape.numQuotientPieces, xn ^ (i : Nat) • pnu.1.proof.1.hPieces i := by
    calc
      _ = ∑ i ∈ Finset.range (List.ofFn pnu.1.proof.1.hPieces).length,
          xn ^ i • (List.ofFn pnu.1.proof.1.hPieces).getD i 0 :=
        vanishingHCommitment_eval (ursOfAugmentedBasis shape.k basis) xn
          (List.ofFn pnu.1.proof.1.hPieces)
      _ = _ := by
        rw [List.length_ofFn, ← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.isLt),
          List.getElem_ofFn]
  have hrepresented : commit (ursOfAugmentedBasis shape.k basis) represented.coeffs +
      represented.uComp • (ursOfAugmentedBasis shape.k basis).u +
      represented.wComp • (ursOfAugmentedBasis shape.k basis).w =
        ∑ i : Fin shape.numQuotientPieces, xn ^ (i : Nat) • pnu.1.proof.1.hPieces i :=
    represented.commitment.trans hvanishing
  have hpieces : commit (ursOfAugmentedBasis shape.k basis) pieceCoeffs +
      pieceU • (ursOfAugmentedBasis shape.k basis).u +
      pieceW • (ursOfAugmentedBasis shape.k basis).w =
        ∑ i : Fin shape.numQuotientPieces, xn ^ (i : Nat) • pnu.1.proof.1.hPieces i :=
    pieces.power_commitment xn
  have hcollision : commitGen (ursOfAugmentedBasis shape.k basis).g represented.coeffs +
      represented.uComp • (ursOfAugmentedBasis shape.k basis).u +
      represented.wComp • (ursOfAugmentedBasis shape.k basis).w =
      commitGen (ursOfAugmentedBasis shape.k basis).g pieceCoeffs +
        pieceU • (ursOfAugmentedBasis shape.k basis).u +
        pieceW • (ursOfAugmentedBasis shape.k basis).w := by
    rw [← commit_eq_commitGen, ← commit_eq_commitGen, hrepresented, hpieces]
  exact separateOrRelationWitness (ursOfAugmentedBasis shape.k basis).g
    (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w
    represented.coeffs pieceCoeffs represented.uComp pieceU represented.wComp pieceW hcollision

/-- Compare the quotient coordinates and project only explicit relation data. -/
def adaptiveActionQuotientRelationFinder
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  match family.adaptiveActionQuotientAgreementOrRelation basis O with
  | PSum.inl _ => none
  | PSum.inr relation =>
      some (augmentedBasis_ursOfAugmentedBasis shape.k basis ▸
        relation.toAlgebraicRelationWitness)

/-- One shared run checks provenance at `theta`, `beta`, `gamma`, `y`, and `x`. -/
def adaptiveActionRepresentationRelationFinder
    (family : ComputedAdaptiveOnlineAGMFSFamily shape) :
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    let execution := (family.adversary basis).runWithAnnotations O
    let data := execution.1
    let annotations := execution.2
    firstAdaptiveRelation?
      ((List.ofFn fun n =>
          family.adaptiveActionRepresentationRelationAtFromAnnotations? basis annotations data n) ++
        (List.ofFn fun n => family.adaptiveActionSourceMismatchAt? basis data n) ++
        [family.adaptiveActionQuotientRelationFinder basis O])

/-- The one-pass Action provenance finder is extensionally equal to the uncached repeated scan. -/
theorem adaptiveActionRepresentationRelationFinder_eq_uncached
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    family.adaptiveActionRepresentationRelationFinder basis O =
      let data := (family.adversary basis).run O
      firstAdaptiveRelation?
        ((List.ofFn fun n => family.adaptiveActionRepresentationRelationAt? basis O data n) ++
          (List.ofFn fun n => family.adaptiveActionSourceMismatchAt? basis data n) ++
          [family.adaptiveActionQuotientRelationFinder basis O]) := by
  simp [adaptiveActionRepresentationRelationFinder]

/-- No aggregate semantic-provenance relation means every stage-local comparison was empty. -/
theorem adaptiveActionRepresentationRelationFinder_none_at
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (hnone : family.adaptiveActionRepresentationRelationFinder basis O = none)
    (n : Fin 5) :
    let data := (family.adversary basis).run O
    family.adaptiveActionRepresentationRelationAt? basis O data n = none := by
  dsimp only
  have hall := (firstAdaptiveRelation?_eq_none_iff _).1 (by
    rw [family.adaptiveActionRepresentationRelationFinder_eq_uncached basis O] at hnone
    exact hnone)
  apply hall
  exact List.mem_append.mpr (Or.inl
    (List.mem_append.mpr (Or.inl (List.mem_ofFn.mpr ⟨n, rfl⟩))))

/-- No aggregate provenance relation also rules out every future source collision. -/
theorem adaptiveActionRepresentationRelationFinder_none_source_at
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (hnone : family.adaptiveActionRepresentationRelationFinder basis O = none)
    (n : Fin 5) :
    let data := (family.adversary basis).run O
    family.adaptiveActionSourceMismatchAt? basis data n = none := by
  dsimp only
  have hall := (firstAdaptiveRelation?_eq_none_iff _).1 (by
    rw [family.adaptiveActionRepresentationRelationFinder_eq_uncached basis O] at hnone
    exact hnone)
  apply hall
  exact List.mem_append.mpr (Or.inl
    (List.mem_append.mpr (Or.inr (List.mem_ofFn.mpr ⟨n, rfl⟩))))

/-- No aggregate Action provenance relation also certifies equality of the decoded quotient MSM
coordinates and the explicit quotient-piece power sum. -/
theorem adaptiveActionRepresentationRelationFinder_none_quotient
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (hnone : family.adaptiveActionRepresentationRelationFinder basis O = none) :
    family.adaptiveActionQuotientRelationFinder basis O = none := by
  have hall := (firstAdaptiveRelation?_eq_none_iff _).1 (by
    rw [family.adaptiveActionRepresentationRelationFinder_eq_uncached basis O] at hnone
    exact hnone)
  apply hall
  exact List.mem_append.mpr (Or.inr (by simp))

/-- An empty quotient relation projection leaves the executable coordinate-equality branch. -/
theorem adaptiveActionQuotientAgreement_of_finder_none
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (hnone : family.adaptiveActionQuotientRelationFinder basis O = none) :
    ∃ agreement,
      family.adaptiveActionQuotientAgreementOrRelation basis O = PSum.inl agreement := by
  unfold adaptiveActionQuotientRelationFinder at hnone
  cases hout : family.adaptiveActionQuotientAgreementOrRelation basis O with
  | inl agreement => exact ⟨agreement, rfl⟩
  | inr relation => simp [hout] at hnone

/-- Outside the combined Action provenance finder, the stage-local polynomial at every covered
point is exactly the polynomial used by the complete pre-`x` decoder source. -/
theorem adaptiveActionStagePolynomial_eq_full
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (hnone : family.adaptiveActionRepresentationRelationFinder basis O = none)
    (n : Fin 5) (P : VestaG)
    (hP : ∃ ap ∈
      ((family.adversary basis).run O).algebraicProof.actionRepresentationsBefore n ++
        family.fixedRepresentations basis,
      ap.point = P) :
    onlinePointPolynomial
        (((family.adversary basis).run O).algebraicProof.preX1AssemblySource
          (family.fixedRepresentations basis)) P =
      onlinePointPolynomial
        (((family.adversary basis).run O).algebraicProof.actionRepresentationsBefore n ++
          family.fixedRepresentations basis) P := by
  apply onlinePointPolynomial_eq_of_sourceMismatch_none
  · intro ap hap
    exact AlgebraicProofString.actionStageSource_subset_preX1AssemblySource
      ((family.adversary basis).run O).algebraicProof
      (family.fixedRepresentations basis) n ap hap
  · exact family.adaptiveActionRepresentationRelationFinder_none_source_at basis O hnone n
  · exact hP

/-- A commitment identity absent from the accepting verifier's assembled query list resolves to
the zero polynomial. -/
theorem acceptedPolynomial_eq_zero_of_no_query
    {shape : Shape}
    (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (pnu : WrappedAlgebraicOutput family basis)
    (rounds : Fin shape.k → Fp)
    (decode : DeployedAlgebraicDecode shape (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (wrappedPreIpaRecord pnu)
      (pnu.1.aMulti (wrappedPreIpaReads pnu))
      (pnu.1.multiU (wrappedPreIpaReads pnu))
      (pnu.1.multiBlind (wrappedPreIpaReads pnu)))
    (hchar : deployedX4PairCount (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (chRecord (wrappedPreIpaReads pnu) rounds) <
        Zcash.Arithmetic.scalarFieldOrder)
    (haccepts : DeployedAccepts shape (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (chRecord (wrappedPreIpaReads pnu) rounds))
    (id : CommitmentId)
    (habsent : ∀ q ∈ assembleQueries (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (chRecord (wrappedPreIpaReads pnu) rounds), q.commId ≠ id) :
    CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => (decode.reRound rounds).toMemberDecode hchar i hi)
        haccepts id = 0 := by
  have hroute : CanonicalMemberConstraintRelation.acceptedRoute haccepts id = none := by
    unfold CanonicalMemberConstraintRelation.acceptedRoute assembledQueryMemberRoute
    dsimp only
    split
    · rfl
    · rename_i q hfind
      have hq := List.mem_of_find?_eq_some hfind
      have hqid : q.commId = id := by simpa using List.find?_some hfind
      exact False.elim (habsent q hq hqid)
  unfold CanonicalMemberConstraintRelation.acceptedPolynomial decodedPolynomialResolver
  rw [hroute]

/-- Transporting a decode and acceptance certificate along key/instance equalities does not
change the polynomial resolver they determine. -/
theorem acceptedPolynomial_transport
    {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk₁ vk₂ : VerifyingKey shape Fp VestaG}
    {ic₁ ic₂ : Fin shape.numProofs → Nat → VestaG}
    (hI : ic₁ = ic₂) (hvk : vk₁ = vk₂)
    {ps : ProofString shape Fp VestaG} {ch : Challenges shape.k Fp}
    {a : Fin (2 ^ shape.k) → Fp} {aU aW : Fp}
    (decode : DeployedAlgebraicDecode shape (ursOfAugmentedBasis shape.k basis) rfl
      vk₁ ic₁ ps ch a aU aW)
    (hchar : deployedX4PairCount vk₁ ic₁ ps ch <
      Zcash.Arithmetic.scalarFieldOrder)
    (haccepts : DeployedAccepts shape (ursOfAugmentedBasis shape.k basis) rfl
      vk₁ ic₁ ps ch) :
    let decode' : DeployedAlgebraicDecode shape (ursOfAugmentedBasis shape.k basis) rfl
      vk₂ ic₂ ps ch a aU aW := hI ▸ hvk ▸ decode
    let hchar' : deployedX4PairCount vk₂ ic₂ ps ch <
      Zcash.Arithmetic.scalarFieldOrder := hI ▸ hvk ▸ hchar
    let haccepts' : DeployedAccepts shape (ursOfAugmentedBasis shape.k basis) rfl
      vk₂ ic₂ ps ch := hI ▸ hvk ▸ haccepts
    CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) haccepts =
      CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi => decode'.toMemberDecode hchar' i hi) haccepts' := by
  subst ic₂
  subst vk₂
  rfl

/-- Transporting a decode and acceptance certificate along key/instance equalities does not
change the canonical constraint model they determine. -/
theorem acceptedModel_transport
    {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk₁ vk₂ : VerifyingKey shape Fp VestaG}
    {ic₁ ic₂ : Fin shape.numProofs → Nat → VestaG}
    (hI : ic₁ = ic₂) (hvk : vk₁ = vk₂)
    {ps : ProofString shape Fp VestaG} {ch : Challenges shape.k Fp}
    {a : Fin (2 ^ shape.k) → Fp} {aU aW : Fp}
    (decode : DeployedAlgebraicDecode shape (ursOfAugmentedBasis shape.k basis) rfl
      vk₁ ic₁ ps ch a aU aW)
    (hchar : deployedX4PairCount vk₁ ic₁ ps ch <
      Zcash.Arithmetic.scalarFieldOrder)
    (haccepts : DeployedAccepts shape (ursOfAugmentedBasis shape.k basis) rfl
      vk₁ ic₁ ps ch)
    (hblinding : vk₁.blindingFactors < vk₁.n) :
    let decode' : DeployedAlgebraicDecode shape (ursOfAugmentedBasis shape.k basis) rfl
      vk₂ ic₂ ps ch a aU aW := hI ▸ hvk ▸ decode
    let hchar' : deployedX4PairCount vk₂ ic₂ ps ch <
      Zcash.Arithmetic.scalarFieldOrder := hI ▸ hvk ▸ hchar
    let haccepts' : DeployedAccepts shape (ursOfAugmentedBasis shape.k basis) rfl
      vk₂ ic₂ ps ch := hI ▸ hvk ▸ haccepts
    let hblinding' : vk₂.blindingFactors < vk₂.n := hvk ▸ hblinding
    CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
        (hblinding := hblinding) haccepts =
      CanonicalMemberConstraintRelation.acceptedModel
        (memberDecode := fun i hi => decode'.toMemberDecode hchar' i hi)
        (hblinding := hblinding') haccepts' := by
  subst ic₂
  subst vk₂
  rfl

/-- Every plain member decoded from the successful adaptive batch witness is the polynomial of
the first matching representation in the run's complete pre-`x` online source. -/
theorem adaptiveDecodedMemberPoly_eq_online
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (pnu : WrappedAlgebraicOutput family.toFamily basis)
    (witness : DeployedBatchWitness family.toFamily basis pnu)
    (hsrc : witness.fixedRepresentations = family.fixedRepresentations basis)
    (decode : DeployedAlgebraicDecode shape (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (wrappedPreIpaRecord pnu)
      (pnu.1.aMulti (wrappedPreIpaReads pnu))
      (pnu.1.multiU (wrappedPreIpaReads pnu))
      (pnu.1.multiBlind (wrappedPreIpaReads pnu)))
    (hbatches : decode.batches = witness.batches)
    {i : Nat} (hi : i < deployedX4PairCount (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1 (wrappedPreIpaRecord pnu))
    (m : Fin (deployedSetQueries (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (wrappedPreIpaRecord pnu) i).length) {P : VestaG}
    (hP : ((deployedSetQueries (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (wrappedPreIpaRecord pnu) i).getD
        (m : Nat) (.point 0, [])).1 = .point P) :
    decode.memberPoly i hi m =
      onlinePointPolynomial
        (pnu.1.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis)) P := by
  unfold DeployedAlgebraicDecode.memberPoly onlinePointPolynomial
  rw [← hsrc, hbatches]
  rw [congrFun (witness.memberCoeffs i hi) m]
  exact congrArg coeffsToPoly
    (deployedMemberRepresentationsOfCovered_coeffs_point pnu.1
      witness.fixedRepresentations witness.membersCovered (wrappedPreIpaReads pnu)
      i hi m P hP)

/-- On a successful accepted decode with no Action provenance relation, every active commitment
available at stage `n` resolves to the polynomial reconstructed from that exact stage source. -/
theorem adaptiveAcceptedPolynomial_eq_actionStage
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10 +
        3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (hnone : family.adaptiveActionRepresentationRelationFinder basis O = none)
    (n : Fin 5) (id : CommitmentId)
    (hactive : adaptiveActionCommitmentActive (actionCircuit.shape.withProofParams pp)
      (ActionTerminal.vkAt basis) id)
    (havailable : adaptiveActionCommitmentAvailable n id)
    (pnu : WrappedAlgebraicOutput family.toFamily basis)
    (hpnu : pnu = ActionTerminal.adaptiveActionRunOutput family basis O)
    (witness : DeployedBatchWitness family.toFamily basis pnu)
    (hsrc : witness.fixedRepresentations = family.fixedRepresentations basis)
    (decode : DeployedAlgebraicDecode
      (actionCircuit.shape.withProofParams pp)
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (wrappedPreIpaRecord pnu)
      (pnu.1.aMulti (wrappedPreIpaReads pnu))
      (pnu.1.multiU (wrappedPreIpaReads pnu))
      (pnu.1.multiBlind (wrappedPreIpaReads pnu)))
    (hbatches : decode.batches = witness.batches)
    (haccepts : DeployedAccepts
      (actionCircuit.shape.withProofParams pp)
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O)))
    (hchar : deployedX4PairCount (shape := actionCircuit.shape.withProofParams pp) (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O)) <
        Zcash.Arithmetic.scalarFieldOrder) :
    let data := (family.adversary basis).run O
    CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi =>
          (decode.reRound (runRounds family.toFamily basis O)).toMemberDecode hchar i hi)
        haccepts id =
      adaptiveActionCommitmentPolynomial pp basis inputs data.algebraicProof.erase
        (data.algebraicProof.actionRepresentationsBefore n ++
          family.fixedRepresentations basis)
        (ActionTerminal.adaptiveActionRunRecord family basis O) id := by
  dsimp only
  let data := (family.adversary basis).run O
  subst pnu
  have hp : (ActionTerminal.adaptiveActionRunOutput family basis O).1 =
      data.toAlgebraicWfProof :=
    (wrappedAdversary_run_fst family.toFamily basis O).trans
      (family.toFamily_runProof basis O)
  obtain ⟨q, hq, hqid⟩ := adaptiveActionActive_query pp basis inputs
    (ActionTerminal.adaptiveActionRunOutput family basis O).1.proof.1
    (ActionTerminal.adaptiveActionRunRecord family basis O) id hactive
  have hqRaw : q ∈ assembleQueries (shape := actionCircuit.shape.withProofParams pp) (family.vk basis)
      (family.instanceCommitment basis)
      (ActionTerminal.adaptiveActionRunOutput family basis O).1.proof.1
      (ActionTerminal.adaptiveActionRunRecord family basis O) := by
    rw [hvk basis, hI basis]
    exact hq
  obtain ⟨P, hpoint, ap, hap, hapPoint⟩ :=
    adaptiveActionActive_point_mem_stage pp family basis O inputs hvk hI n id
      hactive havailable
  have hpProof :
      (ActionTerminal.adaptiveActionRunOutput family basis O).1.proof.1 =
        data.algebraicProof.erase :=
    congrArg (fun output => output.proof.1) hp
  have hpointAction : assembledCommitment (shape := actionCircuit.shape.withProofParams pp)
      (ActionTerminal.vkAt basis)
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      (ActionTerminal.adaptiveActionRunOutput family basis O).1.proof.1
      (ActionTerminal.adaptiveActionRunRecord family basis O) id = .point P := by
    rw [hpProof]
    exact hpoint
  have hpointRaw : assembledCommitment (shape := actionCircuit.shape.withProofParams pp)
      (family.vk basis)
      (family.instanceCommitment basis)
      (ActionTerminal.adaptiveActionRunOutput family basis O).1.proof.1
      (ActionTerminal.adaptiveActionRunRecord family basis O) id = .point P := by
    calc
      _ = q.commitment := by
        rw [← hqid]
        exact (assembleQueries_commitment_eq_assembled
          (shape := actionCircuit.shape.withProofParams pp)
          (family.vk basis) (family.instanceCommitment basis)
          (ActionTerminal.adaptiveActionRunOutput family basis O).1.proof.1
          (ActionTerminal.adaptiveActionRunRecord family basis O) hqRaw).symm
      _ = assembledCommitment (shape := actionCircuit.shape.withProofParams pp)
          (ActionTerminal.vkAt basis)
          (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
          (ActionTerminal.adaptiveActionRunOutput family basis O).1.proof.1
          (ActionTerminal.adaptiveActionRunRecord family basis O) id := by
        rw [← hqid]
        exact assembleQueries_commitment_eq_assembled
          (shape := actionCircuit.shape.withProofParams pp)
          (ActionTerminal.vkAt basis)
          (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
          (ActionTerminal.adaptiveActionRunOutput family basis O).1.proof.1
          (ActionTerminal.adaptiveActionRunRecord family basis O) hq
      _ = .point P := hpointAction
  have hfull := adaptiveAcceptedPolynomial_eq_online_of_query
    (shape := actionCircuit.shape.withProofParams pp) family.toFamily basis
    (ActionTerminal.adaptiveActionRunOutput family basis O)
    (runRounds family.toFamily basis O) (family.fixedRepresentations basis)
    witness hsrc decode hbatches hchar haccepts
    id q hqRaw hqid P hpointRaw
  have hsource :
      (ActionTerminal.adaptiveActionRunOutput family basis O).1.algebraicProof.preX1AssemblySource
          (family.fixedRepresentations basis) =
        data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis) :=
    congrArg (fun output => output.algebraicProof.preX1AssemblySource
      (family.fixedRepresentations basis)) hp
  have hstage := family.adaptiveActionStagePolynomial_eq_full basis O hnone n P
    ⟨ap, hap, hapPoint⟩
  unfold adaptiveActionCommitmentPolynomial adaptiveActionCommitmentPolynomialOf
  rw [if_pos hactive, hpoint]
  exact hfull.trans ((congrArg (fun source => onlinePointPolynomial source P) hsource).trans hstage)

/-- Every non-terminal slot agrees with the exact stage resolver once that slot is available at
the stage.  Identities absent from the assembled query list agree at the zero polynomial. -/
theorem adaptiveAcceptedPolynomial_eq_actionStage_nonterminal
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10 +
        3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (hnone : family.adaptiveActionRepresentationRelationFinder basis O = none)
    (n : Fin 5) (id : CommitmentId)
    (havailable : adaptiveActionCommitmentActive (actionCircuit.shape.withProofParams pp)
      (ActionTerminal.vkAt basis) id →
      adaptiveActionCommitmentAvailable n id)
    (hterminal : id ≠ .vanishingH ∧ id ≠ .randomPoly)
    (pnu : WrappedAlgebraicOutput family.toFamily basis)
    (hpnu : pnu = ActionTerminal.adaptiveActionRunOutput family basis O)
    (witness : DeployedBatchWitness family.toFamily basis pnu)
    (hsrc : witness.fixedRepresentations = family.fixedRepresentations basis)
    (decode : DeployedAlgebraicDecode
      (actionCircuit.shape.withProofParams pp)
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (wrappedPreIpaRecord pnu)
      (pnu.1.aMulti (wrappedPreIpaReads pnu))
      (pnu.1.multiU (wrappedPreIpaReads pnu))
      (pnu.1.multiBlind (wrappedPreIpaReads pnu)))
    (hbatches : decode.batches = witness.batches)
    (haccepts : DeployedAccepts
      (actionCircuit.shape.withProofParams pp)
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O)))
    (hchar : deployedX4PairCount (shape := actionCircuit.shape.withProofParams pp) (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O)) <
        Zcash.Arithmetic.scalarFieldOrder) :
    let data := (family.adversary basis).run O
    CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi =>
          (decode.reRound (runRounds family.toFamily basis O)).toMemberDecode hchar i hi)
        haccepts id =
      adaptiveActionCommitmentPolynomial pp basis inputs data.algebraicProof.erase
        (data.algebraicProof.actionRepresentationsBefore n ++
          family.fixedRepresentations basis)
        (ActionTerminal.adaptiveActionRunRecord family basis O) id := by
  dsimp only
  by_cases hactive : adaptiveActionCommitmentActive (actionCircuit.shape.withProofParams pp)
      (ActionTerminal.vkAt basis) id
  · exact adaptiveAcceptedPolynomial_eq_actionStage pp family basis O inputs hvk hI hnone
      n id hactive (havailable hactive) pnu hpnu witness hsrc decode hbatches
      haccepts hchar
  · have habsent : ∀ q ∈ assembleQueries (shape := actionCircuit.shape.withProofParams pp)
        (family.vk basis)
        (family.instanceCommitment basis) pnu.1.proof.1
        (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O)),
        q.commId ≠ id := by
      intro q hq hqid
      have hqAction : q ∈ assembleQueries (shape := actionCircuit.shape.withProofParams pp)
          (ActionTerminal.vkAt basis)
          (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
          pnu.1.proof.1
          (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O)) := by
        rw [hvk basis, hI basis] at hq
        simpa only [ActionTerminal.vkAt] using hq
      have hkind := adaptiveActionQuery_active_or_terminal pp basis inputs
        pnu.1.proof.1
        (chRecord (wrappedPreIpaReads pnu) (runRounds family.toFamily basis O)) q hqAction
      rw [hqid] at hkind
      rcases hkind with hactive' | hvanishing | hrandom
      · exact hactive hactive'
      · exact hterminal.1 hvanishing
      · exact hterminal.2 hrandom
    have hzero := acceptedPolynomial_eq_zero_of_no_query
      (shape := actionCircuit.shape.withProofParams pp) family.toFamily basis pnu
      (runRounds family.toFamily basis O) decode hchar haccepts id habsent
    unfold adaptiveActionCommitmentPolynomial adaptiveActionCommitmentPolynomialOf
    rw [if_neg hactive]
    exact hzero

/-- Changing only the propositionally equal source list does not change the decoded covered
representation; the coverage certificate is proof-irrelevant. -/
theorem coveredCommitmentRepresentation_source_congr
    {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {source source' : List (AlgebraicPoint (F := Fp) basis)}
    {c : CommitmentRef shape.k Fp VestaG}
    (hsource : source = source')
    (hcovered : CommitmentRefCovered source c)
    (hcovered' : CommitmentRefCovered source' c) :
    coveredCommitmentRepresentation source c hcovered =
      coveredCommitmentRepresentation source' c hcovered' := by
  subst source'
  rfl

/-- Outside the executable quotient-coordinate relation branch, the accepted vanishing member is
the quotient polynomial reassembled from the run's explicit pre-`x` piece coordinates. -/
theorem adaptiveAcceptedVanishing_eq_fullQuotient
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (rounds : Fin shape.k → Fp)
    (hnone : family.adaptiveActionQuotientRelationFinder basis O = none)
    (pnu : WrappedAlgebraicOutput family.toFamily basis)
    (hpnu : pnu = ActionTerminal.adaptiveActionRunOutput family basis O)
    (witness : DeployedBatchWitness family.toFamily basis pnu)
    (hsrc : witness.fixedRepresentations = family.fixedRepresentations basis)
    (decode : DeployedAlgebraicDecode shape (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (wrappedPreIpaRecord pnu)
      (pnu.1.aMulti (wrappedPreIpaReads pnu))
      (pnu.1.multiU (wrappedPreIpaReads pnu))
      (pnu.1.multiBlind (wrappedPreIpaReads pnu)))
    (hbatches : decode.batches = witness.batches)
    (haccepts : DeployedAccepts shape (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (chRecord (wrappedPreIpaReads pnu) rounds))
    (hchar : deployedX4PairCount (family.vk basis) (family.instanceCommitment basis)
      pnu.1.proof.1 (chRecord (wrappedPreIpaReads pnu) rounds) <
        Zcash.Arithmetic.scalarFieldOrder) :
    (CanonicalMemberConstraintRelation.acceptedPolynomial
        (memberDecode := fun i hi =>
          (decode.reRound rounds).toMemberDecode hchar i hi)
        haccepts .vanishingH).eval (chRecord (wrappedPreIpaReads pnu) rounds).x =
      (committedPreXQuotient (family.vk basis)
        (fun i => onlinePointPolynomial
          (pnu.1.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
          (pnu.1.algebraicProof.hPieces i).point)).eval
            (chRecord (wrappedPreIpaReads pnu) rounds).x := by
  subst pnu
  let pnu := ActionTerminal.adaptiveActionRunOutput family basis O
  let ch := chRecord (wrappedPreIpaReads pnu) rounds
  let source := pnu.1.algebraicProof.preX1AssemblySource
    (family.fixedRepresentations basis)
  let xn := ch.x ^ (family.vk basis).n
  let msm := vanishingHCommitment shape.k xn (List.ofFn pnu.1.proof.1.hPieces)
  obtain ⟨agreement, hagreement⟩ :=
    family.adaptiveActionQuotientAgreement_of_finder_none basis O hnone
  have hcovered : CommitmentRefCovered source (.msm msm) := by
    intro pr hpr
    have hpoint : pr.2 ∈ msm.otherPoints := by
      rw [Zcash.Arithmetic.Msm.otherPoints]
      exact List.mem_map.mpr ⟨pr, hpr, rfl⟩
    have hpiece := mem_otherPoints_vanishingHCommitment xn
      (List.ofFn pnu.1.proof.1.hPieces) pr.2 hpoint
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hpiece
    refine ⟨pnu.1.algebraicProof.hPieces i,
      pnu.1.algebraicProof.hPiece_mem_preX1AssemblySource
        (family.fixedRepresentations basis) i, ?_⟩
    change (pnu.1.algebraicProof.hPieces i).point = pr.2 at hi
    exact hi
  let represented := coveredCommitmentRepresentation source (.msm msm) hcovered
  let pieces : AlgebraicColumnRepresentations
      (ursOfAugmentedBasis shape.k basis) pnu.1.proof.1.hPieces :=
    { coeffs := fun i => (onlinePointCoordinates source
          (pnu.1.algebraicProof.hPieces i).point).1
      uComp := fun i => (onlinePointCoordinates source
          (pnu.1.algebraicProof.hPieces i).point).2.1
      wComp := fun i => (onlinePointCoordinates source
          (pnu.1.algebraicProof.hPieces i).point).2.2
      commitment := fun i => by
        simpa using onlinePointCoordinates_commitment source
          (pnu.1.algebraicProof.hPieces i).point
          ⟨pnu.1.algebraicProof.hPieces i,
            pnu.1.algebraicProof.hPiece_mem_preX1AssemblySource
              (family.fixedRepresentations basis) i, rfl⟩ }
  have hcoeff : represented.coeffs = ∑ i : Fin shape.numQuotientPieces,
      xn ^ (i : Nat) • pieces.coeffs i := by
    exact agreement.1
  obtain ⟨q, hq, hqid, -, -⟩ := vanishing_query_mem_assembleQueries
    (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1 ch
  let routing := canonicalRoutingConditions_of_accepts
    (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
    (family.instanceCommitment basis) pnu.1.proof.1 ch haccepts
  have routed := assembledQueryMemberRoute_faithful
    (instanceCommitment := family.instanceCommitment basis)
    (family.vk basis) pnu.1.proof.1 ch routing.1 routing.2 q hq
  have hroute : CanonicalMemberConstraintRelation.acceptedRoute haccepts .vanishingH =
      some routed.slot := by
    simpa only [CanonicalMemberConstraintRelation.acceptedRoute, routing, ← hqid] using
      routed.route_eq
  have hmemberCommit : ((deployedSetQueries (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1 ch routed.slot.setIndex).getD
        (routed.slot.memberIndex : Nat) (.point 0, [])).1 = .msm msm := by
    rw [deployed_member_commitment_eq_assembled
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1 ch
      routed.slot.setIndex routed.slot.memberIndex
      CommitmentId.vanishingH
      (assembledQueryMemberRoute_id
        (instanceCommitment := family.instanceCommitment basis)
        (family.vk basis) pnu.1.proof.1 ch routing.1 routing.2 .vanishingH routed.slot
        (by simpa only [CanonicalMemberConstraintRelation.acceptedRoute, routing] using hroute))
      (.point 0, [])]
    rfl
  let hcoveredW : CommitmentRefCovered
      (pnu.1.algebraicProof.preX1AssemblySource witness.fixedRepresentations)
      (.msm msm) := by
    rw [hsrc]
    exact hcovered
  have hmemberComponents := deployedMemberRepresentationsOfCovered_components pnu.1
    witness.fixedRepresentations witness.membersCovered (wrappedPreIpaReads pnu)
    routed.slot.setIndex routed.slot.setIndex_lt routed.slot.memberIndex (.msm msm)
    hmemberCommit hcoveredW
  have hrepresentedW : coveredCommitmentRepresentation
      (pnu.1.algebraicProof.preX1AssemblySource witness.fixedRepresentations)
      (.msm msm) hcoveredW = represented := by
    unfold represented
    apply coveredCommitmentRepresentation_source_congr
    exact congrArg (pnu.1.algebraicProof.preX1AssemblySource) hsrc
  have hdecodedCoeffRaw : (decode.batches.x1 routed.slot.setIndex
      routed.slot.setIndex_lt).coeffs routed.slot.memberIndex = represented.coeffs := by
    rw [hbatches, congrFun (witness.memberCoeffs routed.slot.setIndex
      routed.slot.setIndex_lt) routed.slot.memberIndex]
    exact hmemberComponents.1.trans
      (congrArg CoveredCommitmentRepresentation.coeffs hrepresentedW)
  have hdecodedCoeff : ((decode.reRound rounds).batches.x1 routed.slot.setIndex
      routed.slot.setIndex_lt).coeffs routed.slot.memberIndex = represented.coeffs := by
    exact hdecodedCoeffRaw
  unfold CanonicalMemberConstraintRelation.acceptedPolynomial decodedPolynomialResolver
  rw [hroute]
  change (coeffsToPoly (((decode.reRound rounds).batches.x1 routed.slot.setIndex
    routed.slot.setIndex_lt).coeffs routed.slot.memberIndex)).eval ch.x = _
  rw [hdecodedCoeff, hcoeff, coeffsToPoly_scaledSum]
  calc
    (reassembledQuotient xn (fun i => coeffsToPoly (pieces.coeffs i))).eval ch.x =
        (preXQuotient (family.vk basis).n
          (fun i => coeffsToPoly (pieces.coeffs i))).eval ch.x := by
      exact reassembledQuotient_eval_eq_preXQuotient_eval
        (family.vk basis).n (fun i => coeffsToPoly (pieces.coeffs i)) ch.x
    _ = (committedPreXQuotient (family.vk basis)
        (fun i => onlinePointPolynomial source
          (pnu.1.algebraicProof.hPieces i).point)).eval ch.x := by
      apply congrArg (fun polynomial : CPoly => polynomial.eval ch.x)
      exact (committedPreXQuotient_eq (family.vk basis)
        (fun i => onlinePointPolynomial source
          (pnu.1.algebraicProof.hPieces i).point)).symm

/-- Avoiding all five actual stage surfaces gives exactly the `x/y/beta/gamma/theta` exclusions
consumed by the Action terminal, with `x` stated on the fixed pre-`x` difference. -/
theorem adaptiveActionExclusions_of_no_surface
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10 +
        3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (hprovenance : family.adaptiveActionRepresentationRelationFinder basis O = none)
    (witness : DeployedBatchWitness family.toFamily basis
      (ActionTerminal.adaptiveActionRunOutput family basis O))
    (hsrc : witness.fixedRepresentations = family.fixedRepresentations basis)
    (rawDecode : DeployedAlgebraicDecode
      (actionCircuit.shape.withProofParams pp)
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) rfl
      (family.vk basis) (family.instanceCommitment basis)
      (ActionTerminal.adaptiveActionRunOutput family basis O).1.proof.1
      (wrappedPreIpaRecord (ActionTerminal.adaptiveActionRunOutput family basis O))
      ((ActionTerminal.adaptiveActionRunOutput family basis O).1.aMulti
        (wrappedPreIpaReads (ActionTerminal.adaptiveActionRunOutput family basis O)))
      ((ActionTerminal.adaptiveActionRunOutput family basis O).1.multiU
        (wrappedPreIpaReads (ActionTerminal.adaptiveActionRunOutput family basis O)))
      ((ActionTerminal.adaptiveActionRunOutput family basis O).1.multiBlind
        (wrappedPreIpaReads (ActionTerminal.adaptiveActionRunOutput family basis O))))
    (hbatches : rawDecode.batches = witness.batches)
    (haccepts : ActionTerminal.adaptiveActionAccepts family basis O)
    (hchar : deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      (ActionTerminal.adaptiveActionRunOutput family basis O).1.proof.1
      (wrappedPreIpaRecord (ActionTerminal.adaptiveActionRunOutput family basis O)) <
        Zcash.Arithmetic.scalarFieldOrder)
    (hsurface : ∀ n : Fin 5,
      let data := (family.adversary basis).run O
      let n11 : Fin 11 := Fin.castLE (by omega) n
      let nu : Fin 11 → Fp := fun i =>
        O (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof i)
      nu n11 ∉ adaptiveActionSurfaceAt pp basis inputs n data.algebraicProof.erase
        (data.algebraicProof.actionRepresentationsBefore n ++
          family.fixedRepresentations basis)
        (fun i => nu (i.castLE (le_of_lt n11.isLt)))) :
    let _pnu := ActionTerminal.adaptiveActionRunOutput family basis O
    let ch := ActionTerminal.adaptiveActionRunRecord family basis O
    let data := (family.adversary basis).run O
    let source := data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis)
    let decode := hI basis ▸ hvk basis ▸
      rawDecode.reRound (runRounds family.toFamily basis O)
    let hacceptsAction := ActionTerminal.adaptiveActionRunAccepts
      pp family basis O inputs hvk hI haccepts
    let actionModel := CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
      (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)) hacceptsAction
    let actionPoly := CanonicalMemberConstraintRelation.acceptedPolynomial
      (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) hacceptsAction
    ch.x ∉ szBadSet (adaptiveActionPreXDifference pp basis inputs
        data.algebraicProof.erase source ch) ∧
      (∀ j, ch.y ∉ szBadSet (foldSplitWitness actionModel.constraints
        actionCircuit.n j)) ∧
      ResolverPermutationChallengeExclusions pp.numProofs
        (ActionTerminal.vkAt basis) ch
        actionPoly actionActiveRows ∧
      TopLevelLookup.ChallengeExclusions actionCircuit pp
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) ch actionPoly := by
  simp only
  let pnu := ActionTerminal.adaptiveActionRunOutput family basis O
  let ch := ActionTerminal.adaptiveActionRunRecord family basis O
  let data := (family.adversary basis).run O
  let nu : Fin 11 → Fp := fun i =>
    O (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof i)
  let source := data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis)
  let pointPoly := onlinePointPolynomial source
  let piecePoly := fun i => onlinePointPolynomial source (data.algebraicProof.hPieces i).point
  let decode := hI basis ▸ hvk basis ▸
    rawDecode.reRound (runRounds family.toFamily basis O)
  let hacceptsAction := ActionTerminal.adaptiveActionRunAccepts
    pp family basis O inputs hvk hI haccepts
  let actionModel := CanonicalMemberConstraintRelation.acceptedModel
    (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
    (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)) hacceptsAction
  let actionPoly := CanonicalMemberConstraintRelation.acceptedPolynomial
    (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) hacceptsAction
  let stageCh (n : Fin 5) : Challenges (actionCircuit.shape.withProofParams pp).k Fp :=
    chRecord (fun i => if _h : (i : Nat) < (n : Nat) then nu ⟨i, by omega⟩ else 0)
      (fun _ => 0)
  let stageSource (n : Fin 5) :=
    data.algebraicProof.actionRepresentationsBefore n ++ family.fixedRepresentations basis
  let stagePoly (n : Fin 5) := adaptiveActionCommitmentPolynomial pp basis inputs
    data.algebraicProof.erase (stageSource n) (stageCh n)
  have hnu : wrappedPreIpaReads pnu = nu := by
    exact (wrappedPreIpaReads_run family.toFamily basis O).trans (by
      simpa only [nu, data] using family.toFamily_runReads basis O)
  have hthetaRead : ch.theta = nu 0 := by
    change wrappedPreIpaReads pnu 0 = nu 0
    rw [hnu]
  have hbetaRead : ch.beta = nu 1 := by
    change wrappedPreIpaReads pnu 1 = nu 1
    rw [hnu]
  have hgammaRead : ch.gamma = nu 2 := by
    change wrappedPreIpaReads pnu 2 = nu 2
    rw [hnu]
  have hyRead : ch.y = nu 3 := by
    change wrappedPreIpaReads pnu 3 = nu 3
    rw [hnu]
  have hxRead : ch.x = nu 4 := by
    change wrappedPreIpaReads pnu 4 = nu 4
    rw [hnu]
  have hcharRaw : deployedX4PairCount (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1 ch <
        Zcash.Arithmetic.scalarFieldOrder := by
    rw [hvk basis, hI basis]
    simpa only [pnu, ch, ActionTerminal.adaptiveActionRunRecord] using hchar
  have hpolyStage (n : Fin 5) (id : CommitmentId)
      (havailable : adaptiveActionCommitmentActive (actionCircuit.shape.withProofParams pp)
        (ActionTerminal.vkAt basis) id →
        adaptiveActionCommitmentAvailable n id)
      (hterminal : id ≠ .vanishingH ∧ id ≠ .randomPoly) :
      actionPoly id = adaptiveActionCommitmentPolynomial pp basis inputs
        data.algebraicProof.erase (stageSource n) ch id := by
    have hraw := adaptiveAcceptedPolynomial_eq_actionStage_nonterminal pp family basis O
      inputs hvk hI hprovenance n id havailable hterminal pnu rfl witness hsrc rawDecode
      hbatches haccepts hcharRaw
    have htransport := acceptedPolynomial_transport (hI basis) (hvk basis)
      (rawDecode.reRound (runRounds family.toFamily basis O)) hcharRaw haccepts
    have hcombined := (congrFun htransport id).symm.trans hraw
    simpa only [actionPoly, decode, hacceptsAction, pnu, ch, data, stageSource,
      ActionTerminal.adaptiveActionRunRecord, ActionTerminal.adaptiveActionRunAccepts] using
      hcombined
  have hpolySurface (n : Fin 5) (id : CommitmentId)
      (havailable : adaptiveActionCommitmentActive (actionCircuit.shape.withProofParams pp)
        (ActionTerminal.vkAt basis) id →
        adaptiveActionCommitmentAvailable n id)
      (hterminal : id ≠ .vanishingH ∧ id ≠ .randomPoly) :
      actionPoly id = stagePoly n id := by
    exact (hpolyStage n id havailable hterminal).trans
      (adaptiveActionCommitmentPolynomial_challenge_congr pp basis inputs
        data.algebraicProof.erase (stageSource n) ch (stageCh n) id hterminal.1)
  have hcolumnAvailable (id : CommitmentId) (hid : id.isColumnInput) :
      adaptiveActionCommitmentActive (actionCircuit.shape.withProofParams pp)
        (ActionTerminal.vkAt basis) id →
        adaptiveActionCommitmentAvailable (0 : Fin 5) id := by
    intro hactive
    cases id <;>
      simp [CommitmentId.isColumnInput, adaptiveActionCommitmentAvailable] at hid ⊢
  have hpermutationAvailable (n : Fin 5) (hn1 : 1 ≤ (n : Nat))
      (id : CommitmentId) (hid : id.isPermutationInput) :
      adaptiveActionCommitmentActive (actionCircuit.shape.withProofParams pp)
        (ActionTerminal.vkAt basis) id →
        adaptiveActionCommitmentAvailable n id := by
    intro hactive
    cases id <;>
      simp [CommitmentId.isPermutationInput, adaptiveActionCommitmentAvailable] at hid ⊢
  have hlookupAvailable (n : Fin 5) (hn1 : 1 ≤ (n : Nat))
      (id : CommitmentId) (hid : id.isLookupInput) :
      adaptiveActionCommitmentActive (actionCircuit.shape.withProofParams pp)
        (ActionTerminal.vkAt basis) id →
        adaptiveActionCommitmentAvailable n id := by
    intro hactive
    cases id <;>
      simp [CommitmentId.isLookupInput, adaptiveActionCommitmentAvailable, hn1] at hid ⊢
  have hnonterminal (id : CommitmentId)
      (hid : id.isColumnInput ∨ id.isPermutationInput ∨ id.isLookupInput) :
      id ≠ .vanishingH ∧ id ≠ .randomPoly := by
    cases id <;> simp [CommitmentId.isColumnInput, CommitmentId.isPermutationInput,
      CommitmentId.isLookupInput] at hid ⊢
  have hs0 := hsurface (0 : Fin 5)
  have hthetaStage : nu 0 ∉
      TopLevelLookup.thetaBadSet actionCircuit pp
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) (stagePoly 0) := by
    simpa [adaptiveActionSurfaceAt, stagePoly, stageCh, stageSource] using hs0
  have hthetaSet := TopLevelLookup.thetaBadSet_congr
    actionCircuit pp (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)
    (poly₁ := actionPoly) (poly₂ := stagePoly 0) (fun id hid =>
      hpolySurface 0 id (hcolumnAvailable id hid) (hnonterminal id (Or.inl hid)))
  have htheta : ch.theta ∉
      TopLevelLookup.thetaBadSet actionCircuit pp
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) actionPoly := by
    rw [hthetaSet]
    simpa only [hthetaRead] using hthetaStage
  have hs1 := hsurface (1 : Fin 5)
  change nu 1 ∉ adaptiveActionSurfaceAt pp basis inputs 1
    data.algebraicProof.erase (stageSource 1)
      (fun i => nu (i.castLE (by omega))) at hs1
  let betaNu : Fin 11 → Fp := fun i =>
    if _h : (i : Nat) < 1 then nu ⟨i, by omega⟩ else 0
  let betaCh : Challenges (actionCircuit.shape.withProofParams pp).k Fp :=
    chRecord betaNu (fun _ => 0)
  have hbetaCh : betaCh = stageCh 1 := by
    unfold betaCh stageCh
    apply congrArg (fun f : Fin 11 → Fp => chRecord f (fun _ => 0))
    funext i
    simp [betaNu]
  have hbetaSurface : nu 1 ∉
      (↑(allResolverPermutationBetaBadSet pp.numProofs (ActionTerminal.vkAt basis)
          (adaptiveActionCommitmentPolynomial pp basis inputs data.algebraicProof.erase
            (stageSource 1) betaCh) actionActiveRows) : Set Fp) ∪
        (↑(allResolverLookupBetaBadSet
          pp.numProofs (ActionTerminal.vkAt basis)
          (ActionTerminal.semanticChRecord betaCh.theta 0
            (k := (actionCircuit.shape.withProofParams pp).k))
          (adaptiveActionCommitmentPolynomial pp basis inputs data.algebraicProof.erase
            (stageSource 1) betaCh)
          (actionCircuit.n -
            actionCircuit.blindingFactors - 2)) : Set Fp) := by
    simpa [adaptiveActionSurfaceAt, betaNu, betaCh] using hs1
  have hbetaStage : nu 1 ∉
      (↑(allResolverPermutationBetaBadSet pp.numProofs (ActionTerminal.vkAt basis)
          (stagePoly 1) actionActiveRows) : Set Fp) ∪
        (↑(allResolverLookupBetaBadSet
          pp.numProofs (ActionTerminal.vkAt basis)
          (ActionTerminal.semanticChRecord (nu 0) 0
            (k := (actionCircuit.shape.withProofParams pp).k)) (stagePoly 1)
          (actionCircuit.n -
            actionCircuit.blindingFactors - 2)) : Set Fp) := by
    rw [hbetaCh] at hbetaSurface
    simpa [stagePoly, stageCh] using hbetaSurface
  rw [Set.mem_union, not_or] at hbetaStage
  have hbetaPermSet := allResolverPermutationBetaBadSet_congr
    pp.numProofs (ActionTerminal.vkAt basis) actionActiveRows
      (poly₁ := actionPoly) (poly₂ := stagePoly 1) (fun id hid =>
      hpolySurface 1 id (hpermutationAvailable 1 (by omega) id hid)
          (hnonterminal id (Or.inr (Or.inl hid))))
  have hbetaPerm : ch.beta ∉ allResolverPermutationBetaBadSet
      pp.numProofs (ActionTerminal.vkAt basis) actionPoly actionActiveRows := by
    rw [hbetaPermSet]
    simpa only [hbetaRead] using hbetaStage.1
  have hbetaLookupSet := allResolverLookupBetaBadSet_congr
    pp.numProofs (ActionTerminal.vkAt basis)
      (actionCircuit.n -
        actionCircuit.blindingFactors - 2)
      (ch₁ := ch) (ch₂ := ActionTerminal.semanticChRecord (nu 0) 0
        (k := (actionCircuit.shape.withProofParams pp).k))
      (by simpa using hthetaRead)
      (fun id hid => hpolySurface 1 id (hlookupAvailable 1 (by omega) id hid)
        (hnonterminal id (Or.inr (Or.inr hid))))
  have hbetaLookup : ch.beta ∉ allResolverLookupBetaBadSet
      pp.numProofs
      (ActionTerminal.vkAt basis) ch actionPoly
      (actionCircuit.n -
        actionCircuit.blindingFactors - 2) := by
    rw [hbetaLookupSet]
    simpa only [hbetaRead] using hbetaStage.2
  have hs2 := hsurface (2 : Fin 5)
  change nu 2 ∉ adaptiveActionSurfaceAt pp basis inputs 2
    data.algebraicProof.erase (stageSource 2)
      (fun i => nu (i.castLE (by omega))) at hs2
  let gammaNu : Fin 11 → Fp := fun i =>
    if _h : (i : Nat) < 2 then nu ⟨i, by omega⟩ else 0
  let gammaCh : Challenges (actionCircuit.shape.withProofParams pp).k Fp :=
    chRecord gammaNu (fun _ => 0)
  have hgammaCh : gammaCh = stageCh 2 := by
    unfold gammaCh stageCh
    apply congrArg (fun f : Fin 11 → Fp => chRecord f (fun _ => 0))
    funext i
    simp [gammaNu]
  have hgammaSurface : nu 2 ∉
      (↑(allResolverPermutationGammaBadSet pp.numProofs (ActionTerminal.vkAt basis)
          (ActionTerminal.semanticChRecord gammaCh.theta gammaCh.beta
            (k := (actionCircuit.shape.withProofParams pp).k))
          (adaptiveActionCommitmentPolynomial pp basis inputs data.algebraicProof.erase
            (stageSource 2) gammaCh) actionActiveRows) : Set Fp) ∪
        (↑(allResolverLookupGammaBadSet
          pp.numProofs (ActionTerminal.vkAt basis)
          (ActionTerminal.semanticChRecord gammaCh.theta gammaCh.beta
            (k := (actionCircuit.shape.withProofParams pp).k))
          (adaptiveActionCommitmentPolynomial pp basis inputs data.algebraicProof.erase
            (stageSource 2) gammaCh)
          (actionCircuit.n -
            actionCircuit.blindingFactors - 2)) : Set Fp) := by
    simpa [adaptiveActionSurfaceAt, gammaNu, gammaCh] using hs2
  have hgammaStage : nu 2 ∉
      (↑(allResolverPermutationGammaBadSet pp.numProofs (ActionTerminal.vkAt basis)
          (ActionTerminal.semanticChRecord (nu 0) (nu 1)
            (k := (actionCircuit.shape.withProofParams pp).k)) (stagePoly 2)
          actionActiveRows) : Set Fp) ∪
        (↑(allResolverLookupGammaBadSet
          pp.numProofs (ActionTerminal.vkAt basis)
          (ActionTerminal.semanticChRecord (nu 0) (nu 1)
            (k := (actionCircuit.shape.withProofParams pp).k)) (stagePoly 2)
          (actionCircuit.n -
            actionCircuit.blindingFactors - 2)) : Set Fp) := by
    rw [hgammaCh] at hgammaSurface
    simpa [stagePoly, stageCh] using hgammaSurface
  rw [Set.mem_union, not_or] at hgammaStage
  have hgammaPermSet := allResolverPermutationGammaBadSet_congr
    pp.numProofs (ActionTerminal.vkAt basis) actionActiveRows
      (ch₁ := ch) (ch₂ := ActionTerminal.semanticChRecord (nu 0) (nu 1)
        (k := (actionCircuit.shape.withProofParams pp).k))
      (by simpa using hbetaRead)
      (poly₁ := actionPoly) (poly₂ := stagePoly 2) (fun id hid =>
        hpolySurface 2 id (hpermutationAvailable 2 (by omega) id hid)
          (hnonterminal id (Or.inr (Or.inl hid))))
  have hgammaPerm : ch.gamma ∉ allResolverPermutationGammaBadSet
      pp.numProofs (ActionTerminal.vkAt basis) ch actionPoly actionActiveRows := by
    rw [hgammaPermSet]
    simpa only [hgammaRead] using hgammaStage.1
  have hgammaLookupSet := allResolverLookupGammaBadSet_congr
    pp.numProofs (ActionTerminal.vkAt basis)
      (actionCircuit.n -
        actionCircuit.blindingFactors - 2)
      (ch₁ := ch) (ch₂ := ActionTerminal.semanticChRecord (nu 0) (nu 1)
        (k := (actionCircuit.shape.withProofParams pp).k))
      (by simpa using hthetaRead)
      (by simpa using hbetaRead)
      (fun id hid => hpolySurface 2 id (hlookupAvailable 2 (by omega) id hid)
        (hnonterminal id (Or.inr (Or.inr hid))))
  have hgammaLookup : ch.gamma ∉ allResolverLookupGammaBadSet
      pp.numProofs
      (ActionTerminal.vkAt basis) ch actionPoly
      (actionCircuit.n -
        actionCircuit.blindingFactors - 2) := by
    rw [hgammaLookupSet]
    simpa only [hgammaRead] using hgammaStage.2
  have hallAvailable (n : Fin 5) (hn3 : 3 ≤ (n : Nat)) (id : CommitmentId)
      (hvanishing : id ≠ .vanishingH) (hrandom : id ≠ .randomPoly) :
      adaptiveActionCommitmentActive (actionCircuit.shape.withProofParams pp)
        (ActionTerminal.vkAt basis) id →
        adaptiveActionCommitmentAvailable n id := by
    intro hactive
    have hn1 : 1 ≤ (n : Nat) := Nat.le_trans (by decide) hn3
    cases id <;>
      simp [adaptiveActionCommitmentAvailable, hn1, hn3] at hvanishing hrandom ⊢
  have hmodelStage (n : Fin 5) (hn3 : 3 ≤ (n : Nat)) : actionModel =
      adaptiveActionCommittedModel pp basis inputs data.algebraicProof.erase
        (stageSource n) (stageCh n) := by
    have hfull : actionModel = adaptiveActionCommittedModel pp basis inputs
        data.algebraicProof.erase (stageSource n) ch := by
      unfold actionModel adaptiveActionCommittedModel
      exact VerifyingKey.constraintModel_congr_nonterminal
        pp.numProofs (ActionTerminal.vkAt basis) ch _ _ _ (fun id hv hr =>
          hpolyStage n id (hallAvailable n hn3 id hv hr) ⟨hv, hr⟩)
    have h0n : (0 : Nat) < (n : Nat) := lt_of_lt_of_le (by decide) hn3
    have h1n : (1 : Nat) < (n : Nat) := lt_of_lt_of_le (by decide) hn3
    have h2n : (2 : Nat) < (n : Nat) := lt_of_lt_of_le (by decide) hn3
    have hthetaStageCh : ch.theta = (stageCh n).theta := by
      calc
        ch.theta = nu 0 := hthetaRead
        _ = (stageCh n).theta := by
          change nu 0 = if _h : (0 : Nat) < (n : Nat) then nu 0 else 0
          rw [dif_pos h0n]
    have hbetaStageCh : ch.beta = (stageCh n).beta := by
      calc
        ch.beta = nu 1 := hbetaRead
        _ = (stageCh n).beta := by
          change nu 1 = if _h : (1 : Nat) < (n : Nat) then nu 1 else 0
          rw [dif_pos h1n]
    have hgammaStageCh : ch.gamma = (stageCh n).gamma := by
      calc
        ch.gamma = nu 2 := hgammaRead
        _ = (stageCh n).gamma := by
          change nu 2 = if _h : (2 : Nat) < (n : Nat) then nu 2 else 0
          rw [dif_pos h2n]
    exact hfull.trans (adaptiveActionCommittedModel_challenge_congr pp basis inputs
      data.algebraicProof.erase (stageSource n) ch (stageCh n)
      hthetaStageCh hbetaStageCh hgammaStageCh)
  have hs3 := hsurface (3 : Fin 5)
  change nu 3 ∉ adaptiveActionSurfaceAt pp basis inputs 3
    data.algebraicProof.erase (stageSource 3)
      (fun i => nu (i.castLE (by omega))) at hs3
  let yNu : Fin 11 → Fp := fun i =>
    if _h : (i : Nat) < 3 then nu ⟨i, by omega⟩ else 0
  let yCh : Challenges (actionCircuit.shape.withProofParams pp).k Fp :=
    chRecord yNu (fun _ => 0)
  have hyCh : yCh = stageCh 3 := by
    unfold yCh stageCh
    apply congrArg (fun f : Fin 11 → Fp => chRecord f (fun _ => 0))
    funext i
    simp [yNu]
  have hySurface : nu 3 ∉ ⋃ j,
      ↑(szBadSet (foldSplitWitness
        (adaptiveActionCommittedModel pp basis inputs data.algebraicProof.erase
          (stageSource 3) yCh).constraints
        actionCircuit.n j)) := by
    simpa [adaptiveActionSurfaceAt, yNu, yCh] using hs3
  have hyStage : nu 3 ∉ ⋃ j,
      ↑(szBadSet (foldSplitWitness
        (adaptiveActionCommittedModel pp basis inputs data.algebraicProof.erase
          (stageSource 3) (stageCh 3)).constraints
        actionCircuit.n j)) := by
    rw [hyCh] at hySurface
    exact hySurface
  have hy : ∀ j, ch.y ∉ szBadSet
      (foldSplitWitness actionModel.constraints actionCircuit.n j) := by
    intro j hj
    apply hyStage
    apply Set.mem_iUnion.mpr
    refine ⟨j, ?_⟩
    rw [← hmodelStage 3 (by omega)]
    simpa only [hyRead] using hj
  have hs4 := hsurface (4 : Fin 5)
  change nu 4 ∉ adaptiveActionSurfaceAt pp basis inputs 4
    data.algebraicProof.erase (stageSource 4)
      (fun i => nu (i.castLE (by omega))) at hs4
  let xNu : Fin 11 → Fp := fun i =>
    if _h : (i : Nat) < 4 then nu ⟨i, by omega⟩ else 0
  let xCh : Challenges (actionCircuit.shape.withProofParams pp).k Fp :=
    chRecord xNu (fun _ => 0)
  have hxCh : xCh = stageCh 4 := by
    unfold xCh stageCh
    apply congrArg (fun f : Fin 11 → Fp => chRecord f (fun _ => 0))
    funext i
    simp [xNu]
  have hxSurface : nu 4 ∉ szBadSet
      (adaptiveActionPreXDifference pp basis inputs data.algebraicProof.erase
      (stageSource 4) xCh) := by
    simpa [adaptiveActionSurfaceAt, xNu, xCh] using hs4
  have hxStage : nu 4 ∉ szBadSet
      (adaptiveActionPreXDifference pp basis inputs data.algebraicProof.erase
        source (stageCh 4)) := by
    rw [hxCh] at hxSurface
    have hsource4 : stageSource 4 = source := by
      exact data.algebraicProof.actionRepresentationsBefore_four_append
        (family.fixedRepresentations basis)
    rw [hsource4] at hxSurface
    exact hxSurface
  have hdiff := adaptiveActionPreXDifference_challenge_congr pp basis inputs
    data.algebraicProof.erase source ch (stageCh 4)
    (by simpa [stageCh] using hthetaRead)
    (by simpa [stageCh] using hbetaRead)
    (by simpa [stageCh] using hgammaRead)
    (by simpa [stageCh] using hyRead)
  have hx : ch.x ∉ szBadSet (adaptiveActionPreXDifference pp basis inputs
      data.algebraicProof.erase source ch) := by
    rw [hdiff]
    simpa only [hxRead] using hxStage
  exact ⟨hx, hy, ⟨hgammaPerm, hbetaPerm⟩,
    ⟨hgammaLookup, hbetaLookup, htheta⟩⟩

/-- Outside the executable representation and quotient-coordinate branches, the accepted
`x`-dependent quotient check and the fixed pre-`x` constraint difference have the same value at
the sampled `x`. -/
theorem adaptiveActionAcceptedDifference_eval_eq_preX
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10 +
        3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (hvk : ∀ basis, family.vk basis = actionCircuit.toVerifierKey
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
    (hI : ∀ basis, family.instanceCommitment basis =
      actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
    (hprovenance : family.adaptiveActionRepresentationRelationFinder basis O = none)
    (witness : DeployedBatchWitness family.toFamily basis
      (ActionTerminal.adaptiveActionRunOutput family basis O))
    (hsrc : witness.fixedRepresentations = family.fixedRepresentations basis)
    (rawDecode : DeployedAlgebraicDecode
      (actionCircuit.shape.withProofParams pp)
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) rfl
      (family.vk basis) (family.instanceCommitment basis)
      (ActionTerminal.adaptiveActionRunOutput family basis O).1.proof.1
      (wrappedPreIpaRecord (ActionTerminal.adaptiveActionRunOutput family basis O))
      ((ActionTerminal.adaptiveActionRunOutput family basis O).1.aMulti
        (wrappedPreIpaReads (ActionTerminal.adaptiveActionRunOutput family basis O)))
      ((ActionTerminal.adaptiveActionRunOutput family basis O).1.multiU
        (wrappedPreIpaReads (ActionTerminal.adaptiveActionRunOutput family basis O)))
      ((ActionTerminal.adaptiveActionRunOutput family basis O).1.multiBlind
        (wrappedPreIpaReads (ActionTerminal.adaptiveActionRunOutput family basis O))))
    (hbatches : rawDecode.batches = witness.batches)
    (haccepts : ActionTerminal.adaptiveActionAccepts family basis O)
    (hchar : deployedX4PairCount
      (actionCircuit.toVerifierKey
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis))
      (actionCircuit.instanceCommitment (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) inputs)
      (ActionTerminal.adaptiveActionRunOutput family basis O).1.proof.1
      (wrappedPreIpaRecord (ActionTerminal.adaptiveActionRunOutput family basis O)) <
        Zcash.Arithmetic.scalarFieldOrder) :
    let _pnu := ActionTerminal.adaptiveActionRunOutput family basis O
    let ch := ActionTerminal.adaptiveActionRunRecord family basis O
    let data := (family.adversary basis).run O
    let source := data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis)
    let _piecePoly := fun i => onlinePointPolynomial source (data.algebraicProof.hPieces i).point
    let decode := hI basis ▸ hvk basis ▸
      rawDecode.reRound (runRounds family.toFamily basis O)
    let hacceptsAction := ActionTerminal.adaptiveActionRunAccepts
      pp family basis O inputs hvk hI haccepts
    let actionModel := CanonicalMemberConstraintRelation.acceptedModel
      (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
      (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
        (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)) hacceptsAction
    let actionPoly := CanonicalMemberConstraintRelation.acceptedPolynomial
      (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) hacceptsAction
    (combineConstraints actionModel.fixedCols actionModel.adviceCols actionModel.instanceCols
        actionModel.gates actionModel.sets actionModel.chunks actionModel.lookups
        actionModel.beta actionModel.gamma actionModel.delta actionModel.theta ch.y
        actionModel.chunkLen actionModel.l0 actionModel.lLast actionModel.lBlind -
      actionPoly .vanishingH * (X ^ actionCircuit.n - 1)).eval ch.x =
    (adaptiveActionPreXDifference pp basis inputs data.algebraicProof.erase source ch).eval
      ch.x := by
  simp only
  let pnu := ActionTerminal.adaptiveActionRunOutput family basis O
  let ch := ActionTerminal.adaptiveActionRunRecord family basis O
  let data := (family.adversary basis).run O
  let source := data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis)
  let piecePoly := fun i => onlinePointPolynomial source (data.algebraicProof.hPieces i).point
  let decode := hI basis ▸ hvk basis ▸
    rawDecode.reRound (runRounds family.toFamily basis O)
  let hacceptsAction := ActionTerminal.adaptiveActionRunAccepts
    pp family basis O inputs hvk hI haccepts
  let actionModel := CanonicalMemberConstraintRelation.acceptedModel
    (memberDecode := fun i hi => decode.toMemberDecode hchar i hi)
    (hblinding := actionCircuit.toVerifierKey_blindingFactors_lt_n
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis)) hacceptsAction
  let actionPoly := CanonicalMemberConstraintRelation.acceptedPolynomial
    (memberDecode := fun i hi => decode.toMemberDecode hchar i hi) hacceptsAction
  have hcharRaw : deployedX4PairCount (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1 ch <
        Zcash.Arithmetic.scalarFieldOrder := by
    rw [hvk basis, hI basis]
    simpa only [pnu, ch, ActionTerminal.adaptiveActionRunRecord] using hchar
  have hacceptsFull : DeployedAccepts
      (actionCircuit.shape.withProofParams pp)
      (ursOfAugmentedBasis (actionCircuit.shape.withProofParams pp).k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      ch := by
    simpa only [ActionTerminal.adaptiveActionAccepts, pnu, ch,
      ActionTerminal.adaptiveActionRunRecord] using haccepts
  have hvanishingRaw := family.adaptiveAcceptedVanishing_eq_fullQuotient basis O
    (runRounds family.toFamily basis O)
    (family.adaptiveActionRepresentationRelationFinder_none_quotient basis O hprovenance)
    pnu rfl witness hsrc rawDecode hbatches hacceptsFull hcharRaw
  have hvanishing : (actionPoly .vanishingH).eval ch.x =
      (committedPreXQuotient (ActionTerminal.vkAt basis) piecePoly).eval ch.x := by
    have hp : pnu.1 = data.toAlgebraicWfProof :=
      (wrappedAdversary_run_fst family.toFamily basis O).trans
        (family.toFamily_runProof basis O)
    have hrawTarget :
        (committedPreXQuotient (family.vk basis)
          (fun i => onlinePointPolynomial
            (pnu.1.algebraicProof.preX1AssemblySource
              (family.fixedRepresentations basis))
            (pnu.1.algebraicProof.hPieces i).point)).eval ch.x =
          (committedPreXQuotient (ActionTerminal.vkAt basis) piecePoly).eval ch.x := by
      calc
        _ = (committedPreXQuotient (family.vk basis) piecePoly).eval ch.x := by
          rw [hp]
          simp only [OnlineMemberProofData.toAlgebraicWfProof_algebraicProof]
          rfl
        _ = (committedPreXQuotient (ActionTerminal.vkAt basis) piecePoly).eval
              ch.x := by
          exact congrArg
            (fun vk => (committedPreXQuotient vk piecePoly).eval ch.x) (hvk basis)
    have htransport := acceptedPolynomial_transport (hI basis) (hvk basis)
      (rawDecode.reRound (runRounds family.toFamily basis O)) hcharRaw hacceptsFull
    have htransportEval := congrArg
      (fun polynomial : CommitmentId → CPoly =>
        (polynomial .vanishingH).eval ch.x) htransport
    have hcombined := htransportEval.symm.trans (hvanishingRaw.trans hrawTarget)
    simpa only [actionPoly, decode, hacceptsAction, pnu, ch,
      ActionTerminal.adaptiveActionRunRecord,
      ActionTerminal.adaptiveActionRunAccepts] using hcombined
  have hpolyStage : ∀ id, id ≠ .vanishingH → id ≠ .randomPoly →
      actionPoly id = adaptiveActionCommitmentPolynomial pp basis inputs
        data.algebraicProof.erase
        (data.algebraicProof.actionRepresentationsBefore (4 : Fin 5) ++
          family.fixedRepresentations basis) ch id := by
    intro id hvanishing hrandom
    have havailable : adaptiveActionCommitmentActive (actionCircuit.shape.withProofParams pp)
        (ActionTerminal.vkAt basis) id →
        adaptiveActionCommitmentAvailable (4 : Fin 5) id := by
      intro hactive
      cases id <;>
        simp [adaptiveActionCommitmentAvailable] at hvanishing hrandom ⊢
    have hraw := adaptiveAcceptedPolynomial_eq_actionStage_nonterminal pp family basis O
      inputs hvk hI hprovenance (4 : Fin 5) id havailable ⟨hvanishing, hrandom⟩
      pnu rfl witness hsrc rawDecode hbatches (by
        simpa only [ActionTerminal.adaptiveActionAccepts, pnu, ch,
          ActionTerminal.adaptiveActionRunRecord] using haccepts) hcharRaw
    have htransport := acceptedPolynomial_transport (hI basis) (hvk basis)
      (rawDecode.reRound (runRounds family.toFamily basis O)) hcharRaw (by
        simpa only [ActionTerminal.adaptiveActionAccepts, pnu, ch,
          ActionTerminal.adaptiveActionRunRecord] using haccepts)
    have hcombined := (congrFun htransport id).symm.trans hraw
    simpa only [actionPoly, decode, hacceptsAction, pnu, ch, data,
      ActionTerminal.adaptiveActionRunRecord,
      ActionTerminal.adaptiveActionRunAccepts] using hcombined
  have hmodelStage : actionModel = adaptiveActionCommittedModel pp basis inputs
      data.algebraicProof.erase
      (data.algebraicProof.actionRepresentationsBefore (4 : Fin 5) ++
        family.fixedRepresentations basis) ch := by
    unfold actionModel adaptiveActionCommittedModel adaptiveActionCommittedModelOf
    exact VerifyingKey.constraintModel_congr_nonterminal
      pp.numProofs (ActionTerminal.vkAt basis) ch _ _ _ hpolyStage
  have hsource4 :
      data.algebraicProof.actionRepresentationsBefore (4 : Fin 5) ++
          family.fixedRepresentations basis = source := by
    exact data.algebraicProof.actionRepresentationsBefore_four_append
      (family.fixedRepresentations basis)
  have hmodel : actionModel = adaptiveActionCommittedModel pp basis inputs
      data.algebraicProof.erase source ch := by
    rw [← hsource4]
    exact hmodelStage
  have hpiecePoly : piecePoly = fun i =>
      onlinePointPolynomial source (data.algebraicProof.erase.hPieces i) := by
    rfl
  change (combineConstraints actionModel.fixedCols actionModel.adviceCols
      actionModel.instanceCols actionModel.gates actionModel.sets actionModel.chunks
      actionModel.lookups actionModel.beta actionModel.gamma actionModel.delta actionModel.theta
      ch.y actionModel.chunkLen actionModel.l0 actionModel.lLast actionModel.lBlind -
    actionPoly .vanishingH * (X ^ actionCircuit.n - 1)).eval
      ch.x =
    (adaptiveActionPreXDifference pp basis inputs data.algebraicProof.erase source ch).eval ch.x
  rw [hmodel]
  simp only [CPolynomial.eval_sub, CPolynomial.eval_mul]
  rw [hvanishing]
  rw [hpiecePoly]
  rw [adaptiveActionPreXDifference_eq]
  simp only [CPolynomial.eval_sub, CPolynomial.eval_mul, ActionTerminal.vkAt,
    actionCircuit.toVerifierKey_n]

end ComputedAdaptiveOnlineAGMFSFamily

/-- Restrict the generic pre-IPA earlier-answer vector to the first five Action squeezes. -/
def adaptiveActionEarlier (n : Fin 5)
    (earlier : Fin ((Fin.castLE (by omega) n : Fin 11) : Nat) → Fp) :
    Fin (n : Nat) → Fp :=
  fun i => earlier ⟨i, by simp⟩

/-- Decode a semantic surface at an actual algebraic pre-IPA prefix without unfolding the
surface itself. -/
theorem adaptivePrefixBad_algebraicFullPrefixesPre
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    (init : List (TranscriptElt Fp VestaG))
    (n : Fin 11)
    (p : AlgebraicWfProof basis vk instanceCommitment)
    (badF : BTranscript Fp VestaG
        (preIpaLen shape init.length 10 + 3 * shape.k) →
      (Fin (n : Nat) → Fp) → Set Fp)
    (O : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k) → Fp) :
    adaptivePrefixBad (shape := shape) init n badF
        (algebraicFullPrefixesPre init p n) O =
      badF (algebraicFullPrefixesPre init p n)
        (fun i => O (algebraicFullPrefixesPre init p
          (i.castLE (le_of_lt n.isLt)))) := by
  unfold adaptivePrefixBad
  have hlen : (algebraicFullPrefixesPre init p n).val.length =
      preIpaLen shape init.length n := by
    exact preIpaSqueezePoints_length_eq init p.proof.1 p.proof.2 n
  rw [if_pos hlen]
  congr 1
  funext i
  exact congrArg O
    (adaptiveEarlierPrefix_algebraicFullPrefixesPre init p n i)

/-- The final-output semantic event at one of the five Action squeezes, decoded through the same
strict-prefix wrapper used by the arbitrary-adaptive squeeze theorem. -/
def adaptiveFinalActionBad
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (n : Fin 5)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (t : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10 +
        3 * (actionCircuit.shape.withProofParams pp).k))
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10 +
        3 * (actionCircuit.shape.withProofParams pp).k) → Fp) : Set Fp :=
  adaptivePrefixBad (shape := actionCircuit.shape.withProofParams pp) family.init
    (Fin.castLE (by omega) n)
    (fun t earlier => adaptiveFallbackActionSurface pp family inputs basis n data t
      (adaptiveActionEarlier n earlier)) t O

/-- At the verifier's actual Action squeeze, the generic first-query surface is exactly the
stage-local semantic bad set instantiated with the genuine earlier oracle answers. -/
theorem OnlineMemberProofData.adaptiveFinalActionBad_eq_surface
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (n : Fin 5)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10 +
        3 * (actionCircuit.shape.withProofParams pp).k) → Fp) :
    adaptiveFinalActionBad pp family inputs basis n data
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof
          (Fin.castLE (by omega) n)) O =
      adaptiveActionSurfaceAt pp basis inputs n data.algebraicProof.erase
        (data.algebraicProof.actionRepresentationsBefore n ++
          family.fixedRepresentations basis)
        (fun i => O (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof
          (i.castLE (by omega)))) := by
  unfold adaptiveFinalActionBad
  rw [adaptivePrefixBad_algebraicFullPrefixesPre]
  unfold adaptiveFallbackActionSurface
  congr 1

/-- Every Action semantic squeeze of a bare malicious adaptive online-AGM adversary is priced at
its first actual annotated query (or the fresh verifier fallback), unless the executable Action
provenance finder has already produced a DLOG relation. -/
theorem ComputedAdaptiveOnlineAGMFSFamily.adaptiveFinalActionBadWithoutRelation_table_le
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (n : Fin 5) {epsilon : ENNReal}
    (hsurface : ∀
      (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
      (_hwf : PsWellFormed ps)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (n : Nat) → Fp),
      uniformChallenge.toOuterMeasure
          (adaptiveActionSurfaceAt pp basis inputs n ps source earlier) ≤ epsilon) :
    (PMF.uniformOfFintype (BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10 +
        3 * (actionCircuit.shape.withProofParams pp).k) → Fp)).toOuterMeasure
      {O | let data := (family.adversary basis).run O
        let n11 : Fin 11 := Fin.castLE (by omega) n
        let t := (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof) n11
        O t ∈ adaptiveFinalActionBad pp family inputs basis n data t O ∧
          family.adaptiveActionRepresentationRelationFinder basis O = none} ≤
      (family.Q + 1 : Nat) * epsilon := by
  apply family.adaptiveFinalPrefixBadWithoutRelation_table_le basis (Fin.castLE (by omega) n)
    (adaptiveFinalActionBad pp family inputs basis n)
    (family.adaptiveActionRepresentationRelationFinder basis)
    (fun t label earlier => adaptiveQueriedActionSurface pp family inputs basis n t label
      (adaptiveActionEarlier n earlier))
    (fun data t earlier => adaptiveFallbackActionSurface pp family inputs basis n data t
      (adaptiveActionEarlier n earlier))
  · intro O
    dsimp only
    intro hbad hnone
    let data := (family.adversary basis).run O
    let t := (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof)
      (Fin.castLE (by omega) n)
    change O t ∈ adaptiveFinalActionBad pp family inputs basis n data t O at hbad
    change O t ∈ LabeledOracleComp.firstLabelOrFallbackBad (family.adversary basis)
      (fun t label O => adaptiveLabeledPrefixBad (shape := actionCircuit.shape.withProofParams pp)
        family.init basis (Fin.castLE (by omega) n)
          (fun t label earlier => adaptiveQueriedActionSurface pp family inputs basis n t label
            (adaptiveActionEarlier n earlier))
          t label O)
      (fun data t O => adaptivePrefixBad (shape := actionCircuit.shape.withProofParams pp)
        family.init (Fin.castLE (by omega) n)
          (fun t earlier => adaptiveFallbackActionSurface pp family inputs basis n data t
            (adaptiveActionEarlier n earlier)) t O)
      t O
    have hlen : t.val.length =
        preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length
          (Fin.castLE (by omega) n) := by
      exact preIpaSqueezePoints_length_eq family.init data.algebraicProof.erase
        data.wellFormed (Fin.castLE (by omega) n)
    unfold LabeledOracleComp.firstLabelOrFallbackBad
    cases hfind : (family.adversary basis).findLabel O t with
    | none =>
        simpa only [adaptiveFinalActionBad] using hbad
    | some label =>
        have hat := family.adaptiveActionRepresentationRelationFinder_none_at
          basis O hnone n
        have hlocal : selectedQueryRepresentationRelation? t (family.adversary basis) O
            (data.algebraicProof.actionRepresentationsBefore n) (by
              intro ap hap
              change ap.point ∈ transcriptGroupPoints
                (preIpaSqueezePoints family.init data.algebraicProof.erase
                  (Fin.castLE (by omega) n))
              exact data.algebraicProof.actionRepresentationsBefore_covered
                family.init data.wellFormed n ap hap) = none := by
          simpa only [
            ComputedAdaptiveOnlineAGMFSFamily.adaptiveActionRepresentationRelationAt?, data, t]
            using hat
        have hprov := selectedQueryRepresentationRelation?_eq_none t
          (family.adversary basis) O (data.algebraicProof.actionRepresentationsBefore n) _ hlocal
        cases hprov with
        | inl hfresh => simp [hfind] at hfresh
        | inr pinned =>
            have hlabel : pinned.query = label := by
              exact Option.some.inj (pinned.found.symm.trans hfind)
            subst label
            have hdecode := decodePreIpaPrefix?_isSome family.init (Fin.castLE (by omega) n)
              data.toAlgebraicWfProof.proof
            change (decodePreIpaPrefix? (shape := actionCircuit.shape.withProofParams pp)
              family.init (Fin.castLE (by omega) n) t).isSome at hdecode
            cases hdec : decodePreIpaPrefix? (shape := actionCircuit.shape.withProofParams pp)
                family.init (Fin.castLE (by omega) n) t with
            | none => simp [hdec] at hdecode
            | some decoded =>
                have hsource := adaptiveActionQuerySource_eq_of_pinned
                  family basis n O decoded pinned
                have hprefixBounded : fullPrefixesPre family.init decoded.proof
                      (Fin.castLE (by omega) n) =
                    fullPrefixesPre family.init data.toAlgebraicWfProof.proof
                      (Fin.castLE (by omega) n) :=
                  decoded.point_eq
                have hprefix : preIpaSqueezePoints family.init decoded.proof.1
                      (Fin.castLE (by omega) n) =
                    preIpaSqueezePoints family.init data.algebraicProof.erase
                      (Fin.castLE (by omega) n) :=
                  congrArg Subtype.val hprefixBounded
                change O t ∈ adaptivePrefixBad
                  (shape := actionCircuit.shape.withProofParams pp) family.init
                    (Fin.castLE (by omega) n)
                    (fun t earlier => adaptiveFallbackActionSurface pp family inputs basis n data t
                      (adaptiveActionEarlier n earlier)) t O at hbad
                unfold adaptivePrefixBad at hbad
                rw [if_pos hlen] at hbad
                unfold adaptiveLabeledPrefixBad
                simp only [if_pos hlen]
                have hsurfaceEq : adaptiveQueriedActionSurface pp family inputs basis n t
                    pinned.query (adaptiveActionEarlier n (fun i => O (adaptiveEarlierPrefix
                      (shape := actionCircuit.shape.withProofParams pp) family.init t
                        (i.castLE (le_of_lt (Fin.castLE (by omega) n).isLt))))) =
                    adaptiveFallbackActionSurface pp family inputs basis n data t
                      (adaptiveActionEarlier n (fun i => O (adaptiveEarlierPrefix
                        (shape := actionCircuit.shape.withProofParams pp) family.init t
                          (i.castLE (le_of_lt (Fin.castLE (by omega) n).isLt))))) := by
                  unfold adaptiveQueriedActionSurface
                  dsimp only
                  split
                  · rename_i hnone
                    have hdecode' := decodePreIpaPrefix?_isSome family.init
                      (⟨n, by omega⟩ : Fin 11) data.toAlgebraicWfProof.proof
                    change (decodePreIpaPrefix? (shape := actionCircuit.shape.withProofParams pp)
                      family.init (⟨n, by omega⟩ : Fin 11) t).isSome at hdecode'
                    rw [hnone] at hdecode'
                    simp at hdecode'
                  · rename_i decoded' hsome
                    have hsource' := adaptiveActionQuerySource_eq_of_pinned
                      family basis n O decoded' pinned
                    have hprefixBounded' : fullPrefixesPre family.init decoded'.proof
                          (Fin.castLE (by omega) n) =
                        fullPrefixesPre family.init data.toAlgebraicWfProof.proof
                          (Fin.castLE (by omega) n) :=
                      decoded'.point_eq
                    have hprefix' : preIpaSqueezePoints family.init decoded'.proof.1
                          (Fin.castLE (by omega) n) =
                        preIpaSqueezePoints family.init data.algebraicProof.erase
                          (Fin.castLE (by omega) n) :=
                      congrArg Subtype.val hprefixBounded'
                    unfold adaptiveFallbackActionSurface
                    rw [hsource']
                    apply adaptiveActionSurfaceAt_congr pp family.init basis inputs n
                      decoded'.proof.1 data.algebraicProof.erase decoded'.proof.2 data.wellFormed
                      _ _ _ hprefix' rfl
                rw [hsurfaceEq]
                exact hbad
  · intro t label earlier
    unfold adaptiveQueriedActionSurface
    dsimp only
    split
    · simp
    · rename_i decoded hdecoded
      exact hsurface decoded.proof.1 decoded.proof.2 _ (adaptiveActionEarlier n earlier)
  · intro data t earlier
    exact hsurface data.algebraicProof.erase data.wellFormed _
      (adaptiveActionEarlier n earlier)

/-- One actual Action semantic bad event, excluding the executable stage-provenance relation. -/
def ComputedAdaptiveOnlineAGMFSFamily.adaptiveActionBadWithoutRelation
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (n : Fin 5) :
    Set (BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10 +
        3 * (actionCircuit.shape.withProofParams pp).k) → Fp) :=
  {O | let data := (family.adversary basis).run O
    let n11 : Fin 11 := Fin.castLE (by omega) n
    let t := algebraicFullPrefixesPre family.init data.toAlgebraicWfProof n11
    O t ∈ adaptiveFinalActionBad pp family inputs basis n data t O ∧
      family.adaptiveActionRepresentationRelationFinder basis O = none}

/-- With the provenance branch fixed to `none`, membership in the priced run-level event is
exactly membership of the actual challenge in its stage-local semantic surface. -/
theorem ComputedAdaptiveOnlineAGMFSFamily.mem_adaptiveActionBadWithoutRelation_iff
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10 +
        3 * (actionCircuit.shape.withProofParams pp).k) → Fp)
    (n : Fin 5)
    (hprovenance : family.adaptiveActionRepresentationRelationFinder basis O = none) :
    let data := (family.adversary basis).run O
    let n11 : Fin 11 := Fin.castLE (by omega) n
    let nu : Fin 11 → Fp := fun i =>
      O (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof i)
    O ∈ family.adaptiveActionBadWithoutRelation pp inputs basis n ↔
      nu n11 ∈ adaptiveActionSurfaceAt pp basis inputs n data.algebraicProof.erase
        (data.algebraicProof.actionRepresentationsBefore n ++
          family.fixedRepresentations basis)
        (fun i => nu (i.castLE (le_of_lt n11.isLt))) := by
  let data := (family.adversary basis).run O
  let n11 : Fin 11 := Fin.castLE (by omega) n
  let t := algebraicFullPrefixesPre family.init data.toAlgebraicWfProof n11
  change (O t ∈ adaptiveFinalActionBad pp family inputs basis n data t O ∧
      family.adaptiveActionRepresentationRelationFinder basis O = none) ↔
    O t ∈ adaptiveActionSurfaceAt pp basis inputs n data.algebraicProof.erase
      (data.algebraicProof.actionRepresentationsBefore n ++
        family.fixedRepresentations basis)
      (fun i => O (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof
        (i.castLE (le_of_lt n11.isLt))))
  rw [data.adaptiveFinalActionBad_eq_surface pp family inputs basis n O]
  simp only [hprovenance, and_true]
  constructor <;> intro h <;> simpa only using h

/-- The actual Action semantic event inherits the annotation-aware first-query price. -/
theorem ComputedAdaptiveOnlineAGMFSFamily.adaptiveActionBadWithoutRelation_measure_le
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (n : Fin 5) {epsilon : ENNReal}
    (hsurface : ∀
      (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
      (_hwf : PsWellFormed ps)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (n : Nat) → Fp),
      uniformChallenge.toOuterMeasure
          (adaptiveActionSurfaceAt pp basis inputs n ps source earlier) ≤ epsilon) :
    (PMF.uniformOfFintype (BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10 +
        3 * (actionCircuit.shape.withProofParams pp).k) → Fp)).toOuterMeasure
      (family.adaptiveActionBadWithoutRelation pp inputs basis n) ≤
        (family.Q + 1 : Nat) * epsilon := by
  simpa only [ComputedAdaptiveOnlineAGMFSFamily.adaptiveActionBadWithoutRelation] using
    family.adaptiveFinalActionBadWithoutRelation_table_le pp inputs basis n hsurface

/-- The union of the five actual Action semantic events is bounded by the sum of their uniform
per-stage surface prices. -/
theorem ComputedAdaptiveOnlineAGMFSFamily.adaptiveActionBadWithoutRelation_all_measure_le
    (pp : ProofParams)
    (family : ComputedAdaptiveOnlineAGMFSFamily (actionCircuit.shape.withProofParams pp))
    (inputs : Fin pp.numProofs → PublicInputs Fp)
    (basis : AugmentedIndex (2 ^ (actionCircuit.shape.withProofParams pp).k) → VestaG)
    (epsilon : Fin 5 → ENNReal)
    (hsurface : ∀ (n : Fin 5)
      (ps : ProofString (actionCircuit.shape.withProofParams pp) Fp VestaG)
      (_hwf : PsWellFormed ps)
      (source : List (AlgebraicPoint (F := Fp) basis))
      (earlier : Fin (n : Nat) → Fp),
      uniformChallenge.toOuterMeasure
          (adaptiveActionSurfaceAt pp basis inputs n ps source earlier) ≤ epsilon n) :
    (PMF.uniformOfFintype (BTranscript Fp VestaG
      (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10 +
        3 * (actionCircuit.shape.withProofParams pp).k) → Fp)).toOuterMeasure
      {O | ∃ n : Fin 5, O ∈ family.adaptiveActionBadWithoutRelation pp inputs basis n} ≤
        (family.Q + 1 : Nat) * ∑ n : Fin 5, epsilon n := by
  have hsub : {O | ∃ n : Fin 5,
      O ∈ family.adaptiveActionBadWithoutRelation pp inputs basis n} ⊆
      ⋃ n : Fin 5, family.adaptiveActionBadWithoutRelation pp inputs basis n := by
    rintro O ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  rw [tsum_fintype]
  calc
    ∑ n : Fin 5,
        (PMF.uniformOfFintype (BTranscript Fp VestaG
          (preIpaLen (actionCircuit.shape.withProofParams pp) family.init.length 10 +
            3 * (actionCircuit.shape.withProofParams pp).k) → Fp)).toOuterMeasure
          (family.adaptiveActionBadWithoutRelation pp inputs basis n) ≤
      ∑ n : Fin 5, (family.Q + 1 : Nat) * epsilon n := by
        gcongr with n
        exact family.adaptiveActionBadWithoutRelation_measure_le pp inputs basis n
          (hsurface n)
    _ = (family.Q + 1 : Nat) * ∑ n : Fin 5, epsilon n := by
      rw [Finset.mul_sum]

end Zcash.Snark
