import Zcash.Circuits.Integration.PermutationCompiler
import Zcash.Circuits.Action.TopLevel
import Zcash.Arithmetic.Domain
import Mathlib.Util.AssertNoSorry

/-!
# Action permutation-column compiler bounds

The Action configure call graph can request at most 53 equality/constant
enablements. This is a deliberately coarse syntactic budget: duplicate
suppression makes the derived list much shorter, but the permutation-domain
proof needs only that it fits inside the certified order of `deltaFp`.

The proof is assembled from generic configure effects. It does not evaluate
the concrete Action constraint system or certify an exact column list.
-/

namespace Zcash.Snark.ActionPermutationDomain

open Halo2
open Configure
open Zcash.Arithmetic (deltaFpOrder scalarFieldOrder)

set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 8192
set_option maxRecDepth 100000

local instance addChipGrowth
    (a b c : Column .advice) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.AddChip.configure a b c) 0 := by
  unfold Zcash.Circuits.AddChip.configure
  infer_instance

local instance condSwapGrowth
    (a b aSwapped bSwapped swap : Column .advice) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.CondSwap.configure
        a b aSwapped bSwapped swap) 1 := by
  unfold Zcash.Circuits.CondSwap.configure
  infer_instance

local instance witnessPointGrowth
    (x y : Column .advice) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.Ecc.WitnessPoint.configure x y) 0 := by
  unfold Zcash.Circuits.Ecc.WitnessPoint.configure
  infer_instance

local instance commitIvkGrowth
    (advices : Fin 10 → Column .advice) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.CommitIvk.configure advices) 0 := by
  unfold Zcash.Circuits.CommitIvk.configure
  infer_instance

local instance eccAddGrowth
    (xP yP xQR yQR lambda alpha beta gamma delta :
      Column .advice) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.Ecc.Add.add.configure
        (xP, yP, xQR, yQR, lambda, alpha, beta, gamma, delta)) 4 := by
  unfold Zcash.Circuits.Ecc.Add.add
  infer_instance

local instance eccAddIncompleteGrowth
    (xP yP xQR yQR : Column .advice) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.Ecc.AddIncomplete.add.configure
        (xP, yP, xQR, yQR)) 4 := by
  unfold Zcash.Circuits.Ecc.AddIncomplete.add
  infer_instance

local instance mulCompleteGrowth
    (zComplete : Column .advice)
    (addConfig : Zcash.Circuits.Ecc.Add.Config) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.Ecc.MulComplete.configure
        zComplete addConfig) 1 := by
  unfold Zcash.Circuits.Ecc.MulComplete.configure
  infer_instance

local instance mulOverflowGrowth
    (K : ℕ)
    (lookupConfig : Zcash.Circuits.LookupRangeCheck.Config K)
    (adv0 adv1 adv2 : Column .advice) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.Ecc.MulOverflow.configure
        K lookupConfig adv0 adv1 adv2) 3 := by
  unfold Zcash.Circuits.Ecc.MulOverflow.configure
  infer_instance

local instance lookupRangeCheckGrowth
    (K : ℕ) (runningSum : Column .advice)
    (tableIdx : TableColumn) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.LookupRangeCheck.configure
        K runningSum tableIdx) 1 := by
  unfold Zcash.Circuits.LookupRangeCheck.configure
  infer_instance

local instance decomposeRunningSumGrowth
    (W : ℕ) (qRangeCheck : Selector) (z : Column .advice) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.DecomposeRunningSum.configure
        W qRangeCheck z) 1 := by
  unfold Zcash.Circuits.DecomposeRunningSum.configure
  infer_instance

local instance merkleGateGrowth
    (aWhole bWhole cWhole leftNode rightNode z1A z1B b1 b2 lWhole :
      Column .advice) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.Sinsemilla.Merkle.Gate.configure
        aWhole bWhole cWhole leftNode rightNode
        z1A z1B b1 b2 lWhole) 0 := by
  unfold Zcash.Circuits.Sinsemilla.Merkle.Gate.configure
  infer_instance

local instance hashPieceGrowth
    (G : Zcash.Circuits.Specs.Sinsemilla.Generators)
    (xA xP bits lambda1 lambda2 witnessPieces : Column .advice)
    (fixedYQ : Column .fixed)
    (genTable : Zcash.Circuits.Sinsemilla.GeneratorTableConfig) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.Sinsemilla.HashPiece.configure
        G xA xP bits lambda1 lambda2 witnessPieces fixedYQ genTable) 5 := by
  unfold Zcash.Circuits.Sinsemilla.HashPiece.configure
  infer_instance

local instance merkleGrowth
    (scfg : Zcash.Circuits.Sinsemilla.HashPiece.Config) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.Sinsemilla.Merkle.configure scfg) 1 := by
  unfold Zcash.Circuits.Sinsemilla.Merkle.configure
  infer_instance

local instance poseidonGrowth
    (state : Fin 3 → Column .advice)
    (partialSbox : Column .advice)
    (rcA rcB : Fin 3 → Column .fixed) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.Poseidon.configure
        state partialSbox rcA rcB) 6 := by
  unfold Zcash.Circuits.Poseidon.configure
  infer_instance

local instance mulIncompleteGrowth
    (z xA xP yP lambda1 lambda2 : Column .advice) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.Ecc.MulIncomplete.configure
        z xA xP yP lambda1 lambda2) 2 := by
  unfold Zcash.Circuits.Ecc.MulIncomplete.configure
  infer_instance

local instance mulGrowth
    (addConfig : Zcash.Circuits.Ecc.Add.Config)
    (lookupConfig : Zcash.Circuits.LookupRangeCheck.Config 10)
    (advices : Fin 10 → Column .advice) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.Ecc.Mul.configure
        addConfig lookupConfig advices) 8 := by
  unfold Zcash.Circuits.Ecc.Mul.configure
  infer_instance

local instance noteDecomposeBGrowth
    (a b c : Column .advice) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.NoteCommit.DecomposeB.configure a b c) 0 := by
  unfold Zcash.Circuits.NoteCommit.DecomposeB.configure
  infer_instance

local instance noteDecomposeDGrowth
    (a b c : Column .advice) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.NoteCommit.DecomposeD.configure a b c) 0 := by
  unfold Zcash.Circuits.NoteCommit.DecomposeD.configure
  infer_instance

local instance noteDecomposeEGrowth
    (a b c : Column .advice) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.NoteCommit.DecomposeE.configure a b c) 0 := by
  unfold Zcash.Circuits.NoteCommit.DecomposeE.configure
  infer_instance

local instance noteDecomposeGGrowth
    (a b : Column .advice) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.NoteCommit.DecomposeG.configure a b) 0 := by
  unfold Zcash.Circuits.NoteCommit.DecomposeG.configure
  infer_instance

local instance noteDecomposeHGrowth
    (a b c : Column .advice) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.NoteCommit.DecomposeH.configure a b c) 0 := by
  unfold Zcash.Circuits.NoteCommit.DecomposeH.configure
  infer_instance

local instance noteGdGrowth
    (a b c d : Column .advice) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.NoteCommit.GdCanonicity.configure a b c d) 0 := by
  unfold Zcash.Circuits.NoteCommit.GdCanonicity.configure
  infer_instance

local instance notePkdGrowth
    (a b c d : Column .advice) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.NoteCommit.PkdCanonicity.configure a b c d) 0 := by
  unfold Zcash.Circuits.NoteCommit.PkdCanonicity.configure
  infer_instance

local instance noteValueGrowth
    (a b c d : Column .advice) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.NoteCommit.ValueCanonicity.configure a b c d) 0 := by
  unfold Zcash.Circuits.NoteCommit.ValueCanonicity.configure
  infer_instance

local instance noteRhoGrowth
    (a b c d : Column .advice) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.NoteCommit.RhoCanonicity.configure a b c d) 0 := by
  unfold Zcash.Circuits.NoteCommit.RhoCanonicity.configure
  infer_instance

local instance notePsiGrowth
    (a b c d : Column .advice) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.NoteCommit.PsiCanonicity.configure a b c d) 0 := by
  unfold Zcash.Circuits.NoteCommit.PsiCanonicity.configure
  infer_instance

local instance noteYGrowth
    (advices : Fin 10 → Column .advice) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.NoteCommit.YCanonicity.configure advices) 0 := by
  unfold Zcash.Circuits.NoteCommit.YCanonicity.configure
  infer_instance

local instance noteCommitGrowth
    (advices : Fin 10 → Column .advice) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.NoteCommit.configure advices) 0 := by
  unfold Zcash.Circuits.NoteCommit.configure
  infer_instance

local instance mulFixedProgramGrowth
    (window : Column .advice) (qRunningSum : Selector) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.Ecc.MulFixed.configureProgram
        window qRunningSum) 1 := by
  unfold Zcash.Circuits.Ecc.MulFixed.configureProgram
  infer_instance

local instance mulFixedTailGrowth
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (window u : Column .advice)
    (addConfig : Zcash.Circuits.Ecc.Add.Config)
    (addIncompleteConfig : Zcash.Circuits.Ecc.AddIncomplete.Config) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.Ecc.MulFixed.configureTail lagrangeCoeffs
        window u addConfig addIncompleteConfig) 1 := by
  unfold Zcash.Circuits.Ecc.MulFixed.configureTail
  infer_instance

local instance mulFixedGrowth
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (window u : Column .advice)
    (addConfig : Zcash.Circuits.Ecc.Add.Config)
    (addIncompleteConfig : Zcash.Circuits.Ecc.AddIncomplete.Config) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.Ecc.MulFixed.configure lagrangeCoeffs
        window u addConfig addIncompleteConfig) 3 := by
  unfold Zcash.Circuits.Ecc.MulFixed.configure
  infer_instance

local instance mulFixedBaseGrowth
    (canonAdvices : Fin 3 → Column .advice)
    (lookupConfig : Zcash.Circuits.LookupRangeCheck.Config 10)
    (superConfig : Zcash.Circuits.Ecc.MulFixed.Config) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.Ecc.MulFixed.BaseFieldElem.configure
        canonAdvices lookupConfig superConfig) 3 := by
  unfold Zcash.Circuits.Ecc.MulFixed.BaseFieldElem.configure
  infer_instance

local instance mulFixedShortGrowth
    (superConfig : Zcash.Circuits.Ecc.MulFixed.Config) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.Ecc.MulFixed.Short.configure superConfig) 0 := by
  unfold Zcash.Circuits.Ecc.MulFixed.Short.configure
  infer_instance

local instance mulFixedFullGrowth
    (superConfig : Zcash.Circuits.Ecc.MulFixed.Config) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.Ecc.MulFixed.FullWidth.configure superConfig) 0 := by
  unfold Zcash.Circuits.Ecc.MulFixed.FullWidth.configure
  infer_instance

local instance eccGrowth
    (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : Zcash.Circuits.LookupRangeCheck.Config 10) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.Ecc.configure
        advices lagrangeCoeffs rangeCheck) 22 := by
  unfold Zcash.Circuits.Ecc.configure
  infer_instance

local instance actionConfigureGrowth
    (G : Zcash.Circuits.Specs.Sinsemilla.Generators) :
    HasPermutationGrowthAtMost
      (Zcash.Circuits.Action.Circuit.configure G) 53 := by
  unfold Zcash.Circuits.Action.Circuit.configure
  infer_instance

private theorem actionConfigureEffect
    (G : Zcash.Circuits.Specs.Sinsemilla.Generators) :
    PermutationGrowthAtMost
      (Zcash.Circuits.Action.Circuit.configure G) 53 :=
  (inferInstance : HasPermutationGrowthAtMost _ 53).law

private theorem actionConfigureNonempty
    (G : Zcash.Circuits.Specs.Sinsemilla.Generators) :
    GuaranteesPermutationNonempty
      (Zcash.Circuits.Action.Circuit.configure G) := by
  unfold Zcash.Circuits.Action.Circuit.configure
  infer_instance

private theorem configuredPermutationColumns_nonempty :
    (Zcash.Circuits.Action.Circuit.configure
      Zcash.Circuits.Specs.Sinsemilla.orchardGenerators
      ({} : ConstraintSystem Fp)).2.permutationColumns ≠ [] :=
  (actionConfigureNonempty
    Zcash.Circuits.Specs.Sinsemilla.orchardGenerators).nonempty _

@[simp]
theorem actionCircuit_configure :
    Zcash.Circuits.Action.actionCircuit.formalCircuit.configure () =
      Zcash.Circuits.Action.Circuit.configure
        Zcash.Circuits.Specs.Sinsemilla.orchardGenerators := by
  rfl

/-- The closed deployed Action CS has exactly the permutation columns produced
by its raw configure program. -/
theorem permutationColumns_eq_configure :
    (Zcash.Circuits.Action.actionCircuit.constraintSystem).permutationColumns =
      (Zcash.Circuits.Action.Circuit.configure
        Zcash.Circuits.Specs.Sinsemilla.orchardGenerators
        ({} : ConstraintSystem Fp)).2.permutationColumns := by
  calc
    _ =
        (Zcash.Circuits.Action.actionCircuit.formalCircuit.configure
          () {}).2.permutationColumns :=
      Halo2.TopLevelCircuit.constraintSystem_permutationColumns _
    _ = _ := by
      rw [actionCircuit_configure]

/-- Action's derived permutation-column family is nonempty because its
configure program equality-enables the primary column. -/
theorem permutationColumns_nonempty :
    (Zcash.Circuits.Action.actionCircuit.constraintSystem).permutationColumns ≠
      [] := by
  rw [permutationColumns_eq_configure]
  exact configuredPermutationColumns_nonempty

/-- Action's derived column-name prefix fits inside the certified order of
`deltaFp`. The proof uses the syntactic budget 53, not the actual list. -/
theorem permutationColumns_le_delta :
    (Zcash.Circuits.Action.actionCircuit.constraintSystem).permutationColumns.length ≤
      deltaFpOrder := by
  rw [permutationColumns_eq_configure]
  have hsmall :=
    (actionConfigureEffect
      Zcash.Circuits.Specs.Sinsemilla.orchardGenerators).upper
      ({} : ConstraintSystem Fp)
  exact hsmall.trans (by
    norm_num [deltaFpOrder, scalarFieldOrder,
      CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])

assert_no_sorry permutationColumns_nonempty
assert_no_sorry permutationColumns_le_delta

end Zcash.Snark.ActionPermutationDomain
