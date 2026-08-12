import Zcash.Circuits.Action.Planner

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

private theorem listCoe_cons {T : Type} (head : T) (tail : List T) :
    (↑(head :: tail) : Multiset T) = head ::ₘ (↑tail : Multiset T) := rfl

private theorem multisetCons_eq_add {T : Type} (head : T)
    (tail : Multiset T) : head ::ₘ tail = {head} + tail :=
  (Multiset.singleton_add head tail).symm

/-- A concise physical region shape for Action's ten advice columns and selected
fixed columns. -/
def plannerShape (advice : List ℕ) (rows : ℕ)
    (fixed : List ℕ := []) : RegionShapeSummary :=
  { columns := advice.map (.column .advice) ++ fixed.map (.column .fixed)
    rowCount := rows }

/-- Action's 33 canonical physical shape blocks in descending planner-key order. -/
def actionPlannerBlocks : List (ℕ × RegionShapeSummary) :=
  [(1, plannerShape [0,1,2,3,4,5,6,7,8,9] 137),
    (1, plannerShape [0,1,2,3,4] 110 [3,12]),
    (1, plannerShape [5,6,7,8,9] 110 [4,13]),
    (1, plannerShape [0,1,2,3,4,5] 86 [3,4,5,6,7,8,9,10,11]),
    (5, plannerShape [0,1,2,3,4,5] 85 [3,4,5,6,7,8,9,10,11]),
    (16, plannerShape [0,1,2,3,4] 53 [3,12]),
    (16, plannerShape [5,6,7,8,9] 53 [4,13]),
    (1, plannerShape [0,1,2,3,4] 52 [3,12]),
    (1, plannerShape [5,6,7,8] 37 [5,6,7,8,9,10]),
    (1, plannerShape [0,1,2,3,4,5] 23 [3,4,5,6,7,8,9,10,11]),
    (1, plannerShape [0,1,2,3,4,5,6,7,8,9] 4),
    (4, plannerShape [9] 26),
    (14, plannerShape [0,1,2,3,4,5,6,7,8] 2),
    (5, plannerShape [9] 15), (11, plannerShape [9] 14),
    (16, plannerShape [0,1,2,3,4] 2),
    (20, plannerShape [5,6,7,8,9] 2),
    (3, plannerShape [6,7,8] 3),
    (8, plannerShape [6,7,8,9] 2),
    (1, plannerShape [0,1,2,3,4,5,6,7] 1),
    (4, plannerShape [6,7,8] 2),
    (16, plannerShape [0,1,2,3,4] 1),
    (16, plannerShape [5,6,7,8,9] 1),
    (2, plannerShape [6,7] 2),
    (2, plannerShape [6,7,8,9] 1),
    (89, plannerShape [9] 3),
    (6, plannerShape [6,7,8] 1),
    (6, plannerShape [0,1] 1), (2, plannerShape [9] 1),
    (61, plannerShape [6] 1), (6, plannerShape [0] 1),
    (56, plannerShape [7] 1), (2, plannerShape [] 0)]

/-- Action's canonical V1 input, retaining repeated blocks symbolically rather
than expanding the 395-region synthesis trace. -/
def actionCanonicalPlannerSummaries : List RegionShapeSummary :=
  actionPlannerBlocks.flatMap fun block =>
    List.replicate block.1 block.2

private def witnessPlannerBlocks : List (ℕ × RegionShapeSummary) :=
  [(2, plannerShape [0] 1),
    (3, plannerShape [0,1] 1),
    (3, plannerShape [0] 1)]

private def crossAddressPlannerBlocks : List (ℕ × RegionShapeSummary) :=
  [(1, plannerShape [0,1,2,3,4,5,6,7,8,9] 4)]

private def checksPlannerBlocks : List (ℕ × RegionShapeSummary) :=
  [(1, plannerShape [0,1,2,3,4,5,6,7,8,9] 137),
    (1, plannerShape [0,1,2,3,4,5] 86 [3,4,5,6,7,8,9,10,11]),
    (3, plannerShape [0,1,2,3,4,5] 85 [3,4,5,6,7,8,9,10,11]),
    (16, plannerShape [0,1,2,3,4] 53 [3,12]),
    (16, plannerShape [5,6,7,8,9] 53 [4,13]),
    (1, plannerShape [0,1,2,3,4] 52 [3,12]),
    (1, plannerShape [5,6,7,8] 37 [5,6,7,8,9,10]),
    (1, plannerShape [0,1,2,3,4,5] 23 [3,4,5,6,7,8,9,10,11]),
    (10, plannerShape [0,1,2,3,4,5,6,7,8] 2),
    (1, plannerShape [9] 15), (3, plannerShape [9] 14),
    (16, plannerShape [0,1,2,3,4] 2),
    (16, plannerShape [5,6,7,8,9] 2),
    (3, plannerShape [6,7,8] 3),
    (16, plannerShape [0,1,2,3,4] 1),
    (16, plannerShape [5,6,7,8,9] 1),
    (67, plannerShape [9] 3),
    (2, plannerShape [6,7,8] 1),
    (1, plannerShape [0,1] 1), (2, plannerShape [9] 1),
    (53, plannerShape [6] 1),
    (48, plannerShape [7] 1), (1, plannerShape [] 0)]

private def notesPlannerBlocks : List (ℕ × RegionShapeSummary) :=
  [(1, plannerShape [0,1,2,3,4] 110 [3,12]),
    (1, plannerShape [5,6,7,8,9] 110 [4,13]),
    (2, plannerShape [0,1,2,3,4,5] 85 [3,4,5,6,7,8,9,10,11]),
    (4, plannerShape [9] 26),
    (4, plannerShape [0,1,2,3,4,5,6,7,8] 2),
    (4, plannerShape [9] 15), (8, plannerShape [9] 14),
    (4, plannerShape [5,6,7,8,9] 2),
    (8, plannerShape [6,7,8,9] 2),
    (1, plannerShape [0,1,2,3,4,5,6,7] 1),
    (4, plannerShape [6,7,8] 2),
    (2, plannerShape [6,7] 2),
    (2, plannerShape [6,7,8,9] 1),
    (22, plannerShape [9] 3),
    (4, plannerShape [6,7,8] 1),
    (2, plannerShape [0,1] 1),
    (8, plannerShape [6] 1), (1, plannerShape [0] 1),
    (8, plannerShape [7] 1), (1, plannerShape [] 0)]

private def expandPlannerBlocks
    (blocks : List (ℕ × RegionShapeSummary)) : List RegionShapeSummary :=
  blocks.flatMap fun block => List.replicate block.1 block.2

private def plannerBlockMultiset
    (blocks : List (ℕ × RegionShapeSummary)) : Multiset RegionShapeSummary :=
  blocks.foldr (fun block result => block.1 • {block.2} + result) 0

private theorem coe_replicate_eq_nsmul {T : Type} (count : ℕ) (item : T) :
    (List.replicate count item : Multiset T) = count • {item} := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.replicate_succ, listCoe_cons, multisetCons_eq_add,
        inductionHypothesis, succ_nsmul]
      ac_rfl

private theorem coe_expandPlannerBlocks
    (blocks : List (ℕ × RegionShapeSummary)) :
    (expandPlannerBlocks blocks : Multiset RegionShapeSummary) =
      plannerBlockMultiset blocks := by
  induction blocks with
  | nil => rfl
  | cons block blocks inductionHypothesis =>
      rw [show expandPlannerBlocks (block :: blocks) =
        List.replicate block.1 block.2 ++ expandPlannerBlocks blocks by
          simp [expandPlannerBlocks]]
      change (List.replicate block.1 block.2 : Multiset RegionShapeSummary) +
        (expandPlannerBlocks blocks : Multiset RegionShapeSummary) = _
      rw [coe_replicate_eq_nsmul, inductionHypothesis]
      rfl

private theorem witnessPlannerBlocks_correct :
    ((Circuit.synthWitnessSynthesisSummary actionConfig).physicalRegionShapes.map
      RegionShapeSummary.normalized : Multiset RegionShapeSummary) =
        plannerBlockMultiset witnessPlannerBlocks := by
  rw [Circuit.synthWitnessSynthesisSummary_physicalRegionShapes]
  simp [witnessPlannerBlocks, plannerBlockMultiset,
    Sinsemilla.loadSynthesisSummary, Circuit.loadPrivateSynthesisSummary,
    Ecc.WitnessPoint.pointSynthesisSummary,
    Ecc.WitnessPoint.pointNonIdSynthesisSummary,
    SynthesisSummary.physicalRegionShapes, SynthesisSummary.ofRegion,
    RegionSynthesisSummary.ofColumns,
    RegionSynthesisSummary.toRegionShapeSummary,
    RegionShapeSummary.withoutSelectors, physicalColumns,
    unionColumns, addColumn,
    RegionShapeSummary.normalized, plannerShape,
    sortRegionColumns,
    RegionColumn.lt, RegionColumn.ordKey, RegionColumn.kindRank,
    actionConfig, Circuit.configure, Circuit.configureBase,
    Circuit.configureChips, Circuit.configureShared,
    Circuit.configureAdvices, Circuit.configureAdviceEqualitiesLow,
    Circuit.configureAdviceEqualitiesHigh, Circuit.configureEqualities,
    Circuit.configureLagrange, AddChip.configure, Ecc.configure,
    LookupRangeCheck.configure, Poseidon.configure,
    Sinsemilla.HashPiece.configure, Sinsemilla.Merkle.configure,
    CondSwap.configure, Ecc.Add.add, Ecc.AddIncomplete.add,
    Ecc.Mul.configure, Ecc.MulFixed.BaseFieldElem.configure,
    Ecc.MulFixed.FullWidth.configure, Ecc.MulFixed.Short.configure,
    Ecc.MulFixed.configure, Ecc.WitnessPoint.configure,
    Ecc.MulComplete.configure, Ecc.MulIncomplete.configure,
    Ecc.MulOverflow.configure, Sinsemilla.Merkle.Gate.configure,
    lookupTableColumn, Configure.run_fst, keygen_norm]
  simp only [listCoe_cons, multisetCons_eq_add, Multiset.coe_nil]
  abel

private theorem crossAddressPlannerBlocks_correct :
    ((Circuit.synthCrossAddressChecksSynthesisSummary
      actionConfig).physicalRegionShapes.map
        RegionShapeSummary.normalized : Multiset RegionShapeSummary) =
      plannerBlockMultiset crossAddressPlannerBlocks := by
  simp [Circuit.synthCrossAddressChecksSynthesisSummary,
    Circuit.crossAddressColumns, crossAddressPlannerBlocks,
    plannerBlockMultiset, SynthesisSummary.physicalRegionShapes,
    SynthesisSummary.ofRegion,
    RegionSynthesisSummary.repeatColumns,
    RegionSynthesisSummary.toRegionShapeSummary,
    RegionShapeSummary.withoutSelectors, physicalColumns,
    RegionShapeSummary.normalized, plannerShape,
    sortRegionColumns, List.insertionSort,
    RegionColumn.lt, RegionColumn.ordKey, RegionColumn.kindRank,
    actionConfig, Circuit.configure, Circuit.configureBase,
    Circuit.configureChips, Circuit.configureShared,
    Circuit.configureAdvices, Circuit.configureAdviceEqualitiesLow,
    Circuit.configureAdviceEqualitiesHigh, Circuit.configureEqualities,
    Circuit.configureLagrange, AddChip.configure, Ecc.configure,
    LookupRangeCheck.configure, Poseidon.configure,
    Sinsemilla.HashPiece.configure, Sinsemilla.Merkle.configure,
    CondSwap.configure, Ecc.Add.add, Ecc.AddIncomplete.add,
    Ecc.Mul.configure, Ecc.MulFixed.BaseFieldElem.configure,
    Ecc.MulFixed.FullWidth.configure, Ecc.MulFixed.Short.configure,
    Ecc.MulFixed.configure, Ecc.WitnessPoint.configure,
    Ecc.MulComplete.configure, Ecc.MulIncomplete.configure,
    Ecc.MulOverflow.configure, Sinsemilla.Merkle.Gate.configure,
    lookupTableColumn, Configure.run_fst, keygen_norm]
  decide

private theorem shortPhysicalShapes :
    (Ecc.MulFixed.Short.circuitSynthesisSummary
      actionConfig.eccConfig.mulFixedShort).physicalRegionShapes.map
        RegionShapeSummary.normalized =
      [plannerShape [0,1,2,3,4,5] 23 [3,4,5,6,7,8,9,10,11],
        plannerShape [0,1,2,3,4,5,6,7,8] 2] := by
  simp only [Ecc.MulFixed.Short.circuitSynthesisSummary,
    Ecc.MulFixed.Short.innerRegionSynthesisSummary,
    Ecc.MulFixed.Short.mswRegionSynthesisSummary,
    Ecc.MulFixed.fixedConstantsLoopSynthesisSummary,
    Ecc.MulFixed.windowChainSynthesisSummary,
    Ecc.MulFixed.processWindowSynthesisSummary,
    DecomposeRunningSum.copyDecomposeSynthesisSummary,
    DecomposeRunningSum.assignLoopSynthesisSummary,
    DecomposeRunningSum.enableLoopSynthesisSummary,
    Ecc.MulFixed.windowStepColumns,
    Ecc.AddIncomplete.synthesisSummary, RegionSynthesisSummary.combine,
    RegionSynthesisSummary.repeatColumns, RegionSynthesisSummary.ofColumns,
    SynthesisSummary.physicalRegionShapes,
    SynthesisSummary.combine_regionShapes,
    SynthesisSummary.ofRegion_regionShapes]
  rw [show actionConfig.eccConfig.mulFixedShort.superConfig.runningSumConfig.z.index = 4 by rfl,
    show (actionConfig.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 0).index = 3 by rfl,
    show (actionConfig.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 1).index = 4 by rfl,
    show (actionConfig.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 2).index = 5 by rfl,
    show (actionConfig.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 3).index = 6 by rfl,
    show (actionConfig.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 4).index = 7 by rfl,
    show (actionConfig.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 5).index = 8 by rfl,
    show (actionConfig.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 6).index = 9 by rfl,
    show (actionConfig.eccConfig.mulFixedShort.superConfig.lagrangeCoeffs 7).index = 10 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.window.index = 4 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.u.index = 5 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.fixedZ.index = 11 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.addConfig.xP.index = 0 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.addConfig.yP.index = 1 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.runningSumConfig.qRangeCheck.index = 18 by rfl,
    show actionConfig.eccConfig.mulFixedShort.qMulFixedShort.index = 20 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.addIncompleteConfig.qAddIncomplete.index = 7 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.addIncompleteConfig.xP.index = 0 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.addIncompleteConfig.yP.index = 1 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.addIncompleteConfig.xQR.index = 2 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.addIncompleteConfig.yQR.index = 3 by rfl]
  simp [RegionShapeSummary.normalized, unionColumns, addColumn,
    sortRegionColumns, RegionColumn.lt, RegionColumn.ordKey,
    RegionColumn.kindRank, plannerShape]
  decide

set_option maxRecDepth 10000 in
private theorem fullWidthPhysicalShapes :
    (Ecc.MulFixed.FullWidth.circuitSynthesisSummary
      actionConfig.eccConfig.mulFixedFull).physicalRegionShapes.map
        RegionShapeSummary.normalized =
      [plannerShape [0,1,2,3,4,5] 85 [3,4,5,6,7,8,9,10,11],
        plannerShape [0,1,2,3,4,5,6,7,8] 2] := by
  simp only [Ecc.MulFixed.FullWidth.circuitSynthesisSummary,
    Ecc.MulFixed.FullWidth.innerRegionSynthesisSummary,
    Ecc.MulFixed.FullWidth.witnessScalarLoopSynthesisSummary,
    Ecc.MulFixed.fixedConstantsLoopSynthesisSummary,
    Ecc.MulFixed.windowChainSynthesisSummary,
    Ecc.MulFixed.processWindowSynthesisSummary,
    Ecc.MulFixed.windowStepColumns,
    Ecc.AddIncomplete.synthesisSummary, Ecc.Add.synthesisSummary,
    RegionSynthesisSummary.combine, RegionSynthesisSummary.repeatColumns,
    RegionSynthesisSummary.ofColumns,
    SynthesisSummary.physicalRegionShapes,
    SynthesisSummary.combine_regionShapes,
    SynthesisSummary.ofRegion_regionShapes]
  rw [show (actionConfig.eccConfig.mulFixedFull.superConfig.lagrangeCoeffs 0).index = 3 by rfl,
    show (actionConfig.eccConfig.mulFixedFull.superConfig.lagrangeCoeffs 1).index = 4 by rfl,
    show (actionConfig.eccConfig.mulFixedFull.superConfig.lagrangeCoeffs 2).index = 5 by rfl,
    show (actionConfig.eccConfig.mulFixedFull.superConfig.lagrangeCoeffs 3).index = 6 by rfl,
    show (actionConfig.eccConfig.mulFixedFull.superConfig.lagrangeCoeffs 4).index = 7 by rfl,
    show (actionConfig.eccConfig.mulFixedFull.superConfig.lagrangeCoeffs 5).index = 8 by rfl,
    show (actionConfig.eccConfig.mulFixedFull.superConfig.lagrangeCoeffs 6).index = 9 by rfl,
    show (actionConfig.eccConfig.mulFixedFull.superConfig.lagrangeCoeffs 7).index = 10 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.window.index = 4 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.u.index = 5 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.fixedZ.index = 11 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addConfig.xP.index = 0 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addConfig.yP.index = 1 by rfl,
    show actionConfig.eccConfig.mulFixedFull.qMulFixedFull.index = 19 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addIncompleteConfig.qAddIncomplete.index = 7 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addIncompleteConfig.xP.index = 0 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addIncompleteConfig.yP.index = 1 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addIncompleteConfig.xQR.index = 2 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addIncompleteConfig.yQR.index = 3 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addConfig.qAdd.index = 8 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addConfig.xQR.index = 2 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addConfig.yQR.index = 3 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addConfig.lambda.index = 4 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addConfig.alpha.index = 5 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addConfig.beta.index = 6 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addConfig.gamma.index = 7 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addConfig.delta.index = 8 by rfl]
  simp [RegionShapeSummary.normalized, unionColumns, addColumn,
    sortRegionColumns, RegionColumn.lt, RegionColumn.ordKey,
    RegionColumn.kindRank, plannerShape]
  decide

set_option maxRecDepth 10000 in
private theorem baseFieldPhysicalShapes :
    (Ecc.MulFixed.BaseFieldElem.circuitSynthesisSummary
      actionConfig.eccConfig.mulFixedBaseField).physicalRegionShapes.map
        RegionShapeSummary.normalized =
      [plannerShape [0,1,2,3,4,5] 86 [3,4,5,6,7,8,9,10,11],
        plannerShape [0,1,2,3,4,5,6,7,8] 2,
        plannerShape [9] 14, plannerShape [6,7,8] 3] := by
  simp only [Ecc.MulFixed.BaseFieldElem.circuitSynthesisSummary,
    Ecc.MulFixed.BaseFieldElem.innerRegionSynthesisSummary,
    Ecc.MulFixed.BaseFieldElem.witnessCheck13SynthesisSummary,
    Ecc.MulFixed.BaseFieldElem.canonicityRegionSynthesisSummary,
    Ecc.MulFixed.fixedConstantsLoopSynthesisSummary,
    Ecc.MulFixed.windowChainSynthesisSummary,
    Ecc.MulFixed.processWindowSynthesisSummary,
    DecomposeRunningSum.copyDecomposeSynthesisSummary,
    DecomposeRunningSum.assignLoopSynthesisSummary,
    DecomposeRunningSum.enableLoopSynthesisSummary,
    Ecc.MulFixed.windowStepColumns,
    Ecc.AddIncomplete.synthesisSummary, Ecc.Add.synthesisSummary,
    LookupRangeCheck.witnessCheckSynthesisSummary,
    RegionSynthesisSummary.combine, RegionSynthesisSummary.repeatColumns,
    RegionSynthesisSummary.ofColumns,
    SynthesisSummary.physicalRegionShapes,
    SynthesisSummary.combine_regionShapes,
    SynthesisSummary.ofRegion_regionShapes]
  rw [show actionConfig.eccConfig.mulFixedBaseField.superConfig.runningSumConfig.z.index = 4 by rfl,
    show (actionConfig.eccConfig.mulFixedBaseField.superConfig.lagrangeCoeffs 0).index = 3 by rfl,
    show (actionConfig.eccConfig.mulFixedBaseField.superConfig.lagrangeCoeffs 1).index = 4 by rfl,
    show (actionConfig.eccConfig.mulFixedBaseField.superConfig.lagrangeCoeffs 2).index = 5 by rfl,
    show (actionConfig.eccConfig.mulFixedBaseField.superConfig.lagrangeCoeffs 3).index = 6 by rfl,
    show (actionConfig.eccConfig.mulFixedBaseField.superConfig.lagrangeCoeffs 4).index = 7 by rfl,
    show (actionConfig.eccConfig.mulFixedBaseField.superConfig.lagrangeCoeffs 5).index = 8 by rfl,
    show (actionConfig.eccConfig.mulFixedBaseField.superConfig.lagrangeCoeffs 6).index = 9 by rfl,
    show (actionConfig.eccConfig.mulFixedBaseField.superConfig.lagrangeCoeffs 7).index = 10 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.superConfig.u.index = 5 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.superConfig.fixedZ.index = 11 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.superConfig.addConfig.xP.index = 0 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.superConfig.addConfig.yP.index = 1 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.superConfig.runningSumConfig.qRangeCheck.index = 18 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.superConfig.addIncompleteConfig.qAddIncomplete.index = 7 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.superConfig.addIncompleteConfig.xP.index = 0 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.superConfig.addIncompleteConfig.yP.index = 1 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.superConfig.addIncompleteConfig.xQR.index = 2 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.superConfig.addIncompleteConfig.yQR.index = 3 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.lookupConfig.runningSum.index = 9 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.lookupConfig.qLookup.index = 2 by rfl]
  simp [RegionShapeSummary.normalized, unionColumns, addColumn,
    sortRegionColumns, RegionColumn.lt, RegionColumn.ordKey,
    RegionColumn.kindRank, plannerShape]
  decide

private theorem merkle1HashPhysicalShape :
    (Sinsemilla.Merkle.HashLayer.hashPhysicalShape
      actionConfig.merkle1.sinsemilla).normalized =
      plannerShape [0,1,2,3,4] 53 [3,12] := by
  simp only [Sinsemilla.Merkle.HashLayer.hashPhysicalShape,
    Sinsemilla.Merkle.HashLayer.hashRegionColumns,
    Sinsemilla.Merkle.HashLayer.hashSlotColumns,
    Sinsemilla.HashPiece.roundColumns]
  rw [show actionConfig.merkle1.sinsemilla.fixedYQ.index = 3 by rfl,
    show actionConfig.merkle1.sinsemilla.qS2.index = 12 by rfl,
    show actionConfig.merkle1.sinsemilla.xA.index = 0 by rfl,
    show actionConfig.merkle1.sinsemilla.bits.index = 2 by rfl,
    show actionConfig.merkle1.sinsemilla.xP.index = 1 by rfl,
    show actionConfig.merkle1.sinsemilla.lambda1.index = 3 by rfl,
    show actionConfig.merkle1.sinsemilla.lambda2.index = 4 by rfl]
  simp [RegionShapeSummary.normalized, physicalColumns, unionColumns, addColumn,
    sortRegionColumns, RegionColumn.lt, RegionColumn.ordKey,
    RegionColumn.kindRank, plannerShape]
  decide

private theorem merkle2HashPhysicalShape :
    (Sinsemilla.Merkle.HashLayer.hashPhysicalShape
      actionConfig.merkle2.sinsemilla).normalized =
      plannerShape [5,6,7,8,9] 53 [4,13] := by
  simp only [Sinsemilla.Merkle.HashLayer.hashPhysicalShape,
    Sinsemilla.Merkle.HashLayer.hashRegionColumns,
    Sinsemilla.Merkle.HashLayer.hashSlotColumns,
    Sinsemilla.HashPiece.roundColumns]
  rw [show actionConfig.merkle2.sinsemilla.fixedYQ.index = 4 by rfl,
    show actionConfig.merkle2.sinsemilla.qS2.index = 13 by rfl,
    show actionConfig.merkle2.sinsemilla.xA.index = 5 by rfl,
    show actionConfig.merkle2.sinsemilla.bits.index = 7 by rfl,
    show actionConfig.merkle2.sinsemilla.xP.index = 6 by rfl,
    show actionConfig.merkle2.sinsemilla.lambda1.index = 8 by rfl,
    show actionConfig.merkle2.sinsemilla.lambda2.index = 9 by rfl]
  simp [RegionShapeSummary.normalized, physicalColumns, unionColumns, addColumn,
    sortRegionColumns, RegionColumn.lt, RegionColumn.ordKey,
    RegionColumn.kindRank, plannerShape]
  decide

set_option maxRecDepth 10000 in
private theorem variableBaseMulPhysicalShape :
    ({ columns := physicalColumns
          (Ecc.Mul.mainCircuitSynthesisSummary actionConfig.eccConfig.mul).columns
       rowCount :=
          (Ecc.Mul.mainCircuitSynthesisSummary actionConfig.eccConfig.mul).rowCount } :
      RegionShapeSummary).normalized =
      plannerShape [0,1,2,3,4,5,6,7,8,9] 137 := by
  simp [Ecc.Mul.mainCircuitSynthesisSummary,
    Ecc.MulComplete.circuitSynthesisSummary,
    Ecc.MulIncomplete.doubleAndAddSynthesisSummary,
    Ecc.MulIncomplete.loopSynthesisSummary,
    Ecc.Add.synthesisSummary,
    RegionSynthesisSummary.combine, RegionSynthesisSummary.ofColumns,
    RegionShapeSummary.normalized,
    physicalColumns, unionColumns, addColumn, sortRegionColumns,
    RegionColumn.lt, RegionColumn.ordKey, RegionColumn.kindRank,
    plannerShape, actionConfig, Circuit.configure,
    Circuit.configureBase, Circuit.configureChips, Circuit.configureShared,
    Circuit.configureAdvices, Circuit.configureAdviceEqualitiesLow,
    Circuit.configureAdviceEqualitiesHigh, Circuit.configureEqualities,
    Circuit.configureLagrange, AddChip.configure, Ecc.configure,
    LookupRangeCheck.configure, Poseidon.configure,
    Sinsemilla.HashPiece.configure, Sinsemilla.Merkle.configure,
    CondSwap.configure, Ecc.Add.add, Ecc.AddIncomplete.add,
    Ecc.Mul.configure, Ecc.MulFixed.BaseFieldElem.configure,
    Ecc.MulFixed.FullWidth.configure, Ecc.MulFixed.Short.configure,
    Ecc.MulFixed.configure, Ecc.WitnessPoint.configure,
    Ecc.MulComplete.configure, Ecc.MulIncomplete.configure,
    Ecc.MulOverflow.configure, Sinsemilla.Merkle.Gate.configure,
    lookupTableColumn, Configure.run_fst, keygen_norm]
  decide

set_option maxRecDepth 10000 in
private theorem checksPlannerBlocks_correct :
    ((Circuit.synthChecksSynthesisSummary actionConfig).physicalRegionShapes.map
      RegionShapeSummary.normalized : Multiset RegionShapeSummary) =
        plannerBlockMultiset checksPlannerBlocks := by
  rw [Circuit.synthChecksSynthesisSummary_physicalRegionShapes]
  unfold checksPlannerBlocks plannerBlockMultiset
  simp only [List.flatMap_cons, List.flatMap_nil,
    Sinsemilla.Merkle.CalculateRoot.synthesisSummary_physicalShapes_eq,
    Sinsemilla.Merkle.Layer.synthesisSummary_physicalShapes_eq,
    Sinsemilla.Merkle.HashLayer.synthesisSummary_physicalShapes_eq,
    synthesis_summary_norm,
    ValueCommit.synthesisSummary, DeriveNullifier.synthesisSummary,
    SpendAuthority.synthesisSummary, CommitIvk.Main.synthesisSummary,
    AddressIntegrity.synthesisSummary,
    CommitIvk.Main.synthPiecesSynthesisSummary,
    CommitIvk.Canonicity.circuitSynthesisSummary,
    Sinsemilla.CommitDomain.commitSynthesisSummary,
    Poseidon.hashSynthesisSummary, Ecc.Mul.mulSynthesisSummary,
    Ecc.Add.synthesisSummary, CommitIvk.synthesisSummary,
    LookupRangeCheck.witnessCheckSynthesisSummary,
    Ecc.MulOverflow.circuitSynthesisSummary,
    Poseidon.addInputRegionSynthesisSummary,
    Poseidon.initRegionSynthesisSummary,
    Poseidon.permuteSynthesisSummary,
    Sinsemilla.HashToPoint.hashCircuitSynthesisSummary,
    Sinsemilla.HashToPoint.hashRegionSynthesisSummary,
    Sinsemilla.Chain.circuitSynthesisSummary,
    Sinsemilla.Chain.slotIterationSynthesisSummary,
    Sinsemilla.Chain.slotSynthesisSummary,
    Sinsemilla.HashPiece.circuitSynthesisSummary,
    Sinsemilla.HashPiece.loopSynthesisSummary,
    RegionSynthesisSummary.repeatColumns,
    SynthesisSummary.combine_physicalRegionShapes,
    SynthesisSummary.ofRegion_physicalRegionShapes,
    SynthesisSummary.foldr_combine_physicalRegionShapes,
    Circuit.loadPrivateSynthesisSummary,
    Sinsemilla.Merkle.Gate.synthesisSummary,
    LookupRangeCheck.witnessShortCheckSynthesisSummary,
    Sinsemilla.HashToPoint.witnessMessagePieceSynthesisSummary,
    List.map_append]
  rw [shortPhysicalShapes, fullWidthPhysicalShapes,
    baseFieldPhysicalShapes]
  simp only [← Multiset.map_coe, ← Multiset.coe_add,
    Multiset.map_add, Multiset.coe_flatten_replicate,
    Multiset.map_nsmul, Multiset.coe_singleton, Multiset.map_singleton]
  simp only [AddChip.synthesisSummary,
    RegionSynthesisSummary.ofColumns,
    RegionSynthesisSummary.toRegionShapeSummary,
    RegionShapeSummary.withoutSelectors, unionColumns]
  simp only [merkle1HashPhysicalShape, merkle2HashPhysicalShape,
    variableBaseMulPhysicalShape]
  simp [CommitIvk.Main.ns, Sinsemilla.Chain.prefixRows,
    Sinsemilla.HashPiece.roundColumns,
    Ecc.WitnessPoint.pointNonIdSynthesisSummary,
    RegionSynthesisSummary.combine,
    actionConfig, Circuit.configure,
    Circuit.configureBase, Circuit.configureChips, Circuit.configureShared,
    Circuit.configureAdvices, Circuit.configureAdviceEqualitiesLow,
    Circuit.configureAdviceEqualitiesHigh, Circuit.configureEqualities,
    Circuit.configureLagrange, AddChip.configure, Ecc.configure,
    CommitIvk.configure, LookupRangeCheck.configure, Poseidon.configure,
    Sinsemilla.HashPiece.configure, Sinsemilla.Merkle.configure,
    CondSwap.configure, Ecc.Add.add, Ecc.AddIncomplete.add,
    Ecc.Mul.configure, Ecc.MulFixed.BaseFieldElem.configure,
    Ecc.MulFixed.FullWidth.configure, Ecc.MulFixed.Short.configure,
    Ecc.MulFixed.configure, Ecc.WitnessPoint.configure,
    Ecc.MulComplete.configure, Ecc.MulIncomplete.configure,
    Ecc.MulOverflow.configure, Sinsemilla.Merkle.Gate.configure,
    lookupTableColumn, Configure.run_fst, keygen_norm]
  simp [plannerShape, SynthesisSummary.physicalRegionShapes,
    SynthesisSummary.ofRegion,
    LookupRangeCheck.copyCheckSynthesisSummary,
    Ecc.MulOverflow.numWords,
    RegionSynthesisSummary.ofColumns,
    RegionSynthesisSummary.toRegionShapeSummary,
    RegionShapeSummary.withoutSelectors,
    RegionShapeSummary.normalized, physicalColumns, unionColumns,
    addColumn, sortRegionColumns, List.insertionSort, List.orderedInsert,
    RegionColumn.lt, RegionColumn.ordKey, RegionColumn.kindRank]
  simp only [listCoe_cons, Multiset.coe_nil]
  letI : DecidableEq RegionShapeSummary := Classical.decEq _
  rw [Multiset.ext]
  intro summary
  simp only [Multiset.count_cons, Multiset.count_add,
    Multiset.count_nsmul, Multiset.count_singleton,
    Multiset.count_zero]
  omega

set_option maxRecDepth 10000 in
private theorem notesPlannerBlocks_correct :
    ((Circuit.synthNotesSynthesisSummary actionConfig).physicalRegionShapes.map
      RegionShapeSummary.normalized : Multiset RegionShapeSummary) =
        plannerBlockMultiset notesPlannerBlocks := by
  rw [Circuit.synthNotesSynthesisSummary_physicalRegionShapes]
  unfold notesPlannerBlocks plannerBlockMultiset
  simp only [List.flatMap_cons, List.flatMap_nil, synthesis_summary_norm,
    NoteCommit.Main.synthesisSummary,
    NoteCommit.Main.synthPiecesSynthesisSummary,
    NoteCommit.Main.synthChecksSynthesisSummary,
    NoteCommit.Main.synthGatesSynthesisSummary,
    NoteCommit.DecomposeB.synthesisSummary,
    NoteCommit.DecomposeD.synthesisSummary,
    NoteCommit.DecomposeE.synthesisSummary,
    NoteCommit.DecomposeG.synthesisSummary,
    NoteCommit.DecomposeH.synthesisSummary,
    NoteCommit.GdCanonicity.synthesisSummary,
    NoteCommit.PkdCanonicity.synthesisSummary,
    NoteCommit.RhoCanonicity.synthesisSummary,
    NoteCommit.ValueCanonicity.synthesisSummary,
    NoteCommit.YCanonicityCheck.synthesisSummary,
    NoteCommit.YCanonicity.synthesisSummary,
    NoteCommit.PsiCanonicity.synthesisSummary,
    Circuit.orchardChecksRegionSynthesisSummary,
    Circuit.orchardChecksSynthesisSummary,
    Sinsemilla.CommitDomain.commitSynthesisSummary,
    Ecc.Add.synthesisSummary,
    LookupRangeCheck.witnessCheckSynthesisSummary,
    LookupRangeCheck.witnessShortCheckSynthesisSummary,
    LookupRangeCheck.witnessCheckDecomposedSynthesisSummary,
    Sinsemilla.HashToPoint.hashCircuitSynthesisSummary,
    Sinsemilla.HashToPoint.hashRegionSynthesisSummary,
    Sinsemilla.Chain.circuitSynthesisSummary,
    Sinsemilla.Chain.slotIterationSynthesisSummary,
    Sinsemilla.Chain.slotSynthesisSummary,
    Sinsemilla.HashPiece.circuitSynthesisSummary,
    Sinsemilla.HashPiece.loopSynthesisSummary,
    RegionSynthesisSummary.repeatColumns,
    SynthesisSummary.combine_physicalRegionShapes,
    SynthesisSummary.ofRegion_physicalRegionShapes,
    SynthesisSummary.foldr_combine_physicalRegionShapes,
    Circuit.loadPrivateSynthesisSummary,
    Ecc.WitnessPoint.pointNonIdSynthesisSummary,
    Sinsemilla.HashToPoint.witnessMessagePieceSynthesisSummary,
    List.map_append]
  rw [fullWidthPhysicalShapes]
  simp only [← Multiset.map_coe, ← Multiset.coe_add,
    Multiset.coe_singleton, Multiset.map_singleton]
  simp only [
    RegionSynthesisSummary.ofColumns,
    RegionSynthesisSummary.toRegionShapeSummary,
    RegionShapeSummary.withoutSelectors, unionColumns]
  simp [NoteCommit.Main.ns, Sinsemilla.Chain.prefixRows,
    Sinsemilla.HashPiece.roundColumns,
    RegionSynthesisSummary.combine,
    actionConfig, Circuit.configure,
    Circuit.configureBase, Circuit.configureChips, Circuit.configureShared,
    Circuit.configureAdvices, Circuit.configureAdviceEqualitiesLow,
    Circuit.configureAdviceEqualitiesHigh, Circuit.configureEqualities,
    Circuit.configureLagrange, AddChip.configure, Ecc.configure,
    NoteCommit.configure, NoteCommit.DecomposeB.configure,
    NoteCommit.DecomposeD.configure, NoteCommit.DecomposeE.configure,
    NoteCommit.DecomposeG.configure, NoteCommit.DecomposeH.configure,
    NoteCommit.GdCanonicity.configure, NoteCommit.PkdCanonicity.configure,
    NoteCommit.PsiCanonicity.configure, NoteCommit.RhoCanonicity.configure,
    NoteCommit.ValueCanonicity.configure, NoteCommit.YCanonicity.configure,
    LookupRangeCheck.configure, Poseidon.configure,
    Sinsemilla.HashPiece.configure, Sinsemilla.Merkle.configure,
    CondSwap.configure, Ecc.Add.add, Ecc.AddIncomplete.add,
    Ecc.Mul.configure, Ecc.MulFixed.BaseFieldElem.configure,
    Ecc.MulFixed.FullWidth.configure, Ecc.MulFixed.Short.configure,
    Ecc.MulFixed.configure, Ecc.WitnessPoint.configure,
    Ecc.MulComplete.configure, Ecc.MulIncomplete.configure,
    Ecc.MulOverflow.configure, Sinsemilla.Merkle.Gate.configure,
    lookupTableColumn, Configure.run_fst, keygen_norm]
  simp [plannerShape,
    RegionShapeSummary.normalized, physicalColumns, unionColumns,
    addColumn, sortRegionColumns, List.insertionSort, List.orderedInsert,
    RegionColumn.lt, RegionColumn.ordKey, RegionColumn.kindRank]
  simp only [listCoe_cons, Multiset.coe_nil]
  letI : DecidableEq RegionShapeSummary := Classical.decEq _
  rw [Multiset.ext]
  intro summary
  simp only [Multiset.count_cons, Multiset.count_add,
    Multiset.count_nsmul, Multiset.count_singleton,
    Multiset.count_zero]
  omega

set_option maxRecDepth 10000 in
private theorem actionOwnerPlannerBlocks_eq :
    plannerBlockMultiset witnessPlannerBlocks +
        plannerBlockMultiset checksPlannerBlocks +
        plannerBlockMultiset notesPlannerBlocks +
        plannerBlockMultiset crossAddressPlannerBlocks =
      plannerBlockMultiset actionPlannerBlocks := by
  unfold witnessPlannerBlocks checksPlannerBlocks notesPlannerBlocks
    crossAddressPlannerBlocks actionPlannerBlocks plannerBlockMultiset
  simp only [List.foldr_cons, List.foldr_nil]
  abel

set_option maxRecDepth 10000 in
private theorem actionCanonicalPlannerSummaries_normalized :
    (actionCanonicalPlannerSummaries.map RegionShapeSummary.normalized :
      Multiset RegionShapeSummary) =
      plannerBlockMultiset actionPlannerBlocks := by
  rw [show actionCanonicalPlannerSummaries =
      expandPlannerBlocks actionPlannerBlocks by rfl,
    ← Multiset.map_coe, coe_expandPlannerBlocks]
  unfold actionPlannerBlocks plannerBlockMultiset
  simp only [List.foldr_cons, List.foldr_nil, Multiset.map_add,
    Multiset.map_nsmul, Multiset.map_singleton, Multiset.map_zero]
  simp [plannerShape, RegionShapeSummary.normalized, sortRegionColumns,
    List.insertionSort, RegionColumn.lt,
    RegionColumn.ordKey, RegionColumn.kindRank]

/-- The Action circuit's reduced synthesis summary contains exactly the compact
planner blocks, modulo the irrelevant order of columns within each region. -/
theorem actionPlannerSummaries_normalized_multiset :
    (actionPlannerSummaries.map RegionShapeSummary.normalized :
      Multiset RegionShapeSummary) =
    (actionCanonicalPlannerSummaries.map RegionShapeSummary.normalized :
      Multiset RegionShapeSummary) := by
  rw [actionPlannerSummaries_eq_physicalRegionShapes,
    actionCircuit_synthesisSummary_eq,
    Circuit.mainPostSynthesisSummary_physicalRegionShapes]
  simp only [List.map_append, ← Multiset.coe_add]
  rw [witnessPlannerBlocks_correct, checksPlannerBlocks_correct,
    notesPlannerBlocks_correct, crossAddressPlannerBlocks_correct,
    actionOwnerPlannerBlocks_eq,
    actionCanonicalPlannerSummaries_normalized]

/-- The same canonical order, split only where one equal-shape run crosses an
occupied interval. Each entry can therefore use the symbolic consecutive-run
planner theorem. Zero-row summaries are omitted because they change neither
the allocation state nor its endpoint. -/
def actionPlannerTrace : List V1.PlannedSummaryBlock :=
  [{ count := 1, summary := plannerShape [0,1,2,3,4,5,6,7,8,9] 137,
      start := 0 },
   { count := 1, summary := plannerShape [0,1,2,3,4] 110 [3,12],
      start := 137 },
   { count := 1, summary := plannerShape [5,6,7,8,9] 110 [4,13],
      start := 137 },
   { count := 1, summary := plannerShape [0,1,2,3,4,5] 86
      [3,4,5,6,7,8,9,10,11], start := 247 },
   { count := 5, summary := plannerShape [0,1,2,3,4,5] 85
      [3,4,5,6,7,8,9,10,11], start := 333 },
   { count := 16, summary := plannerShape [0,1,2,3,4] 53 [3,12],
      start := 758 },
   { count := 16, summary := plannerShape [5,6,7,8,9] 53 [4,13],
      start := 758 },
   { count := 1, summary := plannerShape [0,1,2,3,4] 52 [3,12],
      start := 1606 },
   { count := 1, summary := plannerShape [5,6,7,8] 37 [5,6,7,8,9,10],
      start := 1606 },
   { count := 1, summary := plannerShape [0,1,2,3,4,5] 23
      [3,4,5,6,7,8,9,10,11], start := 1658 },
   { count := 1, summary := plannerShape [0,1,2,3,4,5,6,7,8,9] 4,
      start := 1681 },
   { count := 4, summary := plannerShape [9] 26, start := 247 },
   { count := 14, summary := plannerShape [0,1,2,3,4,5,6,7,8] 2,
      start := 1685 },
   { count := 5, summary := plannerShape [9] 15, start := 351 },
   { count := 11, summary := plannerShape [9] 14, start := 426 },
   { count := 16, summary := plannerShape [0,1,2,3,4] 2,
      start := 1713 },
   { count := 7, summary := plannerShape [5,6,7,8,9] 2,
      start := 1643 },
   { count := 13, summary := plannerShape [5,6,7,8,9] 2,
      start := 1713 },
   { count := 3, summary := plannerShape [6,7,8] 3, start := 247 },
   { count := 8, summary := plannerShape [6,7,8,9] 2, start := 580 },
   { count := 1, summary := plannerShape [0,1,2,3,4,5,6,7] 1,
      start := 1745 },
   { count := 4, summary := plannerShape [6,7,8] 2, start := 256 },
   { count := 16, summary := plannerShape [0,1,2,3,4] 1,
      start := 1746 },
   { count := 1, summary := plannerShape [5,6,7,8,9] 1,
      start := 1657 },
   { count := 6, summary := plannerShape [5,6,7,8,9] 1,
      start := 1739 },
   { count := 9, summary := plannerShape [5,6,7,8,9] 1,
      start := 1746 },
   { count := 2, summary := plannerShape [6,7] 2, start := 264 },
   { count := 2, summary := plannerShape [6,7,8,9] 1, start := 596 },
   { count := 53, summary := plannerShape [9] 3, start := 598 },
   { count := 12, summary := plannerShape [9] 3, start := 1606 },
   { count := 7, summary := plannerShape [9] 3, start := 1658 },
   { count := 2, summary := plannerShape [9] 3, start := 1685 },
   { count := 7, summary := plannerShape [9] 3, start := 1691 },
   { count := 8, summary := plannerShape [9] 3, start := 1755 },
   { count := 6, summary := plannerShape [6,7,8] 1, start := 268 },
   { count := 6, summary := plannerShape [0,1] 1, start := 1762 },
   { count := 1, summary := plannerShape [9] 1, start := 757 },
   { count := 1, summary := plannerShape [9] 1, start := 1642 },
   { count := 61, summary := plannerShape [6] 1, start := 274 },
   { count := 6, summary := plannerShape [0] 1, start := 1768 },
   { count := 56, summary := plannerShape [7] 1, start := 274 }]

def actionPlannerTraceSummaries : List RegionShapeSummary :=
  (V1.PlannedSummaryBlock.blocks actionPlannerTrace).flatMap fun block =>
    List.replicate block.1 block.2

set_option maxRecDepth 10000 in
theorem actionPlannerTrace_endpoint :
    V1.PlannedSummaryBlock.endpointFrom 0 actionPlannerTrace = 1779 := by
  decide

macro "trace_step" : tactic =>
  `(tactic|
    (unfold V1.PlannedSummaryBlock.TraceLawfulAfter
     refine ⟨by norm_num,
       by simp [RegionShapeSummary.WellFormed, plannerShape],
       by simp [plannerShape], ?_, ?_, ?_⟩
     · simp [V1.PlannedSummaryBlock.FitsAfterAt, plannerShape,
         RowIntervalsDisjoint] <;> omega
     · intro candidate hfits
       simp [V1.PlannedSummaryBlock.FitsAfterAt, plannerShape,
         RowIntervalsDisjoint] at hfits
       try norm_num at hfits ⊢
       try omega
     simp only [List.nil_append, List.cons_append, List.append_nil]))

private theorem actionPlannerTrace_chunk1 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionPlannerTrace.take 0)
      ((actionPlannerTrace.drop 0).take 5) := by
  unfold actionPlannerTrace
  trace_step
  trace_step
  trace_step
  trace_step
  trace_step
  trivial

private theorem actionPlannerTrace_chunk2 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionPlannerTrace.take 5)
      ((actionPlannerTrace.drop 5).take 5) := by
  unfold actionPlannerTrace
  trace_step
  trace_step
  trace_step
  trace_step
  trace_step
  trivial

private theorem actionPlannerTrace_chunk3 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionPlannerTrace.take 10)
      ((actionPlannerTrace.drop 10).take 5) := by
  unfold actionPlannerTrace
  trace_step
  trace_step
  trace_step
  trace_step
  trace_step
  trivial

private theorem actionPlannerTrace_chunk4 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionPlannerTrace.take 15)
      ((actionPlannerTrace.drop 15).take 5) := by
  unfold actionPlannerTrace
  trace_step
  trace_step
  trace_step
  trace_step
  trace_step
  trivial

private theorem actionPlannerTrace_chunk5 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionPlannerTrace.take 20)
      ((actionPlannerTrace.drop 20).take 5) := by
  unfold actionPlannerTrace
  trace_step
  trace_step
  trace_step
  trace_step
  trace_step
  trivial

private theorem actionPlannerTrace_chunk6 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionPlannerTrace.take 25)
      ((actionPlannerTrace.drop 25).take 5) := by
  unfold actionPlannerTrace
  trace_step
  trace_step
  trace_step
  trace_step
  trace_step
  trivial

private theorem actionPlannerTrace_chunk7 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionPlannerTrace.take 30)
      ((actionPlannerTrace.drop 30).take 5) := by
  unfold actionPlannerTrace
  trace_step
  trace_step
  trace_step
  trace_step
  trace_step
  trivial

private theorem actionPlannerTrace_chunk8 :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionPlannerTrace.take 35)
      ((actionPlannerTrace.drop 35).take 6) := by
  unfold actionPlannerTrace
  trace_step
  trace_step
  trace_step
  trace_step
  trace_step
  trace_step
  trivial

theorem actionPlannerTrace_traceLawful :
    V1.PlannedSummaryBlock.TraceLawfulAfter [] actionPlannerTrace := by
  rw [show actionPlannerTrace = ((actionPlannerTrace.drop 0).take 5) ++ (((actionPlannerTrace.drop 5).take 5) ++ (((actionPlannerTrace.drop 10).take 5) ++ (((actionPlannerTrace.drop 15).take 5) ++ (((actionPlannerTrace.drop 20).take 5) ++ (((actionPlannerTrace.drop 25).take 5) ++ (((actionPlannerTrace.drop 30).take 5) ++ (((actionPlannerTrace.drop 35).take 6)))))))) by
    simp [actionPlannerTrace]]
  rw [V1.PlannedSummaryBlock.traceLawfulAfter_append]
  constructor
  · simpa [actionPlannerTrace] using actionPlannerTrace_chunk1
  rw [V1.PlannedSummaryBlock.traceLawfulAfter_append]
  constructor
  · simpa [actionPlannerTrace] using actionPlannerTrace_chunk2
  rw [V1.PlannedSummaryBlock.traceLawfulAfter_append]
  constructor
  · simpa [actionPlannerTrace] using actionPlannerTrace_chunk3
  rw [V1.PlannedSummaryBlock.traceLawfulAfter_append]
  constructor
  · simpa [actionPlannerTrace] using actionPlannerTrace_chunk4
  rw [V1.PlannedSummaryBlock.traceLawfulAfter_append]
  constructor
  · simpa [actionPlannerTrace] using actionPlannerTrace_chunk5
  rw [V1.PlannedSummaryBlock.traceLawfulAfter_append]
  constructor
  · simpa [actionPlannerTrace] using actionPlannerTrace_chunk6
  rw [V1.PlannedSummaryBlock.traceLawfulAfter_append]
  constructor
  · simpa [actionPlannerTrace] using actionPlannerTrace_chunk7
  simpa [actionPlannerTrace] using actionPlannerTrace_chunk8

theorem actionPlannerTrace_lawful :
    V1.PlannedSummaryBlock.Lawful V1.AllocationView.empty actionPlannerTrace := by
  exact V1.PlannedSummaryBlock.lawful_of_traceLawfulAfter [] actionPlannerTrace
    (by simp) actionPlannerTrace_traceLawful

theorem actionPlannerTrace_blocks_endpoint :
    (V1.slotSummaryBlocksState
      (V1.PlannedSummaryBlock.blocks actionPlannerTrace) 0
      (∅ : CircuitAllocations)).1 = 1779 := by
  have hresult := V1.PlannedSummaryBlock.slotSummaryBlocksState_eq
    actionPlannerTrace 0 (∅ : CircuitAllocations) V1.AllocationView.empty
    (by simp [V1.AllocationView.Represents, V1.AllocationView.empty])
    (by simp [V1.AllocationView.Valid, V1.AllocationView.empty,
      Allocations.Valid]) actionPlannerTrace_lawful
  exact hresult.1.trans actionPlannerTrace_endpoint

set_option maxRecDepth 10000 in
theorem actionCanonicalPlannerSummaries_eq_trace :
    actionCanonicalPlannerSummaries =
      actionPlannerTraceSummaries ++
        List.replicate 2 (plannerShape [] 0) := by
  unfold actionCanonicalPlannerSummaries actionPlannerTraceSummaries
    V1.PlannedSummaryBlock.blocks actionPlannerBlocks actionPlannerTrace
  simp only [List.map_cons, List.map_nil, List.flatMap_cons,
    List.flatMap_nil]
  rw [show List.replicate 20 (plannerShape [5,6,7,8,9] 2) =
      List.replicate 7 (plannerShape [5,6,7,8,9] 2) ++
        List.replicate 13 (plannerShape [5,6,7,8,9] 2) by
      rw [← List.replicate_add],
    show List.replicate 16 (plannerShape [5,6,7,8,9] 1) =
      List.replicate 1 (plannerShape [5,6,7,8,9] 1) ++
        List.replicate 6 (plannerShape [5,6,7,8,9] 1) ++
          List.replicate 9 (plannerShape [5,6,7,8,9] 1) by
      rw [← List.replicate_add, ← List.replicate_add],
    show List.replicate 2 (plannerShape [6,7] 2) =
      List.replicate 1 (plannerShape [6,7] 2) ++
        List.replicate 1 (plannerShape [6,7] 2) by
      rw [← List.replicate_add],
    show List.replicate 89 (plannerShape [9] 3) =
      List.replicate 53 (plannerShape [9] 3) ++
        List.replicate 12 (plannerShape [9] 3) ++
          List.replicate 7 (plannerShape [9] 3) ++
            List.replicate 2 (plannerShape [9] 3) ++
              List.replicate 7 (plannerShape [9] 3) ++
                List.replicate 8 (plannerShape [9] 3) by
      repeat' rw [← List.replicate_add],
    show List.replicate 2 (plannerShape [9] 1) =
      List.replicate 1 (plannerShape [9] 1) ++
        List.replicate 1 (plannerShape [9] 1) by
      rw [← List.replicate_add]]
  simp only [List.append_assoc, List.append_nil]

set_option maxRecDepth 10000 in
theorem actionCanonicalPlannerSummaries_endpoint :
    (V1.slotSummaryStateFromWith 0 actionCanonicalPlannerSummaries
      (∅ : CircuitAllocations)).1 = 1779 := by
  rw [actionCanonicalPlannerSummaries_eq_trace,
    V1.slotSummaryStateFromWith_append]
  have htrace :
      (V1.slotSummaryStateFromWith 0 actionPlannerTraceSummaries
        (∅ : CircuitAllocations)).1 = 1779 := by
    rw [actionPlannerTraceSummaries,
      V1.slotSummaryStateFromWith_flatMap_replicate]
    exact actionPlannerTrace_blocks_endpoint
  generalize hresult : V1.slotSummaryStateFromWith 0
    actionPlannerTraceSummaries (∅ : CircuitAllocations) = result
  rcases result with ⟨endpoint, allocations⟩
  rw [hresult] at htrace
  simp only at htrace
  rw [show plannerShape [] 0 =
      ({ columns := [], rowCount := 0 } : RegionShapeSummary) by
        simp [plannerShape],
    V1.slotSummaryStateFromWith_replicate_empty]
  exact htrace


end Zcash.Circuits.Action
