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

def emptyPlannerView : V1.AllocationView := fun _ : RegionColumn =>
  (#[] : Allocations)

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


end Zcash.Circuits.Action
