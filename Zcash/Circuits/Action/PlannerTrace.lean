import Zcash.Circuits.Action.Planner
import Clean.Halo2.Keygen.PdqsortCorrectness

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

private def aboveKey (threshold : ℕ)
    (summaries : List RegionShapeSummary) : List RegionShapeSummary :=
  summaries.filter fun summary => decide (threshold < summary.key)

private def atMostKey (threshold : ℕ)
    (summaries : List RegionShapeSummary) : List RegionShapeSummary :=
  summaries.filter fun summary => decide (summary.key ≤ threshold)

private theorem sorted_eq_aboveKey_append_atMostKey
    (threshold : ℕ) (summaries : List RegionShapeSummary)
    (hsorted :
      (summaries.map fun summary =>
        (summary.key : OrderDual ℕ)).SortedLE) :
    summaries = aboveKey threshold summaries ++ atMostKey threshold summaries := by
  induction summaries with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.sortedLE_iff_pairwise, List.map_cons,
        List.pairwise_cons] at hsorted
      by_cases habove : threshold < head.key
      · rw [aboveKey, List.filter_cons_of_pos (by simp [habove]),
          atMostKey, List.filter_cons_of_neg (by simp [habove])]
        apply congrArg (List.cons head)
        apply inductionHypothesis
        rw [List.sortedLE_iff_pairwise]
        exact hsorted.2
      · have htailAtMost : ∀ summary ∈ tail, summary.key ≤ threshold := by
          intro summary hsummary
          have hdescending : summary.key ≤ head.key :=
            hsorted.1 (summary.key : OrderDual ℕ)
              (List.mem_map.mpr ⟨summary, hsummary, rfl⟩)
          omega
        have htailAbove : aboveKey threshold tail = [] := by
          rw [aboveKey, List.filter_eq_nil_iff]
          intro summary hsummary
          simp only [Bool.not_eq_true, decide_eq_false_iff_not]
          exact Nat.not_lt.mpr (htailAtMost summary hsummary)
        have htailAtMostEq : atMostKey threshold tail = tail := by
          rw [atMostKey, List.filter_eq_self]
          intro summary hsummary
          simp only [decide_eq_true_eq]
          exact htailAtMost summary hsummary
        have hheadAtMost : head.key ≤ threshold := by omega
        rw [show aboveKey threshold (head :: tail) = [] by
            rw [aboveKey, List.filter_cons_of_neg (by simp [habove])]
            exact htailAbove,
          show atMostKey threshold (head :: tail) = head :: tail by
            rw [atMostKey,
              List.filter_cons_of_pos (by simp [hheadAtMost])]
            exact congrArg (List.cons head) htailAtMostEq,
          List.nil_append]

private theorem filter_key_sorted
    (predicate : RegionShapeSummary → Bool)
    (summaries : List RegionShapeSummary)
    (hsorted :
      (summaries.map fun summary =>
        (summary.key : OrderDual ℕ)).SortedLE) :
    (((summaries.filter predicate).map fun summary =>
      (summary.key : OrderDual ℕ))).SortedLE := by
  rw [List.sortedLE_iff_pairwise, List.pairwise_map] at hsorted ⊢
  exact hsorted.filter predicate

private theorem perm_replicate_append_singleton_iff
    {T : Type} [DecidableEq T] {items : List T} {repeated singleton : T}
    (hne : repeated ≠ singleton) (count : ℕ) :
    items.Perm (List.replicate count repeated ++ [singleton]) ↔
      ∃ before after, before + after = count ∧
        items = List.replicate before repeated ++
          singleton :: List.replicate after repeated := by
  constructor
  · intro hperm
    have hsingleton : singleton ∈ items :=
      hperm.symm.subset (by simp)
    obtain ⟨beforeItems, afterItems, hitems⟩ :=
      List.mem_iff_append.mp hsingleton
    have hcounts := (List.perm_replicate_append_replicate
      (l := items) (a := repeated) (b := singleton)
      (m := count) (n := 1) hne).mp hperm
    have hbeforeOnly : ∀ item ∈ beforeItems, item = repeated := by
      intro item hitem
      have hmember := hcounts.2.2 (hitems ▸
        List.mem_append.mpr (Or.inl hitem))
      rw [List.mem_cons, List.mem_singleton] at hmember
      rcases hmember with hrepeat | hsingle
      · exact hrepeat
      · have hitemSingleton : singleton ∈ beforeItems := hsingle ▸ hitem
        have hsingletonCount : items.count singleton = 1 := hcounts.2.1
        rw [hitems, List.count_append, List.count_cons] at hsingletonCount
        simp only [BEq.beq, decide_true, if_true] at hsingletonCount
        have hbeforeZero : beforeItems.count singleton = 0 := by omega
        exact (List.count_eq_zero.mp hbeforeZero hitemSingleton).elim
    have hafterOnly : ∀ item ∈ afterItems, item = repeated := by
      intro item hitem
      have hmember := hcounts.2.2 (hitems ▸
        List.mem_append.mpr (Or.inr (List.mem_cons_of_mem singleton hitem)))
      rw [List.mem_cons, List.mem_singleton] at hmember
      rcases hmember with hrepeat | hsingle
      · exact hrepeat
      · have hitemSingleton : singleton ∈ afterItems := hsingle ▸ hitem
        have hsingletonCount : items.count singleton = 1 := hcounts.2.1
        rw [hitems, List.count_append, List.count_cons] at hsingletonCount
        simp only [BEq.beq, decide_true, if_true] at hsingletonCount
        have hafterZero : afterItems.count singleton = 0 := by omega
        exact (List.count_eq_zero.mp hafterZero hitemSingleton).elim
    have hbefore := List.eq_replicate_length.mpr hbeforeOnly
    have hafter := List.eq_replicate_length.mpr hafterOnly
    refine ⟨beforeItems.length, afterItems.length, ?_, ?_⟩
    · have hlength := hperm.length_eq
      rw [hitems] at hlength
      simp only [List.length_append, List.length_cons,
        List.length_replicate, List.length_nil] at hlength
      omega
    · exact hitems.trans (congrArg₂ (fun left right =>
        left ++ singleton :: right) hbefore hafter)
  · rintro ⟨before, after, hcount, rfl⟩
    have hperm := (List.perm_replicate_append_replicate
      (l := List.replicate before repeated ++
        singleton :: List.replicate after repeated)
      (a := repeated) (b := singleton) (m := count) (n := 1) hne).mpr
        (by
          refine ⟨by simp [Ne.symm hne, hcount],
            ?_, ?_⟩
          · rw [List.count_append, List.count_cons,
              List.count_replicate, List.count_replicate]
            simp [hne]
          rw [List.append_subset, List.cons_subset]
          refine ⟨?_, by simp, ?_⟩ <;>
            intro item hitem <;>
            rw [List.mem_replicate] at hitem <;>
            simp [hitem.2])
    simpa [List.replicate_succ] using hperm

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

private theorem expandPlannerBlocks_key_sorted
    {K : Type} [LinearOrder K] (key : RegionShapeSummary → K)
    (blocks : List (ℕ × RegionShapeSummary))
    (hsorted : (blocks.map fun block => key block.2).SortedLE) :
    ((expandPlannerBlocks blocks).map key).SortedLE := by
  induction blocks with
  | nil =>
      rw [List.sortedLE_iff_pairwise]
      exact List.Pairwise.nil
  | cons block rest inductionHypothesis =>
      rw [List.sortedLE_iff_pairwise, List.map_cons,
        List.pairwise_cons] at hsorted
      rw [expandPlannerBlocks, List.flatMap_cons, List.map_append,
        List.sortedLE_iff_pairwise, List.pairwise_append]
      refine ⟨?_, ?_, ?_⟩
      · rw [← List.sortedLE_iff_pairwise]
        simpa only [List.map_replicate] using
          List.sortedLE_replicate (a := key block.2) block.1
      · have hrest := inductionHypothesis (by
          rw [List.sortedLE_iff_pairwise]
          exact hsorted.2)
        rw [List.sortedLE_iff_pairwise] at hrest
        exact hrest
      · intro left hleft right hright
        rw [List.mem_map] at hleft hright
        obtain ⟨leftSummary, hleftSummary, rfl⟩ := hleft
        obtain ⟨rightSummary, hrightSummary, rfl⟩ := hright
        rw [List.mem_replicate] at hleftSummary
        rcases hleftSummary with ⟨_, hleftSummary⟩
        subst leftSummary
        apply hsorted.1
        rw [List.mem_flatMap] at hrightSummary
        obtain ⟨rightBlock, hrightBlock, hrightSummary⟩ := hrightSummary
        rw [List.mem_replicate] at hrightSummary
        rcases hrightSummary with ⟨_, rfl⟩
        exact List.mem_map.mpr ⟨rightBlock, hrightBlock, rfl⟩

private theorem actionCanonicalPlannerSummaries_key_sorted :
    ((actionCanonicalPlannerSummaries.map fun summary =>
      (summary.key : OrderDual ℕ))).SortedLE := by
  rw [show actionCanonicalPlannerSummaries =
      expandPlannerBlocks actionPlannerBlocks by rfl]
  apply expandPlannerBlocks_key_sorted
  unfold actionPlannerBlocks plannerShape RegionShapeSummary.key
    RegionShapeSummary.adviceCols RegionColumn.isAdvice
  decide

private theorem actionSortedPlannerSummaries_key_sorted :
    ((actionSortedPlannerSummaries.map fun summary =>
      (summary.key : OrderDual ℕ))).SortedLE := by
  have hsorted :=
    V1.sortedSummaryOrder_key_sorted actionCircuit.operations
  rw [List.sortedLE_iff_pairwise, List.pairwise_map] at hsorted ⊢
  simpa only [actionSortedPlannerSummaries, List.pairwise_map,
    RegionShapeSummary.withoutSelectors_key] using hsorted

private theorem actionPlannerBlocks_wellFormed :
    actionPlannerBlocks.Forall fun block => block.2.WellFormed := by
  unfold actionPlannerBlocks plannerShape RegionShapeSummary.WellFormed
  decide

private theorem expandPlannerBlocks_wellFormed
    (blocks : List (ℕ × RegionShapeSummary))
    (hblocks : blocks.Forall fun block => block.2.WellFormed) :
    (expandPlannerBlocks blocks).Forall RegionShapeSummary.WellFormed := by
  rw [List.forall_iff_forall_mem]
  intro summary hsummary
  rw [expandPlannerBlocks, List.mem_flatMap] at hsummary
  obtain ⟨block, hblock, hsummary⟩ := hsummary
  rw [List.mem_replicate] at hsummary
  exact hsummary.2 ▸
    List.forall_iff_forall_mem.mp hblocks block hblock

private theorem actionCanonicalPlannerSummaries_wellFormed :
    actionCanonicalPlannerSummaries.Forall RegionShapeSummary.WellFormed := by
  rw [show actionCanonicalPlannerSummaries =
      expandPlannerBlocks actionPlannerBlocks by rfl]
  exact expandPlannerBlocks_wellFormed actionPlannerBlocks
    actionPlannerBlocks_wellFormed

private theorem actionPlannerBlocks_regular_ties :
    actionPlannerBlocks.Forall fun first =>
      actionPlannerBlocks.Forall fun second =>
        first.2.key = second.2.key → first.2.key ≠ 8 →
          first.2.key ≠ 4 →
            (sortRegionColumns first.2.columns =
                sortRegionColumns second.2.columns ∧
              first.2.rowCount = second.2.rowCount) ∨
              (first.2.columns.all fun column =>
                decide (column ∉ second.2.columns)) = true := by
  unfold actionPlannerBlocks plannerShape RegionShapeSummary.key
    RegionShapeSummary.adviceCols RegionColumn.isAdvice
  decide

private theorem actionCanonicalPlannerSummaries_regular_ties
    {first second : RegionShapeSummary}
    (hfirst : first ∈ actionCanonicalPlannerSummaries)
    (hsecond : second ∈ actionCanonicalPlannerSummaries)
    (hkey : first.key = second.key)
    (hne8 : first.key ≠ 8) (hne4 : first.key ≠ 4) :
    first.PlacementEquivalent second ∨
      List.Disjoint first.columns second.columns := by
  rw [actionCanonicalPlannerSummaries, List.mem_flatMap] at hfirst hsecond
  obtain ⟨firstBlock, hfirstBlock, hfirst⟩ := hfirst
  obtain ⟨secondBlock, hsecondBlock, hsecond⟩ := hsecond
  rw [List.mem_replicate] at hfirst hsecond
  have hfirstLaw := List.forall_iff_forall_mem.mp
    actionPlannerBlocks_regular_ties firstBlock hfirstBlock
  have hresult := List.forall_iff_forall_mem.mp hfirstLaw secondBlock
    hsecondBlock (by simpa only [hfirst.2, hsecond.2] using hkey)
    (by simpa only [hfirst.2] using hne8)
    (by simpa only [hfirst.2] using hne4)
  rcases hresult with hequivalent | hdisjoint
  · exact Or.inl (by simpa only [hfirst.2, hsecond.2] using hequivalent)
  · right
    rw [List.disjoint_left]
    intro column hfirstColumn hsecondColumn
    have hnotSecond := List.all_eq_true.mp hdisjoint column
      (by simpa only [hfirst.2] using hfirstColumn)
    simp only [decide_eq_true_eq] at hnotSecond
    exact hnotSecond (by simpa only [hsecond.2] using hsecondColumn)

private def plannerAbove8 (summaries : List RegionShapeSummary) :=
  aboveKey 8 summaries

private def plannerKey8 (summaries : List RegionShapeSummary) :=
  summaries.filter fun summary => decide (summary.key = 8)

private def plannerBetween8And4 (summaries : List RegionShapeSummary) :=
  summaries.filter fun summary => decide (4 < summary.key ∧ summary.key < 8)

private def plannerKey4 (summaries : List RegionShapeSummary) :=
  summaries.filter fun summary => decide (summary.key = 4)

private def plannerBelow4 (summaries : List RegionShapeSummary) :=
  summaries.filter fun summary => decide (summary.key < 4)

private theorem plannerSegments_eq
    (summaries : List RegionShapeSummary)
    (hsorted :
      (summaries.map fun summary =>
        (summary.key : OrderDual ℕ)).SortedLE) :
    summaries =
      plannerAbove8 summaries ++ plannerKey8 summaries ++
        plannerBetween8And4 summaries ++ plannerKey4 summaries ++
          plannerBelow4 summaries := by
  have hsplit8 := sorted_eq_aboveKey_append_atMostKey 8 summaries hsorted
  have hsorted8 := filter_key_sorted
    (fun summary => decide (summary.key ≤ 8)) summaries hsorted
  have hsplit7 := sorted_eq_aboveKey_append_atMostKey 7
    (atMostKey 8 summaries) hsorted8
  have hsorted7 := filter_key_sorted
    (fun summary => decide (summary.key ≤ 7)) (atMostKey 8 summaries)
    hsorted8
  have hsplit4 := sorted_eq_aboveKey_append_atMostKey 4
    (atMostKey 7 (atMostKey 8 summaries)) hsorted7
  have hsorted4 := filter_key_sorted
    (fun summary => decide (summary.key ≤ 4))
    (atMostKey 7 (atMostKey 8 summaries)) hsorted7
  have hsplit3 := sorted_eq_aboveKey_append_atMostKey 3
    (atMostKey 4 (atMostKey 7 (atMostKey 8 summaries))) hsorted4
  have hkey8 :
      aboveKey 7 (atMostKey 8 summaries) = plannerKey8 summaries := by
    unfold aboveKey atMostKey plannerKey8
    rw [List.filter_filter]
    apply List.filter_congr
    intro summary _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hmiddle :
      aboveKey 4 (atMostKey 7 (atMostKey 8 summaries)) =
        plannerBetween8And4 summaries := by
    unfold aboveKey atMostKey plannerBetween8And4
    rw [List.filter_filter, List.filter_filter]
    apply List.filter_congr
    intro summary _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hkey4 :
      aboveKey 3 (atMostKey 4 (atMostKey 7 (atMostKey 8 summaries))) =
        plannerKey4 summaries := by
    unfold aboveKey atMostKey plannerKey4
    rw [List.filter_filter, List.filter_filter, List.filter_filter]
    apply List.filter_congr
    intro summary _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  have hbelow :
      atMostKey 3 (atMostKey 4 (atMostKey 7 (atMostKey 8 summaries))) =
        plannerBelow4 summaries := by
    unfold atMostKey plannerBelow4
    rw [List.filter_filter, List.filter_filter, List.filter_filter]
    apply List.filter_congr
    intro summary _
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  calc
    summaries = aboveKey 8 summaries ++ atMostKey 8 summaries := hsplit8
    _ = aboveKey 8 summaries ++
        (aboveKey 7 (atMostKey 8 summaries) ++
          atMostKey 7 (atMostKey 8 summaries)) :=
      congrArg (fun tail => aboveKey 8 summaries ++ tail) hsplit7
    _ = aboveKey 8 summaries ++
        (aboveKey 7 (atMostKey 8 summaries) ++
          (aboveKey 4 (atMostKey 7 (atMostKey 8 summaries)) ++
            atMostKey 4 (atMostKey 7 (atMostKey 8 summaries)))) :=
      congrArg
        (fun tail => aboveKey 8 summaries ++
          (aboveKey 7 (atMostKey 8 summaries) ++ tail)) hsplit4
    _ = aboveKey 8 summaries ++
        (aboveKey 7 (atMostKey 8 summaries) ++
          (aboveKey 4 (atMostKey 7 (atMostKey 8 summaries)) ++
            (aboveKey 3
                (atMostKey 4 (atMostKey 7 (atMostKey 8 summaries))) ++
              atMostKey 3
                (atMostKey 4 (atMostKey 7 (atMostKey 8 summaries)))))) :=
      congrArg
        (fun tail => aboveKey 8 summaries ++
          (aboveKey 7 (atMostKey 8 summaries) ++
            (aboveKey 4 (atMostKey 7 (atMostKey 8 summaries)) ++ tail)))
        hsplit3
    _ = plannerAbove8 summaries ++ plannerKey8 summaries ++
        plannerBetween8And4 summaries ++ plannerKey4 summaries ++
          plannerBelow4 summaries := by
      rw [hkey8, hmiddle, hkey4, hbelow]
      simp only [plannerAbove8, List.append_assoc]

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

private theorem actionSortedPlannerSummaries_normalized_perm :
    (actionSortedPlannerSummaries.map RegionShapeSummary.normalized).Perm
      (actionCanonicalPlannerSummaries.map
        RegionShapeSummary.normalized) := by
  have hsorted : actionSortedPlannerSummaries.Perm
      actionPlannerSummaries := by
    have hperm :=
      V1.sortedSummaryOrder_perm_synthesisSummary actionCircuit.operations |>.map
        RegionShapeSummary.withoutSelectors
    simpa only [actionSortedPlannerSummaries, actionPlannerSummaries,
      actionCircuit.synthesisSummary_eq_operations] using hperm
  have hcanonical :
      (actionPlannerSummaries.map RegionShapeSummary.normalized).Perm
        (actionCanonicalPlannerSummaries.map
          RegionShapeSummary.normalized) :=
    Multiset.coe_eq_coe.mp actionPlannerSummaries_normalized_multiset
  exact (hsorted.map RegionShapeSummary.normalized).trans hcanonical

private theorem normalized_filter_perm
    (predicate : RegionShapeSummary → Bool)
    (hstable : ∀ summary,
      predicate summary.normalized = predicate summary) :
    ((actionSortedPlannerSummaries.filter predicate).map
        RegionShapeSummary.normalized).Perm
      ((actionCanonicalPlannerSummaries.filter predicate).map
        RegionShapeSummary.normalized) := by
  have hfiltered := actionSortedPlannerSummaries_normalized_perm.filter predicate
  rw [List.filter_map, List.filter_map] at hfiltered
  have hsimplify (summaries : List RegionShapeSummary) :
      summaries.filter (predicate ∘ RegionShapeSummary.normalized) =
        summaries.filter predicate := by
    apply List.filter_congr
    intro summary _
    exact hstable summary
  rw [hsimplify, hsimplify] at hfiltered
  exact hfiltered

private theorem plannerAbove8_normalized_perm :
    ((plannerAbove8 actionSortedPlannerSummaries).map
        RegionShapeSummary.normalized).Perm
      ((plannerAbove8 actionCanonicalPlannerSummaries).map
        RegionShapeSummary.normalized) := by
  apply normalized_filter_perm
  intro summary
  simp only [RegionShapeSummary.normalized_key_eq]

private theorem plannerKey8_normalized_perm :
    ((plannerKey8 actionSortedPlannerSummaries).map
        RegionShapeSummary.normalized).Perm
      ((plannerKey8 actionCanonicalPlannerSummaries).map
        RegionShapeSummary.normalized) := by
  apply normalized_filter_perm
  intro summary
  simp only [RegionShapeSummary.normalized_key_eq]

private theorem plannerBetween8And4_normalized_perm :
    ((plannerBetween8And4 actionSortedPlannerSummaries).map
        RegionShapeSummary.normalized).Perm
      ((plannerBetween8And4 actionCanonicalPlannerSummaries).map
        RegionShapeSummary.normalized) := by
  apply normalized_filter_perm
  intro summary
  simp only [RegionShapeSummary.normalized_key_eq]

private theorem plannerKey4_normalized_perm :
    ((plannerKey4 actionSortedPlannerSummaries).map
        RegionShapeSummary.normalized).Perm
      ((plannerKey4 actionCanonicalPlannerSummaries).map
        RegionShapeSummary.normalized) := by
  apply normalized_filter_perm
  intro summary
  simp only [RegionShapeSummary.normalized_key_eq]

private theorem plannerBelow4_normalized_perm :
    ((plannerBelow4 actionSortedPlannerSummaries).map
        RegionShapeSummary.normalized).Perm
      ((plannerBelow4 actionCanonicalPlannerSummaries).map
        RegionShapeSummary.normalized) := by
  apply normalized_filter_perm
  intro summary
  simp only [RegionShapeSummary.normalized_key_eq]

private def planner8Wide : RegionShapeSummary :=
  plannerShape [6,7,8,9] 2

private def planner8Short : RegionShapeSummary :=
  plannerShape [0,1,2,3,4,5,6,7] 1

private def planner4Narrow : RegionShapeSummary :=
  plannerShape [6,7] 2

private def planner4Wide : RegionShapeSummary :=
  plannerShape [6,7,8,9] 1

private theorem filter_expandPlannerBlocks
    (predicate : RegionShapeSummary → Bool)
    (blocks : List (ℕ × RegionShapeSummary)) :
    (expandPlannerBlocks blocks).filter predicate =
      expandPlannerBlocks (blocks.filter fun block => predicate block.2) := by
  induction blocks with
  | nil => rfl
  | cons block rest inductionHypothesis =>
      rw [expandPlannerBlocks, List.flatMap_cons, List.filter_append,
        show List.filter predicate
            (List.flatMap (fun block => List.replicate block.1 block.2) rest) =
          expandPlannerBlocks
            (List.filter (fun block => predicate block.2) rest) from
          inductionHypothesis]
      by_cases hpredicate : predicate block.2 = true
      · rw [show (block :: rest).filter (fun block =>
            predicate block.2) = block :: rest.filter (fun block =>
              predicate block.2) by simp [hpredicate],
          show expandPlannerBlocks
              (block :: rest.filter (fun block => predicate block.2)) =
            List.replicate block.1 block.2 ++
              expandPlannerBlocks
                (rest.filter (fun block => predicate block.2)) by
            rfl]
        simp [hpredicate]
      · rw [show (block :: rest).filter (fun block =>
            predicate block.2) = rest.filter (fun block =>
              predicate block.2) by simp [hpredicate]]
        simp [hpredicate]

private theorem plannerKey8_canonical_eq :
    plannerKey8 actionCanonicalPlannerSummaries =
      List.replicate 8 planner8Wide ++ [planner8Short] := by
  rw [show actionCanonicalPlannerSummaries =
      expandPlannerBlocks actionPlannerBlocks by rfl,
    plannerKey8, filter_expandPlannerBlocks]
  have hblocks :
      actionPlannerBlocks.filter
          (fun block => decide (block.2.key = 8)) =
        [(8, planner8Wide), (1, planner8Short)] := by
    unfold actionPlannerBlocks planner8Wide planner8Short plannerShape
      RegionShapeSummary.key RegionShapeSummary.adviceCols
      RegionColumn.isAdvice
    simp
  rw [hblocks]
  rfl

private theorem plannerKey4_canonical_eq :
    plannerKey4 actionCanonicalPlannerSummaries =
      List.replicate 2 planner4Narrow ++
        List.replicate 2 planner4Wide := by
  rw [show actionCanonicalPlannerSummaries =
      expandPlannerBlocks actionPlannerBlocks by rfl,
    plannerKey4, filter_expandPlannerBlocks]
  have hblocks :
      actionPlannerBlocks.filter
          (fun block => decide (block.2.key = 4)) =
        [(2, planner4Narrow), (2, planner4Wide)] := by
    unfold actionPlannerBlocks planner4Narrow planner4Wide plannerShape
      RegionShapeSummary.key RegionShapeSummary.adviceCols
      RegionColumn.isAdvice
    simp
  rw [hblocks]
  rfl

private theorem regularPlannerSegment_equivalent
    (predicate : RegionShapeSummary → Bool)
    (hnormalized :
      ((actionSortedPlannerSummaries.filter predicate).map
          RegionShapeSummary.normalized).Perm
        ((actionCanonicalPlannerSummaries.filter predicate).map
          RegionShapeSummary.normalized))
    (hregular : ∀ summary, predicate summary = true →
      summary.key ≠ 8 ∧ summary.key ≠ 4)
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) :
    V1.SummaryStateEquivalent
      (V1.slotSummaryStateFromWith initial
        (actionSortedPlannerSummaries.filter predicate) allocations)
      (V1.slotSummaryStateFromWith initial
        (actionCanonicalPlannerSummaries.filter predicate) allocations) := by
  apply V1.slotSummaryStateFromWith_eq_of_normalized_perm hnormalized
  · exact filter_key_sorted predicate actionSortedPlannerSummaries
      actionSortedPlannerSummaries_key_sorted
  · exact filter_key_sorted predicate actionCanonicalPlannerSummaries
      actionCanonicalPlannerSummaries_key_sorted
  · rw [List.forall_iff_forall_mem]
    intro summary hsummary
    rw [List.mem_filter] at hsummary
    exact List.forall_iff_forall_mem.mp
      actionCanonicalPlannerSummaries_wellFormed summary hsummary.1
  · intro first hfirst second hsecond hkey
    rw [List.mem_filter] at hfirst hsecond
    have hkeys := hregular first hfirst.2
    exact actionCanonicalPlannerSummaries_regular_ties hfirst.1 hsecond.1
      hkey hkeys.1 hkeys.2
  · exact hvalid

private theorem canonicalFiltered_wellFormed
    (predicate : RegionShapeSummary → Bool) :
    (actionCanonicalPlannerSummaries.filter predicate).Forall
      RegionShapeSummary.WellFormed := by
  rw [List.forall_iff_forall_mem]
  intro summary hsummary
  rw [List.mem_filter] at hsummary
  exact List.forall_iff_forall_mem.mp
    actionCanonicalPlannerSummaries_wellFormed summary hsummary.1

private theorem allocationsValid_of_summaryStateEquivalent
    {left right : ℕ × CircuitAllocations}
    (hequivalent : V1.SummaryStateEquivalent left right)
    (hrightValid : right.2.Valid) : left.2.Valid := by
  intro column
  rw [hequivalent.2 column]
  exact hrightValid column

private theorem continueCanonicalSegment
    (summaries : List RegionShapeSummary)
    (hwellFormed : summaries.Forall RegionShapeSummary.WellFormed)
    {left right : ℕ × CircuitAllocations}
    (hrightValid : right.2.Valid)
    (hequivalent : V1.SummaryStateEquivalent left right) :
    V1.SummaryStateEquivalent
      (V1.slotSummaryStateFromWith left.1 summaries left.2)
      (V1.slotSummaryStateFromWith right.1 summaries right.2) :=
  V1.slotSummaryStateFromWith_equivalent summaries hwellFormed
    (allocationsValid_of_summaryStateEquivalent hequivalent hrightValid)
    hrightValid hequivalent

private theorem plannerAbove8_equivalent
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) :
    V1.SummaryStateEquivalent
      (V1.slotSummaryStateFromWith initial
        (plannerAbove8 actionSortedPlannerSummaries) allocations)
      (V1.slotSummaryStateFromWith initial
        (plannerAbove8 actionCanonicalPlannerSummaries) allocations) := by
  apply regularPlannerSegment_equivalent
    (predicate := fun summary => decide (8 < summary.key))
    (hnormalized := plannerAbove8_normalized_perm)
    (initial := initial) (allocations := allocations) (hvalid := hvalid)
  intro summary hsummary
  simp only [decide_eq_true_eq] at hsummary
  omega

private theorem plannerBetween8And4_equivalent
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) :
    V1.SummaryStateEquivalent
      (V1.slotSummaryStateFromWith initial
        (plannerBetween8And4 actionSortedPlannerSummaries) allocations)
      (V1.slotSummaryStateFromWith initial
        (plannerBetween8And4 actionCanonicalPlannerSummaries) allocations) := by
  apply regularPlannerSegment_equivalent
    (predicate := fun summary =>
      decide (4 < summary.key ∧ summary.key < 8))
    (hnormalized := plannerBetween8And4_normalized_perm)
    (initial := initial) (allocations := allocations) (hvalid := hvalid)
  intro summary hsummary
  simp only [decide_eq_true_eq] at hsummary
  omega

private theorem plannerBelow4_equivalent
    (initial : ℕ) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) :
    V1.SummaryStateEquivalent
      (V1.slotSummaryStateFromWith initial
        (plannerBelow4 actionSortedPlannerSummaries) allocations)
      (V1.slotSummaryStateFromWith initial
        (plannerBelow4 actionCanonicalPlannerSummaries) allocations) := by
  apply regularPlannerSegment_equivalent
    (predicate := fun summary => decide (summary.key < 4))
    (hnormalized := plannerBelow4_normalized_perm)
    (initial := initial) (allocations := allocations) (hvalid := hvalid)
  intro summary hsummary
  simp only [decide_eq_true_eq] at hsummary
  omega

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

private def plannerTraceSummaries
    (trace : List V1.PlannedSummaryBlock) : List RegionShapeSummary :=
  (V1.PlannedSummaryBlock.blocks trace).flatMap fun block =>
    List.replicate block.1 block.2

private theorem plannerAbove8_canonical_eq_trace :
    plannerAbove8 actionCanonicalPlannerSummaries =
      plannerTraceSummaries (actionPlannerTrace.take 19) := by
  rw [show actionCanonicalPlannerSummaries =
      expandPlannerBlocks actionPlannerBlocks by rfl,
    plannerAbove8, aboveKey, filter_expandPlannerBlocks]
  have hblocks :
      actionPlannerBlocks.filter
          (fun block => decide (8 < block.2.key)) =
        actionPlannerBlocks.take 18 := by
    unfold actionPlannerBlocks plannerShape RegionShapeSummary.key
      RegionShapeSummary.adviceCols RegionColumn.isAdvice
    simp
  rw [hblocks]
  unfold actionPlannerBlocks actionPlannerTrace plannerTraceSummaries
    V1.PlannedSummaryBlock.blocks expandPlannerBlocks
  simp only [List.map_cons, List.map_nil, List.flatMap_cons,
    List.flatMap_nil, List.take]
  rw [show List.replicate 20 (plannerShape [5,6,7,8,9] 2) =
      List.replicate 7 (plannerShape [5,6,7,8,9] 2) ++
        List.replicate 13 (plannerShape [5,6,7,8,9] 2) by
      rw [← List.replicate_add]]
  simp only [List.append_assoc, List.append_nil]

private theorem plannerBetween8And4_canonical_eq_trace :
    plannerBetween8And4 actionCanonicalPlannerSummaries =
      plannerTraceSummaries ((actionPlannerTrace.drop 21).take 5) := by
  rw [show actionCanonicalPlannerSummaries =
      expandPlannerBlocks actionPlannerBlocks by rfl,
    plannerBetween8And4, filter_expandPlannerBlocks]
  have hblocks :
      actionPlannerBlocks.filter (fun block =>
          decide (4 < block.2.key ∧ block.2.key < 8)) =
        (actionPlannerBlocks.drop 20).take 3 := by
    unfold actionPlannerBlocks plannerShape RegionShapeSummary.key
      RegionShapeSummary.adviceCols RegionColumn.isAdvice
    simp
  rw [hblocks]
  unfold actionPlannerBlocks actionPlannerTrace plannerTraceSummaries
    V1.PlannedSummaryBlock.blocks expandPlannerBlocks
  simp only [List.map_cons, List.map_nil, List.flatMap_cons,
    List.flatMap_nil, List.drop, List.take]
  rw [show List.replicate 16 (plannerShape [5,6,7,8,9] 1) =
      List.replicate 1 (plannerShape [5,6,7,8,9] 1) ++
        List.replicate 6 (plannerShape [5,6,7,8,9] 1) ++
          List.replicate 9 (plannerShape [5,6,7,8,9] 1) by
      rw [← List.replicate_add, ← List.replicate_add]]
  simp only [List.append_assoc, List.append_nil]

private theorem plannerTraceSummaries_append
    (left right : List V1.PlannedSummaryBlock) :
    plannerTraceSummaries (left ++ right) =
      plannerTraceSummaries left ++ plannerTraceSummaries right := by
  simp [plannerTraceSummaries, V1.PlannedSummaryBlock.blocks]

private theorem plannerPrefix4_canonical_eq_trace :
    plannerAbove8 actionCanonicalPlannerSummaries ++
        plannerKey8 actionCanonicalPlannerSummaries ++
          plannerBetween8And4 actionCanonicalPlannerSummaries =
      plannerTraceSummaries (actionPlannerTrace.take 26) := by
  rw [plannerAbove8_canonical_eq_trace, plannerKey8_canonical_eq,
    plannerBetween8And4_canonical_eq_trace]
  have hkey8 :
      List.replicate 8 planner8Wide ++ [planner8Short] =
        plannerTraceSummaries ((actionPlannerTrace.drop 19).take 2) := by
    unfold actionPlannerTrace plannerTraceSummaries
      V1.PlannedSummaryBlock.blocks planner8Wide planner8Short
    simp
  rw [hkey8]
  rw [← plannerTraceSummaries_append, ← plannerTraceSummaries_append]
  congr 1

private def plannedRun (count : ℕ) (summary : RegionShapeSummary)
    (start : ℕ) : List V1.PlannedSummaryBlock :=
  if count = 0 then [] else [{ count, summary, start }]

private def plannerKey8Trace (before after : ℕ) :
    List V1.PlannedSummaryBlock :=
  plannedRun before planner8Wide 580 ++
    [{ count := 1, summary := planner8Short, start := 1745 }] ++
      plannedRun after planner8Wide (580 + before * 2)

private theorem plannerKey8Trace_summaries
    (before after : ℕ) :
    ((V1.PlannedSummaryBlock.blocks
        (plannerKey8Trace before after)).flatMap fun block =>
          List.replicate block.1 block.2) =
      List.replicate before planner8Wide ++
        planner8Short :: List.replicate after planner8Wide := by
  rcases Nat.eq_zero_or_pos before with rfl | hbefore <;>
    rcases Nat.eq_zero_or_pos after with rfl | hafter
  · simp [plannerKey8Trace, plannedRun,
      V1.PlannedSummaryBlock.blocks]
  · simp [plannerKey8Trace, plannedRun, Nat.ne_of_gt hafter,
      V1.PlannedSummaryBlock.blocks]
  · simp [plannerKey8Trace, plannedRun, Nat.ne_of_gt hbefore,
      V1.PlannedSummaryBlock.blocks]
  · simp [plannerKey8Trace, plannedRun, Nat.ne_of_gt hbefore,
      Nat.ne_of_gt hafter, V1.PlannedSummaryBlock.blocks]

private theorem plannerKey8Trace_endpoint
    {before after : ℕ} (hcount : before + after = 8) :
    V1.PlannedSummaryBlock.endpointFrom 1745
      (plannerKey8Trace before after) = 1746 := by
  unfold plannerKey8Trace plannedRun planner8Wide planner8Short plannerShape
  split <;> split <;>
    (simp_all [V1.PlannedSummaryBlock.endpointFrom]; try omega)

macro "trace_step" : tactic =>
  `(tactic|
    (unfold V1.PlannedSummaryBlock.TraceLawfulAfter
     refine ⟨by first | omega | norm_num,
       by simp [RegionShapeSummary.WellFormed, plannerShape,
         planner4Narrow, planner4Wide],
       by simp [plannerShape, planner4Narrow, planner4Wide], ?_, ?_, ?_⟩
     · simp [V1.PlannedSummaryBlock.FitsAfterAt, plannerShape,
         planner4Narrow, planner4Wide,
         RowIntervalsDisjoint] <;> omega
     · intro candidate hfits
       simp [V1.PlannedSummaryBlock.FitsAfterAt, plannerShape,
         planner4Narrow, planner4Wide,
         RowIntervalsDisjoint] at hfits
       try norm_num at hfits ⊢
       try omega
     simp only [List.nil_append, List.cons_append, List.append_nil,
       List.append_assoc]))

private theorem plannerKey8Trace_traceLawful
    {before after : ℕ} (hcount : before + after = 8) :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionPlannerTrace.take 19) (plannerKey8Trace before after) := by
  rcases Nat.eq_zero_or_pos before with rfl | hbefore <;>
    rcases Nat.eq_zero_or_pos after with rfl | hafter
  · omega
  ·
    unfold actionPlannerTrace plannerKey8Trace plannedRun planner8Wide
      planner8Short
    simp only [Nat.zero_mul, Nat.ne_of_gt hafter,
      if_false, if_true, List.nil_append,
      List.cons_append, List.take]
    trace_step
    trace_step
    trivial
  ·
    unfold actionPlannerTrace plannerKey8Trace plannedRun planner8Wide
      planner8Short
    simp only [Nat.ne_of_gt hbefore, if_false, if_true, List.nil_append,
      List.append_nil, List.cons_append, List.take]
    trace_step
    trace_step
    trivial
  ·
    unfold actionPlannerTrace plannerKey8Trace plannedRun planner8Wide
      planner8Short
    simp only [Nat.ne_of_gt hbefore, Nat.ne_of_gt hafter, if_false,
      List.nil_append, List.cons_append, List.take]
    trace_step
    trace_step
    trace_step
    trivial

private def plannerKey8CanonicalTrace : List V1.PlannedSummaryBlock :=
  [{ count := 8, summary := planner8Wide, start := 580 },
    { count := 1, summary := planner8Short, start := 1745 }]

private theorem plannerKey8Trace_finalView
    (view : V1.AllocationView) {before after : ℕ}
    (hcount : before + after = 8) :
    V1.PlannedSummaryBlock.finalView view
        (plannerKey8Trace before after) =
      V1.PlannedSummaryBlock.finalView view plannerKey8CanonicalTrace := by
  rcases Nat.eq_zero_or_pos before with rfl | hbefore <;>
    rcases Nat.eq_zero_or_pos after with rfl | hafter
  · omega
  · have : after = 8 := by omega
    subst after
    simp only [plannerKey8Trace, plannerKey8CanonicalTrace, plannedRun,
      if_pos, Nat.zero_mul, List.nil_append, List.cons_append,
      V1.PlannedSummaryBlock.finalView,
      V1.AllocationView.insertRepeated_one]
    simp only [planner8Wide, plannerShape]
    symm
    apply V1.AllocationView.insertRepeated_insert_comm
    intro index hindex
    omega
  · have : before = 8 := by omega
    subst before
    simp [plannerKey8Trace, plannerKey8CanonicalTrace, plannedRun,
      V1.PlannedSummaryBlock.finalView]
  · simp only [plannerKey8Trace, plannerKey8CanonicalTrace, plannedRun,
      Nat.ne_of_gt hbefore, Nat.ne_of_gt hafter, if_false,
      List.nil_append, List.cons_append,
      V1.PlannedSummaryBlock.finalView,
      V1.AllocationView.insertRepeated_one]
    simp only [planner8Wide, plannerShape]
    rw [← V1.AllocationView.insertRepeated_insert_comm]
    · rw [V1.AllocationView.insertRepeated_add, hcount]
    · intro index hindex
      omega

private inductive PlannerKey4Order
  | narrowNarrowWideWide
  | narrowWideNarrowWide
  | narrowWideWideNarrow
  | wideNarrowNarrowWide
  | wideNarrowWideNarrow
  | wideWideNarrowNarrow

private def PlannerKey4Order.summaries :
    PlannerKey4Order → List RegionShapeSummary
  | .narrowNarrowWideWide =>
      [planner4Narrow, planner4Narrow, planner4Wide, planner4Wide]
  | .narrowWideNarrowWide =>
      [planner4Narrow, planner4Wide, planner4Narrow, planner4Wide]
  | .narrowWideWideNarrow =>
      [planner4Narrow, planner4Wide, planner4Wide, planner4Narrow]
  | .wideNarrowNarrowWide =>
      [planner4Wide, planner4Narrow, planner4Narrow, planner4Wide]
  | .wideNarrowWideNarrow =>
      [planner4Wide, planner4Narrow, planner4Wide, planner4Narrow]
  | .wideWideNarrowNarrow =>
      [planner4Wide, planner4Wide, planner4Narrow, planner4Narrow]

private def PlannerKey4Order.trace :
    PlannerKey4Order → List V1.PlannedSummaryBlock
  | .narrowNarrowWideWide =>
      [{ count := 2, summary := planner4Narrow, start := 264 },
       { count := 2, summary := planner4Wide, start := 596 }]
  | .narrowWideNarrowWide =>
      [{ count := 1, summary := planner4Narrow, start := 264 },
       { count := 1, summary := planner4Wide, start := 596 },
       { count := 1, summary := planner4Narrow, start := 266 },
       { count := 1, summary := planner4Wide, start := 597 }]
  | .narrowWideWideNarrow =>
      [{ count := 1, summary := planner4Narrow, start := 264 },
       { count := 2, summary := planner4Wide, start := 596 },
       { count := 1, summary := planner4Narrow, start := 266 }]
  | .wideNarrowNarrowWide =>
      [{ count := 1, summary := planner4Wide, start := 596 },
       { count := 2, summary := planner4Narrow, start := 264 },
       { count := 1, summary := planner4Wide, start := 597 }]
  | .wideNarrowWideNarrow =>
      [{ count := 1, summary := planner4Wide, start := 596 },
       { count := 1, summary := planner4Narrow, start := 264 },
       { count := 1, summary := planner4Wide, start := 597 },
       { count := 1, summary := planner4Narrow, start := 266 }]
  | .wideWideNarrowNarrow =>
      [{ count := 2, summary := planner4Wide, start := 596 },
       { count := 2, summary := planner4Narrow, start := 264 }]

private theorem PlannerKey4Order.trace_summaries
    (order : PlannerKey4Order) :
    plannerTraceSummaries order.trace = order.summaries := by
  cases order <;>
    simp [plannerTraceSummaries, trace, summaries,
      V1.PlannedSummaryBlock.blocks]

private theorem plannerKey4_perm_order
    (items : List RegionShapeSummary)
    (hperm : items.Perm
      (List.replicate 2 planner4Narrow ++
        List.replicate 2 planner4Wide)) :
    ∃ order, items = PlannerKey4Order.summaries order := by
  classical
  have hlength := hperm.length_eq
  rcases items with _ | ⟨first, items⟩ <;> simp at hlength
  rcases items with _ | ⟨second, items⟩ <;> simp at hlength
  rcases items with _ | ⟨third, items⟩ <;> simp at hlength
  rcases items with _ | ⟨fourth, items⟩ <;> simp at hlength
  rcases items with _ | ⟨fifth, items⟩
  · have hcounts := (List.perm_replicate_append_replicate
        (l := [first, second, third, fourth])
        (a := planner4Narrow) (b := planner4Wide) (m := 2) (n := 2)
        (by simp [planner4Narrow, planner4Wide, plannerShape])).mp hperm
    have hfirst := hcounts.2.2
      (show first ∈ [first, second, third, fourth] by simp)
    have hsecond := hcounts.2.2
      (show second ∈ [first, second, third, fourth] by simp)
    have hthird := hcounts.2.2
      (show third ∈ [first, second, third, fourth] by simp)
    have hfourth := hcounts.2.2
      (show fourth ∈ [first, second, third, fourth] by simp)
    simp only [List.mem_cons] at hfirst
    simp only [List.mem_cons] at hsecond
    simp only [List.mem_cons] at hthird
    simp only [List.mem_cons] at hfourth
    rcases hfirst with hfirst | hfirst <;>
      rcases hsecond with hsecond | hsecond <;>
      rcases hthird with hthird | hthird <;>
      rcases hfourth with hfourth | hfourth <;>
      subst_vars <;> simp_all [planner4Narrow, planner4Wide, plannerShape] <;>
      first
      | exact ⟨.narrowNarrowWideWide, rfl⟩
      | exact ⟨.narrowWideNarrowWide, rfl⟩
      | exact ⟨.narrowWideWideNarrow, rfl⟩
      | exact ⟨.wideNarrowNarrowWide, rfl⟩
      | exact ⟨.wideNarrowWideNarrow, rfl⟩
      | exact ⟨.wideWideNarrowNarrow, rfl⟩
  · simp at hlength

private theorem PlannerKey4Order.endpoint
    (order : PlannerKey4Order) :
    V1.PlannedSummaryBlock.endpointFrom 1762 order.trace = 1762 := by
  cases order <;> decide

private structure PlannerInsertion where
  columns : List RegionColumn
  start : ℕ
  length : ℕ
deriving DecidableEq

private def PlannerInsertion.apply
    (view : V1.AllocationView) (insertion : PlannerInsertion) :
    V1.AllocationView :=
  view.insert insertion.columns insertion.start insertion.length

private def planner4NarrowFirst : PlannerInsertion :=
  ⟨sortRegionColumns planner4Narrow.columns, 264, 2⟩

private def planner4NarrowSecond : PlannerInsertion :=
  ⟨sortRegionColumns planner4Narrow.columns, 266, 2⟩

private def planner4WideFirst : PlannerInsertion :=
  ⟨sortRegionColumns planner4Wide.columns, 596, 1⟩

private def planner4WideSecond : PlannerInsertion :=
  ⟨sortRegionColumns planner4Wide.columns, 597, 1⟩

private def PlannerKey4Order.insertions :
    PlannerKey4Order → List PlannerInsertion
  | .narrowNarrowWideWide =>
      [planner4NarrowFirst, planner4NarrowSecond,
        planner4WideFirst, planner4WideSecond]
  | .narrowWideNarrowWide =>
      [planner4NarrowFirst, planner4WideFirst,
        planner4NarrowSecond, planner4WideSecond]
  | .narrowWideWideNarrow =>
      [planner4NarrowFirst, planner4WideFirst,
        planner4WideSecond, planner4NarrowSecond]
  | .wideNarrowNarrowWide =>
      [planner4WideFirst, planner4NarrowFirst,
        planner4NarrowSecond, planner4WideSecond]
  | .wideNarrowWideNarrow =>
      [planner4WideFirst, planner4NarrowFirst,
        planner4WideSecond, planner4NarrowSecond]
  | .wideWideNarrowNarrow =>
      [planner4WideFirst, planner4WideSecond,
        planner4NarrowFirst, planner4NarrowSecond]

private theorem PlannerKey4Order.insertions_perm
    (order : PlannerKey4Order) :
    order.insertions.Perm narrowNarrowWideWide.insertions := by
  cases order <;> decide

private theorem PlannerKey4Order.finalView_eq_foldl
    (view : V1.AllocationView) (order : PlannerKey4Order) :
    V1.PlannedSummaryBlock.finalView view order.trace =
      order.insertions.foldl PlannerInsertion.apply view := by
  cases order <;>
    simp [trace, insertions, PlannerInsertion.apply,
      V1.PlannedSummaryBlock.finalView,
      V1.AllocationView.insertRepeated, planner4Narrow,
      planner4Wide, plannerShape, planner4NarrowFirst,
      planner4NarrowSecond, planner4WideFirst, planner4WideSecond]

private theorem PlannerKey4Order.finalView
    (view : V1.AllocationView) (order : PlannerKey4Order) :
    V1.PlannedSummaryBlock.finalView view order.trace =
      V1.PlannedSummaryBlock.finalView view
        PlannerKey4Order.narrowNarrowWideWide.trace := by
  rw [order.finalView_eq_foldl, narrowNarrowWideWide.finalView_eq_foldl]
  apply order.insertions_perm.foldl_eq'
  intro left hleft right hright current
  have hleftCanonical : left ∈ narrowNarrowWideWide.insertions :=
    order.insertions_perm.subset hleft
  have hrightCanonical : right ∈ narrowNarrowWideWide.insertions :=
    order.insertions_perm.subset hright
  simp only [insertions, List.mem_cons, List.not_mem_nil, or_false] at hleftCanonical
  simp only [insertions, List.mem_cons, List.not_mem_nil, or_false] at hrightCanonical
  rcases hleftCanonical with hleftCanonical | hleftCanonical |
      hleftCanonical | hleftCanonical <;>
    rcases hrightCanonical with hrightCanonical | hrightCanonical |
      hrightCanonical | hrightCanonical <;>
    subst left <;> subst right
  all_goals first
    | rfl
    | (apply V1.AllocationView.insert_comm_of_ne
       decide)
set_option maxRecDepth 10000 in
theorem actionPlannerTrace_endpoint :
    V1.PlannedSummaryBlock.endpointFrom 0 actionPlannerTrace = 1779 := by
  decide

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

private theorem plannerKey4TraceLawful_narrowWideNarrowWide :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionPlannerTrace.take 26)
      PlannerKey4Order.narrowWideNarrowWide.trace := by
  unfold actionPlannerTrace PlannerKey4Order.trace
  trace_step
  trace_step
  trace_step
  trace_step
  trivial

private theorem plannerKey4TraceLawful_narrowWideWideNarrow :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionPlannerTrace.take 26)
      PlannerKey4Order.narrowWideWideNarrow.trace := by
  unfold actionPlannerTrace PlannerKey4Order.trace
  trace_step
  trace_step
  trace_step
  trivial

private theorem plannerKey4TraceLawful_wideNarrowNarrowWide :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionPlannerTrace.take 26)
      PlannerKey4Order.wideNarrowNarrowWide.trace := by
  unfold actionPlannerTrace PlannerKey4Order.trace
  trace_step
  trace_step
  trace_step
  trivial

private theorem plannerKey4TraceLawful_wideNarrowWideNarrow :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionPlannerTrace.take 26)
      PlannerKey4Order.wideNarrowWideNarrow.trace := by
  unfold actionPlannerTrace PlannerKey4Order.trace
  trace_step
  trace_step
  trace_step
  trace_step
  trivial

private theorem plannerKey4TraceLawful_wideWideNarrowNarrow :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionPlannerTrace.take 26)
      PlannerKey4Order.wideWideNarrowNarrow.trace := by
  unfold actionPlannerTrace PlannerKey4Order.trace
  trace_step
  trace_step
  trivial

private theorem PlannerKey4Order.traceLawful
    (order : PlannerKey4Order) :
    V1.PlannedSummaryBlock.TraceLawfulAfter
      (actionPlannerTrace.take 26) order.trace := by
  cases order
  · unfold actionPlannerTrace trace
    trace_step
    trace_step
    trivial
  · exact plannerKey4TraceLawful_narrowWideNarrowWide
  · exact plannerKey4TraceLawful_narrowWideWideNarrow
  · exact plannerKey4TraceLawful_wideNarrowNarrowWide
  · exact plannerKey4TraceLawful_wideNarrowWideNarrow
  · exact plannerKey4TraceLawful_wideWideNarrowNarrow

private theorem actionPlannerPrefix8_endpoint :
    V1.PlannedSummaryBlock.endpointFrom 0
      (actionPlannerTrace.take 19) = 1745 := by
  unfold actionPlannerTrace V1.PlannedSummaryBlock.endpointFrom
  decide

private theorem actionPlannerPrefix8_lawful :
    V1.PlannedSummaryBlock.Lawful V1.AllocationView.empty
      (actionPlannerTrace.take 19) := by
  have hsplit := V1.PlannedSummaryBlock.lawful_append
    V1.AllocationView.empty (actionPlannerTrace.take 19)
      (actionPlannerTrace.drop 19)
  exact (hsplit.mp (by
    simpa only [List.take_append_drop] using actionPlannerTrace_lawful)).1

private theorem actionPlannerPrefix4_endpoint :
    V1.PlannedSummaryBlock.endpointFrom 0
      (actionPlannerTrace.take 26) = 1762 := by
  unfold actionPlannerTrace V1.PlannedSummaryBlock.endpointFrom
  decide

private theorem actionPlannerPrefix4_lawful :
    V1.PlannedSummaryBlock.Lawful V1.AllocationView.empty
      (actionPlannerTrace.take 26) := by
  have hsplit := V1.PlannedSummaryBlock.lawful_append
    V1.AllocationView.empty (actionPlannerTrace.take 26)
      (actionPlannerTrace.drop 26)
  exact (hsplit.mp (by
    simpa only [List.take_append_drop] using actionPlannerTrace_lawful)).1

private theorem plannerKey8_equivalent
    {leftPrefix rightPrefix : ℕ × CircuitAllocations}
    (hrightPrefix : rightPrefix =
      V1.slotSummaryStateFromWith 0
        (plannerAbove8 actionCanonicalPlannerSummaries)
        (∅ : CircuitAllocations))
    (hprefix : V1.SummaryStateEquivalent leftPrefix rightPrefix) :
    V1.SummaryStateEquivalent
      (V1.slotSummaryStateFromWith leftPrefix.1
        (plannerKey8 actionSortedPlannerSummaries) leftPrefix.2)
      (V1.slotSummaryStateFromWith rightPrefix.1
        (plannerKey8 actionCanonicalPlannerSummaries) rightPrefix.2) := by
  classical
  have hrightAsBlocks : rightPrefix =
      V1.slotSummaryBlocksState
        (V1.PlannedSummaryBlock.blocks (actionPlannerTrace.take 19)) 0
        (∅ : CircuitAllocations) := by
    rw [hrightPrefix, plannerAbove8_canonical_eq_trace,
      plannerTraceSummaries,
      V1.slotSummaryStateFromWith_flatMap_replicate]
  let prefixView := V1.PlannedSummaryBlock.finalView
    V1.AllocationView.empty (actionPlannerTrace.take 19)
  have hprefixResult := V1.PlannedSummaryBlock.slotSummaryBlocksState_eq
    (actionPlannerTrace.take 19) 0 (∅ : CircuitAllocations)
    V1.AllocationView.empty (by
      simp [V1.AllocationView.Represents, V1.AllocationView.empty])
    (by simp [V1.AllocationView.Valid, V1.AllocationView.empty,
      Allocations.Valid]) actionPlannerPrefix8_lawful
  have hrightRepresents : prefixView.Represents rightPrefix.2 := by
    intro column
    rw [hrightAsBlocks]
    exact hprefixResult.2 column
  have hleftRepresents : prefixView.Represents leftPrefix.2 := by
    intro column
    exact (hprefix.2 column).trans (hrightRepresents column)
  have hviewValid : prefixView.Valid :=
    actionPlannerPrefix8_lawful.finalView_valid (by
      simp [V1.AllocationView.Valid, V1.AllocationView.empty,
        Allocations.Valid])
  have hrightEndpoint : rightPrefix.1 = 1745 := by
    rw [hrightAsBlocks, hprefixResult.1, actionPlannerPrefix8_endpoint]
  have hleftEndpoint : leftPrefix.1 = 1745 :=
    hprefix.1.trans hrightEndpoint
  obtain ⟨aligned, haligned, hequivalent⟩ :=
    V1.exists_perm_forall₂_of_map_perm RegionShapeSummary.normalized
      plannerKey8_normalized_perm
  have hplacement : List.Forall₂
      RegionShapeSummary.PlacementEquivalent
      (plannerKey8 actionSortedPlannerSummaries) aligned :=
    hequivalent.imp fun _ _ hnormalized =>
      RegionShapeSummary.placementEquivalent_iff_normalized_eq.mpr
        hnormalized
  have hactualAligned :
      V1.slotSummaryStateFromWith leftPrefix.1
          (plannerKey8 actionSortedPlannerSummaries) leftPrefix.2 =
        V1.slotSummaryStateFromWith leftPrefix.1 aligned leftPrefix.2 :=
    V1.slotSummaryStateFromWith_eq_of_forall₂_placementEquivalent
      hplacement leftPrefix.1 leftPrefix.2
  rw [plannerKey8_canonical_eq] at haligned
  obtain ⟨before, after, hcount, halignedEq⟩ :=
    (perm_replicate_append_singleton_iff
      (show planner8Wide ≠ planner8Short by
        simp [planner8Wide, planner8Short, plannerShape]) 8).mp haligned
  have halignedBlocks :
      V1.slotSummaryStateFromWith leftPrefix.1 aligned leftPrefix.2 =
        V1.slotSummaryBlocksState
          (V1.PlannedSummaryBlock.blocks
            (plannerKey8Trace before after)) leftPrefix.1 leftPrefix.2 := by
    rw [halignedEq, ← plannerKey8Trace_summaries,
      V1.slotSummaryStateFromWith_flatMap_replicate]
  have hcanonicalBlocks :
      V1.slotSummaryStateFromWith rightPrefix.1
          (plannerKey8 actionCanonicalPlannerSummaries) rightPrefix.2 =
        V1.slotSummaryBlocksState
          (V1.PlannedSummaryBlock.blocks plannerKey8CanonicalTrace)
          rightPrefix.1 rightPrefix.2 := by
    have hsummaries : plannerTraceSummaries plannerKey8CanonicalTrace =
        List.replicate 8 planner8Wide ++ [planner8Short] := by
      simp [plannerTraceSummaries, plannerKey8CanonicalTrace,
        V1.PlannedSummaryBlock.blocks]
    rw [plannerKey8_canonical_eq, ← hsummaries,
      plannerTraceSummaries,
      V1.slotSummaryStateFromWith_flatMap_replicate]
  have hprefixCounts : (actionPlannerTrace.take 19).Forall
      fun block => 0 < block.count := by
    unfold actionPlannerTrace
    decide
  have hvariantLawful :=
    V1.PlannedSummaryBlock.lawful_of_traceLawfulAfter
      (actionPlannerTrace.take 19) (plannerKey8Trace before after)
      hprefixCounts (plannerKey8Trace_traceLawful hcount)
  have hcanonicalLawful :=
    V1.PlannedSummaryBlock.lawful_of_traceLawfulAfter
      (actionPlannerTrace.take 19) plannerKey8CanonicalTrace
      hprefixCounts (by
        simpa [plannerKey8CanonicalTrace] using
          plannerKey8Trace_traceLawful (before := 8) (after := 0) rfl)
  rw [hactualAligned, halignedBlocks, hcanonicalBlocks]
  apply V1.PlannedSummaryBlock.slotSummaryBlocksState_equivalent_of_represents
    (left := plannerKey8Trace before after)
    (right := plannerKey8CanonicalTrace)
    (leftInitial := leftPrefix.1) (rightInitial := rightPrefix.1)
    (leftAllocations := leftPrefix.2)
    (rightAllocations := rightPrefix.2) (view := prefixView)
    hleftRepresents hrightRepresents hviewValid hvariantLawful
    hcanonicalLawful
  · rw [hleftEndpoint, hrightEndpoint,
      plannerKey8Trace_endpoint hcount]
    exact plannerKey8Trace_endpoint (before := 8) (after := 0) rfl
  · exact plannerKey8Trace_finalView prefixView hcount

private theorem plannerKey4_equivalent
    {leftPrefix rightPrefix : ℕ × CircuitAllocations}
    (hrightPrefix : rightPrefix =
      V1.slotSummaryStateFromWith 0
        (plannerAbove8 actionCanonicalPlannerSummaries ++
          plannerKey8 actionCanonicalPlannerSummaries ++
            plannerBetween8And4 actionCanonicalPlannerSummaries)
        (∅ : CircuitAllocations))
    (hprefix : V1.SummaryStateEquivalent leftPrefix rightPrefix) :
    V1.SummaryStateEquivalent
      (V1.slotSummaryStateFromWith leftPrefix.1
        (plannerKey4 actionSortedPlannerSummaries) leftPrefix.2)
      (V1.slotSummaryStateFromWith rightPrefix.1
        (plannerKey4 actionCanonicalPlannerSummaries) rightPrefix.2) := by
  classical
  have hrightAsBlocks : rightPrefix =
      V1.slotSummaryBlocksState
        (V1.PlannedSummaryBlock.blocks (actionPlannerTrace.take 26)) 0
        (∅ : CircuitAllocations) := by
    rw [hrightPrefix, plannerPrefix4_canonical_eq_trace,
      plannerTraceSummaries,
      V1.slotSummaryStateFromWith_flatMap_replicate]
  let prefixView := V1.PlannedSummaryBlock.finalView
    V1.AllocationView.empty (actionPlannerTrace.take 26)
  have hprefixResult := V1.PlannedSummaryBlock.slotSummaryBlocksState_eq
    (actionPlannerTrace.take 26) 0 (∅ : CircuitAllocations)
    V1.AllocationView.empty (by
      simp [V1.AllocationView.Represents, V1.AllocationView.empty])
    (by simp [V1.AllocationView.Valid, V1.AllocationView.empty,
      Allocations.Valid]) actionPlannerPrefix4_lawful
  have hrightRepresents : prefixView.Represents rightPrefix.2 := by
    intro column
    rw [hrightAsBlocks]
    exact hprefixResult.2 column
  have hleftRepresents : prefixView.Represents leftPrefix.2 := by
    intro column
    exact (hprefix.2 column).trans (hrightRepresents column)
  have hviewValid : prefixView.Valid :=
    actionPlannerPrefix4_lawful.finalView_valid (by
      simp [V1.AllocationView.Valid, V1.AllocationView.empty,
        Allocations.Valid])
  have hrightEndpoint : rightPrefix.1 = 1762 := by
    rw [hrightAsBlocks, hprefixResult.1, actionPlannerPrefix4_endpoint]
  have hleftEndpoint : leftPrefix.1 = 1762 :=
    hprefix.1.trans hrightEndpoint
  obtain ⟨aligned, haligned, hequivalent⟩ :=
    V1.exists_perm_forall₂_of_map_perm RegionShapeSummary.normalized
      plannerKey4_normalized_perm
  have hplacement : List.Forall₂
      RegionShapeSummary.PlacementEquivalent
      (plannerKey4 actionSortedPlannerSummaries) aligned :=
    hequivalent.imp fun _ _ hnormalized =>
      RegionShapeSummary.placementEquivalent_iff_normalized_eq.mpr
        hnormalized
  have hactualAligned :
      V1.slotSummaryStateFromWith leftPrefix.1
          (plannerKey4 actionSortedPlannerSummaries) leftPrefix.2 =
        V1.slotSummaryStateFromWith leftPrefix.1 aligned leftPrefix.2 :=
    V1.slotSummaryStateFromWith_eq_of_forall₂_placementEquivalent
      hplacement leftPrefix.1 leftPrefix.2
  rw [plannerKey4_canonical_eq] at haligned
  obtain ⟨order, halignedEq⟩ := plannerKey4_perm_order aligned haligned
  have halignedBlocks :
      V1.slotSummaryStateFromWith leftPrefix.1 aligned leftPrefix.2 =
        V1.slotSummaryBlocksState
          (V1.PlannedSummaryBlock.blocks order.trace)
          leftPrefix.1 leftPrefix.2 := by
    rw [halignedEq, ← order.trace_summaries, plannerTraceSummaries,
      V1.slotSummaryStateFromWith_flatMap_replicate]
  have hcanonicalBlocks :
      V1.slotSummaryStateFromWith rightPrefix.1
          (plannerKey4 actionCanonicalPlannerSummaries) rightPrefix.2 =
        V1.slotSummaryBlocksState
          (V1.PlannedSummaryBlock.blocks
            PlannerKey4Order.narrowNarrowWideWide.trace)
          rightPrefix.1 rightPrefix.2 := by
    rw [plannerKey4_canonical_eq,
      show List.replicate 2 planner4Narrow ++
          List.replicate 2 planner4Wide =
        PlannerKey4Order.narrowNarrowWideWide.summaries by rfl,
      ← PlannerKey4Order.narrowNarrowWideWide.trace_summaries,
      plannerTraceSummaries,
      V1.slotSummaryStateFromWith_flatMap_replicate]
  have hprefixCounts : (actionPlannerTrace.take 26).Forall
      fun block => 0 < block.count := by
    unfold actionPlannerTrace
    decide
  have hvariantLawful :=
    V1.PlannedSummaryBlock.lawful_of_traceLawfulAfter
      (actionPlannerTrace.take 26) order.trace hprefixCounts
      order.traceLawful
  have hcanonicalLawful :=
    V1.PlannedSummaryBlock.lawful_of_traceLawfulAfter
      (actionPlannerTrace.take 26)
      PlannerKey4Order.narrowNarrowWideWide.trace hprefixCounts
      PlannerKey4Order.narrowNarrowWideWide.traceLawful
  rw [hactualAligned, halignedBlocks, hcanonicalBlocks]
  apply V1.PlannedSummaryBlock.slotSummaryBlocksState_equivalent_of_represents
    (left := order.trace)
    (right := PlannerKey4Order.narrowNarrowWideWide.trace)
    (leftInitial := leftPrefix.1) (rightInitial := rightPrefix.1)
    (leftAllocations := leftPrefix.2)
    (rightAllocations := rightPrefix.2) (view := prefixView)
    hleftRepresents hrightRepresents hviewValid hvariantLawful
    hcanonicalLawful
  · rw [hleftEndpoint, hrightEndpoint, order.endpoint]
    exact PlannerKey4Order.narrowNarrowWideWide.endpoint
  · exact order.finalView prefixView

private theorem actionSortedPlannerSummaries_equivalent :
    V1.SummaryStateEquivalent
      (V1.slotSummaryStateFromWith 0 actionSortedPlannerSummaries
        (∅ : CircuitAllocations))
      (V1.slotSummaryStateFromWith 0 actionCanonicalPlannerSummaries
        (∅ : CircuitAllocations)) := by
  let leftAbove := V1.slotSummaryStateFromWith 0
    (plannerAbove8 actionSortedPlannerSummaries) (∅ : CircuitAllocations)
  let rightAbove := V1.slotSummaryStateFromWith 0
    (plannerAbove8 actionCanonicalPlannerSummaries) (∅ : CircuitAllocations)
  let leftKey8 := V1.slotSummaryStateFromWith leftAbove.1
    (plannerKey8 actionSortedPlannerSummaries) leftAbove.2
  let rightKey8 := V1.slotSummaryStateFromWith rightAbove.1
    (plannerKey8 actionCanonicalPlannerSummaries) rightAbove.2
  let leftMiddle := V1.slotSummaryStateFromWith leftKey8.1
    (plannerBetween8And4 actionSortedPlannerSummaries) leftKey8.2
  let rightMiddle := V1.slotSummaryStateFromWith rightKey8.1
    (plannerBetween8And4 actionCanonicalPlannerSummaries) rightKey8.2
  let leftKey4 := V1.slotSummaryStateFromWith leftMiddle.1
    (plannerKey4 actionSortedPlannerSummaries) leftMiddle.2
  let rightKey4 := V1.slotSummaryStateFromWith rightMiddle.1
    (plannerKey4 actionCanonicalPlannerSummaries) rightMiddle.2
  let leftBelow := V1.slotSummaryStateFromWith leftKey4.1
    (plannerBelow4 actionSortedPlannerSummaries) leftKey4.2
  let rightBelow := V1.slotSummaryStateFromWith rightKey4.1
    (plannerBelow4 actionCanonicalPlannerSummaries) rightKey4.2
  have hemptyValid : (∅ : CircuitAllocations).Valid :=
    CircuitAllocations.Valid.empty
  have haboveWellFormed :
      (plannerAbove8 actionCanonicalPlannerSummaries).Forall
        RegionShapeSummary.WellFormed :=
    canonicalFiltered_wellFormed
      (fun summary => decide (8 < summary.key))
  have hkey8WellFormed :
      (plannerKey8 actionCanonicalPlannerSummaries).Forall
        RegionShapeSummary.WellFormed :=
    canonicalFiltered_wellFormed
      (fun summary => decide (summary.key = 8))
  have hmiddleWellFormed :
      (plannerBetween8And4 actionCanonicalPlannerSummaries).Forall
        RegionShapeSummary.WellFormed :=
    canonicalFiltered_wellFormed
      (fun summary => decide (4 < summary.key ∧ summary.key < 8))
  have hkey4WellFormed :
      (plannerKey4 actionCanonicalPlannerSummaries).Forall
        RegionShapeSummary.WellFormed :=
    canonicalFiltered_wellFormed
      (fun summary => decide (summary.key = 4))
  have hbelowWellFormed :
      (plannerBelow4 actionCanonicalPlannerSummaries).Forall
        RegionShapeSummary.WellFormed :=
    canonicalFiltered_wellFormed
      (fun summary => decide (summary.key < 4))
  have hrightAboveValid : rightAbove.2.Valid := by
    exact V1.slotSummaryStateFromWith_valid _ _ _ haboveWellFormed hemptyValid
  have hrightKey8Valid : rightKey8.2.Valid := by
    exact V1.slotSummaryStateFromWith_valid _ _ _ hkey8WellFormed
      hrightAboveValid
  have hrightMiddleValid : rightMiddle.2.Valid := by
    exact V1.slotSummaryStateFromWith_valid _ _ _ hmiddleWellFormed
      hrightKey8Valid
  have hrightKey4Valid : rightKey4.2.Valid := by
    exact V1.slotSummaryStateFromWith_valid _ _ _ hkey4WellFormed
      hrightMiddleValid
  have habove : V1.SummaryStateEquivalent leftAbove rightAbove :=
    plannerAbove8_equivalent 0 (∅ : CircuitAllocations) hemptyValid
  have hkey8 : V1.SummaryStateEquivalent leftKey8 rightKey8 := by
    exact plannerKey8_equivalent (rightPrefix := rightAbove) rfl habove
  have hleftKey8Valid : leftKey8.2.Valid :=
    allocationsValid_of_summaryStateEquivalent hkey8 hrightKey8Valid
  have hmiddleLocal : V1.SummaryStateEquivalent leftMiddle
      (V1.slotSummaryStateFromWith leftKey8.1
        (plannerBetween8And4 actionCanonicalPlannerSummaries)
        leftKey8.2) :=
    plannerBetween8And4_equivalent leftKey8.1 leftKey8.2 hleftKey8Valid
  have hmiddleTransport : V1.SummaryStateEquivalent
      (V1.slotSummaryStateFromWith leftKey8.1
        (plannerBetween8And4 actionCanonicalPlannerSummaries) leftKey8.2)
      rightMiddle :=
    continueCanonicalSegment _ hmiddleWellFormed hrightKey8Valid hkey8
  have hmiddle : V1.SummaryStateEquivalent leftMiddle rightMiddle :=
    hmiddleLocal.trans hmiddleTransport
  have hrightMiddleEq : rightMiddle =
      V1.slotSummaryStateFromWith 0
        (plannerAbove8 actionCanonicalPlannerSummaries ++
          plannerKey8 actionCanonicalPlannerSummaries ++
            plannerBetween8And4 actionCanonicalPlannerSummaries)
        (∅ : CircuitAllocations) := by
    symm
    rw [V1.slotSummaryStateFromWith_append,
      V1.slotSummaryStateFromWith_append]
  have hkey4 : V1.SummaryStateEquivalent leftKey4 rightKey4 := by
    exact plannerKey4_equivalent hrightMiddleEq hmiddle
  have hleftKey4Valid : leftKey4.2.Valid :=
    allocationsValid_of_summaryStateEquivalent hkey4 hrightKey4Valid
  have hbelowLocal : V1.SummaryStateEquivalent leftBelow
      (V1.slotSummaryStateFromWith leftKey4.1
        (plannerBelow4 actionCanonicalPlannerSummaries) leftKey4.2) :=
    plannerBelow4_equivalent leftKey4.1 leftKey4.2 hleftKey4Valid
  have hbelowTransport : V1.SummaryStateEquivalent
      (V1.slotSummaryStateFromWith leftKey4.1
        (plannerBelow4 actionCanonicalPlannerSummaries) leftKey4.2)
      rightBelow :=
    continueCanonicalSegment _ hbelowWellFormed hrightKey4Valid hkey4
  have hbelow : V1.SummaryStateEquivalent leftBelow rightBelow :=
    hbelowLocal.trans hbelowTransport
  rw [plannerSegments_eq actionSortedPlannerSummaries
      actionSortedPlannerSummaries_key_sorted,
    plannerSegments_eq actionCanonicalPlannerSummaries
      actionCanonicalPlannerSummaries_key_sorted]
  repeat' rw [V1.slotSummaryStateFromWith_append]
  exact hbelow

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

/-- The consensus-sorted Action region stream ends exactly at row 1779. -/
theorem actionSortedPlannerSummaries_endpoint :
    (V1.slotSummaryStateFromWith 0 actionSortedPlannerSummaries
      (∅ : CircuitAllocations)).1 = 1779 :=
  actionSortedPlannerSummaries_equivalent.1.trans
    actionCanonicalPlannerSummaries_endpoint

/-- Halo 2 V1's physical placement of the Action circuit ends exactly at row 1779. -/
theorem actionCircuit_placementEnd_eq_1779 :
    V1.placementEnd actionCircuit.operations = 1779 := by
  rw [actionCircuit_placementEnd_eq]
  unfold V1.slotSummaryEndFrom
  rw [← V1.slotSummaryStateFromWith_fst]
  exact actionSortedPlannerSummaries_endpoint


end Zcash.Circuits.Action
