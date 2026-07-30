import Zcash.Snark.Soundness.AGM.AdaptiveOnline
import Zcash.Snark.Soundness.Composition.PrefixedSqueeze

/-!
# Semantic challenge surfaces for arbitrary adaptive online-AGM adversaries

These bounds use the first annotated query of a prefix, or a fresh fallback if it was never
queried. Each bad set depends only on the prefix and earlier answers, so no execution cut is
required.
-/

namespace Zcash.Snark

open scoped ENNReal
open Classical

local instance vestaInhabitedAdaptiveSurfaces : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

/-- The prefix of `t` at an earlier pre-IPA squeeze index. -/
def adaptiveEarlierPrefix (init : List (TranscriptElt Fp VestaG))
    {L : ℕ} (t : BTranscript Fp VestaG L) (i : Fin 11) : BTranscript Fp VestaG L :=
  ⟨t.val.take (preIpaLen shape init.length i), by
    rw [List.length_take]
    exact le_trans (min_le_right _ _) t.prop⟩

/-- At a transcript of exactly the index-`n` length, every earlier prefix is a different oracle
point. -/
theorem adaptiveEarlierPrefix_ne
    (init : List (TranscriptElt Fp VestaG)) {L : ℕ}
    (n : Fin 11) (t : BTranscript Fp VestaG L)
    (hlen : t.val.length = preIpaLen shape init.length n)
    (i : Fin (n : ℕ)) :
    adaptiveEarlierPrefix (shape := shape) init t (i.castLE (le_of_lt n.isLt)) ≠ t := by
  intro heq
  have hlens := congrArg (fun q : BTranscript Fp VestaG L => q.val.length) heq
  simp only [adaptiveEarlierPrefix, List.length_take] at hlens
  have hlt : preIpaLen shape init.length (i.castLE (le_of_lt n.isLt)) < t.val.length := by
    rw [hlen]
    exact preIpaLen_lt_at shape init.length i.isLt
  rw [min_eq_left hlt.le] at hlens
  exact (Nat.ne_of_lt hlt) hlens

/-- A semantic bad set decoded from `t` and the answers at all earlier deployed prefixes.  Queries
of any other transcript length receive the empty set, which makes the definition safe for every
unrelated query an arbitrary adversary may issue. -/
noncomputable def adaptivePrefixBad (init : List (TranscriptElt Fp VestaG)) (n : Fin 11)
    (badF : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k) →
      (Fin (n : ℕ) → Fp) → Set Fp)
    (t : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k))
    (O : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k) → Fp) : Set Fp :=
  if t.val.length = preIpaLen shape init.length n then
    badF t (fun i => O (adaptiveEarlierPrefix (shape := shape) init t
      (i.castLE (le_of_lt n.isLt))))
  else ∅

/-- Updating the index-`n` point does not change its decoded bad set. -/
theorem adaptivePrefixBad_update_self (init : List (TranscriptElt Fp VestaG)) (n : Fin 11)
    (badF : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k) →
      (Fin (n : ℕ) → Fp) → Set Fp)
    (t : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k))
    (O : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k) → Fp) (v : Fp) :
    adaptivePrefixBad (shape := shape) init n badF t (Function.update O t v) =
      adaptivePrefixBad (shape := shape) init n badF t O := by
  unfold adaptivePrefixBad
  by_cases hlen : t.val.length = preIpaLen shape init.length n
  · simp only [if_pos hlen]
    congr 1
    funext i
    rw [Function.update_of_ne]
    exact adaptiveEarlierPrefix_ne init n t hlen i
  · simp [hlen]

/-- The decoded prefix bad set inherits any run-uniform per-challenge bound. -/
theorem adaptivePrefixBad_measure_le (init : List (TranscriptElt Fp VestaG)) (n : Fin 11)
    (badF : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k) →
      (Fin (n : ℕ) → Fp) → Set Fp)
    {epsilon : ENNReal}
    (hbad : ∀ t nu, (PMF.uniformOfFintype Fp).toOuterMeasure (badF t nu) ≤ epsilon)
    (t : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k))
    (O : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k) → Fp) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
      (adaptivePrefixBad (shape := shape) init n badF t O) ≤ epsilon := by
  unfold adaptivePrefixBad
  split
  · exact hbad _ _
  · simp

/-- A prefix bad set computed from the AGM annotation fixed before the selected oracle answer.
Queries at unrelated transcript lengths receive the empty set. -/
noncomputable def adaptiveLabeledPrefixBad
    (init : List (TranscriptElt Fp VestaG))
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (n : Fin 11)
    (badF : (t : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k)) →
      AlgebraicTranscriptQuery (F := Fp) basis t → (Fin (n : ℕ) → Fp) → Set Fp)
    (t : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k))
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (O : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k) → Fp) : Set Fp :=
  if t.val.length = preIpaLen shape init.length n then
    badF t label (fun i => O (adaptiveEarlierPrefix (shape := shape) init t
      (i.castLE (le_of_lt n.isLt))))
  else ∅

/-- Reprogramming the selected point does not change a bad set decoded from its pre-answer AGM
annotation and strictly earlier prefix answers. -/
theorem adaptiveLabeledPrefixBad_update_self
    (init : List (TranscriptElt Fp VestaG))
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (n : Fin 11)
    (badF : (t : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k)) →
      AlgebraicTranscriptQuery (F := Fp) basis t → (Fin (n : ℕ) → Fp) → Set Fp)
    (t : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k))
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (O : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k) → Fp) (v : Fp) :
    adaptiveLabeledPrefixBad (shape := shape) init basis n badF t label
        (Function.update O t v) =
      adaptiveLabeledPrefixBad (shape := shape) init basis n badF t label O := by
  unfold adaptiveLabeledPrefixBad
  by_cases hlen : t.val.length = preIpaLen shape init.length n
  · simp only [if_pos hlen]
    congr 1
    funext i
    rw [Function.update_of_ne]
    exact adaptiveEarlierPrefix_ne init n t hlen i
  · simp [hlen]

/-- A label-decoded prefix bad set inherits its pointwise single-challenge bound. -/
theorem adaptiveLabeledPrefixBad_measure_le
    (init : List (TranscriptElt Fp VestaG))
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (n : Fin 11)
    (badF : (t : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k)) →
      AlgebraicTranscriptQuery (F := Fp) basis t → (Fin (n : ℕ) → Fp) → Set Fp)
    {epsilon : ENNReal}
    (hbad : ∀ t label nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badF t label nu) ≤ epsilon)
    (t : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k))
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (O : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k) → Fp) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
      (adaptiveLabeledPrefixBad (shape := shape) init basis n badF t label O) ≤ epsilon := by
  unfold adaptiveLabeledPrefixBad
  split
  · exact hbad _ _ _
  · simp

namespace ComputedAdaptiveOnlineAGMFSFamily

/-- **Arbitrary-adversary semantic squeeze bound.**  No `PrefixDeterminedAt`, sequential phase,
or `ActionSequentialExecution` premise is present. -/
theorem adaptivePrefixSurface_table_le
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (n : Fin 11)
    (badF : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin (n : ℕ) → Fp) → Set Fp)
    {epsilon : ENNReal}
    (hbad : ∀ t nu, (PMF.uniformOfFintype Fp).toOuterMeasure (badF t nu) ≤ epsilon) :
    (PMF.uniformOfFintype (BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)).toOuterMeasure
      {O | O (algebraicFullPrefixesPre family.init
          ((family.adversary basis).run O).toAlgebraicWfProof n) ∈
        adaptivePrefixBad (shape := shape) family.init n badF
          (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O).toAlgebraicWfProof n) O} ≤
      (family.Q + 1 : ℕ) * epsilon := by
  let bad := fun (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
      (_label : AlgebraicTranscriptQuery (F := Fp) basis t) =>
        adaptivePrefixBad (shape := shape) family.init n badF t
  let fallback := fun (_data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
      (t : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k)) =>
        adaptivePrefixBad (shape := shape) family.init n badF t
  have hbound := LabeledOracleComp.firstLabelOrFallbackBad_measure_le
      (family.adversary basis)
      (fun data => algebraicFullPrefixesPre family.init data.toAlgebraicWfProof n)
      bad fallback
      (fun t label O v => adaptivePrefixBad_update_self family.init n badF t O v)
      (fun data t O v => adaptivePrefixBad_update_self family.init n badF t O v)
      (fun t label O => adaptivePrefixBad_measure_le family.init n badF hbad t O)
      (fun data t O => adaptivePrefixBad_measure_le family.init n badF hbad t O)
      (family.queryBound basis)
  have hevent :
      {O | O (algebraicFullPrefixesPre family.init
          ((family.adversary basis).run O).toAlgebraicWfProof n) ∈
        adaptivePrefixBad (shape := shape) family.init n badF
          (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O).toAlgebraicWfProof n) O} =
      {O | O (algebraicFullPrefixesPre family.init
          ((family.adversary basis).run O).toAlgebraicWfProof n) ∈
        LabeledOracleComp.firstLabelOrFallbackBad (family.adversary basis) bad fallback
          (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O).toAlgebraicWfProof n) O} := by
    ext O
    simp only [Set.mem_setOf_eq]
    unfold LabeledOracleComp.firstLabelOrFallbackBad bad fallback
    cases (family.adversary basis).findLabel O
      (algebraicFullPrefixesPre family.init
        ((family.adversary basis).run O).toAlgebraicWfProof n) <;> rfl
  rw [hevent]
  exact hbound

/-- Bounds a first annotated prefix query, or a prefix-local fallback when unqueried. -/
theorem adaptiveLabeledPrefixSurface_table_le
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (n : Fin 11)
    (badF : (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k)) →
      AlgebraicTranscriptQuery (F := Fp) basis t → (Fin (n : ℕ) → Fp) → Set Fp)
    (fallbackF : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin (n : ℕ) → Fp) → Set Fp)
    {epsilon : ENNReal}
    (hbad : ∀ t label nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badF t label nu) ≤ epsilon)
    (hfallback : ∀ t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (fallbackF t nu) ≤ epsilon) :
    (PMF.uniformOfFintype (BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)).toOuterMeasure
      {O | let t := (algebraicFullPrefixesPre family.init
          ((family.adversary basis).run O).toAlgebraicWfProof) n
        O t ∈ LabeledOracleComp.firstLabelOrFallbackBad (family.adversary basis)
          (fun t label O => adaptiveLabeledPrefixBad (shape := shape)
            family.init basis n badF t label O)
          (fun _data t O => adaptivePrefixBad (shape := shape)
            family.init n fallbackF t O) t O} ≤
      (family.Q + 1 : ℕ) * epsilon := by
  apply LabeledOracleComp.firstLabelOrFallbackBad_measure_le
    (family.adversary basis)
    (fun data => (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof) n)
    (fun t label O => adaptiveLabeledPrefixBad (shape := shape)
      family.init basis n badF t label O)
    (fun _data t O => adaptivePrefixBad (shape := shape)
      family.init n fallbackF t O)
  · exact adaptiveLabeledPrefixBad_update_self family.init basis n badF
  · intro _data
    exact adaptivePrefixBad_update_self family.init n fallbackF
  · exact adaptiveLabeledPrefixBad_measure_le family.init basis n badF hbad
  · intro _data
    exact adaptivePrefixBad_measure_le family.init n fallbackF hfallback
  · exact family.queryBound basis

/-- Bounds a final-output bad set when an executable finder covers query-time representation
mismatches. -/
theorem adaptiveFinalPrefixBadWithoutRelation_table_le
    {Relation : Type*}
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (n : Fin 11)
    (finalBad : OnlineMemberProofData (vk := family.vk basis)
        (instanceCommitment := family.instanceCommitment basis) basis
        (family.fixedRepresentations basis) →
      BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) → Set Fp)
    (finder : (BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) → Option Relation)
    (badF : (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k)) →
      AlgebraicTranscriptQuery (F := Fp) basis t → (Fin (n : ℕ) → Fp) → Set Fp)
    (fallbackF : OnlineMemberProofData (vk := family.vk basis)
        (instanceCommitment := family.instanceCommitment basis) basis
        (family.fixedRepresentations basis) →
      BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) →
      (Fin (n : ℕ) → Fp) → Set Fp)
    (hcover : ∀ O,
      let data := (family.adversary basis).run O
      let t := (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof) n
      O t ∈ finalBad data t O → finder O = none →
        O t ∈ LabeledOracleComp.firstLabelOrFallbackBad (family.adversary basis)
          (fun t label O => adaptiveLabeledPrefixBad (shape := shape)
            family.init basis n badF t label O)
          (fun data t O => adaptivePrefixBad (shape := shape)
            family.init n (fallbackF data) t O) t O)
    {epsilon : ENNReal}
    (hbad : ∀ t label nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badF t label nu) ≤ epsilon)
    (hfallback : ∀ data t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (fallbackF data t nu) ≤ epsilon) :
    (PMF.uniformOfFintype (BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)).toOuterMeasure
      {O | let data := (family.adversary basis).run O
        let t := (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof) n
        O t ∈ finalBad data t O ∧ finder O = none} ≤
      (family.Q + 1 : ℕ) * epsilon := by
  apply LabeledOracleComp.finalBadWithoutRelation_measure_le
    (family.adversary basis)
    (fun data => (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof) n)
    finalBad finder
    (fun t label O => adaptiveLabeledPrefixBad (shape := shape)
      family.init basis n badF t label O)
    (fun data t O => adaptivePrefixBad (shape := shape)
      family.init n (fallbackF data) t O)
  · exact hcover
  · exact adaptiveLabeledPrefixBad_update_self family.init basis n badF
  · intro data
    exact adaptivePrefixBad_update_self family.init n (fallbackF data)
  · exact adaptiveLabeledPrefixBad_measure_le family.init basis n badF hbad
  · intro data
    exact adaptivePrefixBad_measure_le family.init n (fallbackF data) (hfallback data)
  · exact family.queryBound basis

end ComputedAdaptiveOnlineAGMFSFamily

end Zcash.Snark
