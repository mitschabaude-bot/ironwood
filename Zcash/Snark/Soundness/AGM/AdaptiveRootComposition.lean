import Zcash.Snark.Soundness.AGM.AdaptiveRootSurfaces

/-!
# Pricing deployed roots for a bare adaptive online AGM

This module instantiates the generic annotation-aware squeeze theorem with the six deployed
multiopen/shift surfaces.  Every queried branch is reconstructed from the first query annotation;
the fresh fallback is reconstructed from the final online proof data.
-/

namespace Zcash.Snark

open Classical
open scoped ENNReal

set_option maxRecDepth 10000

local instance vestaInhabitedAdaptiveRootComposition : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

/-- Extend the answers at strictly earlier deployed prefixes by zero.  A surface at index `n`
may inspect only entries below `n`; the current and later entries are dummy values. -/
def adaptiveEarlierRecord (n : Fin 11) (earlier : Fin (n : Nat) → Fp) : Fin 11 → Fp :=
  fun i => if h : (i : Nat) < (n : Nat) then earlier ⟨i, h⟩ else 0

/-- Translate the pre-IPA squeeze index to the historical six-root budget order
`(ξ,z,x₄,x₃,x₂,x₁)`. -/
def adaptiveRootEventIndex (n : Fin 11) : Fin 6 :=
  if (n : Nat) = 5 then 5
  else if (n : Nat) = 6 then 4
  else if (n : Nat) = 7 then 3
  else if (n : Nat) = 8 then 2
  else if (n : Nat) = 9 then 0
  else 1

/-- Recover the strict pre-`x₁` representation source from an aligned stage source.  The staged
prover points occupy the prefix; verifier-fixed representations occupy the suffix. -/
def adaptiveRootMemberSource
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (n : Fin 11) (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis)) :
    List (AlgebraicPoint (F := Fp) basis) :=
  source.take ps.preX1CommitmentPoints.length ++
    source.drop (ps.commitmentPointsBefore n).length

/-- The exact representation occupying the `q′` slot, isolated from possible equal-point
representations elsewhere in the source. -/
def adaptiveRootQSource
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis)) :
    List (AlgebraicPoint (F := Fp) basis) :=
  (source[ps.preX1CommitmentPoints.length]?).toList

/-- The exact representation occupying the `S` slot. -/
def adaptiveRootSSource
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis)) :
    List (AlgebraicPoint (F := Fp) basis) :=
  (source[ps.preX1CommitmentPoints.length + 1]?).toList

/-- One query-time deployed root surface.  Missing structural coverage yields the empty set;
the actual verifier prefix supplies coverage below, while the empty branch keeps the pointwise
price valid for every unrelated malicious query of the same length. -/
noncomputable def adaptiveRootSurfaceAt
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (n : Fin 11) (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (earlier : Fin (n : Nat) → Fp) : Set Fp :=
  let nu := adaptiveEarlierRecord n earlier
  let memberSource := adaptiveRootMemberSource n ps source
  let qSource := adaptiveRootQSource ps source
  let sSource := adaptiveRootSSource ps source
  if hmembers : AdaptiveMembersCovered vk instanceCommitment ps memberSource then
    if _h5 : (n : Nat) = 5 then
      adaptiveX1AllRootSet vk instanceCommitment ps memberSource hmembers nu
    else if _h6 : (n : Nat) = 6 then
      adaptiveX2RootSet vk instanceCommitment ps memberSource hmembers nu
    else if _h7 : (n : Nat) = 7 then
      if hq : CommitmentRefCovered qSource (.point ps.multiopenQPrime) then
        adaptiveX3RootSet vk instanceCommitment ps memberSource qSource hmembers hq nu
      else ∅
    else if _h8 : (n : Nat) = 8 then
      if hq : CommitmentRefCovered qSource (.point ps.multiopenQPrime) then
        adaptiveX4RootSet vk instanceCommitment ps memberSource qSource hmembers hq nu
      else ∅
    else if _h9 : (n : Nat) = 9 then
      if hq : CommitmentRefCovered qSource (.point ps.multiopenQPrime) then
        if hs : CommitmentRefCovered sSource (.point ps.ipaS) then
          adaptiveXiRootSet vk instanceCommitment ps memberSource qSource sSource
            hmembers hq hs nu
        else ∅
      else ∅
    else if _h10 : (n : Nat) = 10 then
      if hq : CommitmentRefCovered qSource (.point ps.multiopenQPrime) then
        if hs : CommitmentRefCovered sSource (.point ps.ipaS) then
          adaptiveZRootSet vk instanceCommitment ps memberSource qSource sSource
            hmembers hq hs nu
        else ∅
      else ∅
    else ∅
  else ∅

/-- Each query-local surface has exactly its existing direct-route budget. -/
theorem adaptiveRootSurfaceAt_measure_le
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (n : Fin 11) (h5n : 5 ≤ (n : Nat))
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (earlier : Fin (n : Nat) → Fp) :
    uniformChallenge.toOuterMeasure
        (adaptiveRootSurfaceAt vk instanceCommitment n ps source earlier) ≤
      deployedRootEventBudget shape (adaptiveRootEventIndex n) := by
  fin_cases n
  · norm_num at h5n
  · norm_num at h5n
  · norm_num at h5n
  · norm_num at h5n
  · norm_num at h5n
  all_goals simp only at h5n ⊢
  · change uniformChallenge.toOuterMeasure
        (adaptiveRootSurfaceAt vk instanceCommitment 5 ps source earlier) ≤
      deployedRootEventBudget shape (adaptiveRootEventIndex 5)
    by_cases hm : AdaptiveMembersCovered vk instanceCommitment ps
        (adaptiveRootMemberSource 5 ps source)
    · rw [adaptiveRootSurfaceAt, dif_pos hm]
      simpa [adaptiveRootEventIndex, deployedRootEventBudget] using
        adaptiveX1AllRootSet_measure_le vk instanceCommitment ps
          (adaptiveRootMemberSource 5 ps source) hm (adaptiveEarlierRecord 5 earlier)
    · rw [adaptiveRootSurfaceAt, dif_neg hm]
      simp [adaptiveRootEventIndex, deployedRootEventBudget]
  · change uniformChallenge.toOuterMeasure
        (adaptiveRootSurfaceAt vk instanceCommitment 6 ps source earlier) ≤
      deployedRootEventBudget shape (adaptiveRootEventIndex 6)
    by_cases hm : AdaptiveMembersCovered vk instanceCommitment ps
        (adaptiveRootMemberSource 6 ps source)
    · rw [adaptiveRootSurfaceAt, dif_pos hm]
      simpa [adaptiveRootEventIndex, deployedRootEventBudget] using
        adaptiveX2RootSet_measure_le vk instanceCommitment ps
          (adaptiveRootMemberSource 6 ps source) hm (adaptiveEarlierRecord 6 earlier)
    · rw [adaptiveRootSurfaceAt, dif_neg hm]
      simp [adaptiveRootEventIndex, deployedRootEventBudget]
  · change uniformChallenge.toOuterMeasure
        (adaptiveRootSurfaceAt vk instanceCommitment 7 ps source earlier) ≤
      deployedRootEventBudget shape (adaptiveRootEventIndex 7)
    by_cases hm : AdaptiveMembersCovered vk instanceCommitment ps
        (adaptiveRootMemberSource 7 ps source)
    · by_cases hq : CommitmentRefCovered (adaptiveRootQSource ps source)
          (.point ps.multiopenQPrime)
      · rw [adaptiveRootSurfaceAt, dif_pos hm, dif_pos hq]
        simpa [adaptiveRootEventIndex, deployedRootEventBudget] using
          adaptiveX3RootSet_measure_le vk instanceCommitment ps
            (adaptiveRootMemberSource 7 ps source) (adaptiveRootQSource ps source)
            hm hq (adaptiveEarlierRecord 7 earlier)
      · rw [adaptiveRootSurfaceAt, dif_pos hm]
        norm_num
        rw [dif_neg hq]
        simp [adaptiveRootEventIndex, deployedRootEventBudget]
    · rw [adaptiveRootSurfaceAt, dif_neg hm]
      simp [adaptiveRootEventIndex, deployedRootEventBudget]
  · change uniformChallenge.toOuterMeasure
        (adaptiveRootSurfaceAt vk instanceCommitment 8 ps source earlier) ≤
      deployedRootEventBudget shape (adaptiveRootEventIndex 8)
    by_cases hm : AdaptiveMembersCovered vk instanceCommitment ps
        (adaptiveRootMemberSource 8 ps source)
    · by_cases hq : CommitmentRefCovered (adaptiveRootQSource ps source)
          (.point ps.multiopenQPrime)
      · rw [adaptiveRootSurfaceAt, dif_pos hm]
        norm_num
        rw [dif_pos hq]
        simpa [adaptiveRootEventIndex, deployedRootEventBudget] using
          adaptiveX4RootSet_measure_le vk instanceCommitment ps
            (adaptiveRootMemberSource 8 ps source) (adaptiveRootQSource ps source)
            hm hq (adaptiveEarlierRecord 8 earlier)
      · rw [adaptiveRootSurfaceAt, dif_pos hm]
        norm_num
        rw [dif_neg hq]
        simp [adaptiveRootEventIndex, deployedRootEventBudget]
    · rw [adaptiveRootSurfaceAt, dif_neg hm]
      simp [adaptiveRootEventIndex, deployedRootEventBudget]
  · change uniformChallenge.toOuterMeasure
        (adaptiveRootSurfaceAt vk instanceCommitment 9 ps source earlier) ≤
      deployedRootEventBudget shape (adaptiveRootEventIndex 9)
    by_cases hm : AdaptiveMembersCovered vk instanceCommitment ps
        (adaptiveRootMemberSource 9 ps source)
    · by_cases hq : CommitmentRefCovered (adaptiveRootQSource ps source)
          (.point ps.multiopenQPrime)
      · by_cases hs : CommitmentRefCovered (adaptiveRootSSource ps source)
            (.point ps.ipaS)
        · rw [adaptiveRootSurfaceAt, dif_pos hm]
          norm_num
          rw [dif_pos hq, dif_pos hs]
          simpa [adaptiveRootEventIndex, deployedRootEventBudget] using
            adaptiveXiRootSet_measure_le vk instanceCommitment ps
              (adaptiveRootMemberSource 9 ps source) (adaptiveRootQSource ps source)
              (adaptiveRootSSource ps source) hm hq hs (adaptiveEarlierRecord 9 earlier)
        · rw [adaptiveRootSurfaceAt, dif_pos hm]
          norm_num
          rw [dif_pos hq, dif_neg hs]
          simp [adaptiveRootEventIndex, deployedRootEventBudget]
      · rw [adaptiveRootSurfaceAt, dif_pos hm]
        norm_num
        rw [dif_neg hq]
        simp [adaptiveRootEventIndex, deployedRootEventBudget]
    · rw [adaptiveRootSurfaceAt, dif_neg hm]
      simp [adaptiveRootEventIndex, deployedRootEventBudget]
  · change uniformChallenge.toOuterMeasure
        (adaptiveRootSurfaceAt vk instanceCommitment 10 ps source earlier) ≤
      deployedRootEventBudget shape (adaptiveRootEventIndex 10)
    by_cases hm : AdaptiveMembersCovered vk instanceCommitment ps
        (adaptiveRootMemberSource 10 ps source)
    · by_cases hq : CommitmentRefCovered (adaptiveRootQSource ps source)
          (.point ps.multiopenQPrime)
      · by_cases hs : CommitmentRefCovered (adaptiveRootSSource ps source)
            (.point ps.ipaS)
        · rw [adaptiveRootSurfaceAt, dif_pos hm]
          norm_num
          rw [dif_pos hq, dif_pos hs]
          simpa [adaptiveRootEventIndex, deployedRootEventBudget] using
            adaptiveZRootSet_measure_le vk instanceCommitment ps
              (adaptiveRootMemberSource 10 ps source) (adaptiveRootQSource ps source)
              (adaptiveRootSSource ps source) hm hq hs (adaptiveEarlierRecord 10 earlier)
        · rw [adaptiveRootSurfaceAt, dif_pos hm]
          norm_num
          rw [dif_pos hq, dif_neg hs]
          simp [adaptiveRootEventIndex, deployedRootEventBudget]
      · rw [adaptiveRootSurfaceAt, dif_pos hm]
        norm_num
        rw [dif_neg hq]
        simp [adaptiveRootEventIndex, deployedRootEventBudget]
    · rw [adaptiveRootSurfaceAt, dif_neg hm]
      simp [adaptiveRootEventIndex, deployedRootEventBudget]

/-- Canonicalize proof fields emitted after a deployed squeeze.  Making this projection explicit
keeps query-time bad sets manifestly independent of a malicious continuation. -/
def adaptiveRootPrefixProof (n : Fin 11) (ps : ProofString shape Fp VestaG) :
    ProofString shape Fp VestaG :=
  if (n : Nat) < 7 then
    { ps with
      multiopenQPrime := 0
      multiopenU := 0
      ipaS := 0
      ipaRounds := 0
      ipaC := 0
      ipaF := 0 }
  else if (n : Nat) < 8 then
    { ps with
      multiopenU := 0
      ipaS := 0
      ipaRounds := 0
      ipaC := 0
      ipaF := 0 }
  else if (n : Nat) < 9 then
    { ps with
      ipaS := 0
      ipaRounds := 0
      ipaC := 0
      ipaF := 0 }
  else
    { ps with
      ipaRounds := 0
      ipaC := 0
      ipaF := 0 }

/-- Equal deployed prefixes have equal canonical ordinary proof data. -/
theorem adaptiveRootPrefixProof_congr
    (init : List (TranscriptElt Fp VestaG))
    (n : Fin 11) (h5n : 5 ≤ (n : Nat))
    (ps ps' : ProofString shape Fp VestaG)
    (hwf : PsWellFormed ps) (hwf' : PsWellFormed ps')
    (hprefix : preIpaSqueezePoints init ps n = preIpaSqueezePoints init ps' n) :
    adaptiveRootPrefixProof n ps = adaptiveRootPrefixProof n ps' := by
  fin_cases n
  · norm_num at h5n
  · norm_num at h5n
  · norm_num at h5n
  · norm_num at h5n
  · norm_num at h5n
  · have hps := preX1SqueezePoint_inj init hwf hwf' hprefix
    rw [hps]
    simp [adaptiveRootPrefixProof]
  · have hps := preX2SqueezePoint_inj init hwf hwf' hprefix
    rw [hps]
    simp [adaptiveRootPrefixProof]
  · have hps := preX3SqueezePoint_inj init hwf hwf' hprefix
    rw [hps]
    simp [adaptiveRootPrefixProof]
  · have hps := preX4SqueezePoint_inj init hwf hwf' hprefix
    rw [hps]
    simp [adaptiveRootPrefixProof]
  · have h9' := List.append_inj' hprefix rfl
    have h8pt := List.append_inj' h9'.1 rfl
    have hps := preX4SqueezePoint_inj init hwf hwf' h8pt.1
    have hs : ps.ipaS = ps'.ipaS := by
      simpa using congrArg List.head? h8pt.2
    rw [hps, hs]
    simp [adaptiveRootPrefixProof]
  · have h9 := (List.append_inj' hprefix rfl).1
    have h9' := List.append_inj' h9 rfl
    have h8pt := List.append_inj' h9'.1 rfl
    have hps := preX4SqueezePoint_inj init hwf hwf' h8pt.1
    have hs : ps.ipaS = ps'.ipaS := by
      simpa using congrArg List.head? h8pt.2
    rw [hps, hs]
    simp [adaptiveRootPrefixProof]

/-- Canonicalization preserves exactly the ordinary commitment list available at the current
squeeze. -/
@[simp] theorem adaptiveRootPrefixProof_commitmentPointsBefore
    (n : Fin 11) (ps : ProofString shape Fp VestaG) :
    (adaptiveRootPrefixProof n ps).commitmentPointsBefore n =
      ps.commitmentPointsBefore n := by
  fin_cases n <;>
    simp [adaptiveRootPrefixProof, ProofString.commitmentPointsBefore,
      ProofString.preX1CommitmentPoints]

@[simp] theorem adaptiveRootPrefixProof_preX1CommitmentPoints
    (n : Fin 11) (ps : ProofString shape Fp VestaG) :
    (adaptiveRootPrefixProof n ps).preX1CommitmentPoints =
      ps.preX1CommitmentPoints := by
  fin_cases n <;>
    simp [adaptiveRootPrefixProof, ProofString.preX1CommitmentPoints]

/-- If the executable provenance check returned no relation and the prefix was queried, the
stage-local query source is literally the final stage source. -/
theorem adaptiveQuerySource_eq_of_pinned
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (n : Fin 11)
    (h5n : 5 ≤ (n : Nat))
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (decoded : DecodedPreIpaPrefix (shape := shape) family.init n
      ((algebraicFullPrefixesPre family.init
        ((family.adversary basis).run O).toAlgebraicWfProof) n))
    (pinned : SelectedQueryRepresentationPinned
      ((algebraicFullPrefixesPre family.init
        ((family.adversary basis).run O).toAlgebraicWfProof) n)
      (family.adversary basis) O
      (((family.adversary basis).run O).algebraicProof.representationsBefore n)) :
    adaptiveQuerySource family.init basis n h5n decoded pinned.query
        (family.fixedRepresentations basis) =
      ((family.adversary basis).run O).algebraicProof.representationsBefore n ++
        family.fixedRepresentations basis := by
  let data := (family.adversary basis).run O
  let final := data.algebraicProof.representationsBefore n
  have hprefixBounded : fullPrefixesPre family.init decoded.proof n =
      fullPrefixesPre family.init data.toAlgebraicWfProof.proof n := decoded.point_eq
  have hprefix : preIpaSqueezePoints family.init decoded.proof.1 n =
      preIpaSqueezePoints family.init data.algebraicProof.erase n :=
    congrArg Subtype.val hprefixBounded
  have hcanonical := adaptiveRootPrefixProof_congr family.init n h5n
    decoded.proof.1 data.algebraicProof.erase decoded.proof.2 data.wellFormed hprefix
  have hordinary : decoded.proof.1.commitmentPointsBefore n =
      data.algebraicProof.erase.commitmentPointsBefore n := by
    calc
      decoded.proof.1.commitmentPointsBefore n =
          (adaptiveRootPrefixProof n decoded.proof.1).commitmentPointsBefore n := by simp
      _ = (adaptiveRootPrefixProof n data.algebraicProof.erase).commitmentPointsBefore n :=
        congrArg (fun ps => ps.commitmentPointsBefore n) hcanonical
      _ = data.algebraicProof.erase.commitmentPointsBefore n := by simp
  have hselected : pinned.query.representationsFor final pinned.covered = final :=
    algebraicPointList_eq_of_maps_eq
      (pinned.query.representationsFor_points final pinned.covered)
      pinned.coefficients_eq
  let decodedCovered : ∀ P ∈ decoded.proof.1.commitmentPointsBefore n,
      P ∈ transcriptGroupPoints
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof n).val := by
    intro P hP
    rw [← decoded.point_eq]
    exact decoded.proof.1.commitmentPointsBefore_covered family.init decoded.proof.2
      n h5n P hP
  unfold adaptiveQuerySource
  change pinned.query.representationsForPoints
      (decoded.proof.1.commitmentPointsBefore n) decodedCovered ++
        family.fixedRepresentations basis = _
  have hordinaryFinal : decoded.proof.1.commitmentPointsBefore n =
      final.map AlgebraicPoint.point :=
    hordinary.trans (data.algebraicProof.representationsBefore_points n).symm
  let finalCoveredPoints : ∀ P ∈ final.map AlgebraicPoint.point,
      P ∈ transcriptGroupPoints
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof n).val := by
    intro P hP
    obtain ⟨ap, hap, rfl⟩ := List.mem_map.mp hP
    exact pinned.covered ap hap
  have representationsForPoints_congr
      (points points' : List VestaG)
      (hcovered : ∀ P ∈ points, P ∈ transcriptGroupPoints
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof n).val)
      (hcovered' : ∀ P ∈ points', P ∈ transcriptGroupPoints
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof n).val)
      (hpoints : points = points') :
      pinned.query.representationsForPoints points hcovered =
        pinned.query.representationsForPoints points' hcovered' := by
    subst points'
    rfl
  have hqueryPoints : pinned.query.representationsForPoints
      (decoded.proof.1.commitmentPointsBefore n) decodedCovered =
      pinned.query.representationsForPoints
        (final.map AlgebraicPoint.point) finalCoveredPoints := by
    exact representationsForPoints_congr _ _ decodedCovered finalCoveredPoints hordinaryFinal
  rw [hqueryPoints,
    ← pinned.query.representationsFor_eq_representationsForPoints final pinned.covered]
  exact congrArg (fun source => source ++ family.fixedRepresentations basis) hselected

/-- Decode one arbitrary query point and use its full pre-answer AGM annotation. -/
noncomputable def adaptiveQueriedRootSurface
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (n : Fin 11)
    (h5n : 5 ≤ (n : Nat))
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (earlier : Fin (n : Nat) → Fp) : Set Fp :=
  match decodePreIpaPrefix? (shape := shape) family.init n t with
  | none => ∅
  | some decoded =>
      adaptiveRootSurfaceAt (family.vk basis) (family.instanceCommitment basis) n
        (adaptiveRootPrefixProof n decoded.proof.1)
        (adaptiveQuerySource family.init basis n h5n decoded label
          (family.fixedRepresentations basis)) earlier

/-- The queried decoder inherits the pointwise direct-route price. -/
theorem adaptiveQueriedRootSurface_measure_le
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (n : Fin 11)
    (h5n : 5 ≤ (n : Nat))
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (label : AlgebraicTranscriptQuery (F := Fp) basis t)
    (earlier : Fin (n : Nat) → Fp) :
    uniformChallenge.toOuterMeasure
        (adaptiveQueriedRootSurface family basis n h5n t label earlier) ≤
      deployedRootEventBudget shape (adaptiveRootEventIndex n) := by
  rw [adaptiveQueriedRootSurface]
  split
  · simp
  · exact adaptiveRootSurfaceAt_measure_le _ _ n h5n _ _ earlier

/-- Fresh-query fallback reconstructed from the final proof's own online representations. -/
noncomputable def adaptiveFallbackRootSurface
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (n : Fin 11)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (_t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (earlier : Fin (n : Nat) → Fp) : Set Fp :=
  adaptiveRootSurfaceAt (family.vk basis) (family.instanceCommitment basis) n
    (adaptiveRootPrefixProof n data.algebraicProof.erase)
    (data.algebraicProof.representationsBefore n ++ family.fixedRepresentations basis) earlier

theorem adaptiveFallbackRootSurface_measure_le
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (n : Fin 11)
    (h5n : 5 ≤ (n : Nat))
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (earlier : Fin (n : Nat) → Fp) :
    uniformChallenge.toOuterMeasure
        (adaptiveFallbackRootSurface family basis n data t earlier) ≤
      deployedRootEventBudget shape (adaptiveRootEventIndex n) :=
  adaptiveRootSurfaceAt_measure_le _ _ n h5n _ _ earlier

/-! ## Structural coverage of the actual fallback -/

/-- Coverage depends only on the represented group points, not on their coefficient vectors. -/
theorem CommitmentRefCovered.mono_points
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {source₁ source₂ : List (AlgebraicPoint (F := Fp) basis)}
    (hmono : ∀ ap ∈ source₁, ∃ ap' ∈ source₂, ap'.point = ap.point)
    (c : CommitmentRef shape.k Fp VestaG)
    (hcovered : CommitmentRefCovered source₁ c) :
    CommitmentRefCovered source₂ c := by
  cases c with
  | point P =>
      obtain ⟨ap, hap, hP⟩ := hcovered
      obtain ⟨ap', hap', heq⟩ := hmono ap hap
      exact ⟨ap', hap', heq.trans hP⟩
  | msm m =>
      intro pr hpr
      obtain ⟨ap, hap, hP⟩ := hcovered pr hpr
      obtain ⟨ap', hap', heq⟩ := hmono ap hap
      exact ⟨ap', hap', heq.trans hP⟩

theorem AlgebraicProofString.preX1Points_mem_representationsBefore
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 11)
    (ap : AlgebraicPoint (F := Fp) basis) (hap : ap ∈ aps.preX1Points) :
    ap ∈ aps.representationsBefore n := by
  unfold AlgebraicProofString.representationsBefore
  by_cases h7 : (n : Nat) < 7
  · simp [h7, hap]
  · by_cases h9 : (n : Nat) < 9 <;> simp [h7, h9, hap]

theorem AlgebraicProofString.multiopenQPrime_mem_representationsBefore
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 11) (h7n : 7 ≤ (n : Nat)) :
    aps.multiopenQPrime ∈ aps.representationsBefore n := by
  unfold AlgebraicProofString.representationsBefore
  split
  · omega
  · split <;> simp

theorem AlgebraicProofString.ipaS_mem_representationsBefore
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (aps : AlgebraicProofString shape basis) (n : Fin 11) (h9n : 9 ≤ (n : Nat)) :
    aps.ipaS ∈ aps.representationsBefore n := by
  unfold AlgebraicProofString.representationsBefore
  split
  · omega
  · split
    · omega
    · simp

/-- The final proof's member-coverage certificate remains valid after adding all representations
available at a later deployed prefix. -/
theorem OnlineMemberProofData.adaptiveFallbackMembersCovered
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed) (n : Fin 11) :
    AdaptiveMembersCovered vk instanceCommitment data.algebraicProof.erase
      (data.algebraicProof.representationsBefore n ++ fixed) := by
  intro nu i hi m
  apply (data.membersCovered nu i hi m).mono_points
  intro ap hap
  rw [AlgebraicProofString.preX1AssemblySource] at hap
  rcases List.mem_append.mp hap with hpre | hfixed
  · exact ⟨ap, List.mem_append_left _
        (data.algebraicProof.preX1Points_mem_representationsBefore n ap hpre), rfl⟩
  · exact ⟨ap, List.mem_append_right _ hfixed, rfl⟩

theorem OnlineMemberProofData.adaptiveFallbackQPrimeCovered
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed) (n : Fin 11) (h7n : 7 ≤ (n : Nat)) :
    CommitmentRefCovered (data.algebraicProof.representationsBefore n ++ fixed)
      (.point data.algebraicProof.erase.multiopenQPrime) :=
  ⟨data.algebraicProof.multiopenQPrime,
    List.mem_append_left _
      (data.algebraicProof.multiopenQPrime_mem_representationsBefore n h7n), rfl⟩

theorem OnlineMemberProofData.adaptiveFallbackSCovered
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed) (n : Fin 11) (h9n : 9 ≤ (n : Nat)) :
    CommitmentRefCovered (data.algebraicProof.representationsBefore n ++ fixed)
      (.point data.algebraicProof.erase.ipaS) :=
  ⟨data.algebraicProof.ipaS,
    List.mem_append_left _ (data.algebraicProof.ipaS_mem_representationsBefore n h9n), rfl⟩

/-- On the actual proof prefix, normalization recovers exactly the strict pre-`x₁` source used by
the executable deployed unbatcher. -/
theorem OnlineMemberProofData.adaptiveRootMemberSource_eq_preX1
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed) (n : Fin 11) (h5n : 5 ≤ (n : Nat)) :
    adaptiveRootMemberSource n (adaptiveRootPrefixProof n data.algebraicProof.erase)
        (data.algebraicProof.representationsBefore n ++ fixed) =
      data.algebraicProof.preX1AssemblySource fixed := by
  have hprelen : data.algebraicProof.erase.preX1CommitmentPoints.length =
      data.algebraicProof.preX1Points.length := by
    have hpoints := data.algebraicProof.representationsBefore_points (5 : Fin 11)
    have := congrArg List.length hpoints
    simpa [AlgebraicProofString.representationsBefore,
      ProofString.commitmentPointsBefore] using this.symm
  have hstagelen :
      (data.algebraicProof.erase.commitmentPointsBefore n).length =
        (data.algebraicProof.representationsBefore n).length := by
    have hpoints := data.algebraicProof.representationsBefore_points n
    have := congrArg List.length hpoints
    simpa only [List.length_map] using this.symm
  unfold adaptiveRootMemberSource
  rw [adaptiveRootPrefixProof_preX1CommitmentPoints,
    adaptiveRootPrefixProof_commitmentPointsBefore, hprelen, hstagelen]
  fin_cases n
  · norm_num at h5n
  · norm_num at h5n
  · norm_num at h5n
  · norm_num at h5n
  · norm_num at h5n
  all_goals simp [AlgebraicProofString.representationsBefore,
    AlgebraicProofString.preX1AssemblySource]

/-- At every stage where `q′` exists, the isolated slot is its exact algebraic representation. -/
theorem OnlineMemberProofData.adaptiveRootQSource_eq
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed) (n : Fin 11) (h7n : 7 ≤ (n : Nat)) :
    adaptiveRootQSource (adaptiveRootPrefixProof n data.algebraicProof.erase)
        (data.algebraicProof.representationsBefore n ++ fixed) =
      [data.algebraicProof.multiopenQPrime] := by
  have hprelen : data.algebraicProof.erase.preX1CommitmentPoints.length =
      data.algebraicProof.preX1Points.length := by
    have hpoints := data.algebraicProof.representationsBefore_points (5 : Fin 11)
    have := congrArg List.length hpoints
    simpa [AlgebraicProofString.representationsBefore,
      ProofString.commitmentPointsBefore] using this.symm
  unfold adaptiveRootQSource
  rw [adaptiveRootPrefixProof_preX1CommitmentPoints]
  rw [hprelen]
  fin_cases n
  all_goals try norm_num at h7n
  all_goals simp [AlgebraicProofString.representationsBefore]

/-- At every stage where `S` exists, the isolated slot is its exact algebraic representation. -/
theorem OnlineMemberProofData.adaptiveRootSSource_eq
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed) (n : Fin 11) (h9n : 9 ≤ (n : Nat)) :
    adaptiveRootSSource (adaptiveRootPrefixProof n data.algebraicProof.erase)
        (data.algebraicProof.representationsBefore n ++ fixed) =
      [data.algebraicProof.ipaS] := by
  have hprelen : data.algebraicProof.erase.preX1CommitmentPoints.length =
      data.algebraicProof.preX1Points.length := by
    have hpoints := data.algebraicProof.representationsBefore_points (5 : Fin 11)
    have := congrArg List.length hpoints
    simpa [AlgebraicProofString.representationsBefore,
      ProofString.commitmentPointsBefore] using this.symm
  unfold adaptiveRootSSource
  rw [adaptiveRootPrefixProof_preX1CommitmentPoints]
  rw [hprelen]
  fin_cases n
  all_goals try norm_num at h9n
  all_goals simp [AlgebraicProofString.representationsBefore]

/-! ## Arbitrary-adaptive pricing of one deployed root -/

/-- The final-output root event, decoded through the same strict-prefix wrapper used by the
arbitrary adaptive squeeze theorem. -/
noncomputable def adaptiveFinalRootBad
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (n : Fin 11)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) : Set Fp :=
  adaptivePrefixBad (shape := shape) family.init n
    (adaptiveFallbackRootSurface family basis n data) t O

/-- Every deployed root of a bare malicious adaptive online-AGM adversary is priced at its first
actual annotated query (or the fresh verifier fallback), unless the executable provenance finder
has already produced a DLOG relation.  No phase, cut, or honest schedule is an input. -/
theorem ComputedAdaptiveOnlineAGMFSFamily.adaptiveFinalRootBadWithoutRelation_table_le
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (n : Fin 11)
    (h5n : 5 ≤ (n : Nat)) :
    (PMF.uniformOfFintype (BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)).toOuterMeasure
      {O | let data := (family.adversary basis).run O
        let t := (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof) n
        O t ∈ adaptiveFinalRootBad family basis n data t O ∧
          family.adaptivePreIpaRepresentationRelationFinder basis O = none} ≤
      (family.Q + 1 : Nat) *
        deployedRootEventBudget shape (adaptiveRootEventIndex n) := by
  apply family.adaptiveFinalPrefixBadWithoutRelation_table_le basis n
    (adaptiveFinalRootBad family basis n)
    (family.adaptivePreIpaRepresentationRelationFinder basis)
    (adaptiveQueriedRootSurface family basis n h5n)
    (adaptiveFallbackRootSurface family basis n)
  · intro O
    dsimp only
    intro hbad hnone
    let data := (family.adversary basis).run O
    let t := (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof) n
    change O t ∈ adaptiveFinalRootBad family basis n data t O at hbad
    change O t ∈ LabeledOracleComp.firstLabelOrFallbackBad (family.adversary basis)
      (fun t label O => adaptiveLabeledPrefixBad (shape := shape)
        family.init basis n (adaptiveQueriedRootSurface family basis n h5n) t label O)
      (fun data t O => adaptivePrefixBad (shape := shape) family.init n
        (adaptiveFallbackRootSurface family basis n data) t O) t O
    have hlen : t.val.length = preIpaLen shape family.init.length n := by
      exact preIpaSqueezePoints_length_eq family.init data.algebraicProof.erase
        data.wellFormed n
    unfold LabeledOracleComp.firstLabelOrFallbackBad
    cases hfind : (family.adversary basis).findLabel O t with
    | none =>
        simpa only [adaptiveFinalRootBad] using hbad
    | some label =>
        have hat := family.adaptivePreIpaRepresentationRelationFinder_none_at
          basis O hnone n h5n
        have hlocal : selectedQueryRepresentationRelation? t (family.adversary basis) O
            (data.algebraicProof.representationsBefore n) (by
              intro ap hap
              change ap.point ∈ transcriptGroupPoints
                (preIpaSqueezePoints family.init data.algebraicProof.erase n)
              exact data.algebraicProof.representationsBefore_covered family.init
                data.wellFormed n h5n ap hap) = none := by
          simpa only [ComputedAdaptiveOnlineAGMFSFamily.adaptivePreIpaRepresentationRelationAt?]
            using hat
        have hprov := selectedQueryRepresentationRelation?_eq_none t
          (family.adversary basis) O (data.algebraicProof.representationsBefore n) _ hlocal
        cases hprov with
        | inl hfresh => simp [hfind] at hfresh
        | inr pinned =>
            have hlabel : pinned.query = label := by
              exact Option.some.inj (pinned.found.symm.trans hfind)
            subst label
            have hdecode := decodePreIpaPrefix?_isSome family.init n
              data.toAlgebraicWfProof.proof
            change (decodePreIpaPrefix? (shape := shape) family.init n t).isSome at hdecode
            cases hdec : decodePreIpaPrefix? (shape := shape) family.init n t with
            | none => simp [hdec] at hdecode
            | some decoded =>
                have hsource := adaptiveQuerySource_eq_of_pinned family basis n h5n O
                  decoded pinned
                have hprefixBounded : fullPrefixesPre family.init decoded.proof n =
                    fullPrefixesPre family.init data.toAlgebraicWfProof.proof n :=
                  decoded.point_eq
                have hprefix : preIpaSqueezePoints family.init decoded.proof.1 n =
                    preIpaSqueezePoints family.init data.algebraicProof.erase n :=
                  congrArg Subtype.val hprefixBounded
                have hcanonical := adaptiveRootPrefixProof_congr family.init n h5n
                  decoded.proof.1 data.algebraicProof.erase decoded.proof.2 data.wellFormed hprefix
                unfold adaptiveFinalRootBad adaptivePrefixBad at hbad
                simp only [if_pos hlen] at hbad
                unfold adaptiveLabeledPrefixBad
                simp only [if_pos hlen]
                have hsurface : adaptiveQueriedRootSurface family basis n h5n t
                    pinned.query (fun i => O (adaptiveEarlierPrefix (shape := shape)
                      family.init t (i.castLE (le_of_lt n.isLt)))) =
                    adaptiveFallbackRootSurface family basis n data t
                      (fun i => O (adaptiveEarlierPrefix (shape := shape)
                        family.init t (i.castLE (le_of_lt n.isLt)))) := by
                  simp only [adaptiveQueriedRootSurface, hdec]
                  unfold adaptiveFallbackRootSurface
                  rw [hsource, hcanonical]
                rwa [hsurface]
  · exact adaptiveQueriedRootSurface_measure_le family basis n h5n
  · exact adaptiveFallbackRootSurface_measure_le family basis n h5n

end Zcash.Snark
