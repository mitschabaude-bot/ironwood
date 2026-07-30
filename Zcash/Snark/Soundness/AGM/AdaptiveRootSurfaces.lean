import Zcash.Snark.Soundness.AGM.AdaptiveStraightLine

/-!
# Direct root surfaces for arbitrary adaptive online-AGM adversaries

Each root surface is rebuilt from the ordinary prefix and its first-query AGM coordinates.
`AdaptiveStraightLine` handles later representation mismatches.
-/

namespace Zcash.Snark

open Classical CompPoly.CPolynomial
open scoped ENNReal

set_option maxRecDepth 10000

local instance vestaInhabitedAdaptiveRootSurfaces : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

/-- A well-formed ordinary proof decoded from one exact deployed pre-IPA squeeze point. -/
structure DecodedPreIpaPrefix
    (init : List (TranscriptElt Fp VestaG)) (n : Fin 11)
    (t : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k)) where
  proof : WfProof shape
  point_eq : fullPrefixesPre init proof n = t

/-- Choose a prefix decode when the bounded transcript is a valid deployed squeeze point.
Failure produces `none`, and callers assign the empty bad set.  This choice is used only to
describe a probability surface; all relation-producing branches remain executable. -/
noncomputable def decodePreIpaPrefix?
    (init : List (TranscriptElt Fp VestaG)) (n : Fin 11)
    (t : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k)) :
    Option (DecodedPreIpaPrefix (shape := shape) init n t) :=
  if h : Nonempty (DecodedPreIpaPrefix (shape := shape) init n t) then
    some (Classical.choice h)
  else none

/-- The actual verifier-selected prefix always has a decode. -/
theorem decodePreIpaPrefix?_isSome
    (init : List (TranscriptElt Fp VestaG)) (n : Fin 11)
    (p : WfProof shape) :
    (decodePreIpaPrefix? (shape := shape) init n (fullPrefixesPre init p n)).isSome := by
  have h : Nonempty (DecodedPreIpaPrefix (shape := shape) init n
      (fullPrefixesPre init p n)) := ⟨⟨p, rfl⟩⟩
  rw [decodePreIpaPrefix?, dif_pos h]
  rfl

/-- Query-time representations of precisely the prover commitment points available at `n`,
followed by the verifier-fixed representations. -/
def adaptiveQuerySource
    (init : List (TranscriptElt Fp VestaG))
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (n : Fin 11) (h5n : 5 ≤ (n : ℕ))
    {t : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k)}
    (decoded : DecodedPreIpaPrefix (shape := shape) init n t)
    (query : AlgebraicTranscriptQuery (F := Fp) basis t)
    (fixed : List (AlgebraicPoint (F := Fp) basis)) :
    List (AlgebraicPoint (F := Fp) basis) :=
  query.representationsForPoints
      (decoded.proof.1.commitmentPointsBefore n) (by
        intro P hP
        rw [← decoded.point_eq]
        exact decoded.proof.1.commitmentPointsBefore_covered init decoded.proof.2
          n h5n P hP) ++ fixed

/-- Structural member coverage against an explicit stage-local representation source. -/
def AdaptiveMembersCovered
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis)) : Prop :=
  ∀ nu : Fin 11 → Fp, ∀ i : Nat,
    i < deployedX4PairCount vk instanceCommitment ps (chRecord nu (fun _ => 0)) →
      ∀ m : Fin (deployedSetQueries vk instanceCommitment ps
        (chRecord nu (fun _ => 0)) i).length,
        CommitmentRefCovered source
          ((deployedSetQueries vk instanceCommitment ps
            (chRecord nu (fun _ => 0)) i).getD (m : Nat) (.point 0, [])).1

/-- Stage-local AGM coordinates for every commitment routed into one deployed point set. -/
def adaptiveMemberRepresentations
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp) (i : Nat)
    (hi : i < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0))) :
    AlgebraicColumnRepresentations (ursOfAugmentedBasis shape.k basis)
      (deployedSetMemberCommitments (ursOfAugmentedBasis shape.k basis) rfl
        vk instanceCommitment ps (chRecord nu (fun _ => 0)) i) := by
  let memberRef : Fin (deployedSetQueries vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) i).length → CommitmentRef shape.k Fp VestaG :=
    fun m => ((deployedSetQueries vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) i).getD (m : Nat) (.point 0, [])).1
  let represented : ∀ m, CoveredCommitmentRepresentation basis (memberRef m) :=
    fun m => coveredCommitmentRepresentation source (memberRef m) (hcovered nu i hi m)
  refine
    { coeffs := fun m => (represented m).coeffs
      uComp := fun m => (represented m).uComp
      wComp := fun m => (represented m).wComp
      commitment := ?_ }
  intro m
  simpa only [memberRef, deployedSetMemberCommitments_apply] using
    (represented m).commitment

/-- Canonical power-batch coordinates of already represented columns. -/
def AlgebraicColumnRepresentations.toDirectPowerBatch
    {G : Type*} [AddCommGroup G] [Module Fp G]
    {urs : URS G} {numColumns : Nat} {columns : Fin numColumns → G}
    (represented : AlgebraicColumnRepresentations urs columns) (x : Fp) :
    AlgebraicPowerBatch urs columns
      (∑ i : Fin numColumns, x ^ (i : Nat) • represented.coeffs i)
      (∑ i : Fin numColumns, x ^ (i : Nat) * represented.uComp i)
      (∑ i : Fin numColumns, x ^ (i : Nat) * represented.wComp i) x where
  coeffs := represented.coeffs
  uComp := represented.uComp
  wComp := represented.wComp
  commitment := represented.commitment
  reconstruct := rfl
  reconstructU := rfl
  reconstructW := rfl

/-- The direct, pre-`x₁` member batch for one deployed point set. -/
def adaptiveX1Batch
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp) (i : Nat)
    (hi : i < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0))) :=
  (adaptiveMemberRepresentations vk instanceCommitment ps source hcovered nu i hi).toDirectPowerBatch
    (nu 5)

/-- One stage-local `x₁` member-binding polynomial. -/
noncomputable def adaptiveX1RootPolynomial
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp) (i : Nat)
    (hi : i < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0)))
    (idx : Fin ((deployedSetsForEval vk instanceCommitment ps
      (chRecord nu (fun _ => 0))).getD i ([], [], 0)).1.length) : CPoly :=
  memberBindingErrorPolynomial
    (fun m : Fin (deployedSetQueries vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) i).length =>
      coeffsToPoly ((adaptiveX1Batch vk instanceCommitment ps source hcovered nu i hi).coeffs m))
    (fun m : Fin (deployedSetQueries vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) i).length =>
      ((deployedSetQueries vk instanceCommitment ps
        (chRecord nu (fun _ => 0)) i).getD (m : Nat) (.point 0, [])).2.getD
          (idx : Nat) 0)
    ((deployedSetsForEval vk instanceCommitment ps
      (chRecord nu (fun _ => 0))).getD i ([], [], 0)).1[idx]

/-- All query-time `x₁` roots for one set. -/
noncomputable def adaptiveX1RootSet
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp) (i : Nat) : Set Fp :=
  if hi : i < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) then
    {x | ∃ idx : Fin ((deployedSetsForEval vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).getD i ([], [], 0)).1.length,
      idx ∈ (Finset.univ : Finset _) ∧
      x ∈ szBadSet (adaptiveX1RootPolynomial vk instanceCommitment ps source
        hcovered nu i hi idx)}
  else ∅

/-- The single union charged at the adaptive `x₁` squeeze. -/
noncomputable def adaptiveX1AllRootSet
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp) : Set Fp :=
  {x | ∃ i : Fin shape.numPointSets,
    x ∈ adaptiveX1RootSet vk instanceCommitment ps source hcovered nu i}

/-- The query-time `x₁` union has the same shape bound as the final direct decoder. -/
theorem adaptiveX1AllRootSet_measure_le
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
        (adaptiveX1AllRootSet vk instanceCommitment ps source hcovered nu) ≤
      ((shape.numPointSets * queryBudget shape * queryBudget shape : Nat) : ENNReal) /
        Fintype.card Fp := by
  rw [adaptiveX1AllRootSet]
  have hsub : {x | ∃ i : Fin shape.numPointSets,
      x ∈ adaptiveX1RootSet vk instanceCommitment ps source hcovered nu i} ⊆
      ⋃ i : Fin shape.numPointSets,
        adaptiveX1RootSet vk instanceCommitment ps source hcovered nu i := by
    rintro x ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
  rw [tsum_fintype]
  calc
    ∑ i : Fin shape.numPointSets,
        (PMF.uniformOfFintype Fp).toOuterMeasure
          (adaptiveX1RootSet vk instanceCommitment ps source hcovered nu i)
      ≤ ∑ _i : Fin shape.numPointSets,
          (((queryBudget shape * queryBudget shape : Nat) : ENNReal) /
            Fintype.card Fp) := by
        gcongr with i
        rw [adaptiveX1RootSet]
        split
        next hi =>
          have hroot := uniformChallenge_szBadSet_iUnion_le
            (Finset.univ : Finset (Fin ((deployedSetsForEval vk instanceCommitment ps
              (chRecord nu (fun _ => 0))).getD (i : Nat) ([], [], 0)).1.length))
            (adaptiveX1RootPolynomial vk instanceCommitment ps source hcovered nu i hi)
            (deployedSetQueries vk instanceCommitment ps
              (chRecord nu (fun _ => 0)) i).length
            (fun _ _ => powerErrorPolynomial_natDegree_le _)
          refine le_trans hroot ?_
          have hnd := deployedSetsForEval_getD_nodup vk instanceCommitment ps
            (chRecord nu (fun _ => 0)) hi
          have hpoints : ((deployedSetsForEval vk instanceCommitment ps
              (chRecord nu (fun _ => 0))).getD (i : Nat) ([], [], 0)).1.length ≤
              queryBudget shape := by
            rw [← List.toFinset_card_of_nodup hnd,
              deployedSetsForEval_getD_toFinset vk instanceCommitment ps
                (chRecord nu (fun _ => 0)) hi]
            exact le_trans (Finset.card_le_card
              (deployedSetPts_subset vk instanceCommitment ps
                (chRecord nu (fun _ => 0)) i))
              (deployedAllPts_card_le_budget vk instanceCommitment ps
                (chRecord nu (fun _ => 0)))
          have hmembers := deployedSetQueries_length_le vk instanceCommitment ps
            (chRecord nu (fun _ => 0)) i
          gcongr
          simpa using hpoints
        next hi => simp
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      simp only [div_eq_mul_inv]
      ring

/-- Direct `x₁`-compressed coordinate polynomial of one point set, fixed before `x₂`. -/
noncomputable def adaptiveSetColumn
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp)
    (j : Fin (deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0)))) : CPoly :=
  let i := deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) - 1 - (j : Nat)
  let members := adaptiveMemberRepresentations vk instanceCommitment ps source hcovered nu i
    (by dsimp [i]; omega)
  coeffsToPoly (∑ m : Fin (deployedSetQueries vk instanceCommitment ps
    (chRecord nu (fun _ => 0)) i).length,
      (nu 5) ^ (m : Nat) • members.coeffs m)

/-- The `x₂` separation surface rebuilt solely from pre-`x₂` query data. -/
noncomputable def adaptiveX2RootSet
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp) : Set Fp :=
  let ch : Challenges shape.k Fp := chRecord nu (fun _ => 0)
  {x | ∃ node, node ∈ deployedAllPts vk instanceCommitment ps ch ∧
    x ∈ szBadSet (nodeBindingErrorPolynomial
      (deployedAllPts vk instanceCommitment ps ch)
      (deployedAlgebraicSetPoints vk instanceCommitment ps ch)
      (fun j => adaptiveSetColumn vk instanceCommitment ps source hcovered nu j)
      (deployedAlgebraicSetInterpolants vk instanceCommitment ps ch) node)}

/-- The adaptive `x₂` surface retains the direct node-binding budget. -/
theorem adaptiveX2RootSet_measure_le
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp) :
    (PMF.uniformOfFintype Fp).toOuterMeasure
        (adaptiveX2RootSet vk instanceCommitment ps source hcovered nu) ≤
      ((shape.numPointSets * queryBudget shape : Nat) : ENNReal) /
        Fintype.card Fp := by
  let ch : Challenges shape.k Fp := chRecord nu (fun _ => 0)
  refine le_trans (uniformChallenge_szBadSet_iUnion_le
    (deployedAllPts vk instanceCommitment ps ch)
    (fun node => nodeBindingErrorPolynomial
      (deployedAllPts vk instanceCommitment ps ch)
      (deployedAlgebraicSetPoints vk instanceCommitment ps ch)
      (fun j => adaptiveSetColumn vk instanceCommitment ps source hcovered nu j)
      (deployedAlgebraicSetInterpolants vk instanceCommitment ps ch) node)
    (deployedX4PairCount vk instanceCommitment ps ch)
    (fun _ _ => powerErrorPolynomial_natDegree_le _)) ?_
  calc
    (((deployedAllPts vk instanceCommitment ps ch).card *
        deployedX4PairCount vk instanceCommitment ps ch : Nat) : ENNReal) /
        Fintype.card Fp ≤
      (((queryBudget shape * shape.numPointSets : Nat) : ENNReal) /
        Fintype.card Fp) := by
          gcongr
          · exact deployedAllPts_card_le_budget vk instanceCommitment ps ch
          · exact deployedX4PairCount_le_numPointSets vk instanceCommitment ps ch
    _ = _ := by rw [Nat.mul_comm]

/-! ## Direct post-`x₂` columns -/

/-- Executable coordinate columns used by the direct `x₄` batch.  This is factored out of the
proof-carrying representation so consumers can reduce a selected column without elaborating its
commitment proof. -/
def adaptiveX4ColumnCoeffs
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (nu : Fin 11 → Fp) :
    Fin (deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) + 1) → Fin (2 ^ shape.k) → Fp :=
  fun j =>
    if hj : (j : Nat) < deployedX4PairCount vk instanceCommitment ps
        (chRecord nu (fun _ => 0)) then
      let i := x4ColumnSetIndex vk instanceCommitment ps
        (chRecord nu (fun _ => 0)) (j : Nat)
      let members := adaptiveMemberRepresentations vk instanceCommitment ps memberSource hcovered nu i
        (by dsimp [i, x4ColumnSetIndex]; omega)
      ∑ m : Fin (deployedSetQueries vk instanceCommitment ps
          (chRecord nu (fun _ => 0)) i).length,
        (nu 5) ^ (m : Nat) • members.coeffs m
    else (onlinePointCoordinates qSource ps.multiopenQPrime).1

/-- Executable `u` coordinates used by the direct `x₄` batch. -/
def adaptiveX4ColumnUComp
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (nu : Fin 11 → Fp) :
    Fin (deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) + 1) → Fp :=
  fun j =>
    if hj : (j : Nat) < deployedX4PairCount vk instanceCommitment ps
        (chRecord nu (fun _ => 0)) then
      let i := x4ColumnSetIndex vk instanceCommitment ps
        (chRecord nu (fun _ => 0)) (j : Nat)
      let members := adaptiveMemberRepresentations vk instanceCommitment ps memberSource hcovered nu i
        (by dsimp [i, x4ColumnSetIndex]; omega)
      ∑ m : Fin (deployedSetQueries vk instanceCommitment ps
          (chRecord nu (fun _ => 0)) i).length,
        (nu 5) ^ (m : Nat) * members.uComp m
    else (onlinePointCoordinates qSource ps.multiopenQPrime).2.1

/-- Executable `w` coordinates used by the direct `x₄` batch. -/
def adaptiveX4ColumnWComp
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (nu : Fin 11 → Fp) :
    Fin (deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) + 1) → Fp :=
  fun j =>
    if hj : (j : Nat) < deployedX4PairCount vk instanceCommitment ps
        (chRecord nu (fun _ => 0)) then
      let i := x4ColumnSetIndex vk instanceCommitment ps
        (chRecord nu (fun _ => 0)) (j : Nat)
      let members := adaptiveMemberRepresentations vk instanceCommitment ps memberSource hcovered nu i
        (by dsimp [i, x4ColumnSetIndex]; omega)
      ∑ m : Fin (deployedSetQueries vk instanceCommitment ps
          (chRecord nu (fun _ => 0)) i).length,
        (nu 5) ^ (m : Nat) * members.wComp m
    else (onlinePointCoordinates qSource ps.multiopenQPrime).2.2

/-- The executable direct `x₄` coordinates reconstruct their advertised column commitments. -/
theorem adaptiveX4ColumnCommitment
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hqPrime : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (nu : Fin 11 → Fp) (j) :
    commit (ursOfAugmentedBasis shape.k basis)
        (adaptiveX4ColumnCoeffs vk instanceCommitment ps memberSource qSource hcovered nu j) +
        adaptiveX4ColumnUComp vk instanceCommitment ps memberSource qSource hcovered nu j •
          (ursOfAugmentedBasis shape.k basis).u +
        adaptiveX4ColumnWComp vk instanceCommitment ps memberSource qSource hcovered nu j •
          (ursOfAugmentedBasis shape.k basis).w =
      x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl
        vk instanceCommitment ps (chRecord nu (fun _ => 0)) j := by
  by_cases hj : (j : Nat) < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0))
  · simp only [adaptiveX4ColumnCoeffs, adaptiveX4ColumnUComp,
      adaptiveX4ColumnWComp, dif_pos hj]
    let i := x4ColumnSetIndex vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) (j : Nat)
    let members := adaptiveMemberRepresentations vk instanceCommitment ps memberSource hcovered nu i
      (by unfold i x4ColumnSetIndex; omega)
    exact (members.power_commitment (nu 5)).trans
      (x4BatchCommitments_eq_memberPowerSum _ rfl vk instanceCommitment ps
        (chRecord nu (fun _ => 0)) hj).symm
  · simp only [adaptiveX4ColumnCoeffs, adaptiveX4ColumnUComp,
      adaptiveX4ColumnWComp, dif_neg hj]
    simpa only [x4BatchCommitments, if_neg hj] using
      onlinePointCoordinates_commitment qSource ps.multiopenQPrime hqPrime

/-- Query-time coordinates for the `x₄` columns.  Set columns are the direct `x₁` power
sums above; the top column is the first online representation of `q′`. -/
def adaptiveX4ColumnRepresentations
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hqPrime : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (nu : Fin 11 → Fp) :
    AlgebraicColumnRepresentations (ursOfAugmentedBasis shape.k basis)
      (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl
        vk instanceCommitment ps (chRecord nu (fun _ => 0))) where
  coeffs := adaptiveX4ColumnCoeffs vk instanceCommitment ps memberSource qSource hcovered nu
  uComp := adaptiveX4ColumnUComp vk instanceCommitment ps memberSource qSource hcovered nu
  wComp := adaptiveX4ColumnWComp vk instanceCommitment ps memberSource qSource hcovered nu
  commitment := adaptiveX4ColumnCommitment vk instanceCommitment ps memberSource qSource
    hcovered hqPrime nu

/-- A direct `x₄` batch whose coordinate columns are fixed before the `x₄` squeeze. -/
def adaptiveX4Batch
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hqPrime : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (nu : Fin 11 → Fp) :=
  (adaptiveX4ColumnRepresentations vk instanceCommitment ps memberSource qSource
    hcovered hqPrime nu).toDirectPowerBatch
    (nu 8)

/-- The `x₄` value-binding surface rebuilt from the pre-`x₄` annotation. -/
noncomputable def adaptiveX4RootSet
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hqPrime : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (nu : Fin 11 → Fp) : Set Fp :=
  szBadSet (algebraicBatchErrorPolynomial (evalVector shape.k (nu 7))
    (adaptiveX4Batch vk instanceCommitment ps memberSource qSource hcovered hqPrime nu).coeffs
    (x4BatchEvals vk instanceCommitment ps (chRecord nu (fun _ => 0))))

/-- The adaptive `x₄` surface has the direct shape price. -/
theorem adaptiveX4RootSet_measure_le
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hqPrime : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (nu : Fin 11 → Fp) :
    uniformChallenge.toOuterMeasure
        (adaptiveX4RootSet vk instanceCommitment ps memberSource qSource
          hcovered hqPrime nu) ≤
      ((shape.numPointSets + 1 : Nat) : ENNReal) / Fintype.card Fp := by
  rw [adaptiveX4RootSet]
  refine le_trans (uniformChallenge_szBadSet _) ?_
  apply ENNReal.div_le_div_right
  exact_mod_cast le_trans
    (algebraicBatchErrorPolynomial_natDegree_le (evalVector shape.k (nu 7))
      (adaptiveX4Batch vk instanceCommitment ps memberSource qSource hcovered hqPrime nu).coeffs
      (x4BatchEvals vk instanceCommitment ps (chRecord nu (fun _ => 0))))
    (Nat.add_le_add_right
      (deployedX4PairCount_le_numPointSets vk instanceCommitment ps
        (chRecord nu (fun _ => 0))) 1)

/-- The cleared-quotient/collision surface rebuilt from the pre-`x₃` annotation. -/
noncomputable def adaptiveX3RootSet
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hqPrime : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (nu : Fin 11 → Fp) : Set Fp :=
  let ch : Challenges shape.k Fp := chRecord nu (fun _ => 0)
  let batch := adaptiveX4Batch vk instanceCommitment ps memberSource qSource hcovered hqPrime nu
  ↑(szBadSet (deployedX3ErrorPolynomial (ursOfAugmentedBasis shape.k basis) rfl
      vk instanceCommitment ps ch batch) ∪
    deployedAllPts vk instanceCommitment ps ch)

/-- The adaptive `x₃` surface retains the deployed direct shape price. -/
theorem adaptiveX3RootSet_measure_le
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hqPrime : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (nu : Fin 11 → Fp) :
    uniformChallenge.toOuterMeasure
        (adaptiveX3RootSet vk instanceCommitment ps memberSource qSource
          hcovered hqPrime nu) ≤
      ((max (2 ^ shape.k) (queryBudget shape) + 2 * queryBudget shape : Nat) : ENNReal) /
        Fintype.card Fp := by
  let ch : Challenges shape.k Fp := chRecord nu (fun _ => 0)
  let batch := adaptiveX4Batch vk instanceCommitment ps memberSource qSource hcovered hqPrime nu
  rw [adaptiveX3RootSet, uniformChallenge_badSet]
  apply ENNReal.div_le_div_right
  have hroot := deployedX3ErrorPolynomial_natDegree_le
    (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment ps ch batch
  have hroot' :
      (deployedX3ErrorPolynomial (ursOfAugmentedBasis shape.k basis) rfl
        vk instanceCommitment ps ch batch).natDegree ≤
        max (2 ^ shape.k) (deployedAllPts vk instanceCommitment ps ch).card +
          (deployedAllPts vk instanceCommitment ps ch).card := by
    simpa [ursOfAugmentedBasis] using hroot
  have hpts := deployedAllPts_card_le_budget vk instanceCommitment ps ch
  have hcard :
      (szBadSet (deployedX3ErrorPolynomial (ursOfAugmentedBasis shape.k basis) rfl
          vk instanceCommitment ps ch batch) ∪
        deployedAllPts vk instanceCommitment ps ch).card ≤
      max (2 ^ shape.k) (queryBudget shape) + 2 * queryBudget shape := by
    refine le_trans (Finset.card_union_le _ _) ?_
    have hsz := le_trans (szBadSet_card_le _) hroot'
    omega
  exact_mod_cast hcard

/-! ## The two shift-recovery surfaces -/

/-- Direct generator coordinates of the `x₄`-collapsed aggregate. -/
def adaptiveAggregateG
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hqPrime : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (nu : Fin 11 → Fp) : Fin (2 ^ shape.k) → Fp :=
  let cols := adaptiveX4ColumnRepresentations vk instanceCommitment ps memberSource qSource
    hcovered hqPrime nu
  ∑ j : Fin (deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) + 1),
      (nu 8) ^ (j : Nat) • cols.coeffs j

/-- Direct `U` coordinate of the `x₄`-collapsed aggregate. -/
def adaptiveAggregateU
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hqPrime : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (nu : Fin 11 → Fp) : Fp :=
  let cols := adaptiveX4ColumnRepresentations vk instanceCommitment ps memberSource qSource
    hcovered hqPrime nu
  ∑ j : Fin (deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) + 1),
      (nu 8) ^ (j : Nat) * cols.uComp j

/-- The `ξ` shift-recovery surface uses only data present before `ξ`. -/
noncomputable def adaptiveXiRootSet
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource sSource : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hqPrime : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (hS : CommitmentRefCovered sSource (.point ps.ipaS))
    (nu : Fin 11 → Fp) : Set Fp :=
  let ch : Challenges shape.k Fp := chRecord nu (fun _ => 0)
  let aggregate := adaptiveAggregateG vk instanceCommitment ps memberSource qSource
    hcovered hqPrime nu
  let s := coveredCommitmentRepresentation sSource (.point ps.ipaS) hS
  szBadSet (ipaShiftXiPolynomial
    (commitGen (evalVector shape.k ch.x3) aggregate -
      multiopenValue vk instanceCommitment ps ch)
    (commitGen (evalVector shape.k ch.x3) s.coeffs))

/-- The `z` shift-recovery surface uses only data present before `z`. -/
noncomputable def adaptiveZRootSet
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource sSource : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hqPrime : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (hS : CommitmentRefCovered sSource (.point ps.ipaS))
    (nu : Fin 11 → Fp) : Set Fp :=
  let ch : Challenges shape.k Fp := chRecord nu (fun _ => 0)
  let aggregateG := adaptiveAggregateG vk instanceCommitment ps memberSource qSource
    hcovered hqPrime nu
  let aggregateU := adaptiveAggregateU vk instanceCommitment ps memberSource qSource
    hcovered hqPrime nu
  let s := coveredCommitmentRepresentation sSource (.point ps.ipaS) hS
  szBadSet (ipaShiftZPolynomial
    (commitGen (evalVector shape.k ch.x3) aggregateG -
      multiopenValue vk instanceCommitment ps ch)
    aggregateU s.uComp (commitGen (evalVector shape.k ch.x3) s.coeffs) ch.xi)

theorem adaptiveXiRootSet_measure_le
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource sSource : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hqPrime : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (hS : CommitmentRefCovered sSource (.point ps.ipaS))
    (nu : Fin 11 → Fp) :
    uniformChallenge.toOuterMeasure
        (adaptiveXiRootSet vk instanceCommitment ps memberSource qSource sSource
          hcovered hqPrime hS nu) ≤
      1 / Fintype.card Fp := by
  rw [adaptiveXiRootSet]
  exact ipaShiftXi_badSet_measure_le _ _

theorem adaptiveZRootSet_measure_le
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource sSource : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hqPrime : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (hS : CommitmentRefCovered sSource (.point ps.ipaS))
    (nu : Fin 11 → Fp) :
    uniformChallenge.toOuterMeasure
        (adaptiveZRootSet vk instanceCommitment ps memberSource qSource sSource
          hcovered hqPrime hS nu) ≤
      1 / Fintype.card Fp := by
  rw [adaptiveZRootSet]
  exact ipaShiftZ_badSet_measure_le _ _ _ _ _

end Zcash.Snark
