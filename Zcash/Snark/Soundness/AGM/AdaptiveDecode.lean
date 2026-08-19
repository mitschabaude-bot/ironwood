import Zcash.Snark.Soundness.AGM.AdaptiveComposition
import Zcash.Snark.Soundness.AGM.OnlineConstraint

/-!
# Deterministic decode for arbitrary adaptive online-AGM families

This module connects pre-answer AGM coordinates to the executable unbatcher and existing
constraint and Action decoders, without phase objects or existential relation witnesses.
-/

namespace Zcash.Snark

open Classical CompPoly.CPolynomial

local instance vestaInhabitedAdaptiveDecode : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

@[simp] theorem ComputedAdaptiveOnlineAGMFSFamily.toFamily_vk
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) :
    family.toFamily.vk basis = family.vk basis := rfl

@[simp] theorem ComputedAdaptiveOnlineAGMFSFamily.toFamily_instanceCommitment
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) :
    family.toFamily.instanceCommitment basis = family.instanceCommitment basis := rfl

@[simp] theorem OnlineMemberProofData.toAlgebraicWfProof_proof_fst
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed) :
    data.toAlgebraicWfProof.proof.1 = data.algebraicProof.erase := rfl

@[simp] theorem OnlineMemberProofData.toAlgebraicWfProof_algebraicProof
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed) :
    data.toAlgebraicWfProof.algebraicProof = data.algebraicProof := rfl

/-- Final online member coverage is already the normalized adaptive member coverage. -/
theorem OnlineMemberProofData.adaptivePreX1MembersCovered
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed) :
    AdaptiveMembersCovered vk instanceCommitment data.algebraicProof.erase
      (data.algebraicProof.preX1AssemblySource fixed) :=
  data.membersCovered

/-- The normalized adaptive member columns are exactly the executable unbatcher's columns. -/
theorem OnlineMemberProofData.adaptiveMemberRepresentations_eq_deployed
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed)
    (nu : Fin 11 → Fp) (i : Nat)
    (hi : i < deployedX4PairCount vk instanceCommitment data.algebraicProof.erase
      (chRecord nu (fun _ => 0))) :
    let adaptive := adaptiveMemberRepresentations vk instanceCommitment
      data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
      data.adaptivePreX1MembersCovered nu i hi
    let deployed := deployedMemberRepresentationsOfCovered data.toAlgebraicWfProof fixed
      data.membersCovered nu i hi
    adaptive.coeffs = deployed.coeffs ∧ adaptive.uComp = deployed.uComp ∧
      adaptive.wComp = deployed.wComp := by
  dsimp only
  have hcovered : data.adaptivePreX1MembersCovered = data.membersCovered :=
    Subsingleton.elim _ _
  rw [hcovered]
  exact ⟨rfl, rfl, rfl⟩

/-- Member coordinates are insensitive to transport of the proposition-valued coverage
certificate along an equality of representation sources. -/
theorem deployedMemberRepresentationsOfCovered_congr_source
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    (p : AlgebraicWfProof basis vk instanceCommitment)
    (fixed fixed' : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : DeployedMembersCovered vk instanceCommitment p.algebraicProof fixed)
    (hcovered' : DeployedMembersCovered vk instanceCommitment p.algebraicProof fixed')
    (nu : Fin 11 → Fp) (i : Nat)
    (hi : i < deployedX4PairCount vk instanceCommitment p.proof.1
      (chRecord nu (fun _ => 0))) (hfixed : fixed = fixed') :
    deployedMemberRepresentationsOfCovered p fixed hcovered nu i hi =
      deployedMemberRepresentationsOfCovered p fixed' hcovered' nu i hi := by
  subst fixed'
  have hc : hcovered = hcovered' := Subsingleton.elim _ _
  subst hcovered'
  rfl

/-- The exact isolated `q′` slot exposes its emitted coordinates, independent of equal points in
the member or fixed sources. -/
theorem onlinePointCoordinates_singleton
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (ap : AlgebraicPoint (F := Fp) basis) :
    onlinePointCoordinates [ap] ap.point =
      (ap.gPart, ap.coeffs AugmentedIndex.u, ap.coeffs AugmentedIndex.w) := by
  simp [onlinePointCoordinates]

/-- Proof certificates cannot change the coordinates selected from a singleton source. -/
theorem coveredCommitmentRepresentation_singleton_components
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (ap : AlgebraicPoint (F := Fp) basis)
    (hcovered : CommitmentRefCovered [ap] (.point ap.point)) :
    let represented := coveredCommitmentRepresentation [ap] (.point ap.point) hcovered
    represented.coeffs = ap.gPart ∧ represented.uComp = ap.coeffs AugmentedIndex.u ∧
      represented.wComp = ap.coeffs AugmentedIndex.w := by
  dsimp only
  have hcoords := coveredCommitmentRepresentation_point_coordinates [ap] ap.point hcovered
  rw [onlinePointCoordinates_singleton ap] at hcoords
  exact ⟨congrArg Prod.fst hcoords,
    congrArg (fun r => r.2.1) hcoords, congrArg (fun r => r.2.2) hcoords⟩

/-- Hence every adaptive `x₄` column coordinate is the exact column coordinate retained by the
executable direct unbatcher. -/
theorem OnlineMemberProofData.adaptiveX4Columns_eq_deployed
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed) (nu : Fin 11 → Fp) :
    let qCovered : CommitmentRefCovered [data.algebraicProof.multiopenQPrime]
        (.point data.algebraicProof.erase.multiopenQPrime) := ⟨_, by simp, rfl⟩
    let adaptive := adaptiveX4ColumnRepresentations vk instanceCommitment
      data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
      [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered qCovered nu
    let deployed := deployedX4ColumnRepresentationsOfCovered data.toAlgebraicWfProof fixed
      data.membersCovered nu
    adaptive.coeffs = deployed.coeffs ∧ adaptive.uComp = deployed.uComp ∧
      adaptive.wComp = deployed.wComp := by
  dsimp only
  have hcovered : data.adaptivePreX1MembersCovered = data.membersCovered :=
    Subsingleton.elim _ _
  rw [hcovered]
  constructor
  · funext j
    unfold adaptiveX4ColumnRepresentations adaptiveX4ColumnCoeffs
      deployedX4ColumnRepresentationsOfCovered
    simp only [OnlineMemberProofData.toAlgebraicWfProof_proof_fst,
      OnlineMemberProofData.toAlgebraicWfProof_algebraicProof]
    by_cases hj : (j : Nat) < deployedX4PairCount vk instanceCommitment
        data.algebraicProof.erase (chRecord nu (fun _ => 0))
    · simp only [dif_pos hj]
      rw [(data.adaptiveMemberRepresentations_eq_deployed nu
        (x4ColumnSetIndex vk instanceCommitment data.algebraicProof.erase
          (chRecord nu (fun _ => 0)) (j : Nat)) _).1]
      simp only [chRecord]
      congr 1
    · simp only [dif_neg hj]
      exact congrArg Prod.fst
        (onlinePointCoordinates_singleton data.algebraicProof.multiopenQPrime)
  · constructor
    · funext j
      unfold adaptiveX4ColumnRepresentations adaptiveX4ColumnUComp
        deployedX4ColumnRepresentationsOfCovered
      simp only [OnlineMemberProofData.toAlgebraicWfProof_proof_fst,
        OnlineMemberProofData.toAlgebraicWfProof_algebraicProof]
      by_cases hj : (j : Nat) < deployedX4PairCount vk instanceCommitment
          data.algebraicProof.erase (chRecord nu (fun _ => 0))
      · simp only [dif_pos hj]
        rw [(data.adaptiveMemberRepresentations_eq_deployed nu
          (x4ColumnSetIndex vk instanceCommitment data.algebraicProof.erase
            (chRecord nu (fun _ => 0)) (j : Nat)) _).2.1]
        simp only [chRecord]
        congr 1
      · simp only [dif_neg hj]
        exact congrArg (fun r => r.2.1)
          (onlinePointCoordinates_singleton data.algebraicProof.multiopenQPrime)
    · funext j
      unfold adaptiveX4ColumnRepresentations adaptiveX4ColumnWComp
        deployedX4ColumnRepresentationsOfCovered
      simp only [OnlineMemberProofData.toAlgebraicWfProof_proof_fst,
        OnlineMemberProofData.toAlgebraicWfProof_algebraicProof]
      by_cases hj : (j : Nat) < deployedX4PairCount vk instanceCommitment
          data.algebraicProof.erase (chRecord nu (fun _ => 0))
      · simp only [dif_pos hj]
        rw [(data.adaptiveMemberRepresentations_eq_deployed nu
          (x4ColumnSetIndex vk instanceCommitment data.algebraicProof.erase
            (chRecord nu (fun _ => 0)) (j : Nat)) _).2.2]
        simp only [chRecord]
        congr 1
      · simp only [dif_neg hj]
        exact congrArg (fun r => r.2.2)
          (onlinePointCoordinates_singleton data.algebraicProof.multiopenQPrime)

/-- The adaptive `x₄` surface is the deployed decoder's `x₄` surface once the executable
unbatcher's retained columns are identified with their online source. -/
theorem OnlineMemberProofData.adaptiveX4RootSet_eq_deployed
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed) (nu : Fin 11 → Fp)
    (qCovered : CommitmentRefCovered [data.algebraicProof.multiopenQPrime]
      (.point data.algebraicProof.erase.multiopenQPrime))
    {aggregate : Fin (2 ^ shape.k) → Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches (ursOfAugmentedBasis shape.k basis) rfl
      vk instanceCommitment data.algebraicProof.erase (chRecord nu (fun _ => 0))
      aggregate aggregateU aggregateW)
    (hcoeffs : batches.x4.coeffs =
      (adaptiveX4ColumnRepresentations vk instanceCommitment data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered qCovered nu).coeffs) :
    adaptiveX4RootSet vk instanceCommitment data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered qCovered nu =
      deployedX4RootSet (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment
        data.algebraicProof.erase (chRecord nu (fun _ => 0)) batches := by
  have hbatch : (adaptiveX4Batch vk instanceCommitment data.algebraicProof.erase
      (data.algebraicProof.preX1AssemblySource fixed)
      [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered qCovered nu).coeffs =
      batches.x4.coeffs := by
    simpa only [adaptiveX4Batch, AlgebraicColumnRepresentations.toDirectPowerBatch] using
      hcoeffs.symm
  unfold adaptiveX4RootSet deployedX4RootSet
  rw [hbatch]
  rfl

/-- The same retained-column equality identifies the adaptive and deployed `x₃` surfaces. -/
theorem OnlineMemberProofData.adaptiveX3RootSet_eq_deployed
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed) (nu : Fin 11 → Fp)
    (qCovered : CommitmentRefCovered [data.algebraicProof.multiopenQPrime]
      (.point data.algebraicProof.erase.multiopenQPrime))
    {aggregate : Fin (2 ^ shape.k) → Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches (ursOfAugmentedBasis shape.k basis) rfl
      vk instanceCommitment data.algebraicProof.erase (chRecord nu (fun _ => 0))
      aggregate aggregateU aggregateW)
    (hcoeffs : batches.x4.coeffs =
      (adaptiveX4ColumnRepresentations vk instanceCommitment data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered qCovered nu).coeffs) :
    adaptiveX3RootSet vk instanceCommitment data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered qCovered nu =
      deployedX3RootSet (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment
        data.algebraicProof.erase (chRecord nu (fun _ => 0)) batches := by
  have hbatch : (adaptiveX4Batch vk instanceCommitment data.algebraicProof.erase
      (data.algebraicProof.preX1AssemblySource fixed)
      [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered qCovered nu).coeffs =
      batches.x4.coeffs := by
    simpa only [adaptiveX4Batch, AlgebraicColumnRepresentations.toDirectPowerBatch] using
      hcoeffs.symm
  unfold adaptiveX3RootSet deployedX3RootSet
  dsimp only
  unfold deployedX3ErrorPolynomial deployedAlgebraicSetColumns deployedAlgebraicQPrime
  rw [hbatch]

/-- One adaptive set column is the corresponding retained `x₄` column. -/
theorem OnlineMemberProofData.adaptiveSetColumn_eq_deployed
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed) (nu : Fin 11 → Fp)
    (qCovered : CommitmentRefCovered [data.algebraicProof.multiopenQPrime]
      (.point data.algebraicProof.erase.multiopenQPrime))
    {aggregate : Fin (2 ^ shape.k) → Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches (ursOfAugmentedBasis shape.k basis) rfl
      vk instanceCommitment data.algebraicProof.erase (chRecord nu (fun _ => 0))
      aggregate aggregateU aggregateW)
    (hcoeffs : batches.x4.coeffs =
      (adaptiveX4ColumnRepresentations vk instanceCommitment data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered qCovered nu).coeffs)
    (j : Fin (deployedX4PairCount vk instanceCommitment data.algebraicProof.erase
      (chRecord nu (fun _ => 0)))) :
    adaptiveSetColumn vk instanceCommitment data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource fixed)
        data.adaptivePreX1MembersCovered nu j =
      deployedAlgebraicSetColumns (ursOfAugmentedBasis shape.k basis) rfl vk
        instanceCommitment data.algebraicProof.erase (chRecord nu (fun _ => 0))
        batches.x4 j := by
  have hj : (j : Nat) < deployedX4PairCount vk instanceCommitment
      data.algebraicProof.erase (chRecord nu (fun _ => 0)) := j.isLt
  have hc := congrFun hcoeffs ⟨(j : Nat), Nat.lt_succ_of_lt hj⟩
  unfold adaptiveX4ColumnRepresentations adaptiveX4ColumnCoeffs at hc
  simp only [dif_pos hj] at hc
  unfold adaptiveSetColumn deployedAlgebraicSetColumns
  dsimp only
  apply congrArg coeffsToPoly
  simpa only [x4ColumnSetIndex, chRecord] using hc.symm

/-- Consequently the adaptive and deployed `x₂` node-binding unions coincide. -/
theorem OnlineMemberProofData.adaptiveX2RootSet_eq_deployed
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed) (nu : Fin 11 → Fp)
    (qCovered : CommitmentRefCovered [data.algebraicProof.multiopenQPrime]
      (.point data.algebraicProof.erase.multiopenQPrime))
    {aggregate : Fin (2 ^ shape.k) → Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches (ursOfAugmentedBasis shape.k basis) rfl
      vk instanceCommitment data.algebraicProof.erase (chRecord nu (fun _ => 0))
      aggregate aggregateU aggregateW)
    (hcoeffs : batches.x4.coeffs =
      (adaptiveX4ColumnRepresentations vk instanceCommitment data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered qCovered nu).coeffs) :
    adaptiveX2RootSet vk instanceCommitment data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource fixed)
        data.adaptivePreX1MembersCovered nu =
      deployedX2RootSet (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment
        data.algebraicProof.erase (chRecord nu (fun _ => 0)) batches := by
  have hcolumns : (fun j => adaptiveSetColumn vk instanceCommitment
      data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
      data.adaptivePreX1MembersCovered nu j) =
      deployedAlgebraicSetColumns (ursOfAugmentedBasis shape.k basis) rfl vk
        instanceCommitment data.algebraicProof.erase (chRecord nu (fun _ => 0))
        batches.x4 := by
    funext j
    exact data.adaptiveSetColumn_eq_deployed nu qCovered batches hcoeffs j
  unfold adaptiveX2RootSet deployedX2RootSet
  dsimp only
  rw [hcolumns]

/-- Retained per-set member columns identify each adaptive and deployed `x₁` polynomial. -/
theorem OnlineMemberProofData.adaptiveX1RootPolynomial_eq_deployed
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed) (nu : Fin 11 → Fp)
    {aggregate : Fin (2 ^ shape.k) → Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches (ursOfAugmentedBasis shape.k basis) rfl
      vk instanceCommitment data.algebraicProof.erase (chRecord nu (fun _ => 0))
      aggregate aggregateU aggregateW)
    (hmembers : ∀ i
      (hi : i < deployedX4PairCount vk instanceCommitment data.algebraicProof.erase
        (chRecord nu (fun _ => 0))),
      (batches.x1 i hi).coeffs =
        (adaptiveMemberRepresentations vk instanceCommitment data.algebraicProof.erase
          (data.algebraicProof.preX1AssemblySource fixed)
          data.adaptivePreX1MembersCovered nu i hi).coeffs)
    (i : Nat) (hi : i < deployedX4PairCount vk instanceCommitment
      data.algebraicProof.erase (chRecord nu (fun _ => 0)))
    (idx : Fin ((deployedSetsForEval vk instanceCommitment data.algebraicProof.erase
      (chRecord nu (fun _ => 0))).getD i ([], [], 0)).1.length) :
    adaptiveX1RootPolynomial vk instanceCommitment data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource fixed)
        data.adaptivePreX1MembersCovered nu i hi idx =
      deployedX1RootPolynomial (ursOfAugmentedBasis shape.k basis) rfl vk
        instanceCommitment data.algebraicProof.erase (chRecord nu (fun _ => 0))
        batches i hi idx := by
  have hbatch : (adaptiveX1Batch vk instanceCommitment data.algebraicProof.erase
      (data.algebraicProof.preX1AssemblySource fixed)
      data.adaptivePreX1MembersCovered nu i hi).coeffs = (batches.x1 i hi).coeffs := by
    simpa only [adaptiveX1Batch, AlgebraicColumnRepresentations.toDirectPowerBatch] using
      (hmembers i hi).symm
  unfold adaptiveX1RootPolynomial deployedX1RootPolynomial
  rw [hbatch]

/-- The union over all `x₁` point sets therefore coincides as well. -/
theorem OnlineMemberProofData.adaptiveX1AllRootSet_eq_deployed
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed) (nu : Fin 11 → Fp)
    {aggregate : Fin (2 ^ shape.k) → Fp} {aggregateU aggregateW : Fp}
    (batches : DeployedAlgebraicBatches (ursOfAugmentedBasis shape.k basis) rfl
      vk instanceCommitment data.algebraicProof.erase (chRecord nu (fun _ => 0))
      aggregate aggregateU aggregateW)
    (hmembers : ∀ i
      (hi : i < deployedX4PairCount vk instanceCommitment data.algebraicProof.erase
        (chRecord nu (fun _ => 0))),
      (batches.x1 i hi).coeffs =
        (adaptiveMemberRepresentations vk instanceCommitment data.algebraicProof.erase
          (data.algebraicProof.preX1AssemblySource fixed)
          data.adaptivePreX1MembersCovered nu i hi).coeffs) :
    adaptiveX1AllRootSet vk instanceCommitment data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource fixed)
        data.adaptivePreX1MembersCovered nu =
      deployedX1AllRootSet (ursOfAugmentedBasis shape.k basis) rfl vk
        instanceCommitment data.algebraicProof.erase (chRecord nu (fun _ => 0)) batches := by
  apply Set.ext
  intro x
  simp only [adaptiveX1AllRootSet, deployedX1AllRootSet, Set.mem_setOf_eq]
  apply exists_congr
  intro i
  unfold adaptiveX1RootSet deployedX1RootSet
  by_cases hi : (i : Nat) < deployedX4PairCount vk instanceCommitment
      data.algebraicProof.erase (chRecord nu (fun _ => 0))
  · simp only [dif_pos hi, Set.mem_setOf_eq]
    apply exists_congr
    intro idx
    rw [data.adaptiveX1RootPolynomial_eq_deployed nu batches hmembers (i : Nat) hi idx]
  · simp only [dif_neg hi, Set.mem_empty_iff_false]

/-- The adaptive column fold is the executable unbatcher's aggregate. -/
theorem OnlineMemberProofData.adaptiveAggregates_eq
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed) (nu : Fin 11 → Fp)
    (qCovered : CommitmentRefCovered [data.algebraicProof.multiopenQPrime]
      (.point data.algebraicProof.erase.multiopenQPrime))
    {aggregate : Fin (2 ^ shape.k) → Fp} {aggregateU aggregateW : Fp}
    (batch : AlgebraicPowerBatch (ursOfAugmentedBasis shape.k basis)
      (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment
        data.algebraicProof.erase (chRecord nu (fun _ => 0)))
      aggregate aggregateU aggregateW (nu 8))
    (_hcoeffs : batch.coeffs =
      (adaptiveX4ColumnRepresentations vk instanceCommitment data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered qCovered nu).coeffs)
    (_hu : batch.uComp =
      (adaptiveX4ColumnRepresentations vk instanceCommitment data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered qCovered nu).uComp)
    (haggregate : adaptiveAggregateG vk instanceCommitment data.algebraicProof.erase
      (data.algebraicProof.preX1AssemblySource fixed)
      [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered qCovered nu =
      aggregate)
    (haggregateU : adaptiveAggregateU vk instanceCommitment data.algebraicProof.erase
      (data.algebraicProof.preX1AssemblySource fixed)
      [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered qCovered nu =
      aggregateU) :
    adaptiveAggregateG vk instanceCommitment data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered qCovered nu =
        aggregate ∧
      adaptiveAggregateU vk instanceCommitment data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered qCovered nu =
        aggregateU := ⟨haggregate, haggregateU⟩

/-- The two adaptive shift surfaces use exactly the aggregate and `S` coordinates retained by
the executable route. -/
theorem OnlineMemberProofData.adaptiveShiftRootSets_eq
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := vk) (instanceCommitment := instanceCommitment)
      basis fixed) (nu : Fin 11 → Fp)
    (qCovered : CommitmentRefCovered [data.algebraicProof.multiopenQPrime]
      (.point data.algebraicProof.erase.multiopenQPrime))
    (sCovered : CommitmentRefCovered [data.algebraicProof.ipaS]
      (.point data.algebraicProof.erase.ipaS))
    {aggregate : Fin (2 ^ shape.k) → Fp} {aggregateU aggregateW : Fp}
    (batch : AlgebraicPowerBatch (ursOfAugmentedBasis shape.k basis)
      (x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vk instanceCommitment
        data.algebraicProof.erase (chRecord nu (fun _ => 0)))
      aggregate aggregateU aggregateW (nu 8))
    (hcoeffs : batch.coeffs =
      (adaptiveX4ColumnRepresentations vk instanceCommitment data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered qCovered nu).coeffs)
    (hu : batch.uComp =
      (adaptiveX4ColumnRepresentations vk instanceCommitment data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered qCovered nu).uComp)
    (haggregate : adaptiveAggregateG vk instanceCommitment data.algebraicProof.erase
      (data.algebraicProof.preX1AssemblySource fixed)
      [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered qCovered nu =
      aggregate)
    (haggregateU : adaptiveAggregateU vk instanceCommitment data.algebraicProof.erase
      (data.algebraicProof.preX1AssemblySource fixed)
      [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered qCovered nu =
      aggregateU) :
    adaptiveXiRootSet vk instanceCommitment data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] [data.algebraicProof.ipaS]
        data.adaptivePreX1MembersCovered qCovered sCovered nu =
      szBadSet (ipaShiftXiPolynomial
        (commitGen (evalVector shape.k (nu 7)) aggregate -
          multiopenValue vk instanceCommitment data.algebraicProof.erase
            (chRecord nu (fun _ => 0)))
        (commitGen (evalVector shape.k (nu 7)) data.algebraicProof.ipaS.gPart)) ∧
    adaptiveZRootSet vk instanceCommitment data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] [data.algebraicProof.ipaS]
        data.adaptivePreX1MembersCovered qCovered sCovered nu =
      szBadSet (ipaShiftZPolynomial
        (commitGen (evalVector shape.k (nu 7)) aggregate -
          multiopenValue vk instanceCommitment data.algebraicProof.erase
            (chRecord nu (fun _ => 0)))
        aggregateU (data.algebraicProof.ipaS.coeffs AugmentedIndex.u)
        (commitGen (evalVector shape.k (nu 7)) data.algebraicProof.ipaS.gPart) (nu 9)) := by
  have hag := data.adaptiveAggregates_eq nu qCovered batch hcoeffs hu
    haggregate haggregateU
  have hs := coveredCommitmentRepresentation_singleton_components
    data.algebraicProof.ipaS sCovered
  have hscoeff : (coveredCommitmentRepresentation [data.algebraicProof.ipaS]
      (.point data.algebraicProof.erase.ipaS) sCovered).coeffs =
      data.algebraicProof.ipaS.gPart := hs.1
  have hsu : (coveredCommitmentRepresentation [data.algebraicProof.ipaS]
      (.point data.algebraicProof.erase.ipaS) sCovered).uComp =
      data.algebraicProof.ipaS.coeffs AugmentedIndex.u := hs.2.1
  constructor
  · unfold adaptiveXiRootSet
    rw [hag.1]
    dsimp only
    rw [hscoeff]
    rfl
  · unfold adaptiveZRootSet
    rw [hag.1, hag.2]
    dsimp only
    rw [hscoeff, hsu]
    rfl

/-! ## Bare-family runtime normalization -/

@[simp] theorem ComputedAdaptiveOnlineAGMFSFamily.toFamily_runProof
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    runProof family.toFamily basis O = ((family.adversary basis).run O).toAlgebraicWfProof := by
  change (((family.adversary basis).erase.bind fun data =>
    .pure data.toAlgebraicWfProof).run O) = _
  simp only [OracleComp.run_bind, OracleComp.run_pure, LabeledOracleComp.run]

@[simp] theorem ComputedAdaptiveOnlineAGMFSFamily.toFamily_runReads
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    runReads family.toFamily basis O = fun n => O (algebraicFullPrefixesPre family.init
      ((family.adversary basis).run O).toAlgebraicWfProof n) := by
  funext n
  simp only [runReads, family.toFamily_runProof]
  rfl

theorem ComputedAdaptiveOnlineAGMFSFamily.toFamily_wrappedAdversary_run
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    (wrappedAdversary family.toFamily basis).run O =
      (((family.adversary basis).run O).toAlgebraicWfProof,
        fun i => O (Fin.append
          (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O).toAlgebraicWfProof)
          (algebraicFullPrefixes family.init
            ((family.adversary basis).run O).toAlgebraicWfProof) i)) := by
  simp only [wrappedAdversary, OracleComp.run_withReads]
  apply Prod.ext
  · exact family.toFamily_runProof basis O
  · funext i
    change O (Fin.append (algebraicFullPrefixesPre family.toFamily.init
      (runProof family.toFamily basis O))
      (algebraicFullPrefixes family.toFamily.init (runProof family.toFamily basis O)) i) = _
    rw [family.toFamily_runProof]
    rfl

/-- Truncating an actual deployed squeeze point to an earlier squeeze length recovers that
earlier verifier point. -/
theorem adaptiveEarlierPrefix_algebraicFullPrefixesPre
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    (init : List (TranscriptElt Fp VestaG))
    (p : AlgebraicWfProof basis vk instanceCommitment) (n : Fin 11)
    (i : Fin (n : Nat)) :
    adaptiveEarlierPrefix (shape := shape) init (algebraicFullPrefixesPre init p n)
        (i.castLE (le_of_lt n.isLt)) =
      algebraicFullPrefixesPre init p (i.castLE (le_of_lt n.isLt)) := by
  apply Subtype.ext
  have hp := preIpaSqueezePoints_prefix_of_le init p.algebraicProof.erase p.wellFormed
    (i.castLE (le_of_lt n.isLt)) n (Nat.le_of_lt i.isLt)
  have htake := List.prefix_iff_eq_take.mp hp
  rw [preIpaSqueezePoints_length_eq init p.algebraicProof.erase p.wellFormed] at htake
  exact htake.symm

/-- Therefore the earlier-answer vector used by the adaptive surface is the actual verifier
answer vector, truncated strictly before the current squeeze. -/
theorem adaptiveEarlierRecord_actual
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    (init : List (TranscriptElt Fp VestaG))
    (p : AlgebraicWfProof basis vk instanceCommitment) (n : Fin 11)
    (O : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k) → Fp) :
    adaptiveEarlierRecord n (fun i => O (adaptiveEarlierPrefix (shape := shape) init
      (algebraicFullPrefixesPre init p n) (i.castLE (le_of_lt n.isLt)))) =
      fun i : Fin 11 => if _h : (i : Nat) < (n : Nat) then
        O (algebraicFullPrefixesPre init p i) else 0 := by
  funext i
  unfold adaptiveEarlierRecord
  split
  · rename_i h
    simpa using congrArg O (adaptiveEarlierPrefix_algebraicFullPrefixesPre
      init p n ⟨i, h⟩)
  · rfl

set_option maxHeartbeats 600000 in
/-- The generated outcome reconstructs the actual canonical aggregate from the normalized
adaptive columns. -/
theorem ComputedAdaptiveOnlineAGMFSFamily.adaptiveWitnessAggregates
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (witness : DeployedBatchWitness family.toFamily basis
      ((wrappedAdversary family.toFamily basis).run O))
    (hout : deployedRootOutcomeOfCovered family.toOnlineMemberFamily basis O =
      PSum.inl witness) :
    let data := (family.adversary basis).run O
    let nu : Fin 11 → Fp := fun n =>
      O (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof n)
    let qCovered : CommitmentRefCovered [data.algebraicProof.multiopenQPrime]
        (.point data.algebraicProof.erase.multiopenQPrime) := ⟨_, by simp, rfl⟩
    adaptiveAggregateG (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered qCovered nu =
        data.toAlgebraicWfProof.aMulti nu ∧
      adaptiveAggregateU (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered qCovered nu =
        data.toAlgebraicWfProof.multiU nu := by
  dsimp only
  let data := (family.adversary basis).run O
  let nu : Fin 11 → Fp := fun n =>
    O (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof n)
  have hsource := deployedRootOutcomeOfCovered_x4Source family.toOnlineMemberFamily
    basis O witness hout
  have hp : runProof family.toOnlineMemberFamily.toFamily basis O =
      data.toAlgebraicWfProof := family.toFamily_runProof basis O
  have hreads : runReads family.toOnlineMemberFamily.toFamily basis O = nu := by
    simpa only [data, nu] using family.toFamily_runReads basis O
  have hsourceData : HEq witness.x4Source
      (deployedX4ColumnRepresentationsOfCovered data.toAlgebraicWfProof
        (family.fixedRepresentations basis) data.membersCovered nu) :=
    HEq.trans hsource
      (deployedX4ColumnRepresentationsOfCovered_heq _ _ _ _ _ _ _ hp hreads)
  have hpnu : ((wrappedAdversary family.toFamily basis).run O).1 =
      data.toAlgebraicWfProof :=
    (wrappedAdversary_run_fst family.toFamily basis O).trans hp
  have hnupnu : wrappedPreIpaReads ((wrappedAdversary family.toFamily basis).run O) = nu :=
    (wrappedPreIpaReads_run family.toFamily basis O).trans hreads
  have hrec := witness.x4CoveredSource_reconstruct data.toAlgebraicWfProof
    (family.fixedRepresentations basis) data.membersCovered nu hpnu hnupnu hsourceData
  have hcols := data.adaptiveX4Columns_eq_deployed nu
  constructor
  · unfold adaptiveAggregateG
    dsimp only
    rw [hcols.1]
    exact hrec.1
  · unfold adaptiveAggregateU
    dsimp only
    rw [hcols.2.1]
    exact hrec.2

private theorem assembleQueries_prefix5
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (nu : Fin 11 → Fp) :
    assembleQueries vk instanceCommitment (adaptiveRootPrefixProof 5 ps)
        (chRecord nu (fun _ => 0)) =
      assembleQueries vk instanceCommitment ps (chRecord nu (fun _ => 0)) := by
  rfl

private theorem deployedX4PairCount_prefix5
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (nu : Fin 11 → Fp) :
    deployedX4PairCount vk instanceCommitment (adaptiveRootPrefixProof 5 ps)
        (chRecord nu (fun _ => 0)) =
      deployedX4PairCount vk instanceCommitment ps (chRecord nu (fun _ => 0)) := by
  unfold deployedX4PairCount deployedX4Pairs deployedX4Qs
  simp only [List.length_zip, List.length_map, List.length_ofFn]
  rw [assembleQueries_prefix5]

private theorem deployedSetQueries_prefix5
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (nu : Fin 11 → Fp) (i : Nat) :
    deployedSetQueries vk instanceCommitment (adaptiveRootPrefixProof 5 ps)
        (chRecord nu (fun _ => 0)) i =
      deployedSetQueries vk instanceCommitment ps (chRecord nu (fun _ => 0)) i := by
  rfl

private theorem adaptiveMemberRepresentations_prefix5
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hprefix : AdaptiveMembersCovered vk instanceCommitment
      (adaptiveRootPrefixProof 5 ps) source)
    (hfull : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp) (i : Nat)
    (hi : i < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0))) :
    let hiPrefix : i < deployedX4PairCount vk instanceCommitment
        (adaptiveRootPrefixProof 5 ps) (chRecord nu (fun _ => 0)) := by
      rwa [deployedX4PairCount_prefix5]
    (adaptiveMemberRepresentations vk instanceCommitment
        (adaptiveRootPrefixProof 5 ps) source hprefix nu i hiPrefix).coeffs =
      (adaptiveMemberRepresentations vk instanceCommitment ps source hfull nu i hi).coeffs := by
  dsimp only
  have hqueries := deployedSetQueries_prefix5 vk instanceCommitment ps nu i
  cases hqueries
  rfl

private theorem deployedSetsForEval_getD_points_prefix5
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (nu : Fin 11 → Fp) (i : Nat)
    (hi : i < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0))) :
    let _hiPrefix : i < deployedX4PairCount vk instanceCommitment
        (adaptiveRootPrefixProof 5 ps) (chRecord nu (fun _ => 0)) := by
      rwa [deployedX4PairCount_prefix5]
    ((deployedSetsForEval vk instanceCommitment (adaptiveRootPrefixProof 5 ps)
        (chRecord nu (fun _ => 0))).getD i ([], [], 0)).1 =
      ((deployedSetsForEval vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).getD i ([], [], 0)).1 := by
  dsimp only
  rw [deployedSetsForEval_getD_points vk instanceCommitment
      (adaptiveRootPrefixProof 5 ps) (chRecord nu (fun _ => 0)) (by
        rwa [deployedX4PairCount_prefix5]),
    deployedSetsForEval_getD_points vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) hi, assembleQueries_prefix5]

private theorem deployedSetsForEval_getD_evals_prefix5
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (nu : Fin 11 → Fp) (i : Nat)
    (hi : i < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0))) :
    let _hiPrefix : i < deployedX4PairCount vk instanceCommitment
        (adaptiveRootPrefixProof 5 ps) (chRecord nu (fun _ => 0)) := by
      rwa [deployedX4PairCount_prefix5]
    ((deployedSetsForEval vk instanceCommitment (adaptiveRootPrefixProof 5 ps)
        (chRecord nu (fun _ => 0))).getD i ([], [], 0)).2.1 =
      ((deployedSetsForEval vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).getD i ([], [], 0)).2.1 := by
  dsimp only
  rw [deployedSetsForEval_getD_evals vk instanceCommitment
      (adaptiveRootPrefixProof 5 ps) (chRecord nu (fun _ => 0)) (by
        rwa [deployedX4PairCount_prefix5]),
    deployedSetsForEval_getD_evals vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) hi, assembleQueries_prefix5,
    deployedSetQueries_prefix5]

private theorem adaptiveX1RootPolynomial_prefix5
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hprefix : AdaptiveMembersCovered vk instanceCommitment
      (adaptiveRootPrefixProof 5 ps) source)
    (hfull : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp) (i : Nat)
    (hi : i < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0)))
    (idx : Fin ((deployedSetsForEval vk instanceCommitment ps
      (chRecord nu (fun _ => 0))).getD i ([], [], 0)).1.length) :
    let hiPrefix : i < deployedX4PairCount vk instanceCommitment
        (adaptiveRootPrefixProof 5 ps) (chRecord nu (fun _ => 0)) := by
      rwa [deployedX4PairCount_prefix5]
    let idxPrefix : Fin ((deployedSetsForEval vk instanceCommitment
        (adaptiveRootPrefixProof 5 ps) (chRecord nu (fun _ => 0))).getD
          i ([], [], 0)).1.length :=
      ⟨idx, by rw [deployedSetsForEval_getD_points_prefix5
        vk instanceCommitment ps nu i hi]; exact idx.isLt⟩
    adaptiveX1RootPolynomial vk instanceCommitment (adaptiveRootPrefixProof 5 ps)
        source hprefix nu i hiPrefix idxPrefix =
      adaptiveX1RootPolynomial vk instanceCommitment ps source hfull nu i hi idx := by
  dsimp only
  have hmembers := adaptiveMemberRepresentations_prefix5 vk instanceCommitment ps
    source hprefix hfull nu i hi
  have hqueries := deployedSetQueries_prefix5 vk instanceCommitment ps nu i
  cases hqueries
  have hpoints := deployedSetsForEval_getD_points_prefix5
    vk instanceCommitment ps nu i hi
  let idxPrefix : Fin ((deployedSetsForEval vk instanceCommitment
      (adaptiveRootPrefixProof 5 ps) (chRecord nu (fun _ => 0))).getD
        i ([], [], 0)).1.length :=
    ⟨idx, by rw [hpoints]; exact idx.isLt⟩
  have hnode :
      ((deployedSetsForEval vk instanceCommitment (adaptiveRootPrefixProof 5 ps)
          (chRecord nu (fun _ => 0))).getD i ([], [], 0)).1[
            idxPrefix] =
        ((deployedSetsForEval vk instanceCommitment ps
          (chRecord nu (fun _ => 0))).getD i ([], [], 0)).1[idx] := by
    exact getElem_congr hpoints rfl _
  unfold adaptiveX1RootPolynomial
  rw [show (adaptiveX1Batch vk instanceCommitment (adaptiveRootPrefixProof 5 ps)
        source hprefix nu i _).coeffs =
      (adaptiveX1Batch vk instanceCommitment ps source hfull nu i hi).coeffs by
    simpa only [adaptiveX1Batch, AlgebraicColumnRepresentations.toDirectPowerBatch]
      using hmembers, hnode]
  simp only [deployedSetQueries_prefix5]
  rfl

private theorem adaptiveX1AllRootSet_prefix5
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hprefix : AdaptiveMembersCovered vk instanceCommitment
      (adaptiveRootPrefixProof 5 ps) source)
    (hfull : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp) :
    adaptiveX1AllRootSet vk instanceCommitment (adaptiveRootPrefixProof 5 ps)
        source hprefix nu =
      adaptiveX1AllRootSet vk instanceCommitment ps source hfull nu := by
  ext x
  simp only [adaptiveX1AllRootSet, Set.mem_setOf_eq]
  apply exists_congr
  intro i
  unfold adaptiveX1RootSet
  by_cases hiPrefix : (i : Nat) < deployedX4PairCount vk instanceCommitment
      (adaptiveRootPrefixProof 5 ps) (chRecord nu (fun _ => 0))
  · have hi : (i : Nat) < deployedX4PairCount vk instanceCommitment ps
        (chRecord nu (fun _ => 0)) := by
      rwa [← deployedX4PairCount_prefix5]
    simp only [dif_pos hiPrefix, dif_pos hi, Set.mem_setOf_eq]
    have hpoints := deployedSetsForEval_getD_points_prefix5
      vk instanceCommitment ps nu i hi
    constructor
    · rintro ⟨idx, _, hx⟩
      let idxFull : Fin ((deployedSetsForEval vk instanceCommitment ps
          (chRecord nu (fun _ => 0))).getD i ([], [], 0)).1.length :=
        ⟨idx, by rw [← hpoints]; exact idx.isLt⟩
      have hpoly := adaptiveX1RootPolynomial_prefix5 vk instanceCommitment ps source
        hprefix hfull nu i hi idxFull
      refine ⟨idxFull, Finset.mem_univ _, ?_⟩
      rwa [← hpoly]
    · rintro ⟨idx, _, hx⟩
      let idxPrefix : Fin ((deployedSetsForEval vk instanceCommitment
          (adaptiveRootPrefixProof 5 ps) (chRecord nu (fun _ => 0))).getD
            i ([], [], 0)).1.length :=
        ⟨idx, by rw [hpoints]; exact idx.isLt⟩
      have hpoly := adaptiveX1RootPolynomial_prefix5 vk instanceCommitment ps source
        hprefix hfull nu i hi idx
      refine ⟨idxPrefix, Finset.mem_univ _, ?_⟩
      rwa [hpoly]
  · have hi : ¬ (i : Nat) < deployedX4PairCount vk instanceCommitment ps
        (chRecord nu (fun _ => 0)) := by
      rwa [← deployedX4PairCount_prefix5]
    simp only [dif_neg hiPrefix, dif_neg hi, Set.mem_empty_iff_false]

attribute [local irreducible] adaptiveSetColumn

private theorem deployedX4PairCount_prefix6
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (nu : Fin 11 → Fp) :
    deployedX4PairCount vk instanceCommitment (adaptiveRootPrefixProof 6 ps)
        (chRecord nu (fun _ => 0)) =
      deployedX4PairCount vk instanceCommitment ps (chRecord nu (fun _ => 0)) := by
  simpa only [adaptiveRootPrefixProof] using
    deployedX4PairCount_prefix5 vk instanceCommitment ps nu

private theorem deployedSetQueries_prefix6
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (nu : Fin 11 → Fp) (i : Nat) :
    deployedSetQueries vk instanceCommitment (adaptiveRootPrefixProof 6 ps)
        (chRecord nu (fun _ => 0)) i =
      deployedSetQueries vk instanceCommitment ps (chRecord nu (fun _ => 0)) i := by
  simpa only [adaptiveRootPrefixProof] using
    deployedSetQueries_prefix5 vk instanceCommitment ps nu i

private theorem adaptiveMemberRepresentations_prefix6
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hprefix : AdaptiveMembersCovered vk instanceCommitment
      (adaptiveRootPrefixProof 6 ps) source)
    (hfull : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp) (i : Nat)
    (hi : i < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0))) :
    let hiPrefix : i < deployedX4PairCount vk instanceCommitment
        (adaptiveRootPrefixProof 6 ps) (chRecord nu (fun _ => 0)) := by
      rwa [deployedX4PairCount_prefix6]
    (adaptiveMemberRepresentations vk instanceCommitment
        (adaptiveRootPrefixProof 6 ps) source hprefix nu i hiPrefix).coeffs =
      (adaptiveMemberRepresentations vk instanceCommitment ps source hfull nu i hi).coeffs := by
  simpa only [adaptiveRootPrefixProof] using
    adaptiveMemberRepresentations_prefix5 vk instanceCommitment ps source
      hprefix hfull nu i hi

private theorem adaptiveMemberRepresentations_coeffs_heq_index
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp) (i j : Nat)
    (hi : i < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0)))
    (hj : j < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0))) (hij : i = j) :
    HEq (adaptiveMemberRepresentations vk instanceCommitment ps source hcovered
        nu i hi).coeffs
      (adaptiveMemberRepresentations vk instanceCommitment ps source hcovered
        nu j hj).coeffs := by
  subst j
  rfl

private theorem adaptiveMemberRepresentations_powerSum_eq_index
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp) (x : Fp) (i j : Nat)
    (hi : i < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0)))
    (hj : j < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0))) (hij : i = j) :
    (∑ m : Fin (deployedSetQueries vk instanceCommitment ps
        (chRecord nu (fun _ => 0)) i).length, x ^ (m : Nat) •
        (adaptiveMemberRepresentations vk instanceCommitment ps source hcovered
          nu i hi).coeffs m) =
      ∑ m : Fin (deployedSetQueries vk instanceCommitment ps
        (chRecord nu (fun _ => 0)) j).length, x ^ (m : Nat) •
        (adaptiveMemberRepresentations vk instanceCommitment ps source hcovered
          nu j hj).coeffs m := by
  subst j
  rfl

private theorem adaptiveSetColumn_prefix6_at
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hprefix : AdaptiveMembersCovered vk instanceCommitment
      (adaptiveRootPrefixProof 6 ps) source)
    (hfull : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp)
    (j : Fin (deployedX4PairCount vk instanceCommitment
      (adaptiveRootPrefixProof 6 ps) (chRecord nu (fun _ => 0)))) :
    adaptiveSetColumn vk instanceCommitment (adaptiveRootPrefixProof 6 ps)
        source hprefix nu j =
      adaptiveSetColumn vk instanceCommitment ps source hfull nu
        ⟨j, by
          have hc := deployedX4PairCount_prefix6 vk instanceCommitment ps nu
          omega⟩ := by
  have hcount := deployedX4PairCount_prefix6 vk instanceCommitment ps nu
  unfold adaptiveSetColumn
  dsimp only
  rw [adaptiveMemberRepresentations_prefix6 vk instanceCommitment ps source
    hprefix hfull nu _ (by omega)]
  have hindex :
      deployedX4PairCount vk instanceCommitment (adaptiveRootPrefixProof 6 ps)
          (chRecord nu (fun _ => 0)) - 1 - (j : Nat) =
        deployedX4PairCount vk instanceCommitment ps
          (chRecord nu (fun _ => 0)) - 1 - (j : Nat) := by omega
  have hiIndex :
      deployedX4PairCount vk instanceCommitment (adaptiveRootPrefixProof 6 ps)
          (chRecord nu (fun _ => 0)) - 1 - (j : Nat) <
        deployedX4PairCount vk instanceCommitment ps
          (chRecord nu (fun _ => 0)) := by omega
  have hjIndex :
      deployedX4PairCount vk instanceCommitment ps
          (chRecord nu (fun _ => 0)) - 1 - (j : Nat) <
        deployedX4PairCount vk instanceCommitment ps
          (chRecord nu (fun _ => 0)) := by omega
  exact congrArg coeffsToPoly
    (adaptiveMemberRepresentations_powerSum_eq_index vk instanceCommitment ps
      source hfull nu (nu 5) _ _ hiIndex hjIndex hindex)

private theorem adaptiveSetColumns_prefix6
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hprefix : AdaptiveMembersCovered vk instanceCommitment
      (adaptiveRootPrefixProof 6 ps) source)
    (hfull : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp) :
    HEq (fun j : Fin (deployedX4PairCount vk instanceCommitment
        (adaptiveRootPrefixProof 6 ps) (chRecord nu (fun _ => 0))) =>
        adaptiveSetColumn vk instanceCommitment
          (adaptiveRootPrefixProof 6 ps) source hprefix nu j)
      (fun j : Fin (deployedX4PairCount vk instanceCommitment ps
        (chRecord nu (fun _ => 0))) =>
        adaptiveSetColumn vk instanceCommitment ps source hfull nu j) := by
  have hcount := deployedX4PairCount_prefix6 vk instanceCommitment ps nu
  apply (Fin.heq_fun_iff hcount).mpr
  intro j
  exact adaptiveSetColumn_prefix6_at vk instanceCommitment ps source
    hprefix hfull nu j

private theorem assembleQueries_prefix6
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (nu : Fin 11 → Fp) :
    assembleQueries vk instanceCommitment (adaptiveRootPrefixProof 6 ps)
        (chRecord nu (fun _ => 0)) =
      assembleQueries vk instanceCommitment ps (chRecord nu (fun _ => 0)) := by
  simpa only [adaptiveRootPrefixProof] using
    assembleQueries_prefix5 vk instanceCommitment ps nu

private theorem deployedAllPts_prefix6
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (nu : Fin 11 → Fp) :
    deployedAllPts vk instanceCommitment (adaptiveRootPrefixProof 6 ps)
        (chRecord nu (fun _ => 0)) =
      deployedAllPts vk instanceCommitment ps (chRecord nu (fun _ => 0)) := by
  unfold deployedAllPts deployedSetPts
  rw [assembleQueries_prefix6]

private theorem deployedAlgebraicSetPoints_prefix6
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (nu : Fin 11 → Fp) :
    HEq (deployedAlgebraicSetPoints vk instanceCommitment
        (adaptiveRootPrefixProof 6 ps) (chRecord nu (fun _ => 0)))
      (deployedAlgebraicSetPoints vk instanceCommitment ps
        (chRecord nu (fun _ => 0))) := by
  have hcount := deployedX4PairCount_prefix6 vk instanceCommitment ps nu
  apply (Fin.heq_fun_iff hcount).mpr
  intro j
  unfold deployedAlgebraicSetPoints deployedSetPts
  rw [assembleQueries_prefix6]
  have hindex :
      deployedX4PairCount vk instanceCommitment (adaptiveRootPrefixProof 6 ps)
          (chRecord nu (fun _ => 0)) - 1 - (j : Nat) =
        deployedX4PairCount vk instanceCommitment ps
          (chRecord nu (fun _ => 0)) - 1 - (j : Nat) := by omega
  rw [hindex]

private theorem deployedSetsForEval_getD_evals_prefix6
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (nu : Fin 11 → Fp) (i : Nat)
    (hi : i < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0))) :
    ((deployedSetsForEval vk instanceCommitment (adaptiveRootPrefixProof 6 ps)
        (chRecord nu (fun _ => 0))).getD i ([], [], 0)).2.1 =
      ((deployedSetsForEval vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).getD i ([], [], 0)).2.1 := by
  simpa only [adaptiveRootPrefixProof] using
    deployedSetsForEval_getD_evals_prefix5 vk instanceCommitment ps nu i hi

private theorem deployedSetsForEval_reverse_getD_points_prefix6
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (nu : Fin 11 → Fp)
    (j : Fin (deployedX4PairCount vk instanceCommitment
      (adaptiveRootPrefixProof 6 ps) (chRecord nu (fun _ => 0)))) :
    ((deployedSetsForEval vk instanceCommitment (adaptiveRootPrefixProof 6 ps)
        (chRecord nu (fun _ => 0))).reverse.getD j ([], [], 0)).1 =
      ((deployedSetsForEval vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).reverse.getD j ([], [], 0)).1 := by
  have hcount := deployedX4PairCount_prefix6 vk instanceCommitment ps nu
  have hj : (j : Nat) < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) := by omega
  rw [deployedSetsForEval_reverse_getD_points vk instanceCommitment
      (adaptiveRootPrefixProof 6 ps) (chRecord nu (fun _ => 0)) j.isLt,
    deployedSetsForEval_reverse_getD_points vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) hj]
  have hindex :
      deployedX4PairCount vk instanceCommitment (adaptiveRootPrefixProof 6 ps)
          (chRecord nu (fun _ => 0)) - 1 - (j : Nat) =
        deployedX4PairCount vk instanceCommitment ps
          (chRecord nu (fun _ => 0)) - 1 - (j : Nat) := by omega
  rw [hindex, assembleQueries_prefix6]

private theorem deployedSetsForEval_reverse_getD_evals_prefix6
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (nu : Fin 11 → Fp)
    (j : Fin (deployedX4PairCount vk instanceCommitment
      (adaptiveRootPrefixProof 6 ps) (chRecord nu (fun _ => 0)))) :
    ((deployedSetsForEval vk instanceCommitment (adaptiveRootPrefixProof 6 ps)
        (chRecord nu (fun _ => 0))).reverse.getD j ([], [], 0)).2.1 =
      ((deployedSetsForEval vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).reverse.getD j ([], [], 0)).2.1 := by
  have hcount := deployedX4PairCount_prefix6 vk instanceCommitment ps nu
  have hj : (j : Nat) < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) := by omega
  have hp :
      (deployedSetsForEval vk instanceCommitment (adaptiveRootPrefixProof 6 ps)
        (chRecord nu (fun _ => 0))).reverse.getD j ([], [], 0) =
      (deployedSetsForEval vk instanceCommitment (adaptiveRootPrefixProof 6 ps)
        (chRecord nu (fun _ => 0))).getD
          (deployedX4PairCount vk instanceCommitment (adaptiveRootPrefixProof 6 ps)
            (chRecord nu (fun _ => 0)) - 1 - (j : Nat)) ([], [], 0) := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_reverse (by rw [deployedSetsForEval_length]; exact j.isLt),
      deployedSetsForEval_length]
  have hf :
      (deployedSetsForEval vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).reverse.getD j ([], [], 0) =
      (deployedSetsForEval vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).getD
          (deployedX4PairCount vk instanceCommitment ps
            (chRecord nu (fun _ => 0)) - 1 - (j : Nat)) ([], [], 0) := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_reverse (by rw [deployedSetsForEval_length]; exact hj),
      deployedSetsForEval_length]
  rw [hp, hf]
  have hindex :
      deployedX4PairCount vk instanceCommitment (adaptiveRootPrefixProof 6 ps)
          (chRecord nu (fun _ => 0)) - 1 - (j : Nat) =
        deployedX4PairCount vk instanceCommitment ps
          (chRecord nu (fun _ => 0)) - 1 - (j : Nat) := by omega
  rw [hindex]
  exact deployedSetsForEval_getD_evals_prefix6 vk instanceCommitment ps nu _ (by omega)

private theorem deployedAlgebraicSetInterpolants_prefix6
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (nu : Fin 11 → Fp) :
    HEq (deployedAlgebraicSetInterpolants vk instanceCommitment
        (adaptiveRootPrefixProof 6 ps) (chRecord nu (fun _ => 0)))
      (deployedAlgebraicSetInterpolants vk instanceCommitment ps
        (chRecord nu (fun _ => 0))) := by
  have hcount := deployedX4PairCount_prefix6 vk instanceCommitment ps nu
  apply (Fin.heq_fun_iff hcount).mpr
  intro j
  unfold deployedAlgebraicSetInterpolants
  rw [deployedSetsForEval_reverse_getD_points_prefix6
      vk instanceCommitment ps nu j,
    deployedSetsForEval_reverse_getD_evals_prefix6
      vk instanceCommitment ps nu j]

private theorem nodeBindingErrorPolynomial_congr_fin
    {n m : Nat} (hnm : n = m)
    (allPts allPts' : Finset Fp) (hall : allPts = allPts')
    (pts : Fin n → Finset Fp) (pts' : Fin m → Finset Fp)
    (col r : Fin n → CPoly) (col' r' : Fin m → CPoly)
    (hpts : ∀ i : Fin n, pts i = pts' ⟨i, by omega⟩)
    (hcol : ∀ i : Fin n, col i = col' ⟨i, by omega⟩)
    (hr : ∀ i : Fin n, r i = r' ⟨i, by omega⟩)
    (node : Fp) :
    nodeBindingErrorPolynomial allPts pts col r node =
      nodeBindingErrorPolynomial allPts' pts' col' r' node := by
  subst m
  subst allPts'
  have hpts' : pts = pts' := by
    funext i
    simpa only using hpts i
  have hcol' : col = col' := by
    funext i
    simpa only using hcol i
  have hr' : r = r' := by
    funext i
    simpa only using hr i
  subst pts'
  subst col'
  subst r'
  rfl

private theorem adaptiveX2RootSet_prefix6
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hprefix : AdaptiveMembersCovered vk instanceCommitment
      (adaptiveRootPrefixProof 6 ps) source)
    (hfull : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp) :
    adaptiveX2RootSet vk instanceCommitment (adaptiveRootPrefixProof 6 ps)
        source hprefix nu =
      adaptiveX2RootSet vk instanceCommitment ps source hfull nu := by
  have hcount := deployedX4PairCount_prefix6 vk instanceCommitment ps nu
  have hall := deployedAllPts_prefix6 vk instanceCommitment ps nu
  have hptsHeq := deployedAlgebraicSetPoints_prefix6 vk instanceCommitment ps nu
  have hcolsHeq := adaptiveSetColumns_prefix6 vk instanceCommitment ps source
    hprefix hfull nu
  have hrHeq := deployedAlgebraicSetInterpolants_prefix6 vk instanceCommitment ps nu
  have hpts := (Fin.heq_fun_iff hcount).mp hptsHeq
  have hcols := (Fin.heq_fun_iff hcount).mp hcolsHeq
  have hr := (Fin.heq_fun_iff hcount).mp hrHeq
  unfold adaptiveX2RootSet
  dsimp only
  ext x
  simp only [Set.mem_setOf_eq]
  apply exists_congr
  intro node
  have hpoly := nodeBindingErrorPolynomial_congr_fin hcount _ _ hall
    _ _ _ _ _ _ hpts hcols hr node
  rw [hpoly, hall]

private theorem assembleQueries_prefix7
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (nu : Fin 11 → Fp) :
    assembleQueries vk instanceCommitment (adaptiveRootPrefixProof 7 ps)
        (chRecord nu (fun _ => 0)) =
      assembleQueries vk instanceCommitment ps (chRecord nu (fun _ => 0)) := by
  rfl

private theorem deployedX4PairCount_prefix7
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (nu : Fin 11 → Fp) :
    deployedX4PairCount vk instanceCommitment (adaptiveRootPrefixProof 7 ps)
        (chRecord nu (fun _ => 0)) =
      deployedX4PairCount vk instanceCommitment ps (chRecord nu (fun _ => 0)) := by
  unfold deployedX4PairCount deployedX4Pairs deployedX4Qs
  simp only [List.length_zip, List.length_map, List.length_ofFn]
  rw [assembleQueries_prefix7]

private theorem deployedSetQueries_prefix7
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (nu : Fin 11 → Fp) (i : Nat) :
    deployedSetQueries vk instanceCommitment (adaptiveRootPrefixProof 7 ps)
        (chRecord nu (fun _ => 0)) i =
      deployedSetQueries vk instanceCommitment ps (chRecord nu (fun _ => 0)) i := by
  rfl

private theorem adaptiveMemberRepresentations_prefix7
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hprefix : AdaptiveMembersCovered vk instanceCommitment
      (adaptiveRootPrefixProof 7 ps) source)
    (hfull : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp) (i : Nat)
    (hi : i < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0))) :
    let hiPrefix : i < deployedX4PairCount vk instanceCommitment
        (adaptiveRootPrefixProof 7 ps) (chRecord nu (fun _ => 0)) := by
      rwa [deployedX4PairCount_prefix7]
    (adaptiveMemberRepresentations vk instanceCommitment
        (adaptiveRootPrefixProof 7 ps) source hprefix nu i hiPrefix).coeffs =
      (adaptiveMemberRepresentations vk instanceCommitment ps source hfull nu i hi).coeffs := by
  dsimp only
  have hqueries := deployedSetQueries_prefix7 vk instanceCommitment ps nu i
  cases hqueries
  rfl

private theorem adaptiveX4ColumnCoeffs_prefix7_at
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hmPrefix : AdaptiveMembersCovered vk instanceCommitment
      (adaptiveRootPrefixProof 7 ps) memberSource)
    (hmFull : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hqPrefix : CommitmentRefCovered qSource
      (.point (adaptiveRootPrefixProof 7 ps).multiopenQPrime))
    (hqFull : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (nu : Fin 11 → Fp)
    (j : Fin (deployedX4PairCount vk instanceCommitment
      (adaptiveRootPrefixProof 7 ps) (chRecord nu (fun _ => 0)) + 1)) :
    (adaptiveX4ColumnRepresentations vk instanceCommitment
        (adaptiveRootPrefixProof 7 ps) memberSource qSource hmPrefix hqPrefix nu).coeffs j =
      (adaptiveX4ColumnRepresentations vk instanceCommitment ps memberSource qSource
        hmFull hqFull nu).coeffs ⟨j, by
          have hc := deployedX4PairCount_prefix7 vk instanceCommitment ps nu
          omega⟩ := by
  have hcount := deployedX4PairCount_prefix7 vk instanceCommitment ps nu
  unfold adaptiveX4ColumnRepresentations adaptiveX4ColumnCoeffs
  dsimp only
  by_cases hjPrefix : (j : Nat) < deployedX4PairCount vk instanceCommitment
      (adaptiveRootPrefixProof 7 ps) (chRecord nu (fun _ => 0))
  · have hjFull : (j : Nat) < deployedX4PairCount vk instanceCommitment ps
        (chRecord nu (fun _ => 0)) := by omega
    simp only [dif_pos hjPrefix, dif_pos hjFull]
    have hindex :
        x4ColumnSetIndex vk instanceCommitment (adaptiveRootPrefixProof 7 ps)
            (chRecord nu (fun _ => 0)) (j : Nat) =
          x4ColumnSetIndex vk instanceCommitment ps
            (chRecord nu (fun _ => 0)) (j : Nat) := by
      unfold x4ColumnSetIndex
      omega
    have hiPrefix : x4ColumnSetIndex vk instanceCommitment
          (adaptiveRootPrefixProof 7 ps) (chRecord nu (fun _ => 0)) (j : Nat) <
        deployedX4PairCount vk instanceCommitment ps
          (chRecord nu (fun _ => 0)) := by
      unfold x4ColumnSetIndex
      omega
    have hiFull : x4ColumnSetIndex vk instanceCommitment ps
          (chRecord nu (fun _ => 0)) (j : Nat) <
        deployedX4PairCount vk instanceCommitment ps
          (chRecord nu (fun _ => 0)) := by
      unfold x4ColumnSetIndex
      omega
    rw [adaptiveMemberRepresentations_prefix7 vk instanceCommitment ps memberSource
      hmPrefix hmFull nu _ hiPrefix]
    exact adaptiveMemberRepresentations_powerSum_eq_index vk instanceCommitment ps
      memberSource hmFull nu (nu 5) _ _ hiPrefix hiFull hindex
  · have hjFull : ¬ (j : Nat) < deployedX4PairCount vk instanceCommitment ps
        (chRecord nu (fun _ => 0)) := by omega
    simp only [dif_neg hjPrefix, dif_neg hjFull]
    norm_num [adaptiveRootPrefixProof]

private theorem adaptiveX4ColumnCoeffs_prefix7
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hmPrefix : AdaptiveMembersCovered vk instanceCommitment
      (adaptiveRootPrefixProof 7 ps) memberSource)
    (hmFull : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hqPrefix : CommitmentRefCovered qSource
      (.point (adaptiveRootPrefixProof 7 ps).multiopenQPrime))
    (hqFull : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (nu : Fin 11 → Fp) :
    HEq (adaptiveX4ColumnRepresentations vk instanceCommitment
        (adaptiveRootPrefixProof 7 ps) memberSource qSource hmPrefix hqPrefix nu).coeffs
      (adaptiveX4ColumnRepresentations vk instanceCommitment ps memberSource qSource
        hmFull hqFull nu).coeffs := by
  have hcount := congrArg (fun n => n + 1)
    (deployedX4PairCount_prefix7 vk instanceCommitment ps nu)
  apply (Fin.heq_fun_iff hcount).mpr
  intro j
  exact adaptiveX4ColumnCoeffs_prefix7_at vk instanceCommitment ps memberSource
    qSource hmPrefix hmFull hqPrefix hqFull nu j

private theorem adaptiveX4BatchCoeffs_prefix7
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hmPrefix : AdaptiveMembersCovered vk instanceCommitment
      (adaptiveRootPrefixProof 7 ps) memberSource)
    (hmFull : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hqPrefix : CommitmentRefCovered qSource
      (.point (adaptiveRootPrefixProof 7 ps).multiopenQPrime))
    (hqFull : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (nu : Fin 11 → Fp) :
    HEq (adaptiveX4Batch vk instanceCommitment (adaptiveRootPrefixProof 7 ps)
        memberSource qSource hmPrefix hqPrefix nu).coeffs
      (adaptiveX4Batch vk instanceCommitment ps memberSource qSource
        hmFull hqFull nu).coeffs := by
  simpa only [adaptiveX4Batch, AlgebraicColumnRepresentations.toDirectPowerBatch] using
    adaptiveX4ColumnCoeffs_prefix7 vk instanceCommitment ps memberSource qSource
      hmPrefix hmFull hqPrefix hqFull nu

private theorem deployedAlgebraicSetColumns_prefix7
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hmPrefix : AdaptiveMembersCovered vk instanceCommitment
      (adaptiveRootPrefixProof 7 ps) memberSource)
    (hmFull : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hqPrefix : CommitmentRefCovered qSource
      (.point (adaptiveRootPrefixProof 7 ps).multiopenQPrime))
    (hqFull : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (nu : Fin 11 → Fp) :
    HEq (deployedAlgebraicSetColumns (ursOfAugmentedBasis shape.k basis) rfl
        vk instanceCommitment (adaptiveRootPrefixProof 7 ps)
        (chRecord nu (fun _ => 0))
        (adaptiveX4Batch vk instanceCommitment (adaptiveRootPrefixProof 7 ps)
          memberSource qSource hmPrefix hqPrefix nu))
      (deployedAlgebraicSetColumns (ursOfAugmentedBasis shape.k basis) rfl
        vk instanceCommitment ps (chRecord nu (fun _ => 0))
        (adaptiveX4Batch vk instanceCommitment ps memberSource qSource
          hmFull hqFull nu)) := by
  have hcount := deployedX4PairCount_prefix7 vk instanceCommitment ps nu
  have hbatch := adaptiveX4BatchCoeffs_prefix7 vk instanceCommitment ps
    memberSource qSource hmPrefix hmFull hqPrefix hqFull nu
  have hbatchAt := (Fin.heq_fun_iff (congrArg (fun n => n + 1) hcount)).mp hbatch
  apply (Fin.heq_fun_iff hcount).mpr
  intro i
  unfold deployedAlgebraicSetColumns
  exact congrArg coeffsToPoly (hbatchAt ⟨i, Nat.lt_succ_of_lt i.isLt⟩)

set_option maxHeartbeats 800000 in
private theorem adaptiveX4ColumnRepresentations_top
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hm : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hq : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (nu : Fin 11 → Fp) :
    (adaptiveX4ColumnRepresentations vk instanceCommitment ps memberSource qSource
        hm hq nu).coeffs
        ⟨deployedX4PairCount vk instanceCommitment ps (chRecord nu (fun _ => 0)),
          Nat.lt_succ_self _⟩ =
      (onlinePointCoordinates qSource ps.multiopenQPrime).1 := by
  change adaptiveX4ColumnCoeffs vk instanceCommitment ps memberSource qSource hm nu
      ⟨deployedX4PairCount vk instanceCommitment ps (chRecord nu (fun _ => 0)),
        Nat.lt_succ_self _⟩ = _
  unfold adaptiveX4ColumnCoeffs
  simp only [dif_neg (Nat.not_lt.mpr (Nat.le_refl _))]

private theorem deployedAlgebraicQPrime_adaptiveX4Batch
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hm : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hq : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (nu : Fin 11 → Fp) :
    deployedAlgebraicQPrime (ursOfAugmentedBasis shape.k basis) rfl vk
        instanceCommitment ps (chRecord nu (fun _ => 0))
        (adaptiveX4Batch vk instanceCommitment ps memberSource qSource hm hq nu) =
      onlinePointPolynomial qSource ps.multiopenQPrime := by
  unfold deployedAlgebraicQPrime onlinePointPolynomial
  simpa only [adaptiveX4Batch, AlgebraicColumnRepresentations.toDirectPowerBatch] using
    congrArg coeffsToPoly (adaptiveX4ColumnRepresentations_top vk instanceCommitment ps
      memberSource qSource hm hq nu)

private theorem deployedAlgebraicQPrime_prefix7
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hmPrefix : AdaptiveMembersCovered vk instanceCommitment
      (adaptiveRootPrefixProof 7 ps) memberSource)
    (hmFull : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hqPrefix : CommitmentRefCovered qSource
      (.point (adaptiveRootPrefixProof 7 ps).multiopenQPrime))
    (hqFull : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (nu : Fin 11 → Fp) :
    deployedAlgebraicQPrime (ursOfAugmentedBasis shape.k basis) rfl vk
        instanceCommitment (adaptiveRootPrefixProof 7 ps) (chRecord nu (fun _ => 0))
        (adaptiveX4Batch vk instanceCommitment (adaptiveRootPrefixProof 7 ps)
          memberSource qSource hmPrefix hqPrefix nu) =
      deployedAlgebraicQPrime (ursOfAugmentedBasis shape.k basis) rfl vk
        instanceCommitment ps (chRecord nu (fun _ => 0))
        (adaptiveX4Batch vk instanceCommitment ps memberSource qSource
          hmFull hqFull nu) := by
  rw [deployedAlgebraicQPrime_adaptiveX4Batch,
    deployedAlgebraicQPrime_adaptiveX4Batch]
  norm_num [adaptiveRootPrefixProof]

private theorem deployedAllPts_prefix7
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (nu : Fin 11 → Fp) :
    deployedAllPts vk instanceCommitment (adaptiveRootPrefixProof 7 ps)
        (chRecord nu (fun _ => 0)) =
      deployedAllPts vk instanceCommitment ps (chRecord nu (fun _ => 0)) := by
  rfl

private theorem deployedAlgebraicSetPoints_prefix7
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (nu : Fin 11 → Fp) :
    HEq (deployedAlgebraicSetPoints vk instanceCommitment
        (adaptiveRootPrefixProof 7 ps) (chRecord nu (fun _ => 0)))
      (deployedAlgebraicSetPoints vk instanceCommitment ps
        (chRecord nu (fun _ => 0))) := by
  have hcount := deployedX4PairCount_prefix7 vk instanceCommitment ps nu
  apply (Fin.heq_fun_iff hcount).mpr
  intro j
  unfold deployedAlgebraicSetPoints deployedSetPts
  rw [assembleQueries_prefix7]
  have hindex :
      deployedX4PairCount vk instanceCommitment (adaptiveRootPrefixProof 7 ps)
          (chRecord nu (fun _ => 0)) - 1 - (j : Nat) =
        deployedX4PairCount vk instanceCommitment ps
          (chRecord nu (fun _ => 0)) - 1 - (j : Nat) := by omega
  rw [hindex]

private theorem deployedSetsForEval_getD_evals_prefix7
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (nu : Fin 11 → Fp) (i : Nat)
    (hi : i < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0))) :
    ((deployedSetsForEval vk instanceCommitment (adaptiveRootPrefixProof 7 ps)
        (chRecord nu (fun _ => 0))).getD i ([], [], 0)).2.1 =
      ((deployedSetsForEval vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).getD i ([], [], 0)).2.1 := by
  have hiPrefix : i < deployedX4PairCount vk instanceCommitment
      (adaptiveRootPrefixProof 7 ps) (chRecord nu (fun _ => 0)) := by
    have hc := deployedX4PairCount_prefix7 vk instanceCommitment ps nu
    omega
  rw [deployedSetsForEval_getD_evals vk instanceCommitment
      (adaptiveRootPrefixProof 7 ps) (chRecord nu (fun _ => 0)) hiPrefix,
    deployedSetsForEval_getD_evals vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) hi, assembleQueries_prefix7,
    deployedSetQueries_prefix7]

private theorem deployedSetsForEval_reverse_getD_points_prefix7
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (nu : Fin 11 → Fp)
    (j : Fin (deployedX4PairCount vk instanceCommitment
      (adaptiveRootPrefixProof 7 ps) (chRecord nu (fun _ => 0)))) :
    ((deployedSetsForEval vk instanceCommitment (adaptiveRootPrefixProof 7 ps)
        (chRecord nu (fun _ => 0))).reverse.getD j ([], [], 0)).1 =
      ((deployedSetsForEval vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).reverse.getD j ([], [], 0)).1 := by
  have hcount := deployedX4PairCount_prefix7 vk instanceCommitment ps nu
  have hj : (j : Nat) < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) := by omega
  rw [deployedSetsForEval_reverse_getD_points vk instanceCommitment
      (adaptiveRootPrefixProof 7 ps) (chRecord nu (fun _ => 0)) j.isLt,
    deployedSetsForEval_reverse_getD_points vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) hj]
  have hindex :
      deployedX4PairCount vk instanceCommitment (adaptiveRootPrefixProof 7 ps)
          (chRecord nu (fun _ => 0)) - 1 - (j : Nat) =
        deployedX4PairCount vk instanceCommitment ps
          (chRecord nu (fun _ => 0)) - 1 - (j : Nat) := by omega
  rw [hindex, assembleQueries_prefix7]

private theorem deployedSetsForEval_reverse_getD_evals_prefix7
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (nu : Fin 11 → Fp)
    (j : Fin (deployedX4PairCount vk instanceCommitment
      (adaptiveRootPrefixProof 7 ps) (chRecord nu (fun _ => 0)))) :
    ((deployedSetsForEval vk instanceCommitment (adaptiveRootPrefixProof 7 ps)
        (chRecord nu (fun _ => 0))).reverse.getD j ([], [], 0)).2.1 =
      ((deployedSetsForEval vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).reverse.getD j ([], [], 0)).2.1 := by
  have hcount := deployedX4PairCount_prefix7 vk instanceCommitment ps nu
  have hj : (j : Nat) < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) := by omega
  have hp :
      (deployedSetsForEval vk instanceCommitment (adaptiveRootPrefixProof 7 ps)
        (chRecord nu (fun _ => 0))).reverse.getD j ([], [], 0) =
      (deployedSetsForEval vk instanceCommitment (adaptiveRootPrefixProof 7 ps)
        (chRecord nu (fun _ => 0))).getD
          (deployedX4PairCount vk instanceCommitment (adaptiveRootPrefixProof 7 ps)
            (chRecord nu (fun _ => 0)) - 1 - (j : Nat)) ([], [], 0) := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_reverse (by rw [deployedSetsForEval_length]; exact j.isLt),
      deployedSetsForEval_length]
  have hf :
      (deployedSetsForEval vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).reverse.getD j ([], [], 0) =
      (deployedSetsForEval vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).getD
          (deployedX4PairCount vk instanceCommitment ps
            (chRecord nu (fun _ => 0)) - 1 - (j : Nat)) ([], [], 0) := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_reverse (by rw [deployedSetsForEval_length]; exact hj),
      deployedSetsForEval_length]
  rw [hp, hf]
  have hindex :
      deployedX4PairCount vk instanceCommitment (adaptiveRootPrefixProof 7 ps)
          (chRecord nu (fun _ => 0)) - 1 - (j : Nat) =
        deployedX4PairCount vk instanceCommitment ps
          (chRecord nu (fun _ => 0)) - 1 - (j : Nat) := by omega
  rw [hindex]
  exact deployedSetsForEval_getD_evals_prefix7 vk instanceCommitment ps nu _ (by omega)

private theorem deployedAlgebraicSetInterpolants_prefix7
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (nu : Fin 11 → Fp) :
    HEq (deployedAlgebraicSetInterpolants vk instanceCommitment
        (adaptiveRootPrefixProof 7 ps) (chRecord nu (fun _ => 0)))
      (deployedAlgebraicSetInterpolants vk instanceCommitment ps
        (chRecord nu (fun _ => 0))) := by
  have hcount := deployedX4PairCount_prefix7 vk instanceCommitment ps nu
  apply (Fin.heq_fun_iff hcount).mpr
  intro j
  unfold deployedAlgebraicSetInterpolants
  rw [deployedSetsForEval_reverse_getD_points_prefix7
      vk instanceCommitment ps nu j,
    deployedSetsForEval_reverse_getD_evals_prefix7
      vk instanceCommitment ps nu j]

private theorem clearedQuotientErrorPolynomial_congr_fin
    {n m : Nat} (hnm : n = m)
    (allPts allPts' : Finset Fp) (hall : allPts = allPts')
    (pts : Fin n → Finset Fp) (pts' : Fin m → Finset Fp)
    (col r : Fin n → CPoly) (col' r' : Fin m → CPoly)
    (a : Fin n → Fp) (a' : Fin m → Fp)
    (qCol qCol' : CPoly)
    (hpts : ∀ i : Fin n, pts i = pts' ⟨i, by omega⟩)
    (hcol : ∀ i : Fin n, col i = col' ⟨i, by omega⟩)
    (hr : ∀ i : Fin n, r i = r' ⟨i, by omega⟩)
    (ha : ∀ i : Fin n, a i = a' ⟨i, by omega⟩)
    (hq : qCol = qCol') :
    clearedQuotientErrorPolynomial allPts pts col r a qCol =
      clearedQuotientErrorPolynomial allPts' pts' col' r' a' qCol' := by
  subst m
  subst allPts'
  subst qCol'
  have hpts' : pts = pts' := by funext i; simpa only using hpts i
  have hcol' : col = col' := by funext i; simpa only using hcol i
  have hr' : r = r' := by funext i; simpa only using hr i
  have ha' : a = a' := by funext i; simpa only using ha i
  subst pts'
  subst col'
  subst r'
  subst a'
  rfl

private theorem adaptiveX3ErrorPolynomial_prefix7
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hmPrefix : AdaptiveMembersCovered vk instanceCommitment
      (adaptiveRootPrefixProof 7 ps) memberSource)
    (hmFull : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hqPrefix : CommitmentRefCovered qSource
      (.point (adaptiveRootPrefixProof 7 ps).multiopenQPrime))
    (hqFull : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (nu : Fin 11 → Fp) :
    deployedX3ErrorPolynomial (ursOfAugmentedBasis shape.k basis) rfl
        vk instanceCommitment (adaptiveRootPrefixProof 7 ps)
        (chRecord nu (fun _ => 0))
        (adaptiveX4Batch vk instanceCommitment (adaptiveRootPrefixProof 7 ps)
          memberSource qSource hmPrefix hqPrefix nu) =
      deployedX3ErrorPolynomial (ursOfAugmentedBasis shape.k basis) rfl
        vk instanceCommitment ps (chRecord nu (fun _ => 0))
        (adaptiveX4Batch vk instanceCommitment ps memberSource qSource
          hmFull hqFull nu) := by
  let psPrefix := adaptiveRootPrefixProof 7 ps
  let ch : Challenges shape.k Fp := chRecord nu (fun _ => 0)
  let batchPrefix := adaptiveX4Batch vk instanceCommitment psPrefix
    memberSource qSource hmPrefix hqPrefix nu
  let batchFull := adaptiveX4Batch vk instanceCommitment ps
    memberSource qSource hmFull hqFull nu
  have hcount : deployedX4PairCount vk instanceCommitment psPrefix ch =
      deployedX4PairCount vk instanceCommitment ps ch := by
    simpa only [psPrefix, ch] using
      deployedX4PairCount_prefix7 vk instanceCommitment ps nu
  have hall : deployedAllPts vk instanceCommitment psPrefix ch =
      deployedAllPts vk instanceCommitment ps ch := by
    simpa only [psPrefix, ch] using deployedAllPts_prefix7 vk instanceCommitment ps nu
  have hptsHeq : HEq (deployedAlgebraicSetPoints vk instanceCommitment psPrefix ch)
      (deployedAlgebraicSetPoints vk instanceCommitment ps ch) := by
    simpa only [psPrefix, ch] using
      deployedAlgebraicSetPoints_prefix7 vk instanceCommitment ps nu
  have hrHeq : HEq (deployedAlgebraicSetInterpolants vk instanceCommitment psPrefix ch)
      (deployedAlgebraicSetInterpolants vk instanceCommitment ps ch) := by
    simpa only [psPrefix, ch] using
      deployedAlgebraicSetInterpolants_prefix7 vk instanceCommitment ps nu
  have hpts := (Fin.heq_fun_iff hcount).mp hptsHeq
  have hr := (Fin.heq_fun_iff hcount).mp hrHeq
  have hcolHeq : HEq
      (deployedAlgebraicSetColumns (ursOfAugmentedBasis shape.k basis) rfl
        vk instanceCommitment psPrefix ch batchPrefix)
      (deployedAlgebraicSetColumns (ursOfAugmentedBasis shape.k basis) rfl
        vk instanceCommitment ps ch batchFull) := by
    simpa only [psPrefix, ch, batchPrefix, batchFull] using
      deployedAlgebraicSetColumns_prefix7 vk instanceCommitment ps memberSource
        qSource hmPrefix hmFull hqPrefix hqFull nu
  have hcol := (Fin.heq_fun_iff hcount).mp hcolHeq
  have hqCol : deployedAlgebraicQPrime (ursOfAugmentedBasis shape.k basis) rfl
        vk instanceCommitment psPrefix ch batchPrefix =
      deployedAlgebraicQPrime (ursOfAugmentedBasis shape.k basis) rfl
        vk instanceCommitment ps ch batchFull := by
    simpa only [psPrefix, ch, batchPrefix, batchFull] using
      deployedAlgebraicQPrime_prefix7 vk instanceCommitment ps memberSource
        qSource hmPrefix hmFull hqPrefix hqFull nu
  change deployedX3ErrorPolynomial (ursOfAugmentedBasis shape.k basis) rfl
      vk instanceCommitment psPrefix ch batchPrefix =
    deployedX3ErrorPolynomial (ursOfAugmentedBasis shape.k basis) rfl
      vk instanceCommitment ps ch batchFull
  unfold deployedX3ErrorPolynomial
  exact clearedQuotientErrorPolynomial_congr_fin hcount _ _ hall _ _ _ _ _ _
    _ _ _ _ hpts hcol hr (fun _ => rfl) hqCol

private theorem adaptiveX3RootSet_prefix7
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hmPrefix : AdaptiveMembersCovered vk instanceCommitment
      (adaptiveRootPrefixProof 7 ps) memberSource)
    (hmFull : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hqPrefix : CommitmentRefCovered qSource
      (.point (adaptiveRootPrefixProof 7 ps).multiopenQPrime))
    (hqFull : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (nu : Fin 11 → Fp) :
    adaptiveX3RootSet vk instanceCommitment (adaptiveRootPrefixProof 7 ps)
        memberSource qSource hmPrefix hqPrefix nu =
      adaptiveX3RootSet vk instanceCommitment ps memberSource qSource
        hmFull hqFull nu := by
  unfold adaptiveX3RootSet
  dsimp only
  rw [adaptiveX3ErrorPolynomial_prefix7 vk instanceCommitment ps memberSource
      qSource hmPrefix hmFull hqPrefix hqFull nu,
    deployedAllPts_prefix7 vk instanceCommitment ps nu]

private theorem adaptiveX4RootSet_prefix8
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hmPrefix : AdaptiveMembersCovered vk instanceCommitment
      (adaptiveRootPrefixProof 8 ps) memberSource)
    (hmFull : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hqPrefix : CommitmentRefCovered qSource
      (.point (adaptiveRootPrefixProof 8 ps).multiopenQPrime))
    (hqFull : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (nu : Fin 11 → Fp) :
    adaptiveX4RootSet vk instanceCommitment (adaptiveRootPrefixProof 8 ps)
        memberSource qSource hmPrefix hqPrefix nu =
      adaptiveX4RootSet vk instanceCommitment ps memberSource qSource hmFull hqFull nu := by
  rfl

private theorem adaptiveXiRootSet_prefix9
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource sSource : List (AlgebraicPoint (F := Fp) basis))
    (hmPrefix : AdaptiveMembersCovered vk instanceCommitment
      (adaptiveRootPrefixProof 9 ps) memberSource)
    (hmFull : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hqPrefix : CommitmentRefCovered qSource
      (.point (adaptiveRootPrefixProof 9 ps).multiopenQPrime))
    (hqFull : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (hsPrefix : CommitmentRefCovered sSource
      (.point (adaptiveRootPrefixProof 9 ps).ipaS))
    (hsFull : CommitmentRefCovered sSource (.point ps.ipaS))
    (nu : Fin 11 → Fp) :
    adaptiveXiRootSet vk instanceCommitment (adaptiveRootPrefixProof 9 ps)
        memberSource qSource sSource hmPrefix hqPrefix hsPrefix nu =
      adaptiveXiRootSet vk instanceCommitment ps memberSource qSource sSource
        hmFull hqFull hsFull nu := by
  rfl

private theorem adaptiveZRootSet_prefix10
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource sSource : List (AlgebraicPoint (F := Fp) basis))
    (hmPrefix : AdaptiveMembersCovered vk instanceCommitment
      (adaptiveRootPrefixProof 10 ps) memberSource)
    (hmFull : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hqPrefix : CommitmentRefCovered qSource
      (.point (adaptiveRootPrefixProof 10 ps).multiopenQPrime))
    (hqFull : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (hsPrefix : CommitmentRefCovered sSource
      (.point (adaptiveRootPrefixProof 10 ps).ipaS))
    (hsFull : CommitmentRefCovered sSource (.point ps.ipaS))
    (nu : Fin 11 → Fp) :
    adaptiveZRootSet vk instanceCommitment (adaptiveRootPrefixProof 10 ps)
        memberSource qSource sSource hmPrefix hqPrefix hsPrefix nu =
      adaptiveZRootSet vk instanceCommitment ps memberSource qSource sSource
        hmFull hqFull hsFull nu := by
  rfl

private theorem adaptiveMembersCovered_prefix5
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hfull : AdaptiveMembersCovered vk instanceCommitment ps source) :
    AdaptiveMembersCovered vk instanceCommitment (adaptiveRootPrefixProof 5 ps) source := by
  intro nu i hi m
  have hiFull : i < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) := by
    have hc := deployedX4PairCount_prefix5 vk instanceCommitment ps nu
    omega
  have hqueries := deployedSetQueries_prefix5 vk instanceCommitment ps nu i
  cases hqueries
  exact hfull nu i hiFull m

private theorem adaptiveMembersCovered_prefix6
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hfull : AdaptiveMembersCovered vk instanceCommitment ps source) :
    AdaptiveMembersCovered vk instanceCommitment (adaptiveRootPrefixProof 6 ps) source := by
  simpa only [adaptiveRootPrefixProof] using
    adaptiveMembersCovered_prefix5 vk instanceCommitment ps source hfull

private theorem adaptiveMembersCovered_prefix7
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hfull : AdaptiveMembersCovered vk instanceCommitment ps source) :
    AdaptiveMembersCovered vk instanceCommitment (adaptiveRootPrefixProof 7 ps) source := by
  intro nu i hi m
  have hiFull : i < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) := by
    have hc := deployedX4PairCount_prefix7 vk instanceCommitment ps nu
    omega
  have hqueries := deployedSetQueries_prefix7 vk instanceCommitment ps nu i
  cases hqueries
  exact hfull nu i hiFull m

private theorem adaptiveMembersCovered_prefix8
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hfull : AdaptiveMembersCovered vk instanceCommitment ps source) :
    AdaptiveMembersCovered vk instanceCommitment (adaptiveRootPrefixProof 8 ps) source := by
  simpa only [adaptiveRootPrefixProof] using hfull

private theorem adaptiveMembersCovered_prefix9
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hfull : AdaptiveMembersCovered vk instanceCommitment ps source) :
    AdaptiveMembersCovered vk instanceCommitment (adaptiveRootPrefixProof 9 ps) source := by
  simpa only [adaptiveRootPrefixProof] using hfull

private theorem adaptiveMembersCovered_prefix10
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hfull : AdaptiveMembersCovered vk instanceCommitment ps source) :
    AdaptiveMembersCovered vk instanceCommitment (adaptiveRootPrefixProof 10 ps) source := by
  simpa only [adaptiveRootPrefixProof] using hfull

/-- The actual fresh fallback at `x₁` is the normalized decoder surface. -/
theorem OnlineMemberProofData.adaptiveFallbackRootSurface_five
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAdaptiveOnlineAGMFSFamily shape}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (earlier : Fin 5 → Fp) :
    adaptiveFallbackRootSurface family basis 5 data t earlier =
      adaptiveX1AllRootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
        data.adaptivePreX1MembersCovered (adaptiveEarlierRecord 5 earlier) := by
  unfold adaptiveFallbackRootSurface adaptiveRootSurfaceAt
  dsimp only
  rw [data.adaptiveRootMemberSource_eq_preX1 5 (by norm_num)]
  let hprefix := adaptiveMembersCovered_prefix5 (family.vk basis)
    (family.instanceCommitment basis) data.algebraicProof.erase
    (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
    data.adaptivePreX1MembersCovered
  rw [dif_pos hprefix]
  norm_num
  exact adaptiveX1AllRootSet_prefix5 (family.vk basis)
    (family.instanceCommitment basis) data.algebraicProof.erase
    (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
    hprefix data.adaptivePreX1MembersCovered (adaptiveEarlierRecord 5 earlier)

/-- The actual fresh fallback at `x₂` is the normalized decoder surface. -/
theorem OnlineMemberProofData.adaptiveFallbackRootSurface_six
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAdaptiveOnlineAGMFSFamily shape}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (earlier : Fin 6 → Fp) :
    adaptiveFallbackRootSurface family basis 6 data t earlier =
      adaptiveX2RootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
        data.adaptivePreX1MembersCovered (adaptiveEarlierRecord 6 earlier) := by
  unfold adaptiveFallbackRootSurface adaptiveRootSurfaceAt
  dsimp only
  rw [data.adaptiveRootMemberSource_eq_preX1 6 (by norm_num)]
  let hprefix := adaptiveMembersCovered_prefix6 (family.vk basis)
    (family.instanceCommitment basis) data.algebraicProof.erase
    (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
    data.adaptivePreX1MembersCovered
  rw [dif_pos hprefix]
  norm_num
  exact adaptiveX2RootSet_prefix6 (family.vk basis)
    (family.instanceCommitment basis) data.algebraicProof.erase
    (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
    hprefix data.adaptivePreX1MembersCovered (adaptiveEarlierRecord 6 earlier)

/-- The actual fresh fallback at `x₃` is the normalized decoder surface. -/
theorem OnlineMemberProofData.adaptiveFallbackRootSurface_seven
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAdaptiveOnlineAGMFSFamily shape}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (earlier : Fin 7 → Fp) :
    adaptiveFallbackRootSurface family basis 7 data t earlier =
      adaptiveX3RootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
        (adaptiveEarlierRecord 7 earlier) := by
  unfold adaptiveFallbackRootSurface adaptiveRootSurfaceAt
  dsimp only
  rw [data.adaptiveRootMemberSource_eq_preX1 7 (by norm_num),
    data.adaptiveRootQSource_eq 7 (by norm_num)]
  let hprefix := adaptiveMembersCovered_prefix7 (family.vk basis)
    (family.instanceCommitment basis) data.algebraicProof.erase
    (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
    data.adaptivePreX1MembersCovered
  let qFull : CommitmentRefCovered [data.algebraicProof.multiopenQPrime]
      (.point data.algebraicProof.erase.multiopenQPrime) :=
    ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
  let qPrefix : CommitmentRefCovered [data.algebraicProof.multiopenQPrime]
      (.point (adaptiveRootPrefixProof 7 data.algebraicProof.erase).multiopenQPrime) := by
    simpa only [adaptiveRootPrefixProof] using qFull
  rw [dif_pos hprefix]
  norm_num
  rw [dif_pos qPrefix]
  exact adaptiveX3RootSet_prefix7 (family.vk basis)
    (family.instanceCommitment basis) data.algebraicProof.erase
    (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
    [data.algebraicProof.multiopenQPrime] hprefix data.adaptivePreX1MembersCovered
    qPrefix qFull (adaptiveEarlierRecord 7 earlier)

/-- The actual fresh fallback at `x₄` is the normalized decoder surface. -/
theorem OnlineMemberProofData.adaptiveFallbackRootSurface_eight
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAdaptiveOnlineAGMFSFamily shape}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (earlier : Fin 8 → Fp) :
    adaptiveFallbackRootSurface family basis 8 data t earlier =
      adaptiveX4RootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
        (adaptiveEarlierRecord 8 earlier) := by
  unfold adaptiveFallbackRootSurface adaptiveRootSurfaceAt
  dsimp only
  rw [data.adaptiveRootMemberSource_eq_preX1 8 (by norm_num),
    data.adaptiveRootQSource_eq 8 (by norm_num)]
  let hprefix := adaptiveMembersCovered_prefix8 (family.vk basis)
    (family.instanceCommitment basis) data.algebraicProof.erase
    (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
    data.adaptivePreX1MembersCovered
  let qFull : CommitmentRefCovered [data.algebraicProof.multiopenQPrime]
      (.point data.algebraicProof.erase.multiopenQPrime) :=
    ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
  let qPrefix : CommitmentRefCovered [data.algebraicProof.multiopenQPrime]
      (.point (adaptiveRootPrefixProof 8 data.algebraicProof.erase).multiopenQPrime) := by
    simpa only [adaptiveRootPrefixProof] using qFull
  rw [dif_pos hprefix]
  norm_num
  rw [dif_pos qPrefix]
  exact adaptiveX4RootSet_prefix8 (family.vk basis)
    (family.instanceCommitment basis) data.algebraicProof.erase
    (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
    [data.algebraicProof.multiopenQPrime] hprefix data.adaptivePreX1MembersCovered
    qPrefix qFull (adaptiveEarlierRecord 8 earlier)

/-- The actual fresh fallback at `ξ` is the normalized decoder surface. -/
theorem OnlineMemberProofData.adaptiveFallbackRootSurface_nine
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAdaptiveOnlineAGMFSFamily shape}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (earlier : Fin 9 → Fp) :
    adaptiveFallbackRootSurface family basis 9 data t earlier =
      adaptiveXiRootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
        [data.algebraicProof.multiopenQPrime] [data.algebraicProof.ipaS]
        data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
        ⟨data.algebraicProof.ipaS, by simp, rfl⟩
        (adaptiveEarlierRecord 9 earlier) := by
  unfold adaptiveFallbackRootSurface adaptiveRootSurfaceAt
  dsimp only
  rw [data.adaptiveRootMemberSource_eq_preX1 9 (by norm_num),
    data.adaptiveRootQSource_eq 9 (by norm_num),
    data.adaptiveRootSSource_eq 9 (by norm_num)]
  let hprefix := adaptiveMembersCovered_prefix9 (family.vk basis)
    (family.instanceCommitment basis) data.algebraicProof.erase
    (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
    data.adaptivePreX1MembersCovered
  let qFull : CommitmentRefCovered [data.algebraicProof.multiopenQPrime]
      (.point data.algebraicProof.erase.multiopenQPrime) :=
    ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
  let qPrefix : CommitmentRefCovered [data.algebraicProof.multiopenQPrime]
      (.point (adaptiveRootPrefixProof 9 data.algebraicProof.erase).multiopenQPrime) := by
    simpa only [adaptiveRootPrefixProof] using qFull
  let sFull : CommitmentRefCovered [data.algebraicProof.ipaS]
      (.point data.algebraicProof.erase.ipaS) :=
    ⟨data.algebraicProof.ipaS, by simp, rfl⟩
  let sPrefix : CommitmentRefCovered [data.algebraicProof.ipaS]
      (.point (adaptiveRootPrefixProof 9 data.algebraicProof.erase).ipaS) := by
    simpa only [adaptiveRootPrefixProof] using sFull
  rw [dif_pos hprefix]
  norm_num
  rw [dif_pos qPrefix, dif_pos sPrefix]
  exact adaptiveXiRootSet_prefix9 (family.vk basis)
    (family.instanceCommitment basis) data.algebraicProof.erase
    (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
    [data.algebraicProof.multiopenQPrime] [data.algebraicProof.ipaS]
    hprefix data.adaptivePreX1MembersCovered qPrefix qFull sPrefix sFull
    (adaptiveEarlierRecord 9 earlier)

/-- The actual fresh fallback at `z` is the normalized decoder surface. -/
theorem OnlineMemberProofData.adaptiveFallbackRootSurface_ten
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAdaptiveOnlineAGMFSFamily shape}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (t : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k))
    (earlier : Fin 10 → Fp) :
    adaptiveFallbackRootSurface family basis 10 data t earlier =
      adaptiveZRootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
        [data.algebraicProof.multiopenQPrime] [data.algebraicProof.ipaS]
        data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
        ⟨data.algebraicProof.ipaS, by simp, rfl⟩
        (adaptiveEarlierRecord 10 earlier) := by
  unfold adaptiveFallbackRootSurface adaptiveRootSurfaceAt
  dsimp only
  rw [data.adaptiveRootMemberSource_eq_preX1 10 (by norm_num),
    data.adaptiveRootQSource_eq 10 (by norm_num),
    data.adaptiveRootSSource_eq 10 (by norm_num)]
  let hprefix := adaptiveMembersCovered_prefix10 (family.vk basis)
    (family.instanceCommitment basis) data.algebraicProof.erase
    (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
    data.adaptivePreX1MembersCovered
  let qFull : CommitmentRefCovered [data.algebraicProof.multiopenQPrime]
      (.point data.algebraicProof.erase.multiopenQPrime) :=
    ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
  let qPrefix : CommitmentRefCovered [data.algebraicProof.multiopenQPrime]
      (.point (adaptiveRootPrefixProof 10 data.algebraicProof.erase).multiopenQPrime) := by
    simpa only [adaptiveRootPrefixProof] using qFull
  let sFull : CommitmentRefCovered [data.algebraicProof.ipaS]
      (.point data.algebraicProof.erase.ipaS) :=
    ⟨data.algebraicProof.ipaS, by simp, rfl⟩
  let sPrefix : CommitmentRefCovered [data.algebraicProof.ipaS]
      (.point (adaptiveRootPrefixProof 10 data.algebraicProof.erase).ipaS) := by
    simpa only [adaptiveRootPrefixProof] using sFull
  rw [dif_pos hprefix]
  norm_num
  rw [dif_pos qPrefix, dif_pos sPrefix]
  exact adaptiveZRootSet_prefix10 (family.vk basis)
    (family.instanceCommitment basis) data.algebraicProof.erase
    (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
    [data.algebraicProof.multiopenQPrime] [data.algebraicProof.ipaS]
    hprefix data.adaptivePreX1MembersCovered qPrefix qFull sPrefix sFull
    (adaptiveEarlierRecord 10 earlier)

/-- At the verifier's actual squeeze point, the final adaptive bad set is exactly its fresh
fallback instantiated with the genuine earlier oracle answers. -/
theorem OnlineMemberProofData.adaptiveFinalRootBad_eq_fallback
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAdaptiveOnlineAGMFSFamily shape}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (n : Fin 11) :
    let t := algebraicFullPrefixesPre family.init data.toAlgebraicWfProof n
    adaptiveFinalRootBad family basis n data t O =
      adaptiveFallbackRootSurface family basis n data t
        (fun i => O (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof
          (i.castLE (le_of_lt n.isLt)))) := by
  dsimp only
  unfold adaptiveFinalRootBad adaptivePrefixBad
  have hlen : (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof n).val.length =
      preIpaLen shape family.init.length n := by
    exact preIpaSqueezePoints_length_eq family.init data.algebraicProof.erase
      data.wellFormed n
  rw [if_pos hlen]
  congr 1
  funext i
  exact congrArg O (adaptiveEarlierPrefix_algebraicFullPrefixesPre
    family.init data.toAlgebraicWfProof n i)

/-- Extending the actual strict-prefix reads by zero gives their canonical eleven-slot record. -/
theorem adaptiveEarlierRecord_preIpaReads
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    (init : List (TranscriptElt Fp VestaG))
    (p : AlgebraicWfProof basis vk instanceCommitment) (n : Fin 11)
    (O : BTranscript Fp VestaG
      (preIpaLen shape init.length 10 + 3 * shape.k) → Fp) :
    adaptiveEarlierRecord n (fun i =>
      O (algebraicFullPrefixesPre init p (i.castLE (le_of_lt n.isLt)))) =
      fun i : Fin 11 => if _h : (i : Nat) < (n : Nat) then
        O (algebraicFullPrefixesPre init p i) else 0 := by
  funext i
  unfold adaptiveEarlierRecord
  split
  · congr 2
  · rfl

/-- The actual `x₁` event is the executable normalized decoder surface, with only strict-prefix
answers retained. -/
theorem OnlineMemberProofData.adaptiveFinalRootBad_five
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAdaptiveOnlineAGMFSFamily shape}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    let t := algebraicFullPrefixesPre family.init data.toAlgebraicWfProof 5
    adaptiveFinalRootBad family basis 5 data t O =
      adaptiveX1AllRootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
        data.adaptivePreX1MembersCovered
        (fun i : Fin 11 => if _h : (i : Nat) < 5 then
          O (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof i) else 0) := by
  dsimp only
  rw [data.adaptiveFinalRootBad_eq_fallback O 5]
  rw [data.adaptiveFallbackRootSurface_five]
  rw [adaptiveEarlierRecord_preIpaReads]
  norm_num

/-- The actual `x₂` event is the executable normalized decoder surface. -/
theorem OnlineMemberProofData.adaptiveFinalRootBad_six
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAdaptiveOnlineAGMFSFamily shape}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    let t := algebraicFullPrefixesPre family.init data.toAlgebraicWfProof 6
    adaptiveFinalRootBad family basis 6 data t O =
      adaptiveX2RootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
        data.adaptivePreX1MembersCovered
        (fun i : Fin 11 => if _h : (i : Nat) < 6 then
          O (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof i) else 0) := by
  dsimp only
  rw [data.adaptiveFinalRootBad_eq_fallback O 6]
  rw [data.adaptiveFallbackRootSurface_six]
  rw [adaptiveEarlierRecord_preIpaReads]
  norm_num

/-- The actual `x₃` event is the executable normalized decoder surface. -/
theorem OnlineMemberProofData.adaptiveFinalRootBad_seven
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAdaptiveOnlineAGMFSFamily shape}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    let t := algebraicFullPrefixesPre family.init data.toAlgebraicWfProof 7
    adaptiveFinalRootBad family basis 7 data t O =
      adaptiveX3RootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
        (fun i : Fin 11 => if _h : (i : Nat) < 7 then
          O (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof i) else 0) := by
  dsimp only
  rw [data.adaptiveFinalRootBad_eq_fallback O 7]
  rw [data.adaptiveFallbackRootSurface_seven]
  rw [adaptiveEarlierRecord_preIpaReads]
  norm_num

/-- The actual `x₄` event is the executable normalized decoder surface. -/
theorem OnlineMemberProofData.adaptiveFinalRootBad_eight
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAdaptiveOnlineAGMFSFamily shape}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    let t := algebraicFullPrefixesPre family.init data.toAlgebraicWfProof 8
    adaptiveFinalRootBad family basis 8 data t O =
      adaptiveX4RootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
        (fun i : Fin 11 => if _h : (i : Nat) < 8 then
          O (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof i) else 0) := by
  dsimp only
  rw [data.adaptiveFinalRootBad_eq_fallback O 8]
  rw [data.adaptiveFallbackRootSurface_eight]
  rw [adaptiveEarlierRecord_preIpaReads]
  norm_num

/-- The actual `ξ` event is the executable normalized decoder surface. -/
theorem OnlineMemberProofData.adaptiveFinalRootBad_nine
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAdaptiveOnlineAGMFSFamily shape}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    let t := algebraicFullPrefixesPre family.init data.toAlgebraicWfProof 9
    adaptiveFinalRootBad family basis 9 data t O =
      adaptiveXiRootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
        [data.algebraicProof.multiopenQPrime] [data.algebraicProof.ipaS]
        data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
        ⟨data.algebraicProof.ipaS, by simp, rfl⟩
        (fun i : Fin 11 => if _h : (i : Nat) < 9 then
          O (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof i) else 0) := by
  dsimp only
  rw [data.adaptiveFinalRootBad_eq_fallback O 9]
  rw [data.adaptiveFallbackRootSurface_nine]
  rw [adaptiveEarlierRecord_preIpaReads]
  norm_num

/-- The actual `z` event is the executable normalized decoder surface. -/
theorem OnlineMemberProofData.adaptiveFinalRootBad_ten
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAdaptiveOnlineAGMFSFamily shape}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    let t := algebraicFullPrefixesPre family.init data.toAlgebraicWfProof 10
    adaptiveFinalRootBad family basis 10 data t O =
      adaptiveZRootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
        [data.algebraicProof.multiopenQPrime] [data.algebraicProof.ipaS]
        data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
        ⟨data.algebraicProof.ipaS, by simp, rfl⟩
        (fun i : Fin 11 => if _h : (i : Nat) < 10 then
          O (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof i) else 0) := by
  dsimp only
  rw [data.adaptiveFinalRootBad_eq_fallback O 10]
  rw [data.adaptiveFallbackRootSurface_ten]
  rw [adaptiveEarlierRecord_preIpaReads]
  norm_num

/-- Fill the strict prefix below `n` from a full pre-IPA answer record and zero the rest. -/
def adaptiveStrictPrefixRecord (n : Fin 11) (nu : Fin 11 → Fp) : Fin 11 → Fp :=
  fun i => if (i : Nat) < (n : Nat) then nu i else 0

private theorem assembleQueries_strictPrefix5
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG) (nu : Fin 11 → Fp) :
    assembleQueries vk instanceCommitment ps
        (chRecord (adaptiveStrictPrefixRecord 5 nu) (fun _ => 0)) =
      assembleQueries vk instanceCommitment ps (chRecord nu (fun _ => 0)) := by
  rfl

private theorem deployedX4PairCount_strictPrefix5
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG) (nu : Fin 11 → Fp) :
    deployedX4PairCount vk instanceCommitment ps
        (chRecord (adaptiveStrictPrefixRecord 5 nu) (fun _ => 0)) =
      deployedX4PairCount vk instanceCommitment ps (chRecord nu (fun _ => 0)) := by
  unfold deployedX4PairCount deployedX4Pairs deployedX4Qs
  simp only [List.length_zip, List.length_map, List.length_ofFn]
  rw [assembleQueries_strictPrefix5]

private theorem deployedSetQueries_strictPrefix5
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG) (nu : Fin 11 → Fp) (i : Nat) :
    deployedSetQueries vk instanceCommitment ps
        (chRecord (adaptiveStrictPrefixRecord 5 nu) (fun _ => 0)) i =
      deployedSetQueries vk instanceCommitment ps (chRecord nu (fun _ => 0)) i := by
  unfold deployedSetQueries
  rw [assembleQueries_strictPrefix5]

private theorem adaptiveMemberRepresentations_strictPrefix5
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp) (i : Nat)
    (hi : i < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0))) :
    let hiPrefix : i < deployedX4PairCount vk instanceCommitment ps
        (chRecord (adaptiveStrictPrefixRecord 5 nu) (fun _ => 0)) := by
      rwa [deployedX4PairCount_strictPrefix5]
    (adaptiveMemberRepresentations vk instanceCommitment ps source hcovered
        (adaptiveStrictPrefixRecord 5 nu) i hiPrefix).coeffs =
      (adaptiveMemberRepresentations vk instanceCommitment ps source hcovered nu i hi).coeffs := by
  dsimp only
  have hqueries := deployedSetQueries_strictPrefix5 vk instanceCommitment ps nu i
  cases hqueries
  rfl

private theorem deployedSetsForEval_getD_points_strictPrefix5
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG) (nu : Fin 11 → Fp) (i : Nat)
    (hi : i < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0))) :
    let _hiPrefix : i < deployedX4PairCount vk instanceCommitment ps
        (chRecord (adaptiveStrictPrefixRecord 5 nu) (fun _ => 0)) := by
      rwa [deployedX4PairCount_strictPrefix5]
    ((deployedSetsForEval vk instanceCommitment ps
        (chRecord (adaptiveStrictPrefixRecord 5 nu) (fun _ => 0))).getD
          i ([], [], 0)).1 =
      ((deployedSetsForEval vk instanceCommitment ps
        (chRecord nu (fun _ => 0))).getD i ([], [], 0)).1 := by
  dsimp only
  rw [deployedSetsForEval_getD_points vk instanceCommitment ps
      (chRecord (adaptiveStrictPrefixRecord 5 nu) (fun _ => 0)) (by
        rwa [deployedX4PairCount_strictPrefix5]),
    deployedSetsForEval_getD_points vk instanceCommitment ps
      (chRecord nu (fun _ => 0)) hi, assembleQueries_strictPrefix5]

private theorem adaptiveX1RootPolynomial_strictPrefix
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
      (chRecord nu (fun _ => 0))).getD i ([], [], 0)).1.length) :
    let hiPrefix : i < deployedX4PairCount vk instanceCommitment ps
        (chRecord (adaptiveStrictPrefixRecord 5 nu) (fun _ => 0)) := by
      rwa [deployedX4PairCount_strictPrefix5]
    let idxPrefix : Fin ((deployedSetsForEval vk instanceCommitment ps
        (chRecord (adaptiveStrictPrefixRecord 5 nu) (fun _ => 0))).getD
          i ([], [], 0)).1.length :=
      ⟨idx, by rw [deployedSetsForEval_getD_points_strictPrefix5
        vk instanceCommitment ps nu i hi]; exact idx.isLt⟩
    adaptiveX1RootPolynomial vk instanceCommitment ps source hcovered
        (adaptiveStrictPrefixRecord 5 nu) i hiPrefix idxPrefix =
      adaptiveX1RootPolynomial vk instanceCommitment ps source hcovered nu i hi idx := by
  dsimp only
  have hmembers := adaptiveMemberRepresentations_strictPrefix5 vk instanceCommitment ps
    source hcovered nu i hi
  have hqueries := deployedSetQueries_strictPrefix5 vk instanceCommitment ps nu i
  cases hqueries
  have hpoints := deployedSetsForEval_getD_points_strictPrefix5
    vk instanceCommitment ps nu i hi
  let idxPrefix : Fin ((deployedSetsForEval vk instanceCommitment ps
      (chRecord (adaptiveStrictPrefixRecord 5 nu) (fun _ => 0))).getD
        i ([], [], 0)).1.length :=
    ⟨idx, by rw [hpoints]; exact idx.isLt⟩
  have hnode :
      ((deployedSetsForEval vk instanceCommitment ps
          (chRecord (adaptiveStrictPrefixRecord 5 nu) (fun _ => 0))).getD
            i ([], [], 0)).1[idxPrefix] =
        ((deployedSetsForEval vk instanceCommitment ps
          (chRecord nu (fun _ => 0))).getD i ([], [], 0)).1[idx] := by
    exact getElem_congr hpoints rfl _
  unfold adaptiveX1RootPolynomial
  rw [show (adaptiveX1Batch vk instanceCommitment ps source hcovered
        (adaptiveStrictPrefixRecord 5 nu) i _).coeffs =
      (adaptiveX1Batch vk instanceCommitment ps source hcovered nu i hi).coeffs by
    simpa only [adaptiveX1Batch, AlgebraicColumnRepresentations.toDirectPowerBatch]
      using hmembers, hnode]
  simp only [deployedSetQueries_strictPrefix5]
  rfl

private theorem adaptiveX1AllRootSet_strictPrefix
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp) :
    adaptiveX1AllRootSet vk instanceCommitment ps source hcovered
        (adaptiveStrictPrefixRecord 5 nu) =
      adaptiveX1AllRootSet vk instanceCommitment ps source hcovered nu := by
  ext x
  simp only [adaptiveX1AllRootSet, Set.mem_setOf_eq]
  apply exists_congr
  intro i
  unfold adaptiveX1RootSet
  by_cases hiPrefix : (i : Nat) < deployedX4PairCount vk instanceCommitment ps
      (chRecord (adaptiveStrictPrefixRecord 5 nu) (fun _ => 0))
  · have hi : (i : Nat) < deployedX4PairCount vk instanceCommitment ps
        (chRecord nu (fun _ => 0)) := by
      rwa [← deployedX4PairCount_strictPrefix5]
    simp only [dif_pos hiPrefix, dif_pos hi, Set.mem_setOf_eq]
    have hpoints := deployedSetsForEval_getD_points_strictPrefix5
      vk instanceCommitment ps nu i hi
    constructor
    · rintro ⟨idx, _, hx⟩
      let idxFull : Fin ((deployedSetsForEval vk instanceCommitment ps
          (chRecord nu (fun _ => 0))).getD i ([], [], 0)).1.length :=
        ⟨idx, by rw [← hpoints]; exact idx.isLt⟩
      have hpoly := adaptiveX1RootPolynomial_strictPrefix vk instanceCommitment ps
        source hcovered nu i hi idxFull
      refine ⟨idxFull, Finset.mem_univ _, ?_⟩
      rwa [← hpoly]
    · rintro ⟨idx, _, hx⟩
      let idxPrefix : Fin ((deployedSetsForEval vk instanceCommitment ps
          (chRecord (adaptiveStrictPrefixRecord 5 nu) (fun _ => 0))).getD
            i ([], [], 0)).1.length :=
        ⟨idx, by rw [hpoints]; exact idx.isLt⟩
      have hpoly := adaptiveX1RootPolynomial_strictPrefix vk instanceCommitment ps
        source hcovered nu i hi idx
      refine ⟨idxPrefix, Finset.mem_univ _, ?_⟩
      rwa [hpoly]
  · have hi : ¬ (i : Nat) < deployedX4PairCount vk instanceCommitment ps
        (chRecord nu (fun _ => 0)) := by
      rwa [← deployedX4PairCount_strictPrefix5]
    simp only [dif_neg hiPrefix, dif_neg hi, Set.mem_empty_iff_false]

private theorem assembleQueries_strictPrefix6
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG) (nu : Fin 11 → Fp) :
    assembleQueries vk instanceCommitment ps
        (chRecord (adaptiveStrictPrefixRecord 6 nu) (fun _ => 0)) =
      assembleQueries vk instanceCommitment ps (chRecord nu (fun _ => 0)) := by
  rfl

private theorem deployedX4PairCount_strictPrefix6
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG) (nu : Fin 11 → Fp) :
    deployedX4PairCount vk instanceCommitment ps
        (chRecord (adaptiveStrictPrefixRecord 6 nu) (fun _ => 0)) =
      deployedX4PairCount vk instanceCommitment ps (chRecord nu (fun _ => 0)) := by
  unfold deployedX4PairCount deployedX4Pairs deployedX4Qs
  simp only [List.length_zip, List.length_map, List.length_ofFn]
  rw [assembleQueries_strictPrefix6]

private theorem deployedSetQueries_strictPrefix6
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG) (nu : Fin 11 → Fp) (i : Nat) :
    deployedSetQueries vk instanceCommitment ps
        (chRecord (adaptiveStrictPrefixRecord 6 nu) (fun _ => 0)) i =
      deployedSetQueries vk instanceCommitment ps (chRecord nu (fun _ => 0)) i := by
  unfold deployedSetQueries
  rw [assembleQueries_strictPrefix6]

private theorem adaptiveMemberRepresentations_strictPrefix6
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp) (i : Nat)
    (hi : i < deployedX4PairCount vk instanceCommitment ps
      (chRecord nu (fun _ => 0))) :
    let hiPrefix : i < deployedX4PairCount vk instanceCommitment ps
        (chRecord (adaptiveStrictPrefixRecord 6 nu) (fun _ => 0)) := by
      rwa [deployedX4PairCount_strictPrefix6]
    (adaptiveMemberRepresentations vk instanceCommitment ps source hcovered
        (adaptiveStrictPrefixRecord 6 nu) i hiPrefix).coeffs =
      (adaptiveMemberRepresentations vk instanceCommitment ps source hcovered nu i hi).coeffs := by
  dsimp only
  have hqueries := deployedSetQueries_strictPrefix6 vk instanceCommitment ps nu i
  cases hqueries
  rfl

private theorem adaptiveSetColumn_strictPrefix6_at
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp)
    (j : Fin (deployedX4PairCount vk instanceCommitment ps
      (chRecord (adaptiveStrictPrefixRecord 6 nu) (fun _ => 0)))) :
    adaptiveSetColumn vk instanceCommitment ps source hcovered
        (adaptiveStrictPrefixRecord 6 nu) j =
      adaptiveSetColumn vk instanceCommitment ps source hcovered nu
        ⟨j, by
          have hc := deployedX4PairCount_strictPrefix6 vk instanceCommitment ps nu
          omega⟩ := by
  have hcount := deployedX4PairCount_strictPrefix6 vk instanceCommitment ps nu
  unfold adaptiveSetColumn
  dsimp only
  rw [adaptiveMemberRepresentations_strictPrefix6 vk instanceCommitment ps source
    hcovered nu _ (by omega)]
  have hindex :
      deployedX4PairCount vk instanceCommitment ps
          (chRecord (adaptiveStrictPrefixRecord 6 nu) (fun _ => 0)) - 1 - (j : Nat) =
        deployedX4PairCount vk instanceCommitment ps
          (chRecord nu (fun _ => 0)) - 1 - (j : Nat) := by omega
  have hiIndex :
      deployedX4PairCount vk instanceCommitment ps
          (chRecord (adaptiveStrictPrefixRecord 6 nu) (fun _ => 0)) - 1 - (j : Nat) <
        deployedX4PairCount vk instanceCommitment ps
          (chRecord nu (fun _ => 0)) := by omega
  have hjIndex :
      deployedX4PairCount vk instanceCommitment ps
          (chRecord nu (fun _ => 0)) - 1 - (j : Nat) <
        deployedX4PairCount vk instanceCommitment ps
          (chRecord nu (fun _ => 0)) := by omega
  exact congrArg coeffsToPoly
    (adaptiveMemberRepresentations_powerSum_eq_index vk instanceCommitment ps
      source hcovered nu (nu 5) _ _ hiIndex hjIndex hindex)

private theorem adaptiveSetColumns_strictPrefix6
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp) :
    HEq (fun j : Fin (deployedX4PairCount vk instanceCommitment ps
        (chRecord (adaptiveStrictPrefixRecord 6 nu) (fun _ => 0))) =>
        adaptiveSetColumn vk instanceCommitment ps source hcovered
          (adaptiveStrictPrefixRecord 6 nu) j)
      (fun j : Fin (deployedX4PairCount vk instanceCommitment ps
        (chRecord nu (fun _ => 0))) =>
        adaptiveSetColumn vk instanceCommitment ps source hcovered nu j) := by
  have hcount := deployedX4PairCount_strictPrefix6 vk instanceCommitment ps nu
  apply (Fin.heq_fun_iff hcount).mpr
  intro j
  exact adaptiveSetColumn_strictPrefix6_at vk instanceCommitment ps source hcovered nu j

private theorem deployedSetsForEval_strictPrefix6
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG) (nu : Fin 11 → Fp) :
    deployedSetsForEval vk instanceCommitment ps
        (chRecord (adaptiveStrictPrefixRecord 6 nu) (fun _ => 0)) =
      deployedSetsForEval vk instanceCommitment ps (chRecord nu (fun _ => 0)) := by
  unfold deployedSetsForEval
  rw [assembleQueries_strictPrefix6]
  rfl

private theorem deployedAllPts_strictPrefix6
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG) (nu : Fin 11 → Fp) :
    deployedAllPts vk instanceCommitment ps
        (chRecord (adaptiveStrictPrefixRecord 6 nu) (fun _ => 0)) =
      deployedAllPts vk instanceCommitment ps (chRecord nu (fun _ => 0)) := by
  unfold deployedAllPts deployedSetPts
  rw [assembleQueries_strictPrefix6]

private theorem deployedAlgebraicSetPoints_strictPrefix6
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG) (nu : Fin 11 → Fp) :
    HEq (deployedAlgebraicSetPoints vk instanceCommitment ps
        (chRecord (adaptiveStrictPrefixRecord 6 nu) (fun _ => 0)))
      (deployedAlgebraicSetPoints vk instanceCommitment ps
        (chRecord nu (fun _ => 0))) := by
  have hcount := deployedX4PairCount_strictPrefix6 vk instanceCommitment ps nu
  apply (Fin.heq_fun_iff hcount).mpr
  intro j
  unfold deployedAlgebraicSetPoints deployedSetPts
  rw [assembleQueries_strictPrefix6]
  have hindex :
      deployedX4PairCount vk instanceCommitment ps
          (chRecord (adaptiveStrictPrefixRecord 6 nu) (fun _ => 0)) - 1 - (j : Nat) =
        deployedX4PairCount vk instanceCommitment ps
          (chRecord nu (fun _ => 0)) - 1 - (j : Nat) := by omega
  rw [hindex]

private theorem deployedAlgebraicSetInterpolants_strictPrefix6
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG) (nu : Fin 11 → Fp) :
    HEq (deployedAlgebraicSetInterpolants vk instanceCommitment ps
        (chRecord (adaptiveStrictPrefixRecord 6 nu) (fun _ => 0)))
      (deployedAlgebraicSetInterpolants vk instanceCommitment ps
        (chRecord nu (fun _ => 0))) := by
  have hcount := deployedX4PairCount_strictPrefix6 vk instanceCommitment ps nu
  have hsets := deployedSetsForEval_strictPrefix6 vk instanceCommitment ps nu
  apply (Fin.heq_fun_iff hcount).mpr
  intro j
  unfold deployedAlgebraicSetInterpolants
  rw [hsets]

private theorem adaptiveX2RootSet_strictPrefix
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (source : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps source)
    (nu : Fin 11 → Fp) :
    adaptiveX2RootSet vk instanceCommitment ps source hcovered
        (adaptiveStrictPrefixRecord 6 nu) =
      adaptiveX2RootSet vk instanceCommitment ps source hcovered nu := by
  have hcount := deployedX4PairCount_strictPrefix6 vk instanceCommitment ps nu
  have hall := deployedAllPts_strictPrefix6 vk instanceCommitment ps nu
  have hptsHeq := deployedAlgebraicSetPoints_strictPrefix6 vk instanceCommitment ps nu
  have hcolsHeq := adaptiveSetColumns_strictPrefix6 vk instanceCommitment ps source hcovered nu
  have hrHeq := deployedAlgebraicSetInterpolants_strictPrefix6
    vk instanceCommitment ps nu
  have hpts := (Fin.heq_fun_iff hcount).mp hptsHeq
  have hcols := (Fin.heq_fun_iff hcount).mp hcolsHeq
  have hr := (Fin.heq_fun_iff hcount).mp hrHeq
  unfold adaptiveX2RootSet
  dsimp only
  ext x
  simp only [Set.mem_setOf_eq]
  apply exists_congr
  intro node
  have hpoly := nodeBindingErrorPolynomial_congr_fin hcount _ _ hall
    _ _ _ _ _ _ hpts hcols hr node
  rw [hpoly, hall]

set_option maxHeartbeats 800000 in
private theorem adaptiveX3RootSet_strictPrefix
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hq : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (nu : Fin 11 → Fp) :
    adaptiveX3RootSet vk instanceCommitment ps memberSource qSource hcovered hq
        (adaptiveStrictPrefixRecord 7 nu) =
      adaptiveX3RootSet vk instanceCommitment ps memberSource qSource hcovered hq nu := by
  rfl

set_option maxHeartbeats 800000 in
private theorem adaptiveX4RootSet_strictPrefix
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hq : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (nu : Fin 11 → Fp) :
    adaptiveX4RootSet vk instanceCommitment ps memberSource qSource hcovered hq
        (adaptiveStrictPrefixRecord 8 nu) =
      adaptiveX4RootSet vk instanceCommitment ps memberSource qSource hcovered hq nu := by
  rfl

set_option maxHeartbeats 800000 in
private theorem adaptiveXiRootSet_strictPrefix
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource sSource : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hq : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (hs : CommitmentRefCovered sSource (.point ps.ipaS))
    (nu : Fin 11 → Fp) :
    adaptiveXiRootSet vk instanceCommitment ps memberSource qSource sSource hcovered hq hs
        (adaptiveStrictPrefixRecord 9 nu) =
      adaptiveXiRootSet vk instanceCommitment ps memberSource qSource sSource hcovered hq hs nu := by
  rfl

set_option maxHeartbeats 800000 in
private theorem adaptiveZRootSet_strictPrefix
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (vk : VerifyingKey shape Fp VestaG)
    (instanceCommitment : Fin shape.numProofs → Nat → VestaG)
    (ps : ProofString shape Fp VestaG)
    (memberSource qSource sSource : List (AlgebraicPoint (F := Fp) basis))
    (hcovered : AdaptiveMembersCovered vk instanceCommitment ps memberSource)
    (hq : CommitmentRefCovered qSource (.point ps.multiopenQPrime))
    (hs : CommitmentRefCovered sSource (.point ps.ipaS))
    (nu : Fin 11 → Fp) :
    adaptiveZRootSet vk instanceCommitment ps memberSource qSource sSource hcovered hq hs
        (adaptiveStrictPrefixRecord 10 nu) =
      adaptiveZRootSet vk instanceCommitment ps memberSource qSource sSource hcovered hq hs nu := by
  rfl

set_option maxHeartbeats 800000 in
/-- All six fallback surfaces coincide with the executable witness's deployed root sets after
normalizing the wrapped proof, challenge vector, and retained representation source. -/
theorem OnlineMemberProofData.adaptiveRootSets_eq_witness
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAlgebraicFSFamily shape}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis fixed)
    (pnu : WrappedAlgebraicOutput family basis)
    (witness : DeployedBatchWitness family basis pnu)
    (nu : Fin 11 → Fp) (hp : pnu.1 = data.toAlgebraicWfProof)
    (hnu : wrappedPreIpaReads pnu = nu)
    (hfixed : witness.fixedRepresentations = fixed)
    (hsource : HEq witness.x4Source
      (deployedX4ColumnRepresentationsOfCovered data.toAlgebraicWfProof fixed
        data.membersCovered nu))
    (haggregate : adaptiveAggregateG (family.vk basis) (family.instanceCommitment basis)
      data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
      [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered
      ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩ nu =
        pnu.1.aMulti (wrappedPreIpaReads pnu))
    (haggregateU : adaptiveAggregateU (family.vk basis) (family.instanceCommitment basis)
      data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
      [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered
      ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩ nu =
        pnu.1.multiU (wrappedPreIpaReads pnu)) :
    adaptiveX1AllRootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
        data.adaptivePreX1MembersCovered nu =
      deployedX1AllRootSet (ursOfAugmentedBasis shape.k basis) rfl
        (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
        (wrappedPreIpaRecord pnu) witness.batches ∧
    adaptiveX2RootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
        data.adaptivePreX1MembersCovered nu =
      deployedX2RootSet (ursOfAugmentedBasis shape.k basis) rfl
        (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
        (wrappedPreIpaRecord pnu) witness.batches ∧
    adaptiveX3RootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩ nu =
      deployedX3RootSet (ursOfAugmentedBasis shape.k basis) rfl
        (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
        (wrappedPreIpaRecord pnu) witness.batches ∧
    adaptiveX4RootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩ nu =
      deployedX4RootSet (ursOfAugmentedBasis shape.k basis) rfl
        (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
        (wrappedPreIpaRecord pnu) witness.batches ∧
    adaptiveXiRootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] [data.algebraicProof.ipaS]
        data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
        ⟨data.algebraicProof.ipaS, by simp, rfl⟩ nu =
      szBadSet (ipaShiftXiPolynomial
        (commitGen (evalVector shape.k (wrappedPreIpaRecord pnu).x3)
            (pnu.1.aMulti (wrappedPreIpaReads pnu)) -
          multiopenValue (family.vk basis) (family.instanceCommitment basis)
            pnu.1.proof.1 (wrappedPreIpaRecord pnu))
        (commitGen (evalVector shape.k (wrappedPreIpaRecord pnu).x3) pnu.1.s)) ∧
    adaptiveZRootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] [data.algebraicProof.ipaS]
        data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
        ⟨data.algebraicProof.ipaS, by simp, rfl⟩ nu =
      szBadSet (ipaShiftZPolynomial
        (commitGen (evalVector shape.k (wrappedPreIpaRecord pnu).x3)
            (pnu.1.aMulti (wrappedPreIpaReads pnu)) -
          multiopenValue (family.vk basis) (family.instanceCommitment basis)
            pnu.1.proof.1 (wrappedPreIpaRecord pnu))
        (pnu.1.multiU (wrappedPreIpaReads pnu)) pnu.1.sU
        (commitGen (evalVector shape.k (wrappedPreIpaRecord pnu).x3) pnu.1.s)
        (wrappedPreIpaRecord pnu).xi) := by
  rcases pnu with ⟨p, answers⟩
  dsimp only at hp hnu hfixed hsource haggregate haggregateU ⊢
  subst p
  subst nu
  let qCovered : CommitmentRefCovered [data.algebraicProof.multiopenQPrime]
      (.point data.algebraicProof.erase.multiopenQPrime) :=
    ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
  let sCovered : CommitmentRefCovered [data.algebraicProof.ipaS]
      (.point data.algebraicProof.erase.ipaS) :=
    ⟨data.algebraicProof.ipaS, by simp, rfl⟩
  have hs : witness.x4Source = deployedX4ColumnRepresentationsOfCovered
      data.toAlgebraicWfProof fixed data.membersCovered
        (wrappedPreIpaReads (data.toAlgebraicWfProof, answers)) := eq_of_heq hsource
  have hcols := data.adaptiveX4Columns_eq_deployed
    (wrappedPreIpaReads (data.toAlgebraicWfProof, answers))
  have hcoeffs : witness.batches.x4.coeffs =
      (adaptiveX4ColumnRepresentations (family.vk basis)
        (family.instanceCommitment basis) data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered qCovered
        (wrappedPreIpaReads (data.toAlgebraicWfProof, answers))).coeffs :=
    witness.x4Coeffs.trans
      ((congrArg AlgebraicColumnRepresentations.coeffs hs).trans hcols.1.symm)
  have hu : witness.batches.x4.uComp =
      (adaptiveX4ColumnRepresentations (family.vk basis)
        (family.instanceCommitment basis) data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource fixed)
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered qCovered
        (wrappedPreIpaReads (data.toAlgebraicWfProof, answers))).uComp :=
    witness.x4U.trans
      ((congrArg AlgebraicColumnRepresentations.uComp hs).trans hcols.2.1.symm)
  have hmembers : ∀ i (hi : i < deployedX4PairCount (family.vk basis)
      (family.instanceCommitment basis) data.algebraicProof.erase
      (chRecord (wrappedPreIpaReads (data.toAlgebraicWfProof, answers)) (fun _ => 0))),
      (witness.batches.x1 i hi).coeffs =
        (adaptiveMemberRepresentations (family.vk basis) (family.instanceCommitment basis)
          data.algebraicProof.erase
          (data.algebraicProof.preX1AssemblySource fixed)
          data.adaptivePreX1MembersCovered
          (wrappedPreIpaReads (data.toAlgebraicWfProof, answers)) i hi).coeffs := by
    intro i hi
    have hw := witness.memberCoeffs i hi
    have htransport := deployedMemberRepresentationsOfCovered_congr_source
      data.toAlgebraicWfProof witness.fixedRepresentations fixed
      witness.membersCovered data.membersCovered
      (wrappedPreIpaReads (data.toAlgebraicWfProof, answers)) i hi hfixed
    have hw0 : (witness.batches.x1 i hi).coeffs =
        (deployedMemberRepresentationsOfCovered data.toAlgebraicWfProof
          witness.fixedRepresentations witness.membersCovered
          (wrappedPreIpaReads (data.toAlgebraicWfProof, answers)) i hi).coeffs := by
      simpa only using hw
    have hw' : (witness.batches.x1 i hi).coeffs =
        (deployedMemberRepresentationsOfCovered data.toAlgebraicWfProof
          fixed data.membersCovered
          (wrappedPreIpaReads (data.toAlgebraicWfProof, answers)) i hi).coeffs := by
      exact hw0.trans
        (congrArg AlgebraicColumnRepresentations.coeffs htransport)
    exact hw'.trans ((data.adaptiveMemberRepresentations_eq_deployed
      (wrappedPreIpaReads (data.toAlgebraicWfProof, answers)) i hi).1.symm)
  refine ⟨data.adaptiveX1AllRootSet_eq_deployed _ witness.batches hmembers, ?_⟩
  refine ⟨data.adaptiveX2RootSet_eq_deployed _ qCovered witness.batches hcoeffs, ?_⟩
  refine ⟨data.adaptiveX3RootSet_eq_deployed _ qCovered witness.batches hcoeffs, ?_⟩
  refine ⟨data.adaptiveX4RootSet_eq_deployed _ qCovered witness.batches hcoeffs, ?_⟩
  have hshift := data.adaptiveShiftRootSets_eq
    (wrappedPreIpaReads (data.toAlgebraicWfProof, answers)) qCovered sCovered
    witness.batches.x4 hcoeffs hu haggregate haggregateU
  exact ⟨hshift.1, hshift.2⟩

/-- The six normalized online root surfaces agree with one successful executable batch witness. -/
def AdaptiveRootSetsMatchWitness
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAlgebraicFSFamily shape}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis fixed)
    (pnu : WrappedAlgebraicOutput family basis)
    (witness : DeployedBatchWitness family basis pnu)
    (nu : Fin 11 → Fp) : Prop :=
  adaptiveX1AllRootSet (family.vk basis) (family.instanceCommitment basis)
      data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
      data.adaptivePreX1MembersCovered nu =
    deployedX1AllRootSet (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (wrappedPreIpaRecord pnu) witness.batches ∧
  adaptiveX2RootSet (family.vk basis) (family.instanceCommitment basis)
      data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
      data.adaptivePreX1MembersCovered nu =
    deployedX2RootSet (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (wrappedPreIpaRecord pnu) witness.batches ∧
  adaptiveX3RootSet (family.vk basis) (family.instanceCommitment basis)
      data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
      [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered
      ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩ nu =
    deployedX3RootSet (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (wrappedPreIpaRecord pnu) witness.batches ∧
  adaptiveX4RootSet (family.vk basis) (family.instanceCommitment basis)
      data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
      [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered
      ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩ nu =
    deployedX4RootSet (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (wrappedPreIpaRecord pnu) witness.batches ∧
  adaptiveXiRootSet (family.vk basis) (family.instanceCommitment basis)
      data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
      [data.algebraicProof.multiopenQPrime] [data.algebraicProof.ipaS]
      data.adaptivePreX1MembersCovered
      ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
      ⟨data.algebraicProof.ipaS, by simp, rfl⟩ nu =
    szBadSet (ipaShiftXiPolynomial
      (commitGen (evalVector shape.k (wrappedPreIpaRecord pnu).x3)
          (pnu.1.aMulti (wrappedPreIpaReads pnu)) -
        multiopenValue (family.vk basis) (family.instanceCommitment basis)
          pnu.1.proof.1 (wrappedPreIpaRecord pnu))
      (commitGen (evalVector shape.k (wrappedPreIpaRecord pnu).x3) pnu.1.s)) ∧
  adaptiveZRootSet (family.vk basis) (family.instanceCommitment basis)
      data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
      [data.algebraicProof.multiopenQPrime] [data.algebraicProof.ipaS]
      data.adaptivePreX1MembersCovered
      ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
      ⟨data.algebraicProof.ipaS, by simp, rfl⟩ nu =
    szBadSet (ipaShiftZPolynomial
      (commitGen (evalVector shape.k (wrappedPreIpaRecord pnu).x3)
          (pnu.1.aMulti (wrappedPreIpaReads pnu)) -
        multiopenValue (family.vk basis) (family.instanceCommitment basis)
          pnu.1.proof.1 (wrappedPreIpaRecord pnu))
      (pnu.1.multiU (wrappedPreIpaReads pnu)) pnu.1.sU
      (commitGen (evalVector shape.k (wrappedPreIpaRecord pnu).x3) pnu.1.s)
      (wrappedPreIpaRecord pnu).xi)

def AdaptiveX1RootSetMatchesWitness
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAlgebraicFSFamily shape}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis fixed)
    (pnu : WrappedAlgebraicOutput family basis)
    (witness : DeployedBatchWitness family basis pnu) (nu : Fin 11 → Fp) : Prop :=
  adaptiveX1AllRootSet (family.vk basis) (family.instanceCommitment basis)
      data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
      data.adaptivePreX1MembersCovered nu =
    deployedX1AllRootSet (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (wrappedPreIpaRecord pnu) witness.batches

def AdaptiveX2RootSetMatchesWitness
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAlgebraicFSFamily shape}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis fixed)
    (pnu : WrappedAlgebraicOutput family basis)
    (witness : DeployedBatchWitness family basis pnu) (nu : Fin 11 → Fp) : Prop :=
  adaptiveX2RootSet (family.vk basis) (family.instanceCommitment basis)
      data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
      data.adaptivePreX1MembersCovered nu =
    deployedX2RootSet (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (wrappedPreIpaRecord pnu) witness.batches

def AdaptiveX3RootSetMatchesWitness
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAlgebraicFSFamily shape}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis fixed)
    (pnu : WrappedAlgebraicOutput family basis)
    (witness : DeployedBatchWitness family basis pnu) (nu : Fin 11 → Fp) : Prop :=
  adaptiveX3RootSet (family.vk basis) (family.instanceCommitment basis)
      data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
      [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered
      ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩ nu =
    deployedX3RootSet (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (wrappedPreIpaRecord pnu) witness.batches

def AdaptiveX4RootSetMatchesWitness
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAlgebraicFSFamily shape}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis fixed)
    (pnu : WrappedAlgebraicOutput family basis)
    (witness : DeployedBatchWitness family basis pnu) (nu : Fin 11 → Fp) : Prop :=
  adaptiveX4RootSet (family.vk basis) (family.instanceCommitment basis)
      data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
      [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered
      ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩ nu =
    deployedX4RootSet (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (wrappedPreIpaRecord pnu) witness.batches

def AdaptiveXiRootSetMatchesWitness
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAlgebraicFSFamily shape}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis fixed)
    (pnu : WrappedAlgebraicOutput family basis)
    (_witness : DeployedBatchWitness family basis pnu) (nu : Fin 11 → Fp) : Prop :=
  adaptiveXiRootSet (family.vk basis) (family.instanceCommitment basis)
      data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
      [data.algebraicProof.multiopenQPrime] [data.algebraicProof.ipaS]
      data.adaptivePreX1MembersCovered
      ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
      ⟨data.algebraicProof.ipaS, by simp, rfl⟩ nu =
    szBadSet (ipaShiftXiPolynomial
      (commitGen (evalVector shape.k (wrappedPreIpaRecord pnu).x3)
          (pnu.1.aMulti (wrappedPreIpaReads pnu)) -
        multiopenValue (family.vk basis) (family.instanceCommitment basis)
          pnu.1.proof.1 (wrappedPreIpaRecord pnu))
      (commitGen (evalVector shape.k (wrappedPreIpaRecord pnu).x3) pnu.1.s))

def AdaptiveZRootSetMatchesWitness
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAlgebraicFSFamily shape}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis fixed)
    (pnu : WrappedAlgebraicOutput family basis)
    (_witness : DeployedBatchWitness family basis pnu) (nu : Fin 11 → Fp) : Prop :=
  adaptiveZRootSet (family.vk basis) (family.instanceCommitment basis)
      data.algebraicProof.erase (data.algebraicProof.preX1AssemblySource fixed)
      [data.algebraicProof.multiopenQPrime] [data.algebraicProof.ipaS]
      data.adaptivePreX1MembersCovered
      ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
      ⟨data.algebraicProof.ipaS, by simp, rfl⟩ nu =
    szBadSet (ipaShiftZPolynomial
      (commitGen (evalVector shape.k (wrappedPreIpaRecord pnu).x3)
          (pnu.1.aMulti (wrappedPreIpaReads pnu)) -
        multiopenValue (family.vk basis) (family.instanceCommitment basis)
          pnu.1.proof.1 (wrappedPreIpaRecord pnu))
      (pnu.1.multiU (wrappedPreIpaReads pnu)) pnu.1.sU
      (commitGen (evalVector shape.k (wrappedPreIpaRecord pnu).x3) pnu.1.s)
      (wrappedPreIpaRecord pnu).xi)

/-- Individually opaque equalities between all normalized adaptive and deployed root surfaces. -/
structure AdaptiveRootSetMatchesWitness
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAlgebraicFSFamily shape}
    {fixed : List (AlgebraicPoint (F := Fp) basis)}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis fixed)
    (pnu : WrappedAlgebraicOutput family basis)
    (witness : DeployedBatchWitness family basis pnu) (nu : Fin 11 → Fp) : Prop where
  x1 : AdaptiveX1RootSetMatchesWitness data pnu witness nu
  x2 : AdaptiveX2RootSetMatchesWitness data pnu witness nu
  x3 : AdaptiveX3RootSetMatchesWitness data pnu witness nu
  x4 : AdaptiveX4RootSetMatchesWitness data pnu witness nu
  xi : AdaptiveXiRootSetMatchesWitness data pnu witness nu
  z : AdaptiveZRootSetMatchesWitness data pnu witness nu

/-- None of the six actual adaptive deployed-root events occurs on this oracle run. -/
def ComputedAdaptiveOnlineAGMFSFamily.AdaptiveAllRootGood
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) : Prop :=
  let data := (family.adversary basis).run O
  ∀ i : Fin 6,
    let n := deployedRootChallengeIndex i
    O (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof n) ∉
      adaptiveFinalRootBad family basis n data
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof n) O

/-- Shifted aggregate equality obtained from verifier acceptance and absence of the executable IPA
binding attack. -/
def ComputedAdaptiveOnlineAGMFSFamily.AdaptiveShiftedValue
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) : Prop :=
  let pnu := (wrappedAdversary family.toFamily basis).run O
  let nu := wrappedPreIpaReads pnu
  let ch := wrappedPreIpaRecord pnu
  ch.z ≠ 0 ∧
    commitGen (evalVector shape.k ch.x3) (pnu.1.aMulti nu) =
      multiopenValue (family.vk basis) (family.instanceCommitment basis)
        pnu.1.proof.1 ch +
        ch.z⁻¹ * (pnu.1.multiU nu + ch.xi * pnu.1.sU) -
          ch.xi * commitGen (evalVector shape.k ch.x3) pnu.1.s

def adaptiveOraclePreIpaReads
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAdaptiveOnlineAGMFSFamily shape}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) : Fin 11 → Fp :=
  fun n => O (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof n)

set_option maxHeartbeats 800000 in
private theorem adaptiveFinalRootBad_five_full
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAdaptiveOnlineAGMFSFamily shape}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    adaptiveFinalRootBad family basis 5 data
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof 5) O =
      adaptiveX1AllRootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
        data.adaptivePreX1MembersCovered (adaptiveOraclePreIpaReads data O) := by
  rw [data.adaptiveFinalRootBad_five O]
  change adaptiveX1AllRootSet _ _ _ _ _
      (adaptiveStrictPrefixRecord 5 (adaptiveOraclePreIpaReads data O)) = _
  exact adaptiveX1AllRootSet_strictPrefix _ _ _ _ _ _

set_option maxHeartbeats 800000 in
private theorem adaptiveFinalRootBad_six_full
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAdaptiveOnlineAGMFSFamily shape}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    adaptiveFinalRootBad family basis 6 data
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof 6) O =
      adaptiveX2RootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
        data.adaptivePreX1MembersCovered (adaptiveOraclePreIpaReads data O) := by
  rw [data.adaptiveFinalRootBad_six O]
  change adaptiveX2RootSet _ _ _ _ _
      (adaptiveStrictPrefixRecord 6 (adaptiveOraclePreIpaReads data O)) = _
  exact adaptiveX2RootSet_strictPrefix _ _ _ _ _ _

set_option maxHeartbeats 800000 in
private theorem adaptiveFinalRootBad_seven_full
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAdaptiveOnlineAGMFSFamily shape}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    adaptiveFinalRootBad family basis 7 data
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof 7) O =
      adaptiveX3RootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
        (adaptiveOraclePreIpaReads data O) := by
  rw [data.adaptiveFinalRootBad_seven O]
  change adaptiveX3RootSet _ _ _ _ _ _ _
      (adaptiveStrictPrefixRecord 7 (adaptiveOraclePreIpaReads data O)) = _
  exact adaptiveX3RootSet_strictPrefix _ _ _ _ _ _ _ _

set_option maxHeartbeats 800000 in
private theorem adaptiveFinalRootBad_eight_full
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAdaptiveOnlineAGMFSFamily shape}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    adaptiveFinalRootBad family basis 8 data
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof 8) O =
      adaptiveX4RootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
        [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
        (adaptiveOraclePreIpaReads data O) := by
  rw [data.adaptiveFinalRootBad_eight O]
  change adaptiveX4RootSet _ _ _ _ _ _ _
      (adaptiveStrictPrefixRecord 8 (adaptiveOraclePreIpaReads data O)) = _
  exact adaptiveX4RootSet_strictPrefix _ _ _ _ _ _ _ _

set_option maxHeartbeats 800000 in
private theorem adaptiveFinalRootBad_nine_full
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAdaptiveOnlineAGMFSFamily shape}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    adaptiveFinalRootBad family basis 9 data
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof 9) O =
      adaptiveXiRootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
        [data.algebraicProof.multiopenQPrime] [data.algebraicProof.ipaS]
        data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
        ⟨data.algebraicProof.ipaS, by simp, rfl⟩
        (adaptiveOraclePreIpaReads data O) := by
  rw [data.adaptiveFinalRootBad_nine O]
  change adaptiveXiRootSet _ _ _ _ _ _ _ _ _
      (adaptiveStrictPrefixRecord 9 (adaptiveOraclePreIpaReads data O)) = _
  exact adaptiveXiRootSet_strictPrefix _ _ _ _ _ _ _ _ _ _

set_option maxHeartbeats 800000 in
private theorem adaptiveFinalRootBad_ten_full
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {family : ComputedAdaptiveOnlineAGMFSFamily shape}
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    adaptiveFinalRootBad family basis 10 data
        (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof 10) O =
      adaptiveZRootSet (family.vk basis) (family.instanceCommitment basis)
        data.algebraicProof.erase
        (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
        [data.algebraicProof.multiopenQPrime] [data.algebraicProof.ipaS]
        data.adaptivePreX1MembersCovered
        ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩
        ⟨data.algebraicProof.ipaS, by simp, rfl⟩
        (adaptiveOraclePreIpaReads data O) := by
  rw [data.adaptiveFinalRootBad_ten O]
  change adaptiveZRootSet _ _ _ _ _ _ _ _ _
      (adaptiveStrictPrefixRecord 10 (adaptiveOraclePreIpaReads data O)) = _
  exact adaptiveZRootSet_strictPrefix _ _ _ _ _ _ _ _ _ _

def ComputedAdaptiveOnlineAGMFSFamily.AdaptiveDeployedX1Good
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (witness : DeployedBatchWitness family.toFamily basis
      ((wrappedAdversary family.toFamily basis).run O)) : Prop :=
  let pnu := (wrappedAdversary family.toFamily basis).run O
  let ch := wrappedPreIpaRecord pnu
  ch.x1 ∉ deployedX1AllRootSet (ursOfAugmentedBasis shape.k basis) rfl
    (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches

def ComputedAdaptiveOnlineAGMFSFamily.AdaptiveDeployedX2Good
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (witness : DeployedBatchWitness family.toFamily basis
      ((wrappedAdversary family.toFamily basis).run O)) : Prop :=
  let pnu := (wrappedAdversary family.toFamily basis).run O
  let ch := wrappedPreIpaRecord pnu
  ch.x2 ∉ deployedX2RootSet (ursOfAugmentedBasis shape.k basis) rfl
    (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches

def ComputedAdaptiveOnlineAGMFSFamily.AdaptiveDeployedX3Good
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (witness : DeployedBatchWitness family.toFamily basis
      ((wrappedAdversary family.toFamily basis).run O)) : Prop :=
  let pnu := (wrappedAdversary family.toFamily basis).run O
  let ch := wrappedPreIpaRecord pnu
  ch.x3 ∉ deployedX3RootSet (ursOfAugmentedBasis shape.k basis) rfl
    (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches

def ComputedAdaptiveOnlineAGMFSFamily.AdaptiveDeployedX4Good
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (witness : DeployedBatchWitness family.toFamily basis
      ((wrappedAdversary family.toFamily basis).run O)) : Prop :=
  let pnu := (wrappedAdversary family.toFamily basis).run O
  let ch := wrappedPreIpaRecord pnu
  ch.x4 ∉ deployedX4RootSet (ursOfAugmentedBasis shape.k basis) rfl
    (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches

def ComputedAdaptiveOnlineAGMFSFamily.AdaptiveDeployedXiGood
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) : Prop :=
  let pnu := (wrappedAdversary family.toFamily basis).run O
  let ch := wrappedPreIpaRecord pnu
  ch.xi ∉ szBadSet (ipaShiftXiPolynomial
    (commitGen (evalVector shape.k ch.x3) (pnu.1.aMulti (wrappedPreIpaReads pnu)) -
      multiopenValue (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1 ch)
    (commitGen (evalVector shape.k ch.x3) pnu.1.s))

def ComputedAdaptiveOnlineAGMFSFamily.AdaptiveDeployedZGood
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) : Prop :=
  let pnu := (wrappedAdversary family.toFamily basis).run O
  let ch := wrappedPreIpaRecord pnu
  ch.z ∉ szBadSet (ipaShiftZPolynomial
    (commitGen (evalVector shape.k ch.x3) (pnu.1.aMulti (wrappedPreIpaReads pnu)) -
      multiopenValue (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1 ch)
    (pnu.1.multiU (wrappedPreIpaReads pnu)) pnu.1.sU
    (commitGen (evalVector shape.k ch.x3) pnu.1.s) ch.xi)

/-- The six explicit deployed sets are good for the successful adaptive batch witness. -/
structure ComputedAdaptiveOnlineAGMFSFamily.AdaptiveDeployedGoodRoots
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (witness : DeployedBatchWitness family.toFamily basis
      ((wrappedAdversary family.toFamily basis).run O)) : Prop where
  x1 : family.AdaptiveDeployedX1Good basis O witness
  x2 : family.AdaptiveDeployedX2Good basis O witness
  x3 : family.AdaptiveDeployedX3Good basis O witness
  x4 : family.AdaptiveDeployedX4Good basis O witness
  xi : family.AdaptiveDeployedXiGood basis O
  z : family.AdaptiveDeployedZGood basis O

set_option maxHeartbeats 3200000 in
/-- A successful executable outcome identifies all six normalized adaptive surfaces with the
deployed witness surfaces. -/
theorem ComputedAdaptiveOnlineAGMFSFamily.adaptiveRootSetsMatchWitness_of_outcome
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (witness : DeployedBatchWitness family.toFamily basis
      ((wrappedAdversary family.toFamily basis).run O))
    (hout : deployedRootOutcomeOfCovered family.toOnlineMemberFamily basis O =
      PSum.inl witness) :
    let data := (family.adversary basis).run O
    let pnu := (wrappedAdversary family.toFamily basis).run O
    let nu : Fin 11 → Fp := adaptiveOraclePreIpaReads data O
    AdaptiveRootSetMatchesWitness data pnu witness nu := by
  dsimp only
  let data := (family.adversary basis).run O
  let pnu := (wrappedAdversary family.toFamily basis).run O
  let nu : Fin 11 → Fp := adaptiveOraclePreIpaReads data O
  have hp : pnu.1 = data.toAlgebraicWfProof :=
    (wrappedAdversary_run_fst family.toFamily basis O).trans
      (family.toFamily_runProof basis O)
  have hreads : runReads family.toFamily basis O = nu := by
    simpa only [nu, adaptiveOraclePreIpaReads, data] using
      family.toFamily_runReads basis O
  have hnu : wrappedPreIpaReads pnu = nu :=
    (wrappedPreIpaReads_run family.toFamily basis O).trans hreads
  have hfixed : witness.fixedRepresentations = family.fixedRepresentations basis :=
    deployedRootOutcomeOfCovered_fixedRepresentations family.toOnlineMemberFamily
      basis O witness hout
  have hsource0 := deployedRootOutcomeOfCovered_x4Source family.toOnlineMemberFamily
    basis O witness hout
  have hsource : HEq witness.x4Source
      (deployedX4ColumnRepresentationsOfCovered data.toAlgebraicWfProof
        (family.fixedRepresentations basis) data.membersCovered nu) :=
    HEq.trans hsource0
      (deployedX4ColumnRepresentationsOfCovered_heq _ _ _ _ _ _ _
        (family.toFamily_runProof basis O) hreads)
  have haggregate := family.adaptiveWitnessAggregates basis O witness hout
  have haggregateG : adaptiveAggregateG (family.toFamily.vk basis)
      (family.toFamily.instanceCommitment basis) data.algebraicProof.erase
      (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
      [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered
      ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩ nu =
        pnu.1.aMulti (wrappedPreIpaReads pnu) := by
    rw [hp, hnu]
    simpa only [data, nu, adaptiveOraclePreIpaReads] using haggregate.1
  have haggregateU : adaptiveAggregateU (family.toFamily.vk basis)
      (family.toFamily.instanceCommitment basis) data.algebraicProof.erase
      (data.algebraicProof.preX1AssemblySource (family.fixedRepresentations basis))
      [data.algebraicProof.multiopenQPrime] data.adaptivePreX1MembersCovered
      ⟨data.algebraicProof.multiopenQPrime, by simp, rfl⟩ nu =
        pnu.1.multiU (wrappedPreIpaReads pnu) := by
    rw [hp, hnu]
    simpa only [data, nu, adaptiveOraclePreIpaReads] using haggregate.2
  have hroots := @OnlineMemberProofData.adaptiveRootSets_eq_witness shape basis
    family.toFamily (family.fixedRepresentations basis) data pnu witness nu hp hnu hfixed hsource
      haggregateG haggregateU
  rcases hroots with ⟨hr1, hr2, hr3, hr4, hrXi, hrZ⟩
  exact { x1 := hr1, x2 := hr2, x3 := hr3, x4 := hr4, xi := hrXi, z := hrZ }

set_option maxHeartbeats 3200000 in
/-- Avoiding the six actual adaptive events yields all six good deployed-root facts once the
successful witness surfaces have been normalized. -/
theorem ComputedAdaptiveOnlineAGMFSFamily.adaptiveDeployedGoodRoots_of_matches
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (witness : DeployedBatchWitness family.toFamily basis
      ((wrappedAdversary family.toFamily basis).run O))
    (hmatches :
      let data := (family.adversary basis).run O
      let pnu := (wrappedAdversary family.toFamily basis).run O
      let nu : Fin 11 → Fp := adaptiveOraclePreIpaReads data O
      AdaptiveRootSetMatchesWitness data pnu witness nu)
    (hgood : family.AdaptiveAllRootGood basis O) :
    family.AdaptiveDeployedGoodRoots basis O witness := by
  let data := (family.adversary basis).run O
  let pnu := (wrappedAdversary family.toFamily basis).run O
  let nu : Fin 11 → Fp := adaptiveOraclePreIpaReads data O
  let ch := wrappedPreIpaRecord pnu
  have hreads : runReads family.toFamily basis O = nu := by
    simpa only [nu, adaptiveOraclePreIpaReads, data] using
      family.toFamily_runReads basis O
  have hnu : wrappedPreIpaReads pnu = nu :=
    (wrappedPreIpaReads_run family.toFamily basis O).trans hreads
  change AdaptiveRootSetMatchesWitness data pnu witness nu at hmatches
  have hr1 := hmatches.x1
  have hr2 := hmatches.x2
  have hr3 := hmatches.x3
  have hr4 := hmatches.x4
  have hrXi := hmatches.xi
  have hrZ := hmatches.z
  unfold AdaptiveX1RootSetMatchesWitness at hr1
  unfold AdaptiveX2RootSetMatchesWitness at hr2
  unfold AdaptiveX3RootSetMatchesWitness at hr3
  unfold AdaptiveX4RootSetMatchesWitness at hr4
  unfold AdaptiveXiRootSetMatchesWitness at hrXi
  unfold AdaptiveZRootSetMatchesWitness at hrZ
  unfold ComputedAdaptiveOnlineAGMFSFamily.AdaptiveAllRootGood at hgood
  dsimp only at hgood
  have h5 := hgood (5 : Fin 6)
  have h6 := hgood (4 : Fin 6)
  have h7 := hgood (3 : Fin 6)
  have h8 := hgood (2 : Fin 6)
  have h9 := hgood (0 : Fin 6)
  have h10 := hgood (1 : Fin 6)
  change nu 5 ∉ adaptiveFinalRootBad family basis 5 data
    (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof 5) O at h5
  change nu 6 ∉ adaptiveFinalRootBad family basis 6 data
    (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof 6) O at h6
  change nu 7 ∉ adaptiveFinalRootBad family basis 7 data
    (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof 7) O at h7
  change nu 8 ∉ adaptiveFinalRootBad family basis 8 data
    (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof 8) O at h8
  change nu 9 ∉ adaptiveFinalRootBad family basis 9 data
    (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof 9) O at h9
  change nu 10 ∉ adaptiveFinalRootBad family basis 10 data
    (algebraicFullPrefixesPre family.init data.toAlgebraicWfProof 10) O at h10
  rw [adaptiveFinalRootBad_five_full data O] at h5
  rw [adaptiveFinalRootBad_six_full data O] at h6
  rw [adaptiveFinalRootBad_seven_full data O] at h7
  rw [adaptiveFinalRootBad_eight_full data O] at h8
  rw [adaptiveFinalRootBad_nine_full data O] at h9
  rw [adaptiveFinalRootBad_ten_full data O] at h10
  change nu 5 ∉ adaptiveX1AllRootSet (family.toFamily.vk basis)
    (family.toFamily.instanceCommitment basis) _ _ _ nu at h5
  change nu 6 ∉ adaptiveX2RootSet (family.toFamily.vk basis)
    (family.toFamily.instanceCommitment basis) _ _ _ nu at h6
  change nu 7 ∉ adaptiveX3RootSet (family.toFamily.vk basis)
    (family.toFamily.instanceCommitment basis) _ _ _ _ _ nu at h7
  change nu 8 ∉ adaptiveX4RootSet (family.toFamily.vk basis)
    (family.toFamily.instanceCommitment basis) _ _ _ _ _ nu at h8
  change nu 9 ∉ adaptiveXiRootSet (family.toFamily.vk basis)
    (family.toFamily.instanceCommitment basis) _ _ _ _ _ _ _ nu at h9
  change nu 10 ∉ adaptiveZRootSet (family.toFamily.vk basis)
    (family.toFamily.instanceCommitment basis) _ _ _ _ _ _ _ nu at h10
  rw [hr1] at h5
  rw [hr2] at h6
  rw [hr3] at h7
  rw [hr4] at h8
  rw [hrXi] at h9
  rw [hrZ] at h10
  rw [← hnu] at h5 h6 h7 h8 h9 h10
  refine { x1 := ?_, x2 := ?_, x3 := ?_, x4 := ?_, xi := ?_, z := ?_ }
  · simpa [ComputedAdaptiveOnlineAGMFSFamily.AdaptiveDeployedX1Good, ch, pnu,
      wrappedPreIpaRecord, chRecord] using h5
  · simpa [ComputedAdaptiveOnlineAGMFSFamily.AdaptiveDeployedX2Good, ch, pnu,
      wrappedPreIpaRecord, chRecord] using h6
  · simpa [ComputedAdaptiveOnlineAGMFSFamily.AdaptiveDeployedX3Good, ch, pnu,
      wrappedPreIpaRecord, chRecord] using h7
  · simpa [ComputedAdaptiveOnlineAGMFSFamily.AdaptiveDeployedX4Good, ch, pnu,
      wrappedPreIpaRecord, chRecord] using h8
  · simpa [ComputedAdaptiveOnlineAGMFSFamily.AdaptiveDeployedXiGood, ch, pnu,
      wrappedPreIpaRecord, chRecord] using h9
  · simpa [ComputedAdaptiveOnlineAGMFSFamily.AdaptiveDeployedZGood, ch, pnu,
      wrappedPreIpaRecord, chRecord] using h10

set_option maxHeartbeats 800000 in
/-- Avoiding the six actual adaptive events yields all six good deployed-root facts. -/
theorem ComputedAdaptiveOnlineAGMFSFamily.adaptiveDeployedGoodRoots_of_goodRoots
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (witness : DeployedBatchWitness family.toFamily basis
      ((wrappedAdversary family.toFamily basis).run O))
    (hout : deployedRootOutcomeOfCovered family.toOnlineMemberFamily basis O =
      PSum.inl witness)
    (hgood : family.AdaptiveAllRootGood basis O) :
    family.AdaptiveDeployedGoodRoots basis O witness :=
  family.adaptiveDeployedGoodRoots_of_matches basis O witness
    (family.adaptiveRootSetsMatchWitness_of_outcome basis O witness hout) hgood

set_option maxHeartbeats 800000 in
/-- The shifted verifier equality and the packaged deployed good roots produce the existing
deployed algebraic decode. -/
def ComputedAdaptiveOnlineAGMFSFamily.adaptiveAlgebraicDecode_of_deployedGoodRoots
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (witness : DeployedBatchWitness family.toFamily basis
      ((wrappedAdversary family.toFamily basis).run O))
    (hgood : family.AdaptiveDeployedGoodRoots basis O witness)
    (hshifted : family.AdaptiveShiftedValue basis O) :
    let pnu := (wrappedAdversary family.toFamily basis).run O
    DeployedAlgebraicDecode shape (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (wrappedPreIpaRecord pnu) (pnu.1.aMulti (wrappedPreIpaReads pnu))
      (pnu.1.multiU (wrappedPreIpaReads pnu))
      (pnu.1.multiBlind (wrappedPreIpaReads pnu)) := by
  dsimp only
  let pnu := (wrappedAdversary family.toFamily basis).run O
  let ch := wrappedPreIpaRecord pnu
  have hgood1All : ch.x1 ∉ deployedX1AllRootSet
      (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches := by
    simpa [ComputedAdaptiveOnlineAGMFSFamily.AdaptiveDeployedX1Good, ch, pnu] using hgood.x1
  have hgood2 : ch.x2 ∉ deployedX2RootSet
      (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches := by
    simpa [ComputedAdaptiveOnlineAGMFSFamily.AdaptiveDeployedX2Good, ch, pnu] using hgood.x2
  have hgood3 : ch.x3 ∉ deployedX3RootSet
      (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches := by
    simpa [ComputedAdaptiveOnlineAGMFSFamily.AdaptiveDeployedX3Good, ch, pnu] using hgood.x3
  have hgood4 : ch.x4 ∉ deployedX4RootSet
      (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches := by
    simpa [ComputedAdaptiveOnlineAGMFSFamily.AdaptiveDeployedX4Good, ch, pnu] using hgood.x4
  have hgoodXi : ch.xi ∉ szBadSet (ipaShiftXiPolynomial
      (commitGen (evalVector shape.k ch.x3) (pnu.1.aMulti (wrappedPreIpaReads pnu)) -
        multiopenValue (family.vk basis) (family.instanceCommitment basis)
          pnu.1.proof.1 ch)
      (commitGen (evalVector shape.k ch.x3) pnu.1.s)) := by
    simpa [ComputedAdaptiveOnlineAGMFSFamily.AdaptiveDeployedXiGood, ch, pnu] using hgood.xi
  have hgoodZ : ch.z ∉ szBadSet (ipaShiftZPolynomial
      (commitGen (evalVector shape.k ch.x3) (pnu.1.aMulti (wrappedPreIpaReads pnu)) -
        multiopenValue (family.vk basis) (family.instanceCommitment basis)
          pnu.1.proof.1 ch)
      (pnu.1.multiU (wrappedPreIpaReads pnu)) pnu.1.sU
      (commitGen (evalVector shape.k ch.x3) pnu.1.s) ch.xi) := by
    simpa [ComputedAdaptiveOnlineAGMFSFamily.AdaptiveDeployedZGood, ch, pnu] using hgood.z
  unfold ComputedAdaptiveOnlineAGMFSFamily.AdaptiveShiftedValue at hshifted
  dsimp only at hshifted
  have hvalue : commitGen (evalVector shape.k ch.x3)
      (pnu.1.aMulti (wrappedPreIpaReads pnu)) =
      multiopenValue (family.vk basis) (family.instanceCommitment basis)
        pnu.1.proof.1 ch :=
    rawValue_of_shiftedValue_of_good _ _ _ _ _ _ _ hshifted.1 hshifted.2 hgoodXi hgoodZ
  have hgood1 := not_mem_deployedX1RootSet_of_not_mem_all
    (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches hgood1All
  exact deployedAlgebraicDecode_of_good_roots
    (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
      (family.instanceCommitment basis) pnu.1.proof.1 ch witness.batches
      hvalue hgood4 hgood3 hgood2 hgood1

set_option maxHeartbeats 800000 in
/-- Avoiding the six actual adaptive root events turns the successful executable batch outcome and
the shifted verifier equality into the existing deployed algebraic decode. -/
def ComputedAdaptiveOnlineAGMFSFamily.adaptiveAlgebraicDecode_of_goodRoots
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (witness : DeployedBatchWitness family.toFamily basis
      ((wrappedAdversary family.toFamily basis).run O))
    (hout : deployedRootOutcomeOfCovered family.toOnlineMemberFamily basis O =
      PSum.inl witness)
    (hgood : family.AdaptiveAllRootGood basis O)
    (hshifted : family.AdaptiveShiftedValue basis O) :
    let pnu := (wrappedAdversary family.toFamily basis).run O
    DeployedAlgebraicDecode shape (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis) pnu.1.proof.1
      (wrappedPreIpaRecord pnu) (pnu.1.aMulti (wrappedPreIpaReads pnu))
      (pnu.1.multiU (wrappedPreIpaReads pnu))
      (pnu.1.multiBlind (wrappedPreIpaReads pnu)) := by
  exact family.adaptiveAlgebraicDecode_of_deployedGoodRoots basis O witness
    (family.adaptiveDeployedGoodRoots_of_goodRoots basis O witness hout hgood) hshifted

end Zcash.Snark
