import Zcash.Snark.Soundness.ZeroData
import Zcash.Snark.Soundness.AGM.OnlineMembers
import Zcash.Snark.Soundness.AGM.PinnedRootWitness
import Zcash.Snark.Soundness.AGM.DirectX4Columns

/-!
# The constant zero-data prover family, at any shape

`zeroOnlineMemberFamily` is the constant prover at an *arbitrary* shape, over any verifying key
whose two group-valued commitment families are zero.  The `ZeroData` keystone makes its multiopen
representation obligation `0 = 0`, and the zero-data invariant covers every routed member by one
zero source point.  Instantiated at the captured key's scalar metadata it gives a captured-shape
prover with live IPA rounds; `PinnedRootWitness` builds the same thing at the witness shape, where
every assembly list is empty.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm)

local instance vestaInhabitedZeroFamily : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

section Points

variable (basis : AugmentedIndex (2 ^ shape.k) → VestaG)

/-- The zero algebraic point over any basis. -/
def zeroAlgebraicPoint : AlgebraicPoint (F := Fp) basis :=
  ⟨0, ⟨0, by simp [representationEval]⟩⟩

@[simp] theorem zeroAlgebraicPoint_point : (zeroAlgebraicPoint basis).point = 0 := rfl

@[simp] theorem zeroAlgebraicPoint_coeffs (i : AugmentedIndex (2 ^ shape.k)) :
    (zeroAlgebraicPoint basis).coeffs i = 0 := rfl

/-- The zero algebraic proof string at any shape: every group element is the zero point with the
zero representation, and the permutation `lastEval` options follow the deployed schedule. -/
def zeroAlgebraicProofString : AlgebraicProofString shape basis :=
  { adviceCommitments := fun _ _ => zeroAlgebraicPoint basis,
    lookupPermutedInput := fun _ _ => zeroAlgebraicPoint basis,
    lookupPermutedTable := fun _ _ => zeroAlgebraicPoint basis,
    permutationProduct := fun _ _ => zeroAlgebraicPoint basis,
    lookupProduct := fun _ _ => zeroAlgebraicPoint basis,
    vanishingRandom := zeroAlgebraicPoint basis,
    hPieces := fun _ => zeroAlgebraicPoint basis,
    instanceEvals := fun _ _ => 0, adviceEvals := fun _ _ => 0,
    fixedEvals := fun _ => 0, vanishingRandomEval := 0,
    permutationCommonEvals := fun _ => 0,
    permutationSetEvals := fun _ s =>
      ⟨0, 0, if (s : ℕ) + 1 < shape.numPermutationSets then some 0 else none⟩,
    lookupEvals := fun _ _ => ⟨0, 0, 0, 0, 0⟩,
    multiopenQPrime := zeroAlgebraicPoint basis,
    multiopenU := fun _ => 0,
    ipaS := zeroAlgebraicPoint basis,
    ipaRounds := fun _ => (zeroAlgebraicPoint basis, zeroAlgebraicPoint basis),
    ipaC := 0, ipaF := 0 }

/-- Erasing the zero algebraic proof string gives the zero proof string. -/
theorem zeroAlgebraicProofString_erase :
    (zeroAlgebraicProofString basis).erase = zeroProofString shape Fp VestaG := rfl

/-- The zero proof string is well-formed: its permutation `lastEval` options match the deployed
schedule by construction. -/
theorem zeroProofString_wellFormed :
    PsWellFormed (zeroProofString shape Fp VestaG) := by
  intro p s
  by_cases h : (s : ℕ) + 1 < shape.numPermutationSets <;>
    simp [zeroProofString, h]

/-- Every point of the zero proof's pre-`x₁` assembly source over the zero fixed list is the zero
algebraic point. -/
theorem zeroAlgebraicProofString_source_eq
    {ap : AlgebraicPoint (F := Fp) basis}
    (hap : ap ∈ (zeroAlgebraicProofString basis).preX1AssemblySource
      [zeroAlgebraicPoint basis]) :
    ap = zeroAlgebraicPoint basis := by
  simp only [AlgebraicProofString.preX1AssemblySource, AlgebraicProofString.preX1Points,
    List.append_assoc, List.mem_append, List.mem_flatten, List.mem_singleton] at hap
  rcases hap with (⟨l, hl, hap⟩ | ⟨l, hl, hap⟩ | ⟨l, hl, hap⟩ | ⟨l, hl, hap⟩ | ⟨l, hl, hap⟩ |
      hap | hap | hap) <;>
    first
    | (obtain ⟨p, hp⟩ := List.mem_ofFn.mp hl
       rw [← hp] at hap
       obtain ⟨i, hi⟩ := List.mem_ofFn.mp hap
       exact hi.symm)
    | exact hap
    | (obtain ⟨i, hi⟩ := List.mem_ofFn.mp hap
       exact hi.symm)

/-- The zero point occurs in the pre-`x₁` assembly source over the zero fixed list. -/
theorem zeroAlgebraicPoint_mem_preX1Source :
    zeroAlgebraicPoint basis ∈
      (zeroAlgebraicProofString basis).preX1AssemblySource [zeroAlgebraicPoint basis] := by
  simp [AlgebraicProofString.preX1AssemblySource]

/-- Every point of the complete multiopen assembly source is the zero algebraic point. -/
theorem zeroAlgebraicProofString_multiopenSource_eq
    {ap : AlgebraicPoint (F := Fp) basis}
    (hap : ap ∈ (zeroAlgebraicProofString basis).multiopenAssemblySource
      [zeroAlgebraicPoint basis]) :
    ap = zeroAlgebraicPoint basis := by
  rcases List.mem_append.mp hap with h | h
  · exact zeroAlgebraicProofString_source_eq basis h
  · exact List.mem_singleton.mp h

end Points

section Family

/-- The assembled multiopen MSM of the zero data is zero-data, over any key with zero group
commitment families. -/
theorem multiopenMsm_zeroData (vkS : VerifyingKey shape Fp VestaG)
    (hfixed : ∀ i, vkS.fixedCommitment i = 0)
    (hperm : ∀ i, vkS.permutationCommonCommitment i = 0) (ν : Fin 11 → Fp) :
    MsmZeroData (multiopenMsm vkS (fun _ _ => 0) (zeroProofString shape Fp VestaG)
      (chRecord ν (fun _ => 0))) := by
  unfold multiopenMsm
  exact assembledMsm_zeroData rfl vkS hfixed hperm _ (fun _ _ => rfl) _

/-- Every point the zero data's multiopen MSM appends is covered by the assembly source. -/
theorem zeroMultiopenAssemblyCovered (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vkS : VerifyingKey shape Fp VestaG)
    (hfixed : ∀ i, vkS.fixedCommitment i = 0)
    (hperm : ∀ i, vkS.permutationCommonCommitment i = 0) :
    MultiopenAssemblyCovered vkS (fun _ _ => 0) (zeroAlgebraicProofString basis)
      [zeroAlgebraicPoint basis] := by
  intro ν pr hpr
  refine ⟨zeroAlgebraicPoint basis, ?_, ?_⟩
  · exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  · rw [(multiopenMsm_zeroData vkS hfixed hperm ν).2.2.2 pr hpr]
    rfl

/-- **The zero well-formed algebraic proof, at any shape.**  Its multiopen coordinates are the
canonical online lookups into the zero source, so the representation obligation is discharged by
the zero-data keystone rather than a degenerate-shape collapse. -/
def zeroWfProof (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vkS : VerifyingKey shape Fp VestaG)
    (hfixed : ∀ i, vkS.fixedCommitment i = 0)
    (hperm : ∀ i, vkS.permutationCommonCommitment i = 0) :
    AlgebraicWfProof basis vkS (fun _ _ => 0) :=
  AlgebraicWfProof.ofRepresented (zeroAlgebraicProofString basis)
    zeroProofString_wellFormed
    (fun ν => RepresentedMultiopen.ofCoveredList vkS (fun _ _ => 0)
      ((zeroAlgebraicProofString basis).erase) ν
      ((zeroAlgebraicProofString basis).multiopenAssemblySource [zeroAlgebraicPoint basis])
      (zeroMultiopenAssemblyCovered basis vkS hfixed hperm ν))

/-- The zero proof's coordinates are canonical over the zero fixed list. -/
theorem zeroWfProof_canonical (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vkS : VerifyingKey shape Fp VestaG)
    (hfixed : ∀ i, vkS.fixedCommitment i = 0)
    (hperm : ∀ i, vkS.permutationCommonCommitment i = 0) :
    CanonicalOnlineMultiopenCoordinates (zeroWfProof basis vkS hfixed hperm)
      [zeroAlgebraicPoint basis] :=
  { covered := zeroMultiopenAssemblyCovered basis vkS hfixed hperm
    aMulti_eq := fun _ => rfl
    multiU_eq := fun _ => rfl
    multiBlind_eq := fun _ => rfl
    s_eq := rfl
    sU_eq := rfl
    sBlind_eq := rfl }

end Family

section Coordinates

variable (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
  (vkS : VerifyingKey shape Fp VestaG)

/-- Every represented point the zero proof's multiopen lookup returns is the zero point. -/
theorem zeroWfProof_reps_eq (hfixed : ∀ i, vkS.fixedCommitment i = 0)
    (hperm : ∀ i, vkS.permutationCommonCommitment i = 0) (ν : Fin 11 → Fp)
    {t : Fp × AlgebraicPoint (F := Fp) basis}
    (ht : t ∈ (RepresentedMultiopen.ofCoveredList vkS (fun _ _ => 0)
      ((zeroAlgebraicProofString basis).erase) ν
      ((zeroAlgebraicProofString basis).multiopenAssemblySource [zeroAlgebraicPoint basis])
      (zeroMultiopenAssemblyCovered basis vkS hfixed hperm ν)).reps) :
    t.2 = zeroAlgebraicPoint basis := by
  simp only [RepresentedMultiopen.ofCoveredList] at ht
  obtain ⟨pr, _hpr, ht⟩ := List.mem_pmap.mp ht
  rw [← ht]
  refine zeroAlgebraicProofString_multiopenSource_eq basis ?_
  exact List.mem_of_find?_eq_some (Option.some_get _).symm

/-- The zero proof's aggregate coordinates all vanish. -/
theorem zeroWfProof_aMulti (hfixed : ∀ i, vkS.fixedCommitment i = 0)
    (hperm : ∀ i, vkS.permutationCommonCommitment i = 0) (ν : Fin 11 → Fp) :
    (zeroWfProof basis vkS hfixed hperm).aMulti ν = 0 := by
  funext i
  show (multiopenMsm vkS (fun _ _ => 0) (zeroProofString shape Fp VestaG)
      (chRecord ν (fun _ => 0))).gScalars i + repsGPart _ i = 0
  rw [(multiopenMsm_zeroData vkS hfixed hperm ν).1 i]
  rw [zero_add]
  show (List.map _ _).sum = 0
  rw [List.sum_eq_zero]
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  rw [zeroWfProof_reps_eq basis vkS hfixed hperm ν ht]
  show t.1 * (0 : Fp) = 0
  rw [mul_zero]

theorem zeroWfProof_multiU (hfixed : ∀ i, vkS.fixedCommitment i = 0)
    (hperm : ∀ i, vkS.permutationCommonCommitment i = 0) (ν : Fin 11 → Fp) :
    (zeroWfProof basis vkS hfixed hperm).multiU ν = 0 := by
  show (multiopenMsm vkS (fun _ _ => 0) (zeroProofString shape Fp VestaG)
      (chRecord ν (fun _ => 0))).uScalar + repsU _ = 0
  rw [(multiopenMsm_zeroData vkS hfixed hperm ν).2.2.1, zero_add]
  show (List.map _ _).sum = 0
  rw [List.sum_eq_zero]
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  rw [zeroWfProof_reps_eq basis vkS hfixed hperm ν ht]
  show t.1 * (0 : Fp) = 0
  rw [mul_zero]

theorem zeroWfProof_multiBlind (hfixed : ∀ i, vkS.fixedCommitment i = 0)
    (hperm : ∀ i, vkS.permutationCommonCommitment i = 0) (ν : Fin 11 → Fp) :
    (zeroWfProof basis vkS hfixed hperm).multiBlind ν = 0 := by
  show (multiopenMsm vkS (fun _ _ => 0) (zeroProofString shape Fp VestaG)
      (chRecord ν (fun _ => 0))).wScalar + repsW _ = 0
  rw [(multiopenMsm_zeroData vkS hfixed hperm ν).2.1, zero_add]
  show (List.map _ _).sum = 0
  rw [List.sum_eq_zero]
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  rw [zeroWfProof_reps_eq basis vkS hfixed hperm ν ht]
  show t.1 * (0 : Fp) = 0
  rw [mul_zero]

theorem zeroWfProof_s (hfixed : ∀ i, vkS.fixedCommitment i = 0)
    (hperm : ∀ i, vkS.permutationCommonCommitment i = 0) :
    (zeroWfProof basis vkS hfixed hperm).s = 0 := rfl

theorem zeroWfProof_sU (hfixed : ∀ i, vkS.fixedCommitment i = 0)
    (hperm : ∀ i, vkS.permutationCommonCommitment i = 0) :
    (zeroWfProof basis vkS hfixed hperm).sU = 0 := rfl

end Coordinates

section MemberCoverage

variable (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
  (vkS : VerifyingKey shape Fp VestaG)

/-- A reference with zero group content is covered by any source containing the zero point. -/
theorem commitmentRefCovered_of_refZeroData
    {source : List (AlgebraicPoint (F := Fp) basis)}
    (hz : zeroAlgebraicPoint basis ∈ source)
    {ref : CommitmentRef shape.k Fp VestaG} (h : refZeroData ref) :
    CommitmentRefCovered source ref := by
  cases ref with
  | point p =>
      exact ⟨zeroAlgebraicPoint basis, hz, by rw [zeroAlgebraicPoint_point, h]⟩
  | msm m =>
      intro pr hpr
      exact ⟨zeroAlgebraicPoint basis, hz,
        by rw [zeroAlgebraicPoint_point, h.2.2.2 pr hpr]⟩

/-- Every routed member reference of the zero data carries zero group content, at every set
index. -/
theorem deployedSetQueries_refZeroData
    (hfixed : ∀ i, vkS.fixedCommitment i = 0)
    (hperm : ∀ i, vkS.permutationCommonCommitment i = 0)
    (ch : Challenges shape.k Fp) (i : ℕ) :
    ∀ qc ∈ deployedSetQueries vkS (fun _ _ => 0) (zeroProofString shape Fp VestaG) ch i,
      refZeroData qc.1 := by
  intro qc hqc
  unfold deployedSetQueries at hqc
  set grouped := constructIntermediateSets
    (assembleQueries vkS (fun _ _ => 0) (zeroProofString shape Fp VestaG) ch) with hgrouped
  by_cases hi : i < (grouped.sets.zip grouped.points).length
  · rw [List.getD_eq_getElem _ _ hi] at hqc
    have hset : (grouped.sets.zip grouped.points)[i].1 ∈ grouped.sets := by
      rw [List.getElem_zip]
      exact List.getElem_mem _
    obtain ⟨q, hq, hEq⟩ := constructIntermediateSets_sets_ref_provenance _ hset hqc
    rw [hEq]
    exact assembleQueries_refZeroData rfl vkS hfixed hperm _ (fun _ _ => rfl) ch q hq
  · rw [List.getD_eq_default _ _ (le_of_not_gt hi)] at hqc
    exact absurd hqc List.not_mem_nil

/-- **The zero data's routed members are all covered** by the pre-`x₁` source extended with the
zero point. -/
theorem zeroFamily_membersCovered
    (hfixed : ∀ i, vkS.fixedCommitment i = 0)
    (hperm : ∀ i, vkS.permutationCommonCommitment i = 0) :
    DeployedMembersCovered vkS (fun _ _ => 0) (zeroAlgebraicProofString basis)
      [zeroAlgebraicPoint basis] := by
  intro ν i _hi m
  refine commitmentRefCovered_of_refZeroData basis
    (zeroAlgebraicPoint_mem_preX1Source basis) ?_
  have hmem : (deployedSetQueries vkS (fun _ _ => 0)
        (zeroAlgebraicProofString basis).erase (chRecord ν (fun _ => 0)) i).getD
      (m : ℕ) (.point 0, []) ∈
      deployedSetQueries vkS (fun _ _ => 0)
        (zeroAlgebraicProofString basis).erase (chRecord ν (fun _ => 0)) i := by
    rw [List.getD_eq_getElem _ _ m.isLt]
    exact List.getElem_mem _
  exact deployedSetQueries_refZeroData vkS hfixed hperm _ i _ hmem

end MemberCoverage

section Batches

variable (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
  (vkS : VerifyingKey shape Fp VestaG)

/-- Every routed member commitment of the zero data is the zero point, at every set index. -/
theorem deployedSetMemberCommitments_zeroData
    (hfixed : ∀ i, vkS.fixedCommitment i = 0)
    (hperm : ∀ i, vkS.permutationCommonCommitment i = 0)
    (ch : Challenges shape.k Fp) (i : ℕ)
    (m : Fin (deployedSetQueries vkS (fun _ _ => 0)
      (zeroProofString shape Fp VestaG) ch i).length) :
    deployedSetMemberCommitments (ursOfAugmentedBasis shape.k basis) rfl vkS
      (fun _ _ => 0) (zeroProofString shape Fp VestaG) ch i m = 0 := by
  refine refZeroData_eval ?_
  refine deployedSetQueries_refZeroData vkS hfixed hperm ch i _ ?_
  rw [List.getD_eq_getElem _ _ m.isLt]
  exact List.getElem_mem _

/-- Every `x₄` batch column commitment of the zero data is the zero point: the columns below the
pair count are power sums of zero member commitments, and the top column is the zero `q′`. -/
theorem x4BatchCommitments_zeroData
    (hfixed : ∀ i, vkS.fixedCommitment i = 0)
    (hperm : ∀ i, vkS.permutationCommonCommitment i = 0)
    (ch : Challenges shape.k Fp)
    (j : Fin (deployedX4PairCount vkS (fun _ _ => 0)
      (zeroProofString shape Fp VestaG) ch + 1)) :
    x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vkS
      (fun _ _ => 0) (zeroProofString shape Fp VestaG) ch j = 0 := by
  by_cases hj : (j : ℕ) < deployedX4PairCount vkS (fun _ _ => 0)
      (zeroProofString shape Fp VestaG) ch
  · rw [x4BatchCommitments_eq_memberPowerSum _ rfl _ _ _ _ hj]
    rw [Finset.sum_eq_zero]
    intro m _
    rw [deployedSetMemberCommitments_zeroData basis vkS hfixed hperm ch _ m, smul_zero]
  · simp only [x4BatchCommitments, if_neg hj]
    rfl

/-- **All-zero deployed batches at any pair count**, against aggregates, column commitments, and
member commitments supplied as equations — so the construction instantiates directly at a wrapped
run's own proof string.  The `x₄` batch is the all-zero power batch against zero column
commitments; every per-set `x₁` batch is the all-zero power batch against zero member
commitments, and its aggregate columns are the `x₄` batch's own (definitionally zero)
coordinates. -/
def zeroDeployedBatchesFull
    (ic : Fin shape.numProofs → ℕ → VestaG) (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp)
    (hcols : ∀ j, x4BatchCommitments (ursOfAugmentedBasis shape.k basis) rfl vkS
      ic ps ch j = 0)
    (hmembers : ∀ (i : ℕ) (m : Fin (deployedSetQueries vkS ic ps ch i).length),
      deployedSetMemberCommitments (ursOfAugmentedBasis shape.k basis) rfl vkS
        ic ps ch i m = 0)
    (agg : Fin (2 ^ shape.k) → Fp) (aggU aggW : Fp)
    (hagg : agg = fun _ => 0) (haggU : aggU = 0) (haggW : aggW = 0) :
    DeployedAlgebraicBatches (ursOfAugmentedBasis shape.k basis) rfl vkS
      ic ps ch agg aggU aggW := by
  refine DeployedAlgebraicBatches.mk
    (zeroPowerBatchOf (ursOfAugmentedBasis shape.k basis) _ hcols
      agg aggU aggW hagg haggU haggW ch.x4) ?_
  intro i hi
  exact zeroPowerBatchOf (ursOfAugmentedBasis shape.k basis) _ (hmembers i)
    _ _ _ rfl rfl rfl ch.x1

end Batches

section MemberReps

variable (basis : AugmentedIndex (2 ^ shape.k) → VestaG)

/-- The deterministic online coordinates over an all-zero source are zero. -/
theorem onlinePointCoordinates_zeroSource
    {source : List (AlgebraicPoint (F := Fp) basis)}
    (hsource : ∀ ap ∈ source, ap = zeroAlgebraicPoint basis) (P : VestaG) :
    onlinePointCoordinates source P = (0, 0, 0) := by
  unfold onlinePointCoordinates
  cases hfind : source.find? (fun ap => ap.point = P) with
  | none => rfl
  | some ap =>
      rw [hsource ap (List.mem_of_find?_eq_some hfind)]
      rfl

/-- Every represented point an MSM lookup into an all-zero source returns is the zero point. -/
theorem representedMsm_reps_zeroSource {m : Msm shape.k Fp VestaG}
    {source : List (AlgebraicPoint (F := Fp) basis)}
    (hsource : ∀ ap ∈ source, ap = zeroAlgebraicPoint basis)
    (hcov : ∀ pr ∈ m.other, ∃ ap ∈ source, ap.point = pr.2)
    {t : Fp × AlgebraicPoint (F := Fp) basis}
    (ht : t ∈ (RepresentedMsm.ofCoveredList m source hcov).reps) :
    t.2 = zeroAlgebraicPoint basis := by
  simp only [RepresentedMsm.ofCoveredList] at ht
  obtain ⟨pr, _hpr, ht⟩ := List.mem_pmap.mp ht
  rw [← ht]
  refine hsource _ ?_
  exact List.mem_of_find?_eq_some (Option.some_get _).symm

/-- The covered-reference coordinates over an all-zero source vanish for zero-data references. -/
theorem coveredCommitmentRepresentation_zeroData
    {source : List (AlgebraicPoint (F := Fp) basis)}
    (hsource : ∀ ap ∈ source, ap = zeroAlgebraicPoint basis)
    {c : CommitmentRef shape.k Fp VestaG} (hc : refZeroData c)
    (hcov : CommitmentRefCovered source c) :
    (coveredCommitmentRepresentation source c hcov).coeffs = 0 ∧
      (coveredCommitmentRepresentation source c hcov).uComp = 0 ∧
      (coveredCommitmentRepresentation source c hcov).wComp = 0 := by
  cases c with
  | point P =>
      have h := coveredCommitmentRepresentation_point_coordinates source P hcov
      rw [onlinePointCoordinates_zeroSource basis hsource P] at h
      exact ⟨congrArg (fun r => r.1) h, congrArg (fun r => r.2.1) h,
        congrArg (fun r => r.2.2) h⟩
  | msm m =>
      refine ⟨?_, ?_, ?_⟩
      · show m.gScalars + repsGPart (RepresentedMsm.ofCoveredList m source hcov).reps = 0
        funext i
        show m.gScalars i + (List.map _ _).sum = 0
        rw [hc.1 i, zero_add, List.sum_eq_zero]
        intro x hx
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
        rw [representedMsm_reps_zeroSource basis hsource hcov ht]
        show t.1 * (0 : Fp) = 0
        rw [mul_zero]
      · show m.uScalar + repsU (RepresentedMsm.ofCoveredList m source hcov).reps = 0
        rw [hc.2.2.1, zero_add]
        show (List.map _ _).sum = 0
        rw [List.sum_eq_zero]
        intro x hx
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
        rw [representedMsm_reps_zeroSource basis hsource hcov ht]
        show t.1 * (0 : Fp) = 0
        rw [mul_zero]
      · show m.wScalar + repsW (RepresentedMsm.ofCoveredList m source hcov).reps = 0
        rw [hc.2.1, zero_add]
        show (List.map _ _).sum = 0
        rw [List.sum_eq_zero]
        intro x hx
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
        rw [representedMsm_reps_zeroSource basis hsource hcov ht]
        show t.1 * (0 : Fp) = 0
        rw [mul_zero]

end MemberReps

section Assembly

variable (vkS : VerifyingKey shape Fp VestaG)

/-- **The constant zero-data prover family, at any shape.**  The adversary ignores the oracle and
returns the zero proof; the coordinates are canonical online lookups and every routed member is
covered by the zero source point. -/
def zeroOnlineMemberFamily
    (hfixed : ∀ i, vkS.fixedCommitment i = 0)
    (hperm : ∀ i, vkS.permutationCommonCommitment i = 0) :
    ComputedOnlineMemberFSFamily shape where
  toComputedOnlineMultiopenFSFamily :=
    { init := []
      vk := fun _ => vkS
      instanceCommitment := fun _ => fun _ _ => 0
      adversary := fun basis => .pure (zeroWfProof basis vkS hfixed hperm)
      Q := 0
      queryBound := fun _ => .pure _ 0
      fixedRepresentations := fun basis => [zeroAlgebraicPoint basis]
      canonical := fun basis _O => zeroWfProof_canonical basis vkS hfixed hperm }
  membersCovered := fun basis _O => zeroFamily_membersCovered basis vkS hfixed hperm

end Assembly

end Zcash.Snark
