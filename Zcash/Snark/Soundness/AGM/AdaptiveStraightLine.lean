import Zcash.Snark.Soundness.AGM.AdaptiveSurfaces
import Zcash.Snark.Soundness.AGM.DirectX4Columns
import Zcash.Snark.Soundness.AGM.StraightLinePinnedRoots

/-!
# Direct straight-line finders for arbitrary adaptive online-AGM adversaries

These finders consume `ComputedAdaptiveOnlineAGMFSFamily` directly.  They do not construct a
sequential execution or a pinned-root trace.  Probability pricing is supplied separately by the
annotation-aware adaptive squeeze theorems; this file establishes that the relation-producing
branches themselves are executable on the bare adversary model.
-/

namespace Zcash.Snark

variable {shape : Shape}

namespace ComputedAdaptiveOnlineAGMFSFamily

/-- Return the first relation produced by a finite list of executable checks. -/
def firstAdaptiveRelation? {basis : AugmentedIndex (2 ^ shape.k) → VestaG} :
    List (Option (AlgebraicRelationWitness (F := Fp) basis)) →
      Option (AlgebraicRelationWitness (F := Fp) basis)
  | [] => none
  | some relation :: _ => some relation
  | none :: rest => firstAdaptiveRelation? rest

@[simp] theorem firstAdaptiveRelation?_eq_none_iff
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (checks : List (Option (AlgebraicRelationWitness (F := Fp) basis))) :
    firstAdaptiveRelation? checks = none ↔ ∀ check ∈ checks, check = none := by
  induction checks with
  | nil => simp [firstAdaptiveRelation?]
  | cons check rest ih =>
      cases check <;> simp [firstAdaptiveRelation?, ih]

/-- Compare the final representations relevant at one deployed pre-IPA squeeze against that
query's first online-AGM annotation. The proof data is supplied explicitly so a combined finder
can share the adversary run across all six multiopen/IPA surfaces. -/
def adaptivePreIpaRepresentationRelationAt?
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (n : Fin 11) (h5n : 5 ≤ (n : ℕ)) :
    Option (AlgebraicRelationWitness (F := Fp) basis) :=
  let p := data.toAlgebraicWfProof
  let t := algebraicFullPrefixesPre family.init p n
  selectedQueryRepresentationRelation? t (family.adversary basis) O
    (p.algebraicProof.representationsBefore n) (by
      intro ap hap
      change ap.point ∈ transcriptGroupPoints
        (preIpaSqueezePoints family.init p.algebraicProof.erase n)
      exact p.algebraicProof.representationsBefore_covered family.init p.wellFormed
        n h5n ap hap)

/-- One shared-output comparison covers `x₁`, `x₂`, `x₃`, `x₄`, `ξ`, and `z`. -/
def adaptivePreIpaRepresentationRelationFinder
    (family : ComputedAdaptiveOnlineAGMFSFamily shape) :
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    let data := (family.adversary basis).run O
    firstAdaptiveRelation?
      [family.adaptivePreIpaRepresentationRelationAt? basis O data 5 (by omega),
       family.adaptivePreIpaRepresentationRelationAt? basis O data 6 (by omega),
       family.adaptivePreIpaRepresentationRelationAt? basis O data 7 (by omega),
       family.adaptivePreIpaRepresentationRelationAt? basis O data 8 (by omega),
       family.adaptivePreIpaRepresentationRelationAt? basis O data 9 (by omega),
       family.adaptivePreIpaRepresentationRelationAt? basis O data 10 (by omega)]

/-- A successful phase-local comparison is also successful in the combined pre-IPA finder. -/
theorem adaptivePreIpaRepresentationRelationFinder_none_at
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (hnone : family.adaptivePreIpaRepresentationRelationFinder basis O = none)
    (n : Fin 11) (h5n : 5 ≤ (n : ℕ)) :
    let data := (family.adversary basis).run O
    family.adaptivePreIpaRepresentationRelationAt? basis O data n h5n = none := by
  dsimp only
  have hall := (firstAdaptiveRelation?_eq_none_iff _).1 (by
    simpa only [adaptivePreIpaRepresentationRelationFinder] using hnone)
  simp only [List.mem_cons, forall_eq_or_imp] at hall
  rcases hall with ⟨h5, h6, h7, h8, h9, h10⟩
  fin_cases n
  · norm_num at h5n
  · norm_num at h5n
  · norm_num at h5n
  · norm_num at h5n
  · norm_num at h5n
  · simpa using h5
  · simpa using h6
  · simpa using h7
  · simpa using h8
  · simpa using h9
  · simpa using h10

/-- Compare every representation affecting one IPA round root with the first annotation at that
round's actual query. -/
def adaptiveIpaRepresentationRelationAt?
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (data : OnlineMemberProofData (vk := family.vk basis)
      (instanceCommitment := family.instanceCommitment basis) basis
      (family.fixedRepresentations basis))
    (j : Fin shape.k) : Option (AlgebraicRelationWitness (F := Fp) basis) :=
  let p := data.toAlgebraicWfProof
  let t := algebraicFullPrefixes family.init p j
  selectedQueryRepresentationRelation? t (family.adversary basis) O
    (p.algebraicProof.representationsBeforeRound j) (by
      intro ap hap
      change ap.point ∈ transcriptGroupPoints
        (roundTranscriptFin (preIpaTranscript family.init p.algebraicProof.erase)
          p.algebraicProof.erase.ipaRounds j)
      exact p.algebraicProof.representationsBeforeRound_covered family.init p.wellFormed
        j ap hap)

/-- The combined IPA provenance finder covers every round without assuming a recursive extractor
or phase-equipped prover. -/
def adaptiveIpaRepresentationRelationFinder
    (family : ComputedAdaptiveOnlineAGMFSFamily shape) :
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    let data := (family.adversary basis).run O
    firstAdaptiveRelation? (List.ofFn fun j =>
      family.adaptiveIpaRepresentationRelationAt? basis O data j)

/-- No combined IPA relation implies no phase-local mismatch relation at any round. -/
theorem adaptiveIpaRepresentationRelationFinder_none_at
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (hnone : family.adaptiveIpaRepresentationRelationFinder basis O = none)
    (j : Fin shape.k) :
    let data := (family.adversary basis).run O
    family.adaptiveIpaRepresentationRelationAt? basis O data j = none := by
  dsimp only
  have hall := (firstAdaptiveRelation?_eq_none_iff _).1 (by
    simpa only [adaptiveIpaRepresentationRelationFinder] using hnone)
  apply hall
  exact List.mem_ofFn.mpr ⟨j, rfl⟩

/-- Compare the final pre-`x₁` prover coordinates with the coordinates attached to the first
actual `x₁`-prefix query.  Any discrepancy is returned as an explicit relation. -/
def adaptivePreX1RepresentationRelationFinder
    (family : ComputedAdaptiveOnlineAGMFSFamily shape) :
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    let data := (family.adversary basis).run O
    let p := data.toAlgebraicWfProof
    let t := algebraicFullPrefixesPre family.init p 5
    selectedQueryRepresentationRelation? t (family.adversary basis) O
      data.algebraicProof.preX1Points (by
        intro ap hap
        change ap.point ∈ transcriptGroupPoints
          (preIpaSqueezePoints family.init data.algebraicProof.erase 5)
        exact data.algebraicProof.preX1Points_coveredAtX1 family.init ap hap)

/-- If the pre-`x₁` comparison returns no relation, the verifier's `x₁` prefix was fresh or
all final pre-`x₁` coefficient vectors equal the first pre-answer annotation. -/
def adaptivePreX1RepresentationRelationFinder_eq_none
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (hnone : family.adaptivePreX1RepresentationRelationFinder basis O = none) :
    let data := (family.adversary basis).run O
    let p := data.toAlgebraicWfProof
    let t := algebraicFullPrefixesPre family.init p 5
    (family.adversary basis).findLabel O t = none ⊕'
      SelectedQueryRepresentationPinned t (family.adversary basis) O
        data.algebraicProof.preX1Points := by
  dsimp only
  apply selectedQueryRepresentationRelation?_eq_none
  exact hnone

/-- The one-run IPA relation branch on a bare arbitrary adaptive online-AGM family. -/
def adaptiveStraightLineIpaRelationFinder
    (family : ComputedAdaptiveOnlineAGMFSFamily shape) :
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    let data := (family.adversary basis).run O
    let p := data.toAlgebraicWfProof
    let nu : Fin 11 → Fp := fun i => O (algebraicFullPrefixesPre family.init p i)
    let chi : Fin shape.k → Fp := fun j => O (algebraicFullPrefixes family.init p j)
    if hattack : fullAlgebraicBindingAttackZ basis (family.vk basis)
        (family.instanceCommitment basis) p nu chi then
      match p.straightLineBindingAttackZIndexedRootOrRelation nu chi hattack with
      | PSum.inl _ => none
      | PSum.inr relation =>
          some (ComputedStraightLineIpaFSFamily.straightLineCanonicalRelation relation)
    else none

/-- Relation-only projection of the executable online multiopen batch-or-relation walk. -/
def adaptiveDeployedRootRelationFinder
    (family : ComputedAdaptiveOnlineAGMFSFamily shape) :
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    match deployedRootOutcomeOfCovered family.toOnlineMemberFamily basis O with
    | PSum.inl _ => none
    | PSum.inr relation =>
        some (ComputedStraightLineIpaFSFamily.straightLineCanonicalRelation relation)

/-- The complete direct relation finder on the bare adaptive family.  A finite executable list
keeps all provenance, IPA, and online-unbatching branches in one DLOG reduction. -/
def adaptiveStraightLineDeployedRelationFinder
    (family : ComputedAdaptiveOnlineAGMFSFamily shape) :
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) →
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) →
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis O =>
    firstAdaptiveRelation?
      [family.adaptivePreIpaRepresentationRelationFinder basis O,
       family.adaptiveIpaRepresentationRelationFinder basis O,
       family.adaptiveStraightLineIpaRelationFinder basis O,
       family.adaptiveDeployedRootRelationFinder basis O]

/-- No result from the combined finder means every executable provenance subfinder was empty. -/
theorem adaptiveStraightLineDeployedRelationFinder_none_provenance
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (hnone : family.adaptiveStraightLineDeployedRelationFinder basis O = none) :
    family.adaptivePreIpaRepresentationRelationFinder basis O = none ∧
      family.adaptiveIpaRepresentationRelationFinder basis O = none := by
  have hall := (firstAdaptiveRelation?_eq_none_iff _).1 (by
    simpa only [adaptiveStraightLineDeployedRelationFinder] using hnone)
  constructor <;> apply hall <;> simp

/-- No result from the combined finder also excludes the direct IPA relation branch. -/
theorem adaptiveStraightLineDeployedRelationFinder_none_ipa
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (hnone : family.adaptiveStraightLineDeployedRelationFinder basis O = none) :
    family.adaptiveStraightLineIpaRelationFinder basis O = none := by
  have hall := (firstAdaptiveRelation?_eq_none_iff _).1 (by
    simpa only [adaptiveStraightLineDeployedRelationFinder] using hnone)
  apply hall
  simp

/-- No result from the combined finder excludes the executable deployed unbatching relation
branch as well. -/
theorem adaptiveStraightLineDeployedRelationFinder_none_root
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (hnone : family.adaptiveStraightLineDeployedRelationFinder basis O = none) :
    family.adaptiveDeployedRootRelationFinder basis O = none := by
  have hall := (firstAdaptiveRelation?_eq_none_iff _).1 (by
    simpa only [adaptiveStraightLineDeployedRelationFinder] using hnone)
  apply hall
  simp

/-- Therefore the executable deployed unbatcher returned its complete batch witness. -/
theorem adaptiveDeployedRootOutcome_eq_inl_of_finder_none
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (hnone : family.adaptiveStraightLineDeployedRelationFinder basis O = none) :
    ∃ witness, deployedRootOutcomeOfCovered family.toOnlineMemberFamily basis O =
      PSum.inl witness := by
  have hroot := family.adaptiveStraightLineDeployedRelationFinder_none_root basis O hnone
  unfold adaptiveDeployedRootRelationFinder at hroot
  cases hout : deployedRootOutcomeOfCovered family.toOnlineMemberFamily basis O with
  | inl witness => exact ⟨witness, rfl⟩
  | inr relation => simp [hout] at hroot

/-- A successful direct adaptive finder result is a genuine relation over the sampled public
basis. -/
theorem adaptiveStraightLineDeployedRelationFinder_isSome
    (family : ComputedAdaptiveOnlineAGMFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (h : (family.adaptiveStraightLineDeployedRelationFinder basis O).isSome) :
    ∃ relation : AlgebraicRelationWitness (F := Fp) basis,
      family.adaptiveStraightLineDeployedRelationFinder basis O = some relation := by
  exact Option.isSome_iff_exists.mp h

/-- The bare adaptive direct finder has the standard textbook-DLOG reduction.  This theorem
prices only the executable relation branch; annotation-aware root landing terms are added by the
adaptive squeeze composition. -/
theorem adaptiveStraightLineDeployedRelation_prob_le_of_textbookDL
    (B : VestaG) (family : ComputedAdaptiveOnlineAGMFSFamily shape) {bound : ENNReal}
    (hDL : TextbookDLWithCoinsAdvantageLE B
      family.adaptiveStraightLineDeployedRelationFinder bound) :
    (PMF.uniformOfFintype
      ((AugmentedIndex (2 ^ shape.k) → Fp) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp))).toOuterMeasure
        (relSetWithCoins B family.adaptiveStraightLineDeployedRelationFinder) ≤
      bound + 1 / Fintype.card Fp :=
  relationWithCoins_prob_le_of_textbookDL B
    family.adaptiveStraightLineDeployedRelationFinder hDL

end ComputedAdaptiveOnlineAGMFSFamily

end Zcash.Snark
