import Zcash.Snark.Soundness.AGM.Peel
import Zcash.Snark.Soundness.AGM.Prover
import Zcash.Snark.Soundness.Forking.Rewind

/-!
# Deployed capstone from an algebraic prover (issue #15, at the deployed level)

`Soundness.AGM.Peel` extracts an explicit relation witness from the algebraic prover's
representations. This module wires that up to the deployed opening: `deployedAlgebraicRelation` is the
data-carrying analogue of `Soundness.Forking.Rewind.deployed_forking_relation`, concluding the multiopen
inner-product opening **or** an explicit `AugmentedRelationWitness` — with no `Classical.choice`.

## The boundary with the Fiat–Shamir/forking layer

Once the transcript is in hand with its representations (the AGM hypothesis, here the data
`AlgebraicDeployedAcceptV`), both the opening and relation branches are explicit computed data. The
operational forking layer must supply that transcript and its representations; a probability theorem
may prove that this happens often enough, but must not select either output with `Classical.choice`.
`deployedAlgebraicRelationWitness` exposes it in the `AlgebraicRelationWitness` form that
`Soundness.AGM.Probability`'s discrete-log reduction consumes.

At the deployed tie-in, note that `hP`'s vectors (`aDep`, `aMulti`, `s`) are `g`-only: real halo2
commitments are blinded, so those representations are findable only for the **declared-components-adjusted**
points — the `pU`/`pW`/`sU`/`sW` parameters of the Vesta forking capstones (`Soundness.Vesta`, section
doc there) — not for the raw commitments. The bridge supplies the declarations from the prover's
representations; they are pinned up to a computed relation.
-/

namespace Zcash.Snark

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- **Computed deployed opening from an algebraic fork certificate.** The certificate's type enforces
that every prover round point carries coefficients over the complete public `(g, U, W)` basis. Its
erasure is checked by the ordinary deployed validity predicate, and the existing deterministic kernel
then returns either the opening or a concrete relation. The relation branch is exposed in the exact
representation form consumed by the fixed-slot DL reduction. -/
def deployedAlgebraicForkingRelation [DecidableEq G] [Inhabited G] (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (cert : AlgebraicDForkCert (F := Fp) (augmentedBasis urs.g urs.u urs.w) urs.k)
    (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (hvalid : DeployedForkValid urs.g b urs.u urs.w z
      (commit urs aDep + (z * 0) • urs.u + blind • urs.w) cert.toDForkCert) :
    (Σ' a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' AlgebraicRelationWitness (F := Fp) (augmentedBasis urs.g urs.u urs.w) :=
  match deployed_forking_relation urs b v ξ z blind aMulti aDep s cert.toDForkCert hz hb0 hP hvalid with
  | PSum.inl hopen => PSum.inl hopen
  | PSum.inr hrel =>
      PSum.inr (AugmentedRelationWitness.toAlgebraicRelationWitness hrel)

/-- **Computed deployed opening-or-DL endpoint.** Compose the representation-carrying deployed fork
certificate with the fixed-slot DLR-to-DL adapter. The challenge slot and all other basis logs are
fixed inputs. If the deployed kernel returns a relation, `fixedSlotExtractOrMiss` either extracts the
slot's discrete log or records that this exact returned relation has coefficient zero there. -/
def deployedAlgebraicForkingFixedSlot [DecidableEq G] [Inhabited G] (urs : URS G)
    (B : G) (challenge : AugmentedIndex (2 ^ urs.k))
    (embedding : FixedSlotEmbedding (F := Fp) B (augmentedBasis urs.g urs.u urs.w) challenge)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (cert : AlgebraicDForkCert (F := Fp) (augmentedBasis urs.g urs.u urs.w) urs.k)
    (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (hvalid : DeployedForkValid urs.g b urs.u urs.w z
      (commit urs aDep + (z * 0) • urs.u + blind • urs.w) cert.toDForkCert) :
    (Σ' a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' FixedSlotRelationOutcome (F := Fp) B (augmentedBasis urs.g urs.u urs.w) challenge :=
  match deployedAlgebraicForkingRelation urs b v ξ z blind aMulti aDep s cert hz hb0 hP hvalid with
  | PSum.inl hopen => PSum.inl hopen
  | PSum.inr hrel => PSum.inr (fixedSlotExtractOrMiss B _ challenge embedding hrel)

/-! ## Concrete relation producer for the probability experiment -/

/-- All explicit data needed to run the deployed algebraic kernel on one augmented public basis.
The basis determines the URS exactly via `ursOfAugmentedBasis`; in particular this structure cannot
silently swap in unrelated deployed generators. -/
structure DeployedAlgebraicForkingInstance (k : ℕ)
    (basis : AugmentedIndex (2 ^ k) → G) where
  b : Fin (2 ^ k) → Fp
  v : Fp
  ξ : Fp
  z : Fp
  blind : Fp
  aMulti : Fin (2 ^ k) → Fp
  aDep : Fin (2 ^ k) → Fp
  s : Fin (2 ^ k) → Fp
  cert : AlgebraicDForkCert (F := Fp)
    (augmentedBasis (ursOfAugmentedBasis k basis).g
      (ursOfAugmentedBasis k basis).u (ursOfAugmentedBasis k basis).w) k
  hz : z ≠ 0
  hb0 : b 0 = 1
  hP : commit (ursOfAugmentedBasis k basis) aDep =
    commit (ursOfAugmentedBasis k basis) aMulti - v • (ursOfAugmentedBasis k basis).g 0 +
      ξ • commit (ursOfAugmentedBasis k basis) s
  hvalid : DeployedForkValid (ursOfAugmentedBasis k basis).g b
    (ursOfAugmentedBasis k basis).u (ursOfAugmentedBasis k basis).w z
    (commit (ursOfAugmentedBasis k basis) aDep + (z * 0) • (ursOfAugmentedBasis k basis).u +
      blind • (ursOfAugmentedBasis k basis).w) cert.toDForkCert

namespace DeployedAlgebraicForkingInstance

/-- The opening branch produced by one deployed algebraic instance. -/
abbrev Opening {k : ℕ} {basis : AugmentedIndex (2 ^ k) → G}
    (x : DeployedAlgebraicForkingInstance (G := G) k basis) : Type _ :=
  Σ' a, IpaRelation (ursOfAugmentedBasis k basis)
    (commit (ursOfAugmentedBasis k basis) x.aMulti) x.b
    (x.v - x.ξ * innerProduct x.s x.b) a

/-- Run one concrete deployed instance. Its relation branch is transported along the proven identity
between the reconstructed URS basis and the exact sampled basis supplied to the instance. -/
def run [DecidableEq G] {k : ℕ} {basis : AugmentedIndex (2 ^ k) → G}
    (x : DeployedAlgebraicForkingInstance (G := G) k basis) :
    x.Opening ⊕' AlgebraicRelationWitness (F := Fp) basis := by
  letI : Inhabited G := ⟨0⟩
  cases deployedAlgebraicForkingRelation (ursOfAugmentedBasis k basis) x.b x.v x.ξ x.z
      x.blind x.aMulti x.aDep x.s x.cert x.hz x.hb0 x.hP x.hvalid with
  | inl hopen => exact PSum.inl hopen
  | inr hrel =>
      rw [augmentedBasis_ursOfAugmentedBasis] at hrel
      exact PSum.inr hrel

/-- One concrete deployed algebraic instance produces a relation exactly when its computed `run`
lands in the relation branch. This is a proposition about an explicit execution result, not an
existentially selected relation. -/
def ProducesRelation [DecidableEq G] {k : ℕ} {basis : AugmentedIndex (2 ^ k) → G}
    (x : DeployedAlgebraicForkingInstance (G := G) k basis) : Prop :=
  ∃ r, x.run = PSum.inr r

end DeployedAlgebraicForkingInstance

/-- The supplied deployed producer emits an explicit relation on this basis. This predicate is the
consumer-side contract that an operational adversary must connect to its own accept event. -/
def deployedAlgebraicRelationProduced [DecidableEq G] {k : ℕ}
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → G,
      Option (DeployedAlgebraicForkingInstance (G := G) k basis))
    (basis : AugmentedIndex (2 ^ k) → G) : Prop :=
  ∃ x, instances basis = some x ∧ x.ProducesRelation

/-- Bases on which the supplied deployed producer computes an explicit relation. This is the exact
event that the probability layer transports across a URS setup distribution. -/
def deployedAlgebraicRelationEvent [DecidableEq G] {k : ℕ}
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → G,
      Option (DeployedAlgebraicForkingInstance (G := G) k basis)) :
    Set (AugmentedIndex (2 ^ k) → G) :=
  { basis | deployedAlgebraicRelationProduced instances basis }

/-- The concrete relation finder consumed by `Soundness.AGM.Probability`: on each sampled augmented
basis, run the supplied deployed forking instance when one was produced, return `some` only on its
computed relation branch, and return `none` when there is no valid certificate or the result is a
valid opening. Thus the probability event is tied to the deployed producer, not an unrelated abstract
relation oracle. -/
def deployedAlgebraicRelationFinder [DecidableEq G] {k : ℕ}
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → G,
      Option (DeployedAlgebraicForkingInstance (G := G) k basis)) :
    (basis : AugmentedIndex (2 ^ k) → G) →
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis =>
    match instances basis with
    | none => none
    | some x =>
      match x.run with
      | PSum.inl _ => none
      | PSum.inr hrel => some hrel

/-- The relation finder succeeds exactly on the explicit relation branch of the supplied deployed
instance. This pins the event consumed by `relSet` to the computed capstone result. -/
theorem deployedAlgebraicRelationFinder_isSome_iff [DecidableEq G] {k : ℕ}
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → G,
      Option (DeployedAlgebraicForkingInstance (G := G) k basis))
    (basis : AugmentedIndex (2 ^ k) → G) :
    (deployedAlgebraicRelationFinder instances basis).isSome ↔
      deployedAlgebraicRelationProduced instances basis := by
  unfold deployedAlgebraicRelationProduced deployedAlgebraicRelationFinder
  cases hinst : instances basis with
  | none => simp
  | some x =>
    cases hrun : x.run with
    | inl hopen => simp [DeployedAlgebraicForkingInstance.ProducesRelation, hrun]
    | inr hrel => simp [DeployedAlgebraicForkingInstance.ProducesRelation, hrun]

/-- **The deployed opening from an algebraic prover.** Data-carrying analogue of
`deployed_forking_relation`: given the algebraic prover's deployed transcript `t` *with its
representations supplied as data* (`AlgebraicDeployedAcceptV`, in place of the existentially-extracted
forking tree), the deployed opening either yields the multiopen inner-product relation, or an
**explicit** `AugmentedRelationWitness` over `(g, U, W)` — computed from the accept equations and the
leaf representation, the node representations being AGM admissibility data — with no
`Classical.choice`. -/
def deployedAlgebraicRelation [DecidableEq G] [Inhabited G] (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (t : DeployedIpaTreeV Fp G urs.k) (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (ht : AlgebraicDeployedAcceptV urs.g b urs.u urs.w z (commit urs aDep) 0 blind t) :
    (Σ' a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' AugmentedRelationWitness (F := Fp) urs.g urs.u urs.w := by
  cases deployedToAcceptVWitness hz urs.g b (commit urs aDep) 0 blind t ht with
  | inl hclean =>
    obtain ⟨a, ha⟩ := ipaRelation_extract urs b (commit urs aDep) 0 (projTree t) hclean
    have h1 := ipaRelation_unshift urs (commit urs aDep + v • urs.g 0) b v a hb0
      (by rw [add_sub_cancel_right]; exact ha)
    have h2 : commit urs aDep + v • urs.g 0 = commit urs aMulti + ξ • commit urs s := by
      rw [hP]; abel
    rw [h2] at h1
    exact PSum.inl ⟨_, ipaRelation_unblind_value urs (commit urs aMulti) b v ξ s _ h1⟩
  | inr hrel => exact PSum.inr hrel

/-- The same, with the relation branch in the `AlgebraicRelationWitness (augmentedBasis …)` form that
`Soundness.AGM.Probability`'s reduction (`relSet` / `succSet`) consumes — the explicit adversary output
of the discrete-log reduction, sourced from the prover's representations. -/
def deployedAlgebraicRelationWitness [DecidableEq G] [Inhabited G] (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (t : DeployedIpaTreeV Fp G urs.k) (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (ht : AlgebraicDeployedAcceptV urs.g b urs.u urs.w z (commit urs aDep) 0 blind t) :
    (Σ' a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' AlgebraicRelationWitness (F := Fp) (augmentedBasis urs.g urs.u urs.w) :=
  match deployedAlgebraicRelation urs b v ξ z blind aMulti aDep s t hz hb0 hP ht with
  | PSum.inl hopen => PSum.inl hopen
  | PSum.inr r => PSum.inr r.toAlgebraicRelationWitness

end Zcash.Snark
