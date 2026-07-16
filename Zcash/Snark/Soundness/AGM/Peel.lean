import Zcash.Snark.Soundness.Deployed.IpaPeel
import Zcash.Snark.Soundness.AGM.Probability

/-!
# Algebraic-prover model: explicit relation witnesses from prover representations

This module is the algebraic-group-model input boundary of issue #15, at the peel level. Every
prover-emitted round point is paired with a representation over the complete public basis
`(g, U, W)`, and every reduction below is a plain computable `def` producing either the clean
transcript or the shared `NontrivialRelation` data used by the deployed soundness layer — replacing
the Prop-level peel (`¬ IpaAcceptV` located by decidability) with data the DL reduction can consume.

The peel returns an **explicit** `AugmentedRelationWitness` — whose coefficients are literally the
prover's representation difference `aP - honest` — with no `Classical.choice`:

* `separateOrRelationWitness` / `relationOfFoldGensWitness` / `deployedLeafPeelWitness` — data-carrying
  analogues of the `Soundness.Deployed.Binding` / `Soundness.Deployed.IpaPeel` steps.
* `deployedToAcceptVWitness` — the recursive peel, returning `IpaAcceptV ⊕' AugmentedRelationWitness`.
* `algebraicRelationOfDeployedAccept` — bridges the explicit witness into the
  `AlgebraicRelationWitness (augmentedBasis g U W)` that the probability wrapper's reduction consumes.

`Soundness.AGM.Capstone` wires this boundary to the deployed opening. The operational forking layer
must supply both the transcript and these representations as data; it must not recover either with
choice from an accept-probability existence theorem.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G]

/-- Data version of `separate_or_relation`: the relation coefficients are the explicit difference
`a - a'` from the prover's representations. -/
def separateOrRelationWitness {n : ℕ} (g : Fin n → G) (U W : G)
    (a a' : Fin n → F) (α α' β β' : F)
    (e : commitGen g a + α • U + β • W = commitGen g a' + α' • U + β' • W) :
    (a = a' ∧ α = α' ∧ β = β') ⊕' AugmentedRelationWitness (F := F) g U W := by
  by_cases h : a = a' ∧ α = α' ∧ β = β'
  · exact PSum.inl h
  · exact PSum.inr (NontrivialRelation.ofCombinationCollision e h)

/-- Data version of `relation_of_foldGens`: an explicit witness over the folded generators lifts to
an explicit witness over the originals. -/
def relationOfFoldGensWitness {k : ℕ} (g : Fin (2 ^ (k + 1)) → G) (U W : G) (u : F)
    (r : AugmentedRelationWitness (F := F) (foldGens g u) U W) :
    AugmentedRelationWitness (F := F) g U W :=
  NontrivialRelation.ofFoldedGens u r

/-- Data version of `deployed_leaf_peel`: taking the prover's leaf representation `aP` as **data**, the
combined leaf equation either splits into the clean leaf checks or yields an **explicit**
`AugmentedRelationWitness` over `(g, U, W)`. -/
def deployedLeafPeelWitness {n : ℕ} {g : Fin n → G} {b : Fin n → F} {U W : G} {z : F}
    (aP : Fin n → F) {v blind c f : F} (hz : z ≠ 0)
    (e : commitGen g aP + (z * v) • U + blind • W
       = commitGen g (fun _ => c) + (z * commitGen b (fun _ => c)) • U + f • W) :
    (commitGen g aP = commitGen g (fun _ => c) ∧ v = commitGen b (fun _ => c))
      ⊕' AugmentedRelationWitness (F := F) g U W := by
  cases separateOrRelationWitness g U W aP (fun _ => c) (z * v)
      (z * commitGen b (fun _ => c)) blind f e with
  | inl h => exact PSum.inl ⟨congrArg (commitGen g) h.1, mul_left_cancel₀ hz h.2.1⟩
  | inr hrel => exact PSum.inr hrel

/-- Reassemble a prover-emitted deployed IPA point from its `g`, value, and blinding tracks. -/
def deployedRoundPoint (U W : G) (z : F) (L : G) (Lv Lw : F) : G :=
  L + (z * Lv) • U + Lw • W

/-- Complete AGM representations for every group element output at a deployed IPA node.

The tree stores each round point in components: its `g`-part (`L`/`R`), value coefficient
(`Lv`/`Rv`), and blinding coefficient (`Lw`/`Rw`). The actual prover output is therefore
`L + (z * Lv) • U + Lw • W` (and similarly for `R`). Each such point is represented over the
*original* public basis `(g, U, W)`, including all descendants of the fork tree. Keeping the root
basis fixed is the usual AGM convention and makes this data directly consumable by the relation
reduction. -/
def AlgebraicTreeRepresentations {n : ℕ} (g : Fin n → G) (U W : G) (z : F) :
    {d : ℕ} → DeployedIpaTreeV F G d → Type _
  | 0, .leaf _ _ _ => PUnit
  | _ + 1, .node L R Lv Rv Lw Rw _ _ _ t₁ t₂ t₃ =>
      GroupRepresentation (F := F) (augmentedBasis g U W)
        (deployedRoundPoint (F := F) U W z L Lv Lw) ×
      GroupRepresentation (F := F) (augmentedBasis g U W)
        (deployedRoundPoint (F := F) U W z R Rv Rw) ×
      AlgebraicTreeRepresentations g U W z t₁ ×
      AlgebraicTreeRepresentations g U W z t₂ ×
      AlgebraicTreeRepresentations g U W z t₃

/-- A deployed accepting tree together with the AGM data for every prover-emitted group point.

Unlike the former abbreviation, this is a data type, not an alias for ordinary acceptance: callers
cannot enter the algebraic capstone without supplying the node representations. -/
structure AlgebraicDeployedAcceptV {d : ℕ} (g : Fin (2 ^ d) → G) (b : Fin (2 ^ d) → F)
    (U W : G) (z : F) (P : G) (v blind : F) (t : DeployedIpaTreeV F G d) : Type _ where
  accepts : DeployedIpaAcceptV g b U W z P v blind t
  representations : AlgebraicTreeRepresentations g U W z t

/-- **Explicit-witness peel (algebraic prover).** From the accepting transcript, the deployed
recursion yields either the clean `IpaAcceptV` transcript or an **explicit**
`AugmentedRelationWitness` over `(g, U, W)` — its coefficients computed from the accept equations and
the tree's *leaf* representation `aP`, with no `Classical.choice`. The node representations of
`AlgebraicDeployedAcceptV` are AGM admissibility data, not consumed by this computation.
Data-carrying analogue of `deployed_to_acceptV`. -/
def deployedToAcceptVWitnessCore {U W : G} {z : F} (hz : z ≠ 0) :
    {d : ℕ} → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → F) → (P : G) → (v blind : F) →
      (t : DeployedIpaTreeV F G d) → DeployedIpaAcceptV g b U W z P v blind t →
      IpaAcceptV g b P v (projTree t) ⊕' AugmentedRelationWitness (F := F) g U W
  | 0, g, b, P, v, blind, .leaf c f aP, h => by
      cases deployedLeafPeelWitness aP hz h.2 with
      | inl h1 => exact PSum.inl ⟨h.1.trans h1.1, h1.2⟩
      | inr hrel => exact PSum.inr hrel
  | _ + 1, g, b, P, v, blind, .node L R Lv Rv Lw Rw u₁ u₂ u₃ t₁ t₂ t₃, h => by
      obtain ⟨h12, h13, h23, hz1, hz2, hz3, h1, h2, h3⟩ := h
      cases deployedToAcceptVWitnessCore hz _ _ _ _ _ t₁ h1 with
      | inl hc₁ =>
        cases deployedToAcceptVWitnessCore hz _ _ _ _ _ t₂ h2 with
        | inl hc₂ =>
          cases deployedToAcceptVWitnessCore hz _ _ _ _ _ t₃ h3 with
          | inl hc₃ => exact PSum.inl ⟨h12, h13, h23, hz1, hz2, hz3, hc₁, hc₂, hc₃⟩
          | inr hr₃ => exact PSum.inr (relationOfFoldGensWitness g U W u₃ hr₃)
        | inr hr₂ => exact PSum.inr (relationOfFoldGensWitness g U W u₂ hr₂)
      | inr hr₁ => exact PSum.inr (relationOfFoldGensWitness g U W u₁ hr₁)

/-- **Explicit-witness peel (algebraic prover).** The representation-bearing input is required at
the public boundary; the deterministic peel then computes from its accepting transcript. -/
def deployedToAcceptVWitness {U W : G} {z : F} (hz : z ≠ 0) {d : ℕ}
    (g : Fin (2 ^ d) → G) (b : Fin (2 ^ d) → F) (P : G) (v blind : F)
    (t : DeployedIpaTreeV F G d) (h : AlgebraicDeployedAcceptV g b U W z P v blind t) :
    IpaAcceptV g b P v (projTree t) ⊕' AugmentedRelationWitness (F := F) g U W :=
  deployedToAcceptVWitnessCore hz g b P v blind t h.accepts

/-- **Bridge to the probability wrapper.** From the algebraic prover's data-carrying accept, the
deployed opening is either the clean `IpaAcceptV` transcript or an explicit
`AlgebraicRelationWitness` over the augmented basis `(g, U, W)` — computed from the accept equations
and the leaf representation, the node representations being AGM admissibility data — precisely the
adversary output that `Soundness.AGM.Probability`'s reduction consumes (`succSet`/`relSet`), with
**no** `Classical.choice`. This is the algebraic-prover model of issue #15 wired to the DL reduction
at the peel level. -/
def algebraicRelationOfDeployedAccept {d : ℕ} {U W : G} {z : F} (hz : z ≠ 0)
    (g : Fin (2 ^ d) → G) (b : Fin (2 ^ d) → F) (P : G) (v blind : F)
    (t : DeployedIpaTreeV F G d) (h : AlgebraicDeployedAcceptV g b U W z P v blind t) :
    IpaAcceptV g b P v (projTree t)
      ⊕' AlgebraicRelationWitness (F := F) (augmentedBasis g U W) :=
  match deployedToAcceptVWitness hz g b P v blind t h with
  | PSum.inl hc => PSum.inl hc
  | PSum.inr r => PSum.inr r.toAlgebraicRelationWitness

end Zcash.Snark
