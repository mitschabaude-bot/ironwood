import Zcash.Snark.Soundness.Vesta
import Zcash.Snark.Soundness.AGM.Probability
import Zcash.Snark.Soundness.AGM.Capstone

/-!
# Deployed-curve instantiation of the AGM probability wrapper (Vesta)

The generic probability wrapper (`Soundness.AGM.Probability`) specializes to the deployed *index
shapes* — the augmented basis index `AugmentedIndex (2 ^ urs.k)` and the URS index `Fin (2 ^ urs.k)` —
over the Vesta group `VestaG` with scalar field `Fp`. This is the concrete-curve endpoint of the
"relation finder ⇒ discrete-log solver" reduction for the computed relation branch of the deployed
Orchard verifier capstones.

**The uniform-basis seam.** In these theorems the producer acts on the reduction's *sampled* basis
`scalarBasis B s` (uniform scalars times `B`), not on one fixed tuple of deployed generators.
`OrchardUniformURSIdentification` states the exact setup requirement: the pushforward distribution
of the deployed setup coins through its basis sampler equals the sampled-basis distribution.
`orchard_uniformURSIdentification_of_generatorRO` derives that equality when the basis is read from
a uniform group-valued random oracle at distinct parameter queries; the remaining setup idealization
is the identification of halo2's concrete hash-to-curve with that oracle. The probability transfer
below is therefore a theorem about the concrete relation event, rather than an assumed equality
involving an otherwise arbitrary external probability. The operational adversary must still produce
`DeployedAlgebraicForkingInstance` data and connect its accept event to that relation event; that is
the Fiat–Shamir integration boundary.
-/

open scoped ENNReal

namespace Zcash.Snark

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass CompElliptic.CurveOrder

/-- Vesta specialization of the computed deployed opening-or-DL endpoint. All transcript and AGM
representation data remain explicit inputs; the result is computed and preserves the precise
relation in the fixed-slot miss branch. -/
def orchardDeployedAlgebraicForkingFixedSlot
    (urs : URS VestaG) (B : VestaG) (challenge : AugmentedIndex (2 ^ urs.k))
    (embedding : FixedSlotEmbedding (F := Fp) B (augmentedBasis urs.g urs.u urs.w) challenge)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (cert : AlgebraicDForkCert (F := Fp) (augmentedBasis urs.g urs.u urs.w) urs.k)
    (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (hvalid : DeployedForkValid urs.g b urs.u urs.w z
      (commit urs aDep + (z * 0) • urs.u + blind • urs.w) cert.toDForkCert) :
    (Σ' a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' FixedSlotRelationOutcome (F := Fp) B (augmentedBasis urs.g urs.u urs.w) challenge := by
  letI : Inhabited VestaG := ⟨0⟩
  exact deployedAlgebraicForkingFixedSlot urs B challenge embedding b v ξ z blind
    aMulti aDep s cert hz hb0 hP hvalid

/-! ## Exact deployed-producer event -/

/-- Scalar samples on which the supplied deployed algebraic producer computes its relation branch. -/
noncomputable def orchardDeployedRelationSet (k : ℕ) (B : VestaG)
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → VestaG,
      Option (DeployedAlgebraicForkingInstance (G := VestaG) k basis)) :
    Finset (AugmentedIndex (2 ^ k) → Fp) := by
  classical
  exact Finset.univ.filter fun scalars =>
    deployedAlgebraicRelationProduced instances (scalarBasis B scalars)

/-- The explicit producer-branch event is exactly the `relSet` consumed by the generic DL
reduction. No deployed-accept probability is assumed here: the equality follows by executing the
supplied instances and inspecting their computed sum branch. -/
theorem orchard_deployed_relation_set_eq_relSet (k : ℕ) (B : VestaG)
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → VestaG,
      Option (DeployedAlgebraicForkingInstance (G := VestaG) k basis)) :
    orchardDeployedRelationSet k B instances =
      relSet B (deployedAlgebraicRelationFinder instances) := by
  classical
  ext scalars
  simp only [orchardDeployedRelationSet, relSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (deployedAlgebraicRelationFinder_isSome_iff instances (scalarBasis B scalars)).symm

/-- **Deployed producer, advantage form.** The generic fixed-slot accounting instantiated with the
actual relation finder obtained by running `DeployedAlgebraicForkingInstance.run` on every sampled
augmented Vesta basis. This removes the formerly unrelated abstract `A` from the deployed endpoint. -/
theorem orchard_deployed_reduction_advantage_ge (k : ℕ) (B : VestaG)
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → VestaG,
      Option (DeployedAlgebraicForkingInstance (G := VestaG) k basis)) :
    (1 : ℝ≥0∞) / Fintype.card (AugmentedIndex (2 ^ k)) *
        (PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → Fp)).toOuterMeasure
          (relSet B (deployedAlgebraicRelationFinder instances))
      ≤ (PMF.uniformOfFintype
          ((AugmentedIndex (2 ^ k) → Fp) × AugmentedIndex (2 ^ k))).toOuterMeasure
          (succSet B (deployedAlgebraicRelationFinder instances)) :=
  reduction_advantage_ge B (deployedAlgebraicRelationFinder instances)

/-- **Deployed producer under textbook DL hardness.** Bound the relation probability of the concrete
deployed algebraic producer, evaluated on the uniformly sampled augmented Vesta basis. -/
theorem orchard_deployed_relation_prob_le_of_textbookDL (k : ℕ) (B : VestaG)
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → VestaG,
      Option (DeployedAlgebraicForkingInstance (G := VestaG) k basis))
    {bound : ℝ≥0∞}
    (hDL : TextbookDLAdvantageLE B (deployedAlgebraicRelationFinder instances) bound) :
    (PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → Fp)).toOuterMeasure
        (relSet B (deployedAlgebraicRelationFinder instances))
      ≤ Fintype.card (AugmentedIndex (2 ^ k)) * bound :=
  relation_prob_le_of_textbookDL B (deployedAlgebraicRelationFinder instances) hDL

/-- The textbook-DL bound stated directly on the computed relation branch of the supplied deployed
instances. This is the PR-28 side of the probability weld; an operational adversary must prove that
its own relation-producing executions populate `instances`. -/
theorem orchard_deployed_relation_event_prob_le_of_textbookDL (k : ℕ) (B : VestaG)
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → VestaG,
      Option (DeployedAlgebraicForkingInstance (G := VestaG) k basis))
    {bound : ℝ≥0∞}
    (hDL : TextbookDLAdvantageLE B (deployedAlgebraicRelationFinder instances) bound) :
    (PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → Fp)).toOuterMeasure
        (orchardDeployedRelationSet k B instances)
      ≤ Fintype.card (AugmentedIndex (2 ^ k)) * bound := by
  rw [orchard_deployed_relation_set_eq_relSet]
  exact orchard_deployed_relation_prob_le_of_textbookDL k B instances hDL

/-- The deployed URS setup distribution is the sampled-basis distribution used by the fixed-slot
reduction. `basisOf` exposes the augmented basis generated from the setup coins; the equality is of
the complete pushforward PMFs, independent of any particular adversary or event. For a fixed URS
this is intentionally not derivable merely from Vesta cyclicity. -/
def OrchardUniformURSIdentification {Ω : Type*} (setup : PMF Ω) (k : ℕ) (B : VestaG)
    (basisOf : Ω → AugmentedIndex (2 ^ k) → VestaG) : Prop :=
  setup.map basisOf =
    (PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → Fp)).map (scalarBasis B)

/-- Uniform group-valued random-oracle answers at the distinct parameter queries used to derive the
augmented URS basis. This is a probability-event definition, not a data-producing reduction. -/
noncomputable def orchardGeneratorROSetup {T : Type*} [DecidableEq T]
    {k : ℕ} (query : AugmentedIndex (2 ^ k) → T) :
    PMF (↥(Set.range query) → VestaG) := by
  letI : Fintype VestaG := Fintype.ofFinite VestaG
  exact PMF.uniformOfFintype (↥(Set.range query) → VestaG)

/-- Read an augmented basis from the generator random oracle at its distinct parameter queries. -/
def orchardGeneratorROBasis {T : Type*} {k : ℕ}
    (query : AugmentedIndex (2 ^ k) → T) :
    (↥(Set.range query) → VestaG) → AugmentedIndex (2 ^ k) → VestaG :=
  fun O i => O ⟨query i, Set.mem_range_self i⟩

/-- Reading the augmented URS basis from a uniform group-valued random oracle at distinct parameter
queries satisfies `OrchardUniformURSIdentification`. This is the random-oracle model of halo2's
deterministic parameter derivation (`gᵢ = H(0 || i)`, `W = H(1)`, `U = H(2)`): distinct queries give
independent uniform Vesta points. For nonzero `B`, scalar multiplication by `B` is a bijection from
`Fp` to `VestaG`, so that uniform point basis is exactly the sampled-scalar basis used by the
fixed-slot reduction.

This theorem discharges the former free-standing PMF equality inside the generator-RO model. The
cryptographic identification of halo2's concrete hash-to-curve with that oracle remains the standard
hash-to-curve-as-random-oracle idealization. -/
theorem orchard_uniformURSIdentification_of_generatorRO {T : Type*} [DecidableEq T]
    (k : ℕ) (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ k) → T) (hquery : Function.Injective query) :
    OrchardUniformURSIdentification
      (orchardGeneratorROSetup query) k B
      (orchardGeneratorROBasis query) := by
  classical
  letI : Fintype VestaG := Fintype.ofFinite VestaG
  have hinj : Function.Injective (fun c : Fp => c • B) := by
    intro c c' h
    rcases eq_or_ne c c' with hcc | hcc
    · exact hcc
    · exfalso
      apply hB
      change c • B = c' • B at h
      have hd : c - c' ≠ 0 := sub_ne_zero.mpr hcc
      have hzero : (c - c') • B = 0 := by rw [sub_smul, h, sub_self]
      rw [← one_smul Fp B, ← inv_mul_cancel₀ hd, mul_smul, hzero, smul_zero]
  have hcard : Fintype.card Fp = Fintype.card VestaG := by
    rw [card_Fp, ← Nat.card_eq_fintype_card, Vesta.card_eq]
  let pointEquiv : Fp ≃ VestaG := Equiv.ofBijective (fun c : Fp => c • B)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩)
  have hscalar :
      (PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → Fp)).map (scalarBasis B) =
        PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → VestaG) := by
    simpa [scalarBasis, pointEquiv] using
      (map_uniformOfFintype_equiv
        (Equiv.arrowCongr (Equiv.refl (AugmentedIndex (2 ^ k))) pointEquiv))
  unfold OrchardUniformURSIdentification orchardGeneratorROSetup
  simpa [orchardGeneratorROBasis] using
    (uniformOfFintype_map_eval_injective query hquery).trans hscalar.symm

/-- A uniform-URS setup transports the concrete deployed-producer relation event exactly to the
sampled-scalar event used by `relSet`. -/
theorem orchard_deployed_relation_prob_eq_of_uniformURS {Ω : Type*} (setup : PMF Ω)
    (k : ℕ) (B : VestaG) (basisOf : Ω → AugmentedIndex (2 ^ k) → VestaG)
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → VestaG,
      Option (DeployedAlgebraicForkingInstance (G := VestaG) k basis))
    (hURS : OrchardUniformURSIdentification setup k B basisOf) :
    setup.toOuterMeasure (basisOf ⁻¹' deployedAlgebraicRelationEvent instances) =
      (PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → Fp)).toOuterMeasure
        (orchardDeployedRelationSet k B instances) := by
  have h := congrArg
    (fun p : PMF (AugmentedIndex (2 ^ k) → VestaG) =>
      p.toOuterMeasure (deployedAlgebraicRelationEvent instances)) hURS
  change (setup.map basisOf).toOuterMeasure (deployedAlgebraicRelationEvent instances) =
    ((PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → Fp)).map (scalarBasis B)).toOuterMeasure
      (deployedAlgebraicRelationEvent instances) at h
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply] at h
  calc
    setup.toOuterMeasure (basisOf ⁻¹' deployedAlgebraicRelationEvent instances)
        = (PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → Fp)).toOuterMeasure
            (scalarBasis B ⁻¹' deployedAlgebraicRelationEvent instances) := h
    _ = (PMF.uniformOfFintype (AugmentedIndex (2 ^ k) → Fp)).toOuterMeasure
          (orchardDeployedRelationSet k B instances) := by
      congr 1
      ext scalars
      simp only [Set.mem_preimage, deployedAlgebraicRelationEvent, Set.mem_setOf_eq,
        orchardDeployedRelationSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Transfer textbook-DL hardness to the concrete relation event under an explicit URS setup
distribution. Unlike the former wrapper, the left side is an actual event determined by `basisOf`
and the supplied data-producing instances, not an arbitrary probability variable. -/
theorem orchard_deployed_relation_prob_le_of_uniformURS_textbookDL {Ω : Type*} (setup : PMF Ω)
    (k : ℕ) (B : VestaG) (basisOf : Ω → AugmentedIndex (2 ^ k) → VestaG)
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → VestaG,
      Option (DeployedAlgebraicForkingInstance (G := VestaG) k basis))
    {bound : ℝ≥0∞} (hURS : OrchardUniformURSIdentification setup k B basisOf)
    (hDL : TextbookDLAdvantageLE B (deployedAlgebraicRelationFinder instances) bound) :
    setup.toOuterMeasure (basisOf ⁻¹' deployedAlgebraicRelationEvent instances) ≤
      Fintype.card (AugmentedIndex (2 ^ k)) * bound := by
  rw [orchard_deployed_relation_prob_eq_of_uniformURS setup k B basisOf instances hURS]
  exact orchard_deployed_relation_event_prob_le_of_textbookDL k B instances hDL

/-- Under the generator random-oracle model, bound the concrete deployed relation event directly by
textbook DL. The setup-identification equality is derived from distinct generator queries and Vesta's
prime-order scalar action rather than supplied as a free-standing hypothesis. -/
theorem orchard_deployed_relation_prob_le_of_generatorRO_textbookDL
    {T : Type*} [DecidableEq T] (k : ℕ) (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ k) → T) (hquery : Function.Injective query)
    (instances : ∀ basis : AugmentedIndex (2 ^ k) → VestaG,
      Option (DeployedAlgebraicForkingInstance (G := VestaG) k basis))
    {bound : ℝ≥0∞}
    (hDL : TextbookDLAdvantageLE B (deployedAlgebraicRelationFinder instances) bound) :
    (orchardGeneratorROSetup query).toOuterMeasure
        (orchardGeneratorROBasis query ⁻¹' deployedAlgebraicRelationEvent instances) ≤
      Fintype.card (AugmentedIndex (2 ^ k)) * bound :=
  orchard_deployed_relation_prob_le_of_uniformURS_textbookDL
    (orchardGeneratorROSetup query) k B (orchardGeneratorROBasis query) instances
    (orchard_uniformURSIdentification_of_generatorRO k B hB query hquery) hDL

/-- **Binding from discrete-log hardness, at the deployed curve.** At the augmented basis *index*
`AugmentedIndex (2 ^ urs.k)` over Vesta: if this reduction solves the discrete log of the challenge
slot with probability at most `bound` (`DLAdvantageLE`), then an algebraic adversary against the
sampled basis `scalarBasis B s` finds a nontrivial relation with probability at most `|ι| · bound`.
Reading the sampled basis as the deployed `(g, U, W)` is the uniform-basis seam (module doc). Direct
specialization of `relation_prob_le_of_DL` to `ι := AugmentedIndex (2 ^ urs.k)`, `F := Fp`,
`G := VestaG`. -/
theorem orchard_relation_prob_le_of_DL
    (urs : URS VestaG) (B : VestaG)
    (A : (b : AugmentedIndex (2 ^ urs.k) → VestaG) →
      Option (AlgebraicRelationWitness (F := Fp) b))
    {bound : ℝ≥0∞} (h : DLAdvantageLE B A bound) :
    (PMF.uniformOfFintype (AugmentedIndex (2 ^ urs.k) → Fp)).toOuterMeasure (relSet B A)
      ≤ Fintype.card (AugmentedIndex (2 ^ urs.k)) * bound :=
  relation_prob_le_of_DL B A h

/-- The deployed-curve advantage-preserving reduction: over the uniform product, the reduction's
discrete-log-solving probability is at least `1/|ι|` times the algebraic adversary's relation-finding
probability on the sampled basis (uniform-basis seam: module doc). Specialization of
`reduction_advantage_ge` at the deployed index shape. -/
theorem orchard_reduction_advantage_ge
    (urs : URS VestaG) (B : VestaG)
    (A : (b : AugmentedIndex (2 ^ urs.k) → VestaG) →
      Option (AlgebraicRelationWitness (F := Fp) b)) :
    (1 : ℝ≥0∞) / Fintype.card (AugmentedIndex (2 ^ urs.k))
        * (PMF.uniformOfFintype (AugmentedIndex (2 ^ urs.k) → Fp)).toOuterMeasure (relSet B A)
      ≤ (PMF.uniformOfFintype ((AugmentedIndex (2 ^ urs.k) → Fp) × AugmentedIndex (2 ^ urs.k))).toOuterMeasure
          (succSet B A) :=
  reduction_advantage_ge B A

/-- **Commitment binding from plain discrete log (URS index shape).** Specializing the reduction to
the URS *index* `Fin (2 ^ urs.k)` over Vesta: under textbook single-generator DL hardness for this
reduction (`TextbookDLAdvantageLE`), an algebraic adversary finds a nontrivial relation over the
sampled basis `scalarBasis B s` with probability at most `2^k · bound`. The binding reading — a
commitment collision on the URS yields such a relation via its difference `a - a'`
(`relationWitnessOfCollision`), so collisions are as hard as discrete log — additionally requires the
uniform-basis seam (module doc): the deployed URS generators distributed as uniform multiples of a
generator `B`. The statement itself is about the sampled basis; `urs` enters only through `urs.k`. -/
theorem commitment_binding_prob_le_of_textbookDL
    (urs : URS VestaG) (B : VestaG)
    (A : (b : Fin (2 ^ urs.k) → VestaG) → Option (AlgebraicRelationWitness (F := Fp) b))
    {bound : ℝ≥0∞} (h : TextbookDLAdvantageLE B A bound) :
    (PMF.uniformOfFintype (Fin (2 ^ urs.k) → Fp)).toOuterMeasure (relSet B A)
      ≤ Fintype.card (Fin (2 ^ urs.k)) * bound :=
  relation_prob_le_of_textbookDL B A h

/-- **Binding from *textbook* discrete-log hardness at the augmented basis index.** The
`TextbookDLAdvantageLE` form of `orchard_relation_prob_le_of_DL`, at the index shape the deployed
relation branch actually produces (`deployedAlgebraicRelationWitness` lands in
`AlgebraicRelationWitness (augmentedBasis g U W)`, indexed by `AugmentedIndex (2 ^ urs.k)`): under
standard single-generator DL hardness for the reduction built from `A`, an algebraic adversary
against the sampled augmented basis finds a nontrivial relation with probability at most
`|ι| · bound`. Uniform-basis seam as in the module doc; direct specialization of
`relation_prob_le_of_textbookDL`. -/
theorem orchard_relation_prob_le_of_textbookDL
    (urs : URS VestaG) (B : VestaG)
    (A : (b : AugmentedIndex (2 ^ urs.k) → VestaG) →
      Option (AlgebraicRelationWitness (F := Fp) b))
    {bound : ℝ≥0∞} (h : TextbookDLAdvantageLE B A bound) :
    (PMF.uniformOfFintype (AugmentedIndex (2 ^ urs.k) → Fp)).toOuterMeasure (relSet B A)
      ≤ Fintype.card (AugmentedIndex (2 ^ urs.k)) * bound :=
  relation_prob_le_of_textbookDL B A h

end Zcash.Snark
