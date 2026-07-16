import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.Forking.Oracle
import Zcash.Snark.Soundness.Forking.Extractor
import Zcash.Snark.Soundness.Forking.Ordering

/-!
# The deployed verifier under random-oracle rewinding

This module carries the live Fiat–Shamir forking path. First, `ofOracle`/`roChallenges` instantiate
`deriveChallenges` with a random oracle, and `reprogramRounds` proves that re-running the deployed schedule
under round-prefix reprogramming is exactly the same as replacing the IPA round-challenge vector. That
identification is load-bearing in the `_rewind` Vesta capstones.

Second, the probability chain replaces a posited forked transcript tree by an accept-probability hypothesis:
`extractable_of_prob` yields an `Extractable` challenge tree, `proverAccept_forkValid` turns it into a
`DeployedForkValid` certificate, `deployed_forking_relation` extracts the opened value, and
`deployed_forking_soundness_of_bridge` isolates the remaining prover-as-oracle bridge. Its deterministic
content is proven below (`deployedVerifierEq_iff_flatAccept`, `deployedVerifierEq_iff_flatAccept_adaptive`).
The floor left is the execution-semantics identification for a rewound RO adversary — the
querying-adversary/query-loss experiment that would *derive* `hprob`'s accept probability — plus
Blake2b-as-random-oracle. The uniform *measure* of `hprob` is justified standalone by
`roChallenges_ipaRound_uniform` (see its section for the scope).
-/

namespace Zcash.Snark

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- A random-oracle-backed Fiat–Shamir instance: the squeeze *is* the oracle `O`. -/
def ofOracle (O : List (TranscriptElt Fp G) → Fp) : FiatShamir Fp G := ⟨O⟩

/-- The challenges a proof induces under random oracle `O` — the deployed verifier's own Fiat–Shamir coins,
`deriveChallenges` run through `ofOracle O`. -/
def roChallenges {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) : Challenges shape.k Fp :=
  deriveChallenges (ofOracle O) init ps

/-! ## Redrawing the round vector *is* reprogramming the deployed oracle

The forking layer redraws the IPA round-challenge vector `χ` and evaluates the verifier at
`{ch with ipaRound := χ}`; the random-oracle model rewinds by *reprogramming* the oracle
(`Soundness.Forking.Oracle.reprogram`) at the round prefixes and re-running the schedule. These are the same
operation, and `roChallenges_reprogramRounds` proves it. The round prefixes are pairwise distinct and longer
than every pre-IPA squeeze input (`roundTranscriptFin_length`/`_injective`), so reprogramming them changes
exactly the round challenges (`deriveChallenges_ipaRound_eq`, the seal) and nothing upstream — which is why the
proof consumes the round-by-round transcript ordering (`Soundness.Forking.Ordering`). This puts the ordering
module on the Fiat–Shamir path: the `_rewind` capstones (`Soundness.Vesta`) state their accept probability over
reprogrammed-oracle runs and reach the `_deployed` capstones through this identification. -/

open Classical in
/-- The `k`-point extension of `reprogram`: reprogram the oracle at *every* IPA round prefix of the fixed
proof string at once, answering `χ j` at the round-`j` transcript (as `reprogram … (χ j)` would) and `O`
elsewhere. Redrawing the whole round vector — what the forking probability ranges over — runs the deployed
schedule under this oracle (`roChallenges_reprogramRounds`). -/
noncomputable def reprogramRounds {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fin shape.k → Fp) :
    List (TranscriptElt Fp G) → Fp :=
  fun t => if h : ∃ j : Fin shape.k,
      t = roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j
    then χ h.choose else O t

/-- At the round-`j` prefix, the reprogrammed oracle answers `χ j` (well-defined because distinct rounds
have distinct prefixes, `roundTranscriptFin_injective`). -/
theorem reprogramRounds_apply_round {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fin shape.k → Fp)
    (j : Fin shape.k) :
    reprogramRounds O init ps χ
      (roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j) = χ j := by
  have hex : ∃ j' : Fin shape.k,
      roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j
        = roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j' := ⟨j, rfl⟩
  simp only [reprogramRounds]
  rw [dif_pos hex]
  exact (congrArg χ (roundTranscriptFin_injective _ _ hex.choose_spec)).symm

/-- Off the round prefixes, the reprogrammed oracle is `O`. -/
theorem reprogramRounds_apply_ne {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fin shape.k → Fp)
    {t : List (TranscriptElt Fp G)}
    (ht : ∀ j : Fin shape.k, t ≠ roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j) :
    reprogramRounds O init ps χ t = O t := by
  simp only [reprogramRounds]
  rw [dif_neg]
  rintro ⟨j, hj⟩
  exact ht j hj

/-- Every transcript no longer than the pre-IPA base is untouched by the round reprogramming: the round
prefixes are strictly longer (`roundTranscriptFin_length`). In particular every pre-IPA squeeze input. -/
theorem reprogramRounds_apply_short {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fin shape.k → Fp)
    {t : List (TranscriptElt Fp G)} (ht : t.length ≤ (preIpaTranscript init ps).length) :
    reprogramRounds O init ps χ t = O t :=
  reprogramRounds_apply_ne O init ps χ (fun j h => by
    have hlen := congrArg List.length h
    rw [roundTranscriptFin_length] at hlen
    omega)

private theorem Challenges.ext' {k : ℕ} {F : Type*} {c₁ c₂ : Challenges k F}
    (hθ : c₁.theta = c₂.theta) (hβ : c₁.beta = c₂.beta) (hγ : c₁.gamma = c₂.gamma)
    (hy : c₁.y = c₂.y) (hx : c₁.x = c₂.x) (h1 : c₁.x1 = c₂.x1) (h2 : c₁.x2 = c₂.x2)
    (h3 : c₁.x3 = c₂.x3) (h4 : c₁.x4 = c₂.x4) (hξ : c₁.xi = c₂.xi) (hz : c₁.z = c₂.z)
    (hu : c₁.ipaRound = c₂.ipaRound) : c₁ = c₂ := by
  cases c₁; cases c₂; simp_all

/-- **Redrawing the round vector is reprogramming the deployed oracle.** Running the deployed schedule under
the oracle reprogrammed at all `k` round prefixes yields exactly the honest run with its IPA round vector
replaced by `χ`. The pre-IPA challenges are untouched (their squeeze inputs are no longer than the base,
`reprogramRounds_apply_short`), and round `j`'s challenge is the reprogrammed answer `χ j` — the
transcript-ordering seal `deriveChallenges_ipaRound_eq`. This is the identification the forking layer's
`{ch with ipaRound := χ}` events rest on, and the load-bearing consumer of `Soundness.Forking.Ordering`. -/
theorem roChallenges_reprogramRounds {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fin shape.k → Fp) :
    roChallenges (reprogramRounds O init ps χ) init ps
      = { roChallenges O init ps with ipaRound := χ } := by
  refine Challenges.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    first
      | (funext j
         show (deriveChallenges (ofOracle (reprogramRounds O init ps χ)) init ps).ipaRound j = χ j
         rw [deriveChallenges_ipaRound_eq]
         exact reprogramRounds_apply_round O init ps χ j)
      | exact reprogramRounds_apply_short O init ps χ (by
          simp only [preIpaTranscript, List.length_append, List.length_cons, List.length_nil]
          omega)

/-! ## Challenge-vector uniformity: a standalone justification for `hprob`'s measure

`hprob` is stated over `PMF.uniformOfFintype (Fin k → Fp)`, the uniform measure on the IPA round-challenge
vector. That a random oracle induces this distribution was an axiom; it is now a theorem:

* `roChallenges_ipaRound_apply` — each round challenge is the oracle's answer at that round's transcript prefix,
  `(roChallenges O init ps).ipaRound j = O (φ j)`, `φ = roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds`.
* `roChallenges_ipaRound_uniform` — the `k` prefixes are pairwise distinct (`roundTranscriptFin_injective`), so
  reading a uniform random oracle at them (`uniformOfFintype_map_eval_injective`) is the uniform challenge vector.

**Scope.** This is a *standalone* justification, not a link in any capstone: nothing consumes
`roChallenges_ipaRound_uniform`, and every `hprob` below is stated directly over `PMF.uniformOfFintype`. The
theorem shows that measure is what a uniform random oracle induces; it is not substituted into the reduction.
It has two limits:

* it samples the oracle only at the `k` round prefixes — the marginal on the round vector, not a full query
  domain;
* it is for the fixed proof string `ps`. In the `_adaptive`/`_rewind` events the reprogrammed prefixes depend
  on `χ`, so tying `hprob`'s measure to a rewound-oracle experiment there belongs to the execution-semantics
  floor (a forger querying `O`, with query-loss — `Forking.Oracle`), above `hprob`, not this theorem. -/

/-- Each round challenge is the oracle's answer at that round's transcript prefix:
`(roChallenges O init ps).ipaRound j = O (roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j)`.
`roChallenges` is `deriveChallenges` through `ofOracle O`, whose squeeze is `O`, so this is
`deriveChallenges_ipaRound_eq` at the oracle — the challenge vector depends on the oracle's values at the `k`
prefixes alone. -/
theorem roChallenges_ipaRound_apply {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (j : Fin shape.k) :
    (roChallenges O init ps).ipaRound j
      = O (roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j) :=
  deriveChallenges_ipaRound_eq (ofOracle O) init ps j

/-- **Challenge-vector uniformity from a uniform random oracle.** Sampling the oracle uniformly over its query
domain — the finite set `↥(Set.range φ)` of the `k` round prefixes
`φ = roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds` — and reading its answers (`fun O j => O ⟨φ j, _⟩`,
the round-challenge vector by `roChallenges_ipaRound_apply`) is distributed as
`PMF.uniformOfFintype (Fin shape.k → Fp)`. This is `uniformOfFintype_map_eval_injective` at `φ`, whose injectivity
(`roundTranscriptFin_injective`, the prefixes are distinct) makes the `k` answers independent-uniform. For its
scope — a standalone justification of `hprob`'s measure, over the fixed-`ps` marginal, consumed by no capstone —
see the section above. -/
theorem roChallenges_ipaRound_uniform [DecidableEq G] {shape : Shape}
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) :
    (PMF.uniformOfFintype
        (↥(Set.range (roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds)) → Fp)).map
        (fun O j => O (Equiv.ofInjective _
          (roundTranscriptFin_injective (preIpaTranscript init ps) ps.ipaRounds) j))
      = PMF.uniformOfFintype (Fin shape.k → Fp) :=
  uniformOfFintype_map_eval_injective _
    (roundTranscriptFin_injective (preIpaTranscript init ps) ps.ipaRounds)

open scoped ENNReal in
open Classical in
/-- **Accept-measure monotonicity into the capstones' `hprob`.** The deployed accept (`DeployedAccepts`,
the `assemble?` guards plus the MSM identity) implies the explicit verifier equation pointwise
(`deployedAccepts_verifierEq`), so any threshold beaten by the *deployed-accept* event is beaten by the
`DeployedIpaVerifierEq` event the capstones consume. Stated over arbitrary proof-string/challenge-record
families, it covers the constant, `_rewind`, and `_adaptive_rewind` event shapes alike — use it to feed a
capstone `hprob` from a genuine deployed-accept probability. -/
theorem kerr_lt_verifierEq_of_deployedAccepts [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (psf : (Fin shape.k → Fp) → ProofString shape Fp G)
    (chf : (Fin shape.k → Fp) → Challenges shape.k Fp) {ε : ℝ≥0∞}
    (h : ε < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
        (Finset.univ.filter (fun χ => DeployedAccepts urs hk vk (psf χ) (chf χ)))) :
    ε < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
        (Finset.univ.filter (fun χ =>
          DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk (psf χ) (chf χ))) := by
  refine lt_of_lt_of_le h ((PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure.mono ?_)
  intro χ hχ
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hχ ⊢
  exact deployedAccepts_verifierEq urs hk vk (psf χ) (chf χ) hχ

/-! ## The deployed forking opening: the value-placement composed end to end

This closes the deterministic chain. From the flat forking output threading halo2's *adjusted* commitment
`P' = ⟨aDep,G⟩ = multiopen − [v]g₀ + [ξ]⟨s,G⟩` (the verifier's `add_constant_term(-v)` plus the synthetic
blinding `[ξ]S`), `deployed_forking_tree` extracts an opening of `P'` to inner product `0`; the
adjusted-commitment theorems then lift it to an opening of the *multiopen* commitment `⟨aMulti,G⟩` to its
**true** value `v − ξ·⟨s,b⟩` — `ipaRelation_unshift` (keyed on `b₀ = 1`) restores the value and
`ipaRelation_unblind_value` strips the blinding *unconditionally*. So every link from the rewinding output to
the deployed inner-product relation is a theorem; the residual is `DeployedForkValid` (the rewinding itself),
the `g`-span/adjusted form, `b₀ = 1`, and Blake2b-as-random-oracle. -/

/-- **The deployed forking opening.** A flat forking output (`DeployedForkValid`, no posited decomposition)
threading halo2's adjusted commitment `⟨aDep,G⟩ = ⟨aMulti,G⟩ − [v]g₀ + [ξ]⟨s,G⟩` yields an inner-product
opening of the multiopen commitment `⟨aMulti,G⟩` to the value `v − ξ·⟨s,b⟩` for the supplied `S`-opening
`s` — unique under binding: two distinct openings of `ps.ipaS` shift it by `ξ·⟨Δ,b⟩` while exhibiting a
`g`-relation, the computed `NontrivialRelation` branch — or the multiopen opening. The extraction
(`deployed_forking_tree`) opens `⟨aDep,G⟩` to inner product `0`; `ipaRelation_unshift`
(keyed on `b₀ = 1`) restores the value, and `ipaRelation_unblind_value` strips the synthetic blinding
*unconditionally* — reporting that opened value whatever the prover's blinder `s` is (no `⟨s,b⟩ = 0`
assumed; the honest case `⟨s,b⟩ = 0` recovers the claimed `v`). As a *computable* `def`, the opening is
returned as **computed data**
(`ipaRelation_extract`), not the prime-order-vacuous `∃ a, …`: neither the opening witness nor the relation
coefficients can be produced without the `cert` (the discrete-log preimage the reviewer's vacuity witness
needs is not computable), so this reduction is genuinely non-vacuous. The `deployed_forking_soundness*`
capstones that wrap it are the honest floor — they forget the data to `∃` because the `cert` is only
classically obtained (the random-oracle experiment, `Forking.Oracle`, is unmodeled). -/
def deployed_forking_relation [DecidableEq G] [Inhabited G] (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (cert : DForkCert Fp G urs.k) (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (hvalid : DeployedForkValid urs.g b urs.u urs.w z
        (commit urs aDep + (z * 0) • urs.u + blind • urs.w) cert) :
    (Σ' a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w :=
  match deployed_forking_tree hz urs.g b aDep 0 blind cert hvalid with
  | .inl ⟨blind', t, ht⟩ =>
      if hclean : IpaAcceptV urs.g b (commit urs aDep) 0 (projTree t) then
        match ipaRelation_extract urs b (commit urs aDep) 0 (projTree t) hclean with
        | ⟨a, ha⟩ =>
            PSum.inl ⟨_, ipaRelation_unblind_value urs (commit urs aMulti) b v ξ s _
              (by
                have h1 := ipaRelation_unshift urs (commit urs aDep + v • urs.g 0) b v a hb0
                  (by rw [add_sub_cancel_right]; exact ha)
                have h2 : commit urs aDep + v • urs.g 0 = commit urs aMulti + ξ • commit urs s := by
                  rw [hP]; abel
                rw [h2] at h1; exact h1)⟩
      else
        PSum.inr (NontrivialRelation.ofDeployedTree hz urs.g b (commit urs aDep) 0 blind' t ht hclean)
  | .inr hrel => PSum.inr hrel

/-! ## Closing the rewinding gap: the forked transcripts are *produced* by the probability

`deployed_forking_relation` still took `DeployedForkValid` (the forked transcripts) as a hypothesis; this
discharges it. In the random-oracle model the challenge vector is uniform, so the prover's accept event is a
finite set whose measure is its accept *probability*. When that probability exceeds the knowledge error
`kerr/Nᵏ = 3k/N`, `extractable_of_prob` — the averaging argument that *is* the multi-round forking lemma —
forces a full `(3,…,3)` forking tree to exist, and `proverAccept_forkValid` reads off the `DeployedForkValid`
certificate. So the rewinding output is no longer assumed: the accept probability beating the knowledge error
produces it, in the ideal RO model. The residual is Blake2b-as-random-oracle (what makes the challenge
uniform), the prover-as-strategy `P`, and the standard structural/honest-prover facts. -/

open scoped ENNReal in
open Classical in
/-- **Challenge inversion is measure-preserving.** Componentwise inversion `χ ↦ (·⁻¹) ∘ χ` is an involution
on `Fin d → Fp` — a field satisfies `a⁻¹⁻¹ = a` for *every* `a` (including `0`, since `0⁻¹ = 0`) — hence a
bijection of the uniform random-oracle sample space onto itself, so inverting the challenge vector leaves any
accept event's probability unchanged. This is the probabilistic half of the consistency bridge: the deployed
verifier folds generators by `foldGens g u⁻¹` (`foldAll`) while the extraction tree folds by `foldGens g u`,
so the two accept events differ by exactly this inversion — equal probability, and the soundness hypothesis on
the tree predicate is the deployed verifier's accept probability. -/
theorem uniformOfFintype_measure_inv {d : ℕ} (acc : (Fin d → Fp) → Prop) :
    (PMF.uniformOfFintype (Fin d → Fp)).toOuterMeasure
        (Finset.univ.filter (fun χ : Fin d → Fp => acc (fun i => (χ i)⁻¹)))
      = (PMF.uniformOfFintype (Fin d → Fp)).toOuterMeasure (Finset.univ.filter acc) := by
  rw [PMF.toOuterMeasure_apply_finset, PMF.toOuterMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul]
  congr 1
  norm_cast
  refine Finset.card_bij' (fun χ _ => (fun i => (χ i)⁻¹)) (fun χ _ => (fun i => (χ i)⁻¹))
    ?hi ?hj ?li ?ri
  case hi =>
    intro χ hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ ⊢
    exact hχ
  case hj =>
    intro χ hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ ⊢
    have hχχ : (fun i => ((χ i)⁻¹)⁻¹) = χ := by funext i; rw [inv_inv]
    rw [hχχ]; exact hχ
  case li => intro χ _; funext i; simp only [inv_inv]
  case ri => intro χ _; funext i; simp only [inv_inv]

open scoped ENNReal in
/-- **The synthetic blinder's soundness budget (ξ-randomization).** A malicious IPA blinder `S = ⟨s,G⟩` with
`⟨s,b⟩ = δ ≠ 0` shifts the opened value of the multiopen commitment by `−ξδ` (`ipaRelation_unblind_value`):
the plain commitment opens to `v − ξδ` rather than the claimed `v`. Because the verifier squeezes `ξ` *after*
the prover has committed `S` (`deriveChallenges`), `δ` is fixed before `ξ`, so the shifted value `v − ξδ`
hits any fixed target `c` for at most one challenge `ξ = (v−c)/δ` — a set of uniform random-oracle measure
`≤ 1/p`. This is the `1/p` soundness role of `[ξ]S`: it replaces the honest-prover assumption `⟨s,b⟩ = 0`
(the `hs` of `ipaRelation_unblind`) by a Schwartz–Zippel exclusion over `ξ`. -/
theorem blinder_shift_badSet_measure (δ c : Fp) (hδ : δ ≠ 0) :
    uniformChallenge.toOuterMeasure (Finset.univ.filter (fun ξ : Fp => ξ * δ = c))
      ≤ 1 / (Fintype.card Fp : ℝ≥0∞) := by
  rw [uniformChallenge_badSet]
  have hcard : (Finset.univ.filter (fun ξ : Fp => ξ * δ = c)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro ξ₁ h₁ ξ₂ h₂
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    exact mul_right_cancel₀ hδ (h₁.trans h₂.symm)
  gcongr
  exact_mod_cast hcard

/-- The deployed accept condition along one challenge path, in the **flat verifier's** IPA fold convention:
generators (and eval vector) fold by `foldGens · u⁻¹` — exactly halo2's `foldAll`/`computeS` direction — rather
than the extraction tree's `foldGens · u` (`proverAccept`). Everything else — the commitment fold
`[u⁻¹]L + [u]R`, the leaf check — is identical. Its `CF`-fold matches `DeployedIpaVerifierEq`
(`deployedVerifierEq_cf` identifies the verifier equation with `CF = 0`); the per-path identification is the
explicit `hbridge` of `deployed_forking_soundness_of_bridge`, not proved here. -/
def flatAccept : {d : ℕ} → Prover Fp G d → (Fin (2 ^ d) → G) → (Fin (2 ^ d) → Fp) → (U W : G) → (z : Fp) →
    G → (Fin d → Fp) → Prop
  | 0, .leaf c f, g, b, U, W, z, Pwhole, _ =>
      Pwhole = commitGen g (fun _ => c) + (z * commitGen b (fun _ => c)) • U + f • W
  | _ + 1, .node L R cont, g, b, U, W, z, Pwhole, χ =>
      flatAccept (cont (χ 0)) (foldGens g (χ 0)⁻¹) (foldGens b (χ 0)⁻¹) U W z
        (Pwhole + (χ 0)⁻¹ • L + (χ 0) • R) (Fin.tail χ)

/-- The prover strategy re-indexed for the flat convention: swap each round's `(L, R)` and feed every
continuation the inverted challenge. The involution that, together with challenge inversion, turns the
extraction tree's fold convention into the flat verifier's. -/
def invProver : {d : ℕ} → Prover Fp G d → Prover Fp G d
  | 0, .leaf c f => .leaf c f
  | _ + 1, .node L R cont => .node R L (fun u => invProver (cont u⁻¹))

/-- `invProver` is an involution. -/
theorem invProver_invProver : {d : ℕ} → (P : Prover Fp G d) → invProver (invProver P) = P
  | 0, .leaf _ _ => rfl
  | _ + 1, .node L R cont => by
      simp only [invProver]
      congr 1
      funext u
      rw [inv_inv, invProver_invProver (cont u)]

/-- **The convention bridge (pointwise).** The extraction tree's accept predicate `proverAccept` (folding
generators by `foldGens g u`) at challenge vector `χ` is *exactly* the flat verifier predicate `flatAccept`
(folding by `foldGens g u⁻¹`) for the re-indexed prover `invProver P` at the inverted challenges `χ⁻¹`. The two
IPA fold conventions differ only by this challenge inversion and an `L`/`R` swap — both discharged here by
structural induction (`inv_inv`, `Fin.tail` of an inverted vector, and commutativity of the commitment fold).
No correctness gap: the tree predicate *is* the flat verifier predicate, relabelled. -/
theorem proverAccept_iff_flatAccept {U W : G} {z : Fp} : {d : ℕ} → (P : Prover Fp G d) →
    (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → Fp) → (Pwhole : G) → (χ : Fin d → Fp) →
    (proverAccept P g b U W z Pwhole χ ↔
      flatAccept (invProver P) g b U W z Pwhole (fun i => (χ i)⁻¹))
  | 0, .leaf _ _, _, _, _, _ => Iff.rfl
  | d + 1, .node L R cont, g, b, Pwhole, χ => by
      rw [proverAccept, proverAccept_iff_flatAccept (cont (χ 0)) (foldGens g (χ 0)) (foldGens b (χ 0))
        (Pwhole + (χ 0)⁻¹ • L + (χ 0) • R) (Fin.tail χ), invProver, flatAccept]
      simp only [inv_inv]
      have htail : (Fin.tail fun i => (χ i)⁻¹) = (fun i => ((Fin.tail χ) i)⁻¹) := by
        funext i; rfl
      rw [htail, show Pwhole + (χ 0) • R + (χ 0)⁻¹ • L = Pwhole + (χ 0)⁻¹ • L + (χ 0) • R from by abel]

open scoped ENNReal in
open Classical in
/-- **The convention bridge (probabilistic) — the consistency gap, closed.** The extraction tree's accept
predicate (`proverAccept`, fold `foldGens g u`) and the flat verifier predicate (`flatAccept`, fold
`foldGens g u⁻¹` — halo2's actual `foldAll`/`computeS` direction) have *equal* accept probability under the
uniform random oracle. Pointwise they are the same event up to challenge inversion
(`proverAccept_iff_flatAccept`), and inversion is measure-preserving (`uniformOfFintype_measure_inv`). So the
`u`-vs-`u⁻¹` IPA fold convention is not a correctness gap: the tree predicate and the flat-convention
predicate share an accept probability. (Identifying `flatAccept` itself with the deployed verifier's *actual*
accept event is the separate prover-as-oracle bridge, `deployed_forking_soundness_of_bridge`.) -/
theorem proverAccept_measure_eq_flatAccept {d : ℕ} {U W : G} {z : Fp} (P : Prover Fp G d)
    (g : Fin (2 ^ d) → G) (b : Fin (2 ^ d) → Fp) (Pwhole : G) :
    (PMF.uniformOfFintype (Fin d → Fp)).toOuterMeasure
        (Finset.univ.filter (proverAccept P g b U W z Pwhole))
      = (PMF.uniformOfFintype (Fin d → Fp)).toOuterMeasure
        (Finset.univ.filter (flatAccept (invProver P) g b U W z Pwhole)) := by
  have hset : (Finset.univ.filter (proverAccept P g b U W z Pwhole))
      = Finset.univ.filter
          (fun χ : Fin d → Fp => flatAccept (invProver P) g b U W z Pwhole (fun i => (χ i)⁻¹)) := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact proverAccept_iff_flatAccept P g b Pwhole χ
  rw [hset, uniformOfFintype_measure_inv]

open scoped ENNReal in
/-- **The forking soundness for an abstract prover strategy.** For a strategy tree `P`, if its accept event
`proverAccept P …` has probability exceeding the knowledge error `kerr (card Fp) k / (card Fp)ᵏ` (`= 3k/N`)
over the uniform challenge vector, then the multiopen commitment `⟨aMulti,G⟩` opens to its **true** value
`v − ξ·⟨s,b⟩` — or a nontrivial relation. The chain: `extractable_of_prob` (the averaging argument) turns the
probability into a forking tree, `proverAccept_forkValid` into a `DeployedForkValid` certificate, and
`deployed_forking_relation` into the opening. This is the **abstract** layer — `P` is an arbitrary strategy,
the challenge vector uniform. Tying it to the deployed verifier (that the actual proof realizes such a `P`
whose accept event is `DeployedIpaVerifierEq`, over the RO-derived challenge) is the explicit bridge
`deployed_forking_soundness_of_bridge`. The residual is that bridge (the prover-as-oracle / Blake2b floor) and
the structural facts (`b₀ = 1`, the adjusted/`g`-span form `hP`); the synthetic blinder is stripped
unconditionally (no `s(x) = 0` assumed). -/
noncomputable def deployed_forking_soundness [DecidableEq G] [Inhabited G] (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (P : Prover Fp G urs.k) (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    [DecidablePred (proverAccept P urs.g b urs.u urs.w z
      (commit urs aDep + (z * 0) • urs.u + blind • urs.w))]
    (hprob : (kerr (Fintype.card Fp) urs.k : ℝ≥0∞) / Fintype.card (Fin urs.k → Fp)
        < (PMF.uniformOfFintype (Fin urs.k → Fp)).toOuterMeasure
            (Finset.univ.filter (proverAccept P urs.g b urs.u urs.w z
              (commit urs aDep + (z * 0) • urs.u + blind • urs.w)))) :
    (∃ a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  -- `proverAccept_forkValid` yields the certificate behind a `Prop` `∃`; naming it as data (`Classical.choose`)
  -- is what makes this composition `noncomputable` — the honest random-oracle floor (`Forking.Oracle`). The
  -- deterministic `deployed_forking_relation` it wraps is a genuine *computed* reduction returning the opening
  -- as data; here that data is forgotten to `∃` since the certificate itself is only classically obtained.
  have hpf := proverAccept_forkValid P urs.g b
    (commit urs aDep + (z * 0) • urs.u + blind • urs.w) (extractable_of_prob _ hprob)
  rcases deployed_forking_relation urs b v ξ z blind aMulti aDep s hpf.choose hz hb0 hP hpf.choose_spec
    with ⟨a, ha⟩ | r
  · exact PSum.inl ⟨a, ha⟩
  · exact PSum.inr r

open scoped ENNReal in
open Classical in
/-- **The deployed forking soundness, in the verifier's own fold convention.** `deployed_forking_soundness`
with the accept-probability hypothesis stated over `flatAccept` — folding generators by `foldGens g u⁻¹`,
halo2's `foldAll`/`computeS` direction — instead of the extraction tree's `proverAccept` (`foldGens g u`). The
two have equal accept probability (`proverAccept_measure_eq_flatAccept`, via the measure-preserving challenge
inversion), so the `u`-vs-`u⁻¹` consistency gap is discharged by theorem. The hypothesis is still the
*strategy* predicate `flatAccept Q`; identifying `Q` with the deployed proof is the explicit bridge
`deployed_forking_soundness_of_bridge`. -/
noncomputable def deployed_forking_soundness_flat [DecidableEq G] [Inhabited G] (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (Q : Prover Fp G urs.k) (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (hprob : (kerr (Fintype.card Fp) urs.k : ℝ≥0∞) / Fintype.card (Fin urs.k → Fp)
        < (PMF.uniformOfFintype (Fin urs.k → Fp)).toOuterMeasure
            (Finset.univ.filter (flatAccept Q urs.g b urs.u urs.w z
              (commit urs aDep + (z * 0) • urs.u + blind • urs.w)))) :
    (∃ a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  refine deployed_forking_soundness urs b v ξ z blind aMulti aDep s (invProver Q) hz hb0 hP ?_
  rw [proverAccept_measure_eq_flatAccept (invProver Q) urs.g b
        (commit urs aDep + (z * 0) • urs.u + blind • urs.w), invProver_invProver Q]
  exact hprob

/-! ## Discharging the deterministic half of the prover-as-oracle bridge `hbridge`

`hbridge` bundles a deterministic algebra half — the deployed verifier equation folds, along each challenge
path, to the flat tree predicate `flatAccept` of the proof read as a `Prover` — with the irreducible
random-oracle half (the accept *probability* is over uniform rewindable challenges). This section discharges
the **algebra half**: `deployedVerifierEq_iff_flatAccept` proves halo2's actual `DeployedIpaVerifierEq` is
`flatAccept (proverOfRounds …)` at the challenge vector, so `hbridge` is a *theorem* for the deployed verifier,
not an assumption. The round-by-round ordering behind the prefix-respecting `Prover` shape is likewise a
theorem (`Soundness.Forking.Ordering`, sealed to the deployed schedule by `deriveChallenges_ipaRound_eq`;
`proverRoundPoint_proverOfRounds` below reads the fixed round points off `proverOfRounds` on every challenge
path). The residual is then only the random-oracle adversary experiment above `hprob` (the querying forger and
its query-loss) and Blake2b-as-random-oracle — challenge-vector uniformity is justified standalone
(`roChallenges_ipaRound_uniform`; see its section, consumed by no capstone). -/

/-- The prover-strategy tree the deployed non-interactive proof realises: at each IPA round it commits the
proof's **fixed** round points `(Lⱼ, Rⱼ)` (they are written in the proof string, so the continuation ignores
the challenge), and the leaf carries the final folded opening scalar `c` and blinding `f`. This is the concrete
`Prover` object that `hbridge` posits abstractly — here built explicitly from the proof string. -/
def proverOfRounds : {d : ℕ} → (Fin d → G × G) → Fp → Fp → Prover Fp G d
  | 0, _, c, f => .leaf c f
  | _ + 1, R, c, f => .node (R 0).1 (R 0).2 (fun _ => proverOfRounds (Fin.tail R) c f)

/-- The deployed fixed-proof prover commits constant round points: on *every* challenge path,
`proverRoundPoint` of `proverOfRounds R c f` at depth `j` is `R j` — the degenerate
(challenge-independent) case of `proverRoundPoint_prefix`, and the prover-tree side of the deployed
schedule's ordering (`deriveChallenges_ipaRound_eq`). So the tree `hbridge` instantiates satisfies the
round-by-round prefix-determination by construction. -/
theorem proverRoundPoint_proverOfRounds : {d : ℕ} → (R : Fin d → G × G) → (c f : Fp) →
    (χ : Fin d → Fp) → (j : ℕ) → (hj : j < d) →
    proverRoundPoint (proverOfRounds R c f) χ j = some (R ⟨j, hj⟩)
  | 0, _, _, _, _, _, hj => absurd hj (Nat.not_lt_zero _)
  | _ + 1, R, _, _, _, 0, hj => by
      show some ((R 0).1, (R 0).2) = some (R ⟨0, hj⟩)
      exact congrArg some (congrArg R (Fin.ext (by simp)))
  | _ + 1, R, c, f, χ, j + 1, hj => by
      show proverRoundPoint (proverOfRounds (Fin.tail R) c f) (Fin.tail χ) j = _
      rw [proverRoundPoint_proverOfRounds (Fin.tail R) c f (Fin.tail χ) j (Nat.lt_of_succ_lt_succ hj)]
      rfl

/-- `foldGens` commutes with reindexing the generators along a `Fin.cast` (`loHalf`/`hiHalf` read only the
index value, which `Fin.cast` preserves). The bookkeeping lemma letting the `flatAccept` fold — indexed by the
round count `d` — meet the closed-form `CF` fold, indexed by the challenge-*list* length `(List.ofFn χ).length`
(propositionally, not definitionally, `d`). -/
theorem foldGens_comp_cast {m n : ℕ} (h : n = m) (g : Fin (2 ^ (m + 1)) → G) (u : Fp) :
    foldGens (fun j : Fin (2 ^ (n + 1)) => g (Fin.cast (by rw [h]) j)) u
      = fun i : Fin (2 ^ n) => foldGens g u (Fin.cast (by rw [h]) i) := by
  subst h; rfl

/-- Fin-indexed generator fold: fold `g` by `foldGens · (χ j)⁻¹` down all `d` rounds to a single generator.
The cast-free counterpart of the deployed list fold `foldAll (List.ofFn χ) …`, matching `flatAccept`'s
per-round generator fold exactly, so the identity's induction stays cast-free. -/
def foldAllFin : {d : ℕ} → (Fin d → Fp) → (Fin (2 ^ d) → G) → G
  | 0, _, g => g 0
  | _ + 1, χ, g => foldAllFin (Fin.tail χ) (foldGens g (χ 0)⁻¹)

/-- `foldAll` reindexed along a list equality: rewrites the list and the generators' `Fin.cast` together (via
`subst`), the tool that peels `foldAll (List.ofFn χ)` past the dependent cast that blocks a bare `rw`. -/
theorem foldAll_congr_cast {u u' : List Fp} (h : u = u') (g : Fin (2 ^ u.length) → G) :
    foldAll u g = foldAll u' (fun j => g (Fin.cast (by rw [h]) j)) := by
  subst h; rfl

/-- **The Fin↔list generator-fold bridge.** The cast-free `foldAllFin χ g` equals the deployed list fold
`foldAll (List.ofFn χ) (g ∘ cast) 0`. Peels one round on each side (`foldAllFin` by definition, `foldAll` via
`foldAll_congr_cast` past the dependent cast) and reconciles the folded generators by `foldGens_comp_cast`. -/
theorem foldAllFin_eq : {d : ℕ} → (χ : Fin d → Fp) → (g : Fin (2 ^ d) → G) →
    foldAllFin χ g = foldAll (List.ofFn χ) (fun j => g (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j)) 0
  | 0, _, g => by simp only [foldAllFin]; rfl
  | d + 1, χ, g => by
      have hchal : List.ofFn χ = χ 0 :: List.ofFn (Fin.tail χ) := by rw [List.ofFn_succ]; rfl
      rw [foldAllFin, foldAllFin_eq (Fin.tail χ) (foldGens g (χ 0)⁻¹), foldAll_congr_cast hchal, foldAll]
      simp only [Fin.cast_cast]
      exact congrArg (fun gen => foldAll (List.ofFn (Fin.tail χ)) gen 0)
        (foldGens_comp_cast (List.length_ofFn (f := Fin.tail χ)) g (χ 0)⁻¹).symm

/-- `CF` reindexed along a challenge-list equality: rewrites the challenge list and the generators' `Fin.cast`
together (via `subst`). -/
theorem CF_congr_chal {u u' : List Fp} (h : u = u') (rounds : List (G × G))
    (g : Fin (2 ^ u.length) → G) (P : G) (c Uc Wc : Fp) (U W : G) :
    CF rounds u g P c Uc U Wc W
      = CF rounds u' (fun j => g (Fin.cast (by rw [h]) j)) P c Uc U Wc W := by
  subst h; rfl

/-- **The verifier-fold ↔ tree-fold identity — the deterministic core of `hbridge`.** For the concrete prover
tree `proverOfRounds R c f` built from a proof's fixed round points, the flat verifier predicate `flatAccept`
along challenge path `χ` is *exactly* the closed-form verifier equation `CF … = 0` over the round list
`List.ofFn R` and challenge list `List.ofFn χ`. Proven by induction on the round count: the leaf reconciles the
final opening (base), and each round folds one `(Lⱼ, Rⱼ)` into the commitment (`CF_cons`, the round point
undecomposed) while the value coefficient tracks the eval-vector fold `foldAllFin χ b`. No `sorry`/`axiom`. -/
theorem flatAccept_proverOfRounds :
    {d : ℕ} → (R : Fin d → G × G) → (c f : Fp) → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → Fp) →
    (U W : G) → (z : Fp) → (P : G) → (χ : Fin d → Fp) →
    (flatAccept (proverOfRounds R c f) g b U W z P χ ↔
      CF (List.ofFn R) (List.ofFn χ)
          (fun j => g (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j)) P c
          (-(z * c * foldAllFin χ b)) U (-f) W = 0)
  | 0, R, c, f, g, b, U, W, z, P, χ => by
      rw [proverOfRounds, flatAccept]
      simp only [CF, gPart]
      rw [← foldAllFin_eq]
      have hg : commitGen g (fun _ : Fin (2 ^ 0) => c) = c • g 0 := by simp [commitGen]
      have hb : commitGen b (fun _ : Fin (2 ^ 0) => c) = c * b 0 := by simp [commitGen]
      simp only [roundSum, List.ofFn_zero, List.zip_nil_right, List.map_nil, List.sum_nil, add_zero,
        foldAllFin, hg, hb]
      constructor
      · intro h; rw [h]; module
      · intro h; linear_combination (norm := module) h
  | d + 1, R, c, f, g, b, U, W, z, P, χ => by
      have hchal : List.ofFn χ = χ 0 :: List.ofFn (Fin.tail χ) := by rw [List.ofFn_succ]; rfl
      have hround : List.ofFn R = ((R 0).1, (R 0).2) :: List.ofFn (Fin.tail R) := by
        rw [List.ofFn_succ]; rfl
      rw [proverOfRounds, flatAccept,
          flatAccept_proverOfRounds (Fin.tail R) c f (foldGens g (χ 0)⁻¹) (foldGens b (χ 0)⁻¹) U W z
            (P + (χ 0)⁻¹ • (R 0).1 + (χ 0) • (R 0).2) (Fin.tail χ)]
      rw [hround, CF_congr_chal hchal]
      rw [show (((R 0).1, (R 0).2) : G × G)
            = ((R 0).1 + (0 : Fp) • U + (0 : Fp) • W, (R 0).2 + (0 : Fp) • U + (0 : Fp) • W) by simp]
      rw [CF_cons]
      simp only [mul_zero, add_zero, Fin.cast_cast]
      refine iff_of_eq (congrArg (· = (0 : G)) ?_)
      congr 1
      exact (foldGens_comp_cast (List.length_ofFn (f := Fin.tail χ)) g (χ 0)⁻¹).symm

/-- The Fin-indexed eval-vector fold is the flat `computeB` (the `b`-value bridge, Fin form): folds the powers
vector `evalVector d x` down `χ` to `computeB x (List.ofFn χ)`. `foldAllFin_eq` moves to the list fold and
`foldAll_evalVector` telescopes it. -/
theorem foldAllFin_evalVector {d : ℕ} (χ : Fin d → Fp) (x : Fp) :
    foldAllFin χ (evalVector d x) = computeB x (List.ofFn χ) := by
  rw [foldAllFin_eq]
  have hev : (fun j => evalVector d x (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j))
      = evalVector (List.ofFn χ).length x := by
    funext j; simp only [evalVector, Fin.val_cast]
  rw [hev]
  exact foldAll_evalVector x (List.ofFn χ)

/-- **`hbridge`, discharged for the deployed verifier (the algebra half).** halo2's actual verifier equation
`DeployedIpaVerifierEq` at any IPA challenge vector `ch.ipaRound` is *exactly* the flat verifier predicate
`flatAccept` of the concrete prover tree `proverOfRounds ps.ipaRounds ps.ipaC ps.ipaF` read off the proof —
with the eval vector `evalVector shape.k ch.x3` and the adjusted commitment `multiopen + [-v]g₀ + [ξ]S`. This is
the deterministic content of the prover-as-oracle bridge, now a **theorem**, not an assumption: chaining
`deployedVerifierEq_cf` (the verifier equation is `CF = 0`), `flatAccept_proverOfRounds` (`flatAccept` of the
tree is that same `CF = 0`), and `foldAllFin_evalVector` (the `U`-coefficient is `computeB`). The only residual
is the random-oracle adversary experiment above `hprob` (the querying forger and its query-loss) and
Blake2b-as-random-oracle — the uniform *measure* of `hprob` is justified standalone
(`roChallenges_ipaRound_uniform`; see its section). -/
theorem deployedVerifierEq_iff_flatAccept {shape : Shape} [DecidableEq Fp] [DecidableEq G] [Inhabited G]
    (g : Fin (2 ^ shape.k) → G) (w u : G) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) :
    DeployedIpaVerifierEq g w u vk ps ch ↔
      flatAccept (proverOfRounds ps.ipaRounds ps.ipaC ps.ipaF) g (evalVector shape.k ch.x3) u w ch.z
        (multiopenCommitment g w u vk ps ch
          + (∑ i, ([-(multiopenValue vk ps ch)].getD i.val 0) • g i) + ch.xi • ps.ipaS)
        ch.ipaRound := by
  rw [deployedVerifierEq_cf, flatAccept_proverOfRounds, foldAllFin_evalVector,
    show (-ps.ipaC * computeB ch.x3 (List.ofFn ch.ipaRound) * ch.z)
      = -(ch.z * ps.ipaC * computeB ch.x3 (List.ofFn ch.ipaRound)) from by ring]

/-! ## The staged (round-adaptive) adversary: `hbridge` discharged beyond the constant strategy

`deployedVerifierEq_iff_flatAccept` reads the *fixed* proof string as the constant strategy, so the accept
event it identifies is one proof's accept set over the challenge space (the static dichotomy). Rewinding a
real adversary produces more: the rewound runs share the pre-IPA prefix but answer each challenge path with
their *own* round points and final opening — a prefix-respecting **staged** adversary, which is exactly a
`Prover` tree together with the fixed pre-IPA data. This section discharges the bridge for *every* such
strategy: `pathData` reads the strategy's outputs along one challenge path, `spliceIpa` forms its proof
string at that path (pre-IPA fields fixed, IPA fields the path outputs), and
`deployedVerifierEq_iff_flatAccept_adaptive` proves halo2's verifier equation on that proof *is*
`flatAccept P` at the vector. So the corresponding capstones' `hprob` (`Soundness.Vesta`, the `_adaptive`
pair) is the accept probability of an adaptive strategy — the object rewinding produces — rather than of one
fixed proof. What remains is the execution-semantics identification (that a rewound random-oracle adversary
*induces* such a staged strategy, with its RO-query loss) and Blake2b-as-random-oracle; the uniform measure of
`hprob` is justified standalone (`roChallenges_ipaRound_uniform`; see its section), for the fixed proof string —
the adaptive splices' χ-dependent prefixes are part of this same floor. The
transcript-ordering and reprogramming content is internalized by `Forking.Ordering`,
`roChallenges_reprogramRounds`, and the Vesta `_adaptive_rewind` capstones. -/

/-- A strategy's outputs along one challenge path: the round points `(Lⱼ, Rⱼ)` it commits and the final
opening `(c, f)` it sends when the round challenges are `χ` — `pathData P χ = (rounds, c, f)`. The round-`0`
point is challenge-independent (the `Prover` node fixes it before its challenge); later points read only the
challenge prefix, by the tree shape. -/
def pathData : {d : ℕ} → Prover Fp G d → (Fin d → Fp) → (Fin d → G × G) × Fp × Fp
  | 0, .leaf c f, _ => (Fin.elim0, c, f)
  | _ + 1, .node L R cont, χ =>
      (Fin.cons (L, R) (pathData (cont (χ 0)) (Fin.tail χ)).1, (pathData (cont (χ 0)) (Fin.tail χ)).2)

/-- The staged adversary's proof string at one challenge path: every pre-IPA field is the fixed `ps`'s, and
the IPA fields (`ipaRounds`, `ipaC`, `ipaF`) are replaced — with the strategy's path outputs, in the intended
use. Rewinding shares the pre-IPA prefix and re-answers the rounds; this is that shape as data. -/
def spliceIpa {shape : Shape} (ps : ProofString shape Fp G) (R : Fin shape.k → G × G) (c f : Fp) :
    ProofString shape Fp G :=
  { ps with ipaRounds := R, ipaC := c, ipaF := f }

omit [AddCommGroup G] [Module Fp G] in
/-- Splicing a strategy path's IPA fields leaves the pre-IPA Fiat–Shamir challenges unchanged. After replacing
the IPA round vector by `χ`, the spliced proof and the original proof therefore have the same `Challenges`
record: only the `ipaRound` field differs, and both sides overwrite it. This is the pre-IPA half of the
staged rewinding capstone; `roChallenges_reprogramRounds` supplies the round-vector half. -/
theorem roChallenges_spliceIpa_pre {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (R : Fin shape.k → G × G)
    (c f : Fp) (χ : Fin shape.k → Fp) :
    { roChallenges O init (spliceIpa ps R c f) with ipaRound := χ }
      = { roChallenges O init ps with ipaRound := χ } := by
  refine Challenges.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl

/-- `flatAccept` reads the strategy only along the challenge path: the adaptive tree `P` at `χ` agrees with
the constant prover built from `P`'s own path outputs `pathData P χ`. The per-path bridge from the adaptive
tree to `flatAccept_proverOfRounds`'s constant form. -/
theorem flatAccept_pathData {U W : G} {z : Fp} : {d : ℕ} → (P : Prover Fp G d) →
    (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → Fp) → (Pwhole : G) → (χ : Fin d → Fp) →
    (flatAccept P g b U W z Pwhole χ ↔
      flatAccept (proverOfRounds (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2)
        g b U W z Pwhole χ)
  | 0, .leaf _ _, _, _, _, _ => Iff.rfl
  | d + 1, .node L R cont, g, b, Pwhole, χ => by
      rw [flatAccept, flatAccept_pathData (cont (χ 0)) (foldGens g (χ 0)⁻¹) (foldGens b (χ 0)⁻¹)
        (Pwhole + (χ 0)⁻¹ • L + (χ 0) • R) (Fin.tail χ), pathData, proverOfRounds]
      simp only [Fin.cons_zero, Fin.tail_cons]
      rw [flatAccept]

open Classical in
/-- **`hbridge`, discharged for the staged (round-adaptive) adversary.** halo2's actual verifier equation on
the strategy's spliced proof — pre-IPA fields the fixed `ps`'s, IPA fields the strategy's own outputs along
`χ` — at IPA challenges `χ` is *exactly* `flatAccept P` at `χ`, with the eval vector
`evalVector shape.k ch.x3` and the adjusted commitment built from the fixed `ps`. Chains
`deployedVerifierEq_iff_flatAccept` on the spliced proof (whose pre-IPA projections are definitionally
`ps`'s) with `flatAccept_pathData`. The constant-strategy identification is the special case
`P := proverOfRounds ps.ipaRounds ps.ipaC ps.ipaF`; here `hbridge` is a theorem for every prefix-respecting
strategy — the shape a rewound adversary's runs take. -/
theorem deployedVerifierEq_iff_flatAccept_adaptive {shape : Shape} [DecidableEq G] [Inhabited G]
    (g : Fin (2 ^ shape.k) → G) (w u : G) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (P : Prover Fp G shape.k) (χ : Fin shape.k → Fp) :
    DeployedIpaVerifierEq g w u vk
        (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2) {ch with ipaRound := χ} ↔
      flatAccept P g (evalVector shape.k ch.x3) u w ch.z
        (multiopenCommitment g w u vk ps ch
          + (∑ i, ([-(multiopenValue vk ps ch)].getD i.val 0) • g i) + ch.xi • ps.ipaS) χ := by
  rw [deployedVerifierEq_iff_flatAccept]
  have e1 : multiopenValue vk
      (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2) {ch with ipaRound := χ}
      = multiopenValue vk ps ch := rfl
  have e2 : multiopenCommitment g w u vk
      (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2) {ch with ipaRound := χ}
      = multiopenCommitment g w u vk ps ch := rfl
  rw [e1, e2]
  exact (flatAccept_pathData P g (evalVector shape.k ch.x3)
    (multiopenCommitment g w u vk ps ch
      + (∑ i, ([-(multiopenValue vk ps ch)].getD i.val 0) • g i) + ch.xi • ps.ipaS) χ).symm

/-! ## The deterministic content of the prover-as-oracle bridge `hbridge` is proven

`hbridge` (the hypothesis of `deployed_forking_soundness_of_bridge` below) is the **pointwise**
identification — it carries no probability — of the deployed verifier's accept event, as a function of the
challenge vector, with the flat predicate `flatAccept Q` of a prefix-respecting prover strategy `Q`.

Its deterministic content is a **theorem**: `deployedVerifierEq_iff_flatAccept` (the constant strategy
`proverOfRounds ps.ipaRounds ps.ipaC ps.ipaF`, round points fixed by the proof string) and
`deployedVerifierEq_iff_flatAccept_adaptive` (every staged strategy) prove halo2's actual verifier equation
`DeployedIpaVerifierEq` *is* `flatAccept` at the challenge vector — `flatAccept_proverOfRounds`
(`flatAccept` ↔ `CF = 0`) composed with `deployedVerifierEq_cf` (`CF = 0` ↔ the equation). The round-by-round
transcript ordering behind the prefix-respecting shape is likewise proven and sealed to the deployed schedule
(`Soundness.Forking.Ordering`, `deriveChallenges_ipaRound_eq`; `proverRoundPoint_proverOfRounds` for the tree
side).

**Where it is discharged.** The Vesta capstones (`Soundness.Vesta`) take halo2's **actual** accept
`DeployedIpaVerifierEq` — no abstract `hbridge` — and prove the bridge internally, at the cost of the
`S`-opening witness `commit urs s = ps.ipaS` (and the `shape.k`↔`urs.k` transport, by `subst`). The `_deployed`
pair uses the *constant* strategy, so its `hprob` is that fixed proof's accept measure over the whole challenge
space — the static dichotomy, *not* the Fiat–Shamir attack event; the `_adaptive` pair uses `spliceIpa`/
`pathData`, so its `hprob` is a round-adaptive adversary's accept probability, the object rewinding produces.
The abstract theorems (`deployed_forking_soundness_of_bridge` below,
`orchard_verifier_vesta_forking_opening`/`_constraint`) keep `hbridge` as a *modular* hypothesis over an
abstract `accepts`/`Q`.

What `hbridge` still names is the execution-semantics floor: a rewound random-oracle adversary *induces* such a
staged strategy, with its RO-query loss, deriving `hprob`'s accept probability — alongside
Blake2b-as-random-oracle. The uniform *measure* of `hprob` is justified standalone
(`roChallenges_ipaRound_uniform`; see its section). -/

open scoped ENNReal in
open Classical in
/-- **The deployed forking soundness from an explicit prover-as-oracle bridge.** The honest top of the forking
chain: from the deployed verifier's *actual* accept event `accepts χ` (the proof a function of `χ` — the
Fiat–Shamir/random-oracle model), the **explicit** faithfulness bridge `hbridge` identifying it with the
strategy predicate `flatAccept Q`, and the accept *probability* beating the knowledge error, it concludes the
deployed opening. `hbridge`'s deterministic content is a theorem (`deployedVerifierEq_iff_flatAccept`; see the
section above), so it is *dischargeable* — this theorem keeps it as an explicit hypothesis (discharging it in
place also needs the `S`-opening fact `commit urs s = ps.ipaS`). With `hbridge` supplied, the residual is
*only* the random-oracle adversary experiment above `hprob` (a querying forger and the rewinding query-loss)
plus Blake2b-as-random-oracle; every other link — challenge-vector uniformity (`roChallenges_ipaRound_uniform`),
extraction, root-consistency, value placement, the `u`-vs-`u⁻¹` convention, the transcript ordering — is a
theorem. The granular replacement for the monolithic `FiatShamirTree`. -/
noncomputable def deployed_forking_soundness_of_bridge [DecidableEq G] [Inhabited G] (urs : URS G)
    (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp) (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    (Q : Prover Fp G urs.k) (accepts : (Fin urs.k → Fp) → Prop)
    (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (hbridge : ∀ χ, accepts χ ↔ flatAccept Q urs.g b urs.u urs.w z
        (commit urs aDep + (z * 0) • urs.u + blind • urs.w) χ)
    (hprob : (kerr (Fintype.card Fp) urs.k : ℝ≥0∞) / Fintype.card (Fin urs.k → Fp)
        < (PMF.uniformOfFintype (Fin urs.k → Fp)).toOuterMeasure (Finset.univ.filter accepts)) :
    (∃ a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  refine deployed_forking_soundness_flat urs b v ξ z blind aMulti aDep s Q hz hb0 hP ?_
  have hset : Finset.univ.filter accepts
      = Finset.univ.filter (flatAccept Q urs.g b urs.u urs.w z
          (commit urs aDep + (z * 0) • urs.u + blind • urs.w)) := by
    ext χ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hbridge χ
  rwa [hset] at hprob

end Zcash.Snark
