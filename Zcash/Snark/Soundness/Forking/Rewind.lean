import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.UniformMeasure
import Zcash.Snark.Soundness.Forking.Oracle
import Zcash.Snark.Soundness.Forking.Ordering

/-!
# Random-oracle reprogramming for the deployed verifier

`ofOracle` and `roChallenges` run the deployed schedule with a random oracle. `reprogramRounds` and
the `reprogramX*` family show that changing the oracle at one squeeze prefix is the same as
replacing that challenge, leaving every other read untouched.

`Soundness.Forking.Adversary` builds the querying-adversary reduction on top. Identifying Blake2b
with the modeled random oracle remains an assumption.
-/

namespace Zcash.Snark

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- A random-oracle-backed Fiat–Shamir instance: the squeeze *is* the oracle `O`. -/
def ofOracle (O : List (TranscriptElt Fp G) → Fp) : FiatShamir Fp G := ⟨O⟩

/-- Run the deployed challenge schedule with oracle `O`. -/
def roChallenges {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) : Challenges shape.k Fp :=
  deriveChallenges (ofOracle O) init ps

/-! ## Redrawing the round vector *is* reprogramming the deployed oracle

The forking proof replaces the IPA challenge vector. The random-oracle experiment instead changes the
oracle at each round prefix and reruns the schedule. `roChallenges_reprogramRounds` proves these are
the same operation. Distinct, longer round prefixes ensure that earlier challenges are unchanged.
-/

open Classical in
/-- Change the oracle answer at every IPA round prefix to the corresponding value in `χ`. -/
noncomputable def reprogramRounds {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fin shape.k → Fp) :
    List (TranscriptElt Fp G) → Fp :=
  fun t => if h : ∃ j : Fin shape.k,
      t = roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j
    then χ h.choose else O t

omit [AddCommGroup G] [Module Fp G] in
/-- At the round-`j` prefix, the reprogrammed oracle answers `χ j`. -/
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

omit [AddCommGroup G] [Module Fp G] in
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

omit [AddCommGroup G] [Module Fp G] in
/-- Reprogramming leaves every transcript no longer than the pre-IPA prefix unchanged. -/
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

omit [AddCommGroup G] [Module Fp G] in
/-- Rerunning the deployed schedule with `reprogramRounds` replaces only its IPA round vector. -/
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

/-! ## Challenge-vector uniformity

For a fixed proof, distinct round prefixes yield a uniform challenge vector. Computed adversaries
instead use the full query experiment in `Soundness.Forking.Adversary`. -/

omit [AddCommGroup G] [Module Fp G] in
/-- Each deployed IPA round challenge is the oracle answer at its round prefix. -/
theorem roChallenges_ipaRound_apply {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (j : Fin shape.k) :
    (roChallenges O init ps).ipaRound j
      = O (roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j) :=
  deriveChallenges_ipaRound_eq (ofOracle O) init ps j

omit [AddCommGroup G] [Module Fp G] in
/-- A uniform random oracle gives a uniform IPA challenge vector at the distinct round prefixes. -/
theorem roChallenges_ipaRound_uniform [DecidableEq G] {shape : Shape}
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) :
    (PMF.uniformOfFintype
        (↥(Set.range (roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds)) → Fp)).map
        (fun O j => O (Equiv.ofInjective _
          (roundTranscriptFin_injective (preIpaTranscript init ps) ps.ipaRounds) j))
      = PMF.uniformOfFintype (Fin shape.k → Fp) :=
  uniformOfFintype_map_eval_injective _
    (roundTranscriptFin_injective (preIpaTranscript init ps) ps.ipaRounds)

/-! ## Redrawing the batching challenge is reprogramming at the `x₄` squeeze

The multiopen rewinding (`Soundness.Multiopen.Decode`) forks on the batching
challenge: redraw `x₄`, re-run, and collect accepting runs at distinct values. `reprogramX4` is the
one-point analogue of `reprogramRounds` at the sealed `x₄` prefix (`preX4Transcript`,
`deriveChallenges_x4_eq`), and its pointwise apply lemmas (`reprogramX4_apply_x4`/`_short`/`_long`)
give the identification field by field: re-running the deployed schedule under it is exactly the
honest run with `x₄` replaced — every other squeeze input has a different length, so nothing else
moves. Both halves of what the `{ch with x4 := ξ}` runs then owe the terminal capstones are theorems
(`Soundness.Multiopen.Deployed`): the flat-batch power form of the deployed statement in `x₄` is proven
over the fingerprinted grouping's aggregates (`deployedCommitment_x4_batch`/`multiopenValue_x4_batch`),
and the accept-probability step is the single-squeeze counting floor
(`exists_injective_accepting_of_measure`) — the same
seam shape the round-forking ladder carries, extending the IPA-round ordering treatment to the
multiopen squeeze points. -/

open Classical in
/-- Reprogram the oracle at the `x₄` squeeze prefix of the fixed proof string, answering `ξ` there
and `O` elsewhere. -/
noncomputable def reprogramX4 {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (ξ : Fp) :
    List (TranscriptElt Fp G) → Fp :=
  fun t => if t = preX4Transcript init ps then ξ else O t

omit [AddCommGroup G] [Module Fp G] in
/-- At the `x₄` prefix the reprogrammed oracle answers `ξ`. -/
theorem reprogramX4_apply_x4 {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (ξ : Fp) :
    reprogramX4 O init ps ξ (preX4Transcript init ps) = ξ := by
  simp [reprogramX4]

omit [AddCommGroup G] [Module Fp G] in
/-- Off the `x₄` prefix the reprogrammed oracle is `O`. -/
theorem reprogramX4_apply_ne {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (ξ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t ≠ preX4Transcript init ps) :
    reprogramX4 O init ps ξ t = O t := by
  simp [reprogramX4, ht]

omit [AddCommGroup G] [Module Fp G] in
/-- Any input whose length differs from the `x₄` prefix — every other squeeze input of the deployed
schedule — is untouched by the `x₄` reprogramming. -/
theorem reprogramX4_apply_length {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (ξ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t.length ≠ (preX4Transcript init ps).length) :
    reprogramX4 O init ps ξ t = O t :=
  reprogramX4_apply_ne O init ps ξ (fun h => ht (congrArg List.length h))

omit [AddCommGroup G] [Module Fp G] in
/-- An input strictly shorter than the `x₄` prefix is untouched (the pre-`x₄` squeeze inputs). -/
theorem reprogramX4_apply_short {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (ξ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t.length < (preX4Transcript init ps).length) :
    reprogramX4 O init ps ξ t = O t :=
  reprogramX4_apply_length O init ps ξ ht.ne

omit [AddCommGroup G] [Module Fp G] in
/-- An input strictly longer than the `x₄` prefix is untouched (the `ξ`/`z` and IPA-round inputs). -/
theorem reprogramX4_apply_long {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (ξ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : (preX4Transcript init ps).length < t.length) :
    reprogramX4 O init ps ξ t = O t :=
  reprogramX4_apply_length O init ps ξ ht.ne'

/-! **From the pointwise reprogramming to the challenge-level identity.** The
lemmas above pin `reprogramX4`'s behaviour at every squeeze input: it answers `ξ` at the `x₄` prefix
(`reprogramX4_apply_x4`) and leaves every other input at `O` (`reprogramX4_apply_short`/`_long`,
since the pre-`x₄` squeeze inputs are strictly shorter than the `x₄` prefix and the `ξ`/`z`/IPA-round
inputs strictly longer — `preIpaTranscript_length_eq_preX4`, `roundTranscriptFin_length`). Composed with
the squeeze seals `deriveChallenges_x{3,4}_eq`, these give, field by field, that running the deployed
schedule under `reprogramX4` reproduces the honest run with `x₄` replaced by `ξ` — i.e. the
`{ch with x4 := ξ}` events the multiopen rewinding ranges over are oracle-reprogramming events, the
multiopen-squeeze analogue of `roChallenges_reprogramRounds` for the IPA rounds.

Packaging this as a single `Challenges`-record equality (as `roChallenges_reprogramRounds` does) is
left implicit: each field projection forces whnf of the entire `deriveChallenges` record, and unlike
the round case the batching challenge's inlined `x₄` prefix makes that packaging prohibitively
expensive to elaborate. Downstream consumers take the per-run accept
facts, not the record identity, so the pointwise lemmas above are the operative form. -/

/-! ## Redrawing the compression challenge is reprogramming at the `x₁` squeeze

The within-set rewinding (`Soundness.Multiopen.Deployed`, the member-column decode) forks one squeeze
earlier: redraw `x₁`, and the rewound prover re-sends the post-`x₁` proof fields — `q′`, `u`, and the
IPA opening (`spliceMultiopen`) — so `x₃`/`x₄`/`ξ`/`z` and the round challenges re-randomize through
their squeeze inputs (which absorb the fresh `q′`/`u`), while everything absorbed before `x₁` — the
column commitments, every claimed evaluation (`adviceEvals_mem_preX1Transcript` and companions), hence
the whole query list and the fingerprinted grouping — is shared across runs. `reprogramX1` is the
one-point reprogramming at the sealed `x₁` prefix (`preX1Transcript`, `deriveChallenges_x1_eq`); as
with `reprogramX4`, the pointwise apply lemmas are the operative form, and the run events the member
decode ranges over are `x1RunChallenges`/`spliceMultiopen` records (`Soundness.Multiopen.Deployed`). -/

open Classical in
/-- Reprogram the oracle at the `x₁` squeeze prefix of the fixed proof string, answering `χ` there
and `O` elsewhere. -/
noncomputable def reprogramX1 {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp) :
    List (TranscriptElt Fp G) → Fp :=
  fun t => if t = preX1Transcript init ps then χ else O t

omit [AddCommGroup G] [Module Fp G] in
/-- At the `x₁` prefix the reprogrammed oracle answers `χ`. -/
theorem reprogramX1_apply_x1 {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp) :
    reprogramX1 O init ps χ (preX1Transcript init ps) = χ := by
  simp [reprogramX1]

omit [AddCommGroup G] [Module Fp G] in
/-- Off the `x₁` prefix the reprogrammed oracle is `O`. -/
theorem reprogramX1_apply_ne {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t ≠ preX1Transcript init ps) :
    reprogramX1 O init ps χ t = O t := by
  simp [reprogramX1, ht]

omit [AddCommGroup G] [Module Fp G] in
/-- Any input whose length differs from the `x₁` prefix — every other squeeze input of the deployed
schedule (`preX2Transcript_length_eq` and the chain onward) — is untouched by the `x₁`
reprogramming. -/
theorem reprogramX1_apply_length {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t.length ≠ (preX1Transcript init ps).length) :
    reprogramX1 O init ps χ t = O t :=
  reprogramX1_apply_ne O init ps χ (fun h => ht (congrArg List.length h))

omit [AddCommGroup G] [Module Fp G] in
/-- An input strictly shorter than the `x₁` prefix is untouched (the pre-`x₁` squeeze inputs). -/
theorem reprogramX1_apply_short {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t.length < (preX1Transcript init ps).length) :
    reprogramX1 O init ps χ t = O t :=
  reprogramX1_apply_length O init ps χ ht.ne

omit [AddCommGroup G] [Module Fp G] in
/-- An input strictly longer than the `x₁` prefix is untouched (the `x₂`/`x₃`/`x₄`/`ξ`/`z` and
IPA-round inputs — on the rewound run these absorb the spliced post-`x₁` fields, and their lengths
stay strictly beyond the `x₁` prefix). -/
theorem reprogramX1_apply_long {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : (preX1Transcript init ps).length < t.length) :
    reprogramX1 O init ps χ t = O t :=
  reprogramX1_apply_length O init ps χ ht.ne'

/-! ## Redrawing the interpolation and set-separation challenges: reprogramming at `x₃` and `x₂`

The r-polynomial layer (the claimed-evaluation binding) forks one and two squeezes above the `x₄`
collapse: redraw `x₃` and the rewound prover re-sends the post-`x₃` fields (`u`, the IPA opening) —
the quotient commitment `q′` and the point-set aggregates are absorbed before `x₃`
(`qPrime_mem_preX3Transcript`, the pre-`x₁` commitments), so they are shared across runs while the
claimed set evaluations re-randomize; redraw `x₂` and additionally the interpolation point
re-randomizes, separating the per-set contributions by `x₂`-powers. `reprogramX3`/`reprogramX2` are
the one-point reprogrammings at the sealed prefixes (`preX3Transcript`/`preX2Transcript`,
`deriveChallenges_x3_eq`/`_x2_eq`); as with `reprogramX4`, the pointwise apply lemmas are the
operative form. -/

open Classical in
/-- Reprogram the oracle at the `x₃` squeeze prefix of the fixed proof string, answering `χ` there
and `O` elsewhere. -/
noncomputable def reprogramX3 {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp) :
    List (TranscriptElt Fp G) → Fp :=
  fun t => if t = preX3Transcript init ps then χ else O t

omit [AddCommGroup G] [Module Fp G] in
/-- At the `x₃` prefix the reprogrammed oracle answers `χ`. -/
theorem reprogramX3_apply_x3 {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp) :
    reprogramX3 O init ps χ (preX3Transcript init ps) = χ := by
  simp [reprogramX3]

omit [AddCommGroup G] [Module Fp G] in
/-- Off the `x₃` prefix the reprogrammed oracle is `O`. -/
theorem reprogramX3_apply_ne {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t ≠ preX3Transcript init ps) :
    reprogramX3 O init ps χ t = O t := by
  simp [reprogramX3, ht]

omit [AddCommGroup G] [Module Fp G] in
/-- Any input whose length differs from the `x₃` prefix is untouched by the `x₃` reprogramming. -/
theorem reprogramX3_apply_length {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t.length ≠ (preX3Transcript init ps).length) :
    reprogramX3 O init ps χ t = O t :=
  reprogramX3_apply_ne O init ps χ (fun h => ht (congrArg List.length h))

omit [AddCommGroup G] [Module Fp G] in
/-- An input strictly shorter than the `x₃` prefix is untouched (the pre-`x₃` squeeze inputs). -/
theorem reprogramX3_apply_short {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t.length < (preX3Transcript init ps).length) :
    reprogramX3 O init ps χ t = O t :=
  reprogramX3_apply_length O init ps χ ht.ne

omit [AddCommGroup G] [Module Fp G] in
/-- An input strictly longer than the `x₃` prefix is untouched (the `x₄`/`ξ`/`z` and IPA-round
inputs). -/
theorem reprogramX3_apply_long {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : (preX3Transcript init ps).length < t.length) :
    reprogramX3 O init ps χ t = O t :=
  reprogramX3_apply_length O init ps χ ht.ne'

open Classical in
/-- Reprogram the oracle at the `x₂` squeeze prefix of the fixed proof string, answering `χ` there
and `O` elsewhere. -/
noncomputable def reprogramX2 {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp) :
    List (TranscriptElt Fp G) → Fp :=
  fun t => if t = preX2Transcript init ps then χ else O t

omit [AddCommGroup G] [Module Fp G] in
/-- At the `x₂` prefix the reprogrammed oracle answers `χ`. -/
theorem reprogramX2_apply_x2 {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp) :
    reprogramX2 O init ps χ (preX2Transcript init ps) = χ := by
  simp [reprogramX2]

omit [AddCommGroup G] [Module Fp G] in
/-- Off the `x₂` prefix the reprogrammed oracle is `O`. -/
theorem reprogramX2_apply_ne {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t ≠ preX2Transcript init ps) :
    reprogramX2 O init ps χ t = O t := by
  simp [reprogramX2, ht]

omit [AddCommGroup G] [Module Fp G] in
/-- Any input whose length differs from the `x₂` prefix is untouched by the `x₂` reprogramming. -/
theorem reprogramX2_apply_length {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t.length ≠ (preX2Transcript init ps).length) :
    reprogramX2 O init ps χ t = O t :=
  reprogramX2_apply_ne O init ps χ (fun h => ht (congrArg List.length h))

omit [AddCommGroup G] [Module Fp G] in
/-- An input strictly shorter than the `x₂` prefix is untouched (the pre-`x₂` squeeze inputs,
`preX2Transcript_length_eq` placing `x₁` immediately below). -/
theorem reprogramX2_apply_short {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t.length < (preX2Transcript init ps).length) :
    reprogramX2 O init ps χ t = O t :=
  reprogramX2_apply_length O init ps χ ht.ne

omit [AddCommGroup G] [Module Fp G] in
/-- An input strictly longer than the `x₂` prefix is untouched (the `x₃`/`x₄`/`ξ`/`z` and IPA-round
inputs — `preX3Transcript_length_eq` and the chain onward). -/
theorem reprogramX2_apply_long {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (χ : Fp)
    {t : List (TranscriptElt Fp G)} (ht : (preX2Transcript init ps).length < t.length) :
    reprogramX2 O init ps χ t = O t :=
  reprogramX2_apply_length O init ps χ ht.ne'

/-! ## Redrawing the gate-check challenge is reprogramming at the `x` squeeze

The good-challenge derivation (`Soundness.GoodChallenge` and the `_xgood` capstone rungs)
spends an accept measure over the vanishing-check challenge `x`. The runs it ranges over are
reprogramming events at the sealed `x` prefix (`preXTranscript`, `deriveChallenges_x_eq` —
`Soundness.Forking.Ordering`): everything the Schwartz–Zippel difference polynomial is built from —
the column commitments (`adviceCommitments_mem_preXTranscript`) and the quotient pieces
(`hPieces_mem_preXTranscript`) — is absorbed before the `x` squeeze, so the polynomial is pinned
across the rewound runs while `x` alone resamples. As with `reprogramX4`/`reprogramX1`, the pointwise
apply lemmas are the operative form (the pre-`x` squeeze inputs are strictly shorter, the
post-`x` inputs strictly longer — `preXTranscript_length_lt_preX1Transcript` and the length chain
onward). -/

open Classical in
/-- Reprogram the oracle at the `x` squeeze prefix of the fixed proof string, answering `xv` there
and `O` elsewhere. -/
noncomputable def reprogramX {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (xv : Fp) :
    List (TranscriptElt Fp G) → Fp :=
  fun t => if t = preXTranscript init ps then xv else O t

omit [AddCommGroup G] [Module Fp G] in
/-- At the `x` prefix the reprogrammed oracle answers `xv`. -/
theorem reprogramX_apply_x {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (xv : Fp) :
    reprogramX O init ps xv (preXTranscript init ps) = xv := by
  simp [reprogramX]

omit [AddCommGroup G] [Module Fp G] in
/-- Off the `x` prefix the reprogrammed oracle is `O`. -/
theorem reprogramX_apply_ne {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (xv : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t ≠ preXTranscript init ps) :
    reprogramX O init ps xv t = O t := by
  simp [reprogramX, ht]

omit [AddCommGroup G] [Module Fp G] in
/-- Any input whose length differs from the `x` prefix — every other squeeze input of the deployed
schedule — is untouched by the `x` reprogramming. -/
theorem reprogramX_apply_length {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (xv : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t.length ≠ (preXTranscript init ps).length) :
    reprogramX O init ps xv t = O t :=
  reprogramX_apply_ne O init ps xv (fun h => ht (congrArg List.length h))

omit [AddCommGroup G] [Module Fp G] in
/-- An input strictly shorter than the `x` prefix is untouched (the `θ`/`β`/`γ`/`y` squeeze
inputs). -/
theorem reprogramX_apply_short {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (xv : Fp)
    {t : List (TranscriptElt Fp G)} (ht : t.length < (preXTranscript init ps).length) :
    reprogramX O init ps xv t = O t :=
  reprogramX_apply_length O init ps xv ht.ne

omit [AddCommGroup G] [Module Fp G] in
/-- An input strictly longer than the `x` prefix is untouched (the compression, multiopen, `ξ`/`z`,
and IPA-round inputs — `preXTranscript_length_lt_preX1Transcript` and the length chain onward). -/
theorem reprogramX_apply_long {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (xv : Fp)
    {t : List (TranscriptElt Fp G)} (ht : (preXTranscript init ps).length < t.length) :
    reprogramX O init ps xv t = O t :=
  reprogramX_apply_length O init ps xv ht.ne'

open scoped ENNReal in
/-- If a nonzero blinding shift is fixed before uniform `ξ`, it hits any target with probability at
most `1 / |Fp|`. -/
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

/-! ## Splicing the IPA block

An adversary supplies different IPA fields along different challenge paths. `spliceIpa` inserts one
such block into a fixed pre-IPA proof, and `roChallenges_spliceIpa_pre` records that doing so leaves
every pre-IPA challenge alone.
-/

/-- Replace a proof's IPA fields while keeping its pre-IPA fields fixed. -/
def spliceIpa {shape : Shape} (ps : ProofString shape Fp G) (R : Fin shape.k → G × G) (c f : Fp) :
    ProofString shape Fp G :=
  { ps with ipaRounds := R, ipaC := c, ipaF := f }

omit [AddCommGroup G] [Module Fp G] in
/-- Splicing IPA fields leaves all pre-IPA Fiat–Shamir challenges unchanged. -/
theorem roChallenges_spliceIpa_pre {shape : Shape} (O : List (TranscriptElt Fp G) → Fp)
    (init : List (TranscriptElt Fp G)) (ps : ProofString shape Fp G) (R : Fin shape.k → G × G)
    (c f : Fp) (χ : Fin shape.k → Fp) :
    { roChallenges O init (spliceIpa ps R c f) with ipaRound := χ }
      = { roChallenges O init ps with ipaRound := χ } := by
  refine Challenges.ext' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> rfl


end Zcash.Snark
