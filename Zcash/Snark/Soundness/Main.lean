import Mathlib
import Zcash.Snark.Soundness.KnowledgeSoundness
import Zcash.Snark.Verifier.Assemble
import Zcash.Snark.Soundness.Consistency
import Zcash.Snark.Soundness.IpaSoundness
import Zcash.Snark.Soundness.Deployed.IpaPeel
import Zcash.Snark.Soundness.Deployed.Verification
import Zcash.Snark.Soundness.Forking.Assembly

/-!
# Soundness composition: conditional, and the deployed accept condition

This module composes IPA knowledge soundness into SNARK-relation soundness for the Orchard
verifier, in two layers:

* the `_conditional` family, over an opaque `accepts : Prop`. The suffix avoids overclaiming:
  these are scaffolds, not finished soundness.
* the deployed family, over the concrete accept `DeployedAccepts`: the rejecting `assemble?`
  succeeds and its MSM — the *fingerprint*, the transcribed form of halo2's final verifier
  check — evaluates to the group identity.

## The deployed route

The route derives the IPA opening and the gate constraint with `P`/`v` *pinned* to the proof's
`multiopenCommitment`/`multiopenValue` (read off `(vk, ps, ch)`, not free parameters; the
commitment is opened up to its declared blinding — see
`The tree opens the commitment up to declared U/W components` below):

1. `deployedAccepts_verifierEq` (*proven*) — the accept entails halo2's explicit IPA verifier
   equation `DeployedIpaVerifierEq`. Fidelity of that closed form to the Rust is the
   transcription layer (`assembleFinalMsm`/`ipaFold`, checked by the fingerprint), not re-proved
   here.
2. `FiatShamirTree` (*legacy residual*) — the equation yields a forked transcript
   (`ForkedTranscript`, as data): the deployed tree opening the pinned `P`/`v`; bundles the
   Fiat–Shamir forking with the extraction content it supplies (inventory in its docstring).
   `ForkedTranscript.ofAccepts` composes 1–2 above. Its (a)–(c) content is discharged on the live
   forking path (`Soundness.Forking.Rewind`, `deployed_forking_relation` — a computable reduction —
   and the Vesta `_forking_*` capstones), leaving the random-oracle rewinding as the floor.
3. The fork *either* peels cleanly onto `IpaAcceptV` — then `ipa_soundV` extracts the opening
   witness and `orchard_verifier_deployed_opening_of_forked`/`_constraint_of_forked` conclude
   `S` — *or* `NontrivialRelation.ofUnopenedFork` (*proven*, via
   `NontrivialRelation.ofDeployedTree`) computes a discrete-log relation among `(g, U, W)`,
   which DLR hardness forbids.

## The reduction form

Commitment binding is load-bearing in the peel, but the statements assume no independence of
`(g, U, W)`: in a prime-order group a nontrivial relation always *exists*, so that assumption
would be false — and a `… ∨ ∃-relation` conclusion would be propositionally `True`. Per the
breaks-as-computed-data convention (`Zcash.Security.RandomOracle`, and the Ironwood Book's
formal-verification conventions), the relation is instead *computed*: `NontrivialRelation`
carries the coefficients as data, the reductions are plain `def`s, and the positive soundness
statement is the contrapositive under DLR hardness — no efficient adversary can produce what
`NontrivialRelation.ofUnopenedFork` computes, so the clean opening holds. The binding-signature
argument makes the same move (`NontrivialRelation.ofImbalance` in
`Zcash.Security.BindingSignature.Balance`).

## Assumptions (the conditional family)

* **Opaque accept.** `accepts` is a free `Prop`, so `orchard_verifier_sound_conditional` says
  nothing about the fingerprint. The `_deployed` variants take `DeployedAccepts` instead.
* **Extraction bundled with Fiat–Shamir.** `ExtractableFromAcceptance` assumes the IPA
  knowledge-soundness conclusion, so the proven extraction lemmas (`accepting_fold_eq`,
  `extract_correct`) are off this path.
* **Circuit satisfaction assumed.** It also supplies `circuitSat a` rather than deriving it from
  the deployed gate check (`constraint_identity_of_accept` + the multiopen decode).

What is proven lives in the component lemmas (`extract_correct`, `accepting_fold_eq`,
`quotientCheck_sound`, and the computed binding reduction `NontrivialDLRelation.ofCollision`);
the open work is wiring
them onto this path. `Soundness.Vesta` instantiates the capstones at the concrete curve;
`Soundness.KnowledgeSoundness` lists the assumptions.
-/

namespace Zcash.Snark

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-- Assumption: if the proof is accepted, there exist a consistent transcript tree and a witness
`a` opening the commitment (`IpaRelation urs P b v a`) and satisfying the circuit
(`circuitSat a`). This assumes more than Fiat–Shamir: it bundles the extraction conclusion that
`accepting_fold_eq`/`extract_correct` already prove, so those lemmas are off this path; splitting
the two apart is open. -/
def ExtractableFromAcceptance (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → Fp) (v : Fp)
    (circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop) (accepts : Prop) : Prop :=
  accepts → ∃ (t : Tree Fp urs.k) (a : Fin (2 ^ urs.k) → Fp),
    Consistent t a ∧ IpaRelation urs P b v a ∧ circuitSat a

-- Tracked semantic-adequacy gap: `S` is a free `Prop` and `hencodes` an assumed hypothesis, so
-- the chain stops at "the extracted witness satisfies the gates" (`SnarkRelation`) and never
-- reaches "…therefore a valid Orchard action" (note well-formed, value balanced, nullifier
-- correctly derived, spend authorized). Closing it means instantiating `S` to the concrete
-- Orchard statement and proving `hencodes` — the output-side dual of the input-side
-- VK-correctness gap (see `Verifier/Assemble.lean`). Large; not started.
/-- **Conditional soundness (the scaffold).** *If* acceptance yields the extraction data
(`hextract`), then the statement `S` follows via `hencodes`. `accepts` is opaque and the
extraction is assumed (see the module docstring's assumption list); the deployed
`_opening`/`_constraint` theorems below take the concrete accept and derive what is assumed
here. -/
theorem orchard_verifier_sound_conditional (urs : URS G)
    {P : G} {b : Fin (2 ^ urs.k) → Fp} {v : Fp} {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop}
    {accepts : Prop} (haccepts : accepts)
    (hextract : ExtractableFromAcceptance urs P b v circuitSat accepts)
    {S : Prop} (hencodes : ∀ a, SnarkRelation urs P b v circuitSat a → S) :
    S := by
  obtain ⟨t, a, hcons, hopen, hsat⟩ := hextract haccepts
  exact hencodes a (knowledge_sound urs hcons hopen hsat).2

/-- The deployed verifier's accept condition: `assemble? vk ps ch` succeeds and the assembled MSM
evaluates to the group identity against the URS. Proof data that `assemble?` rejects (duplicate
queries, a mismatched `multiopenU` count, malformed permutation last-evals, zero inverse
denominators) is `False`. `hk` aligns the circuit shape's `k` with the URS's. -/
def DeployedAccepts [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : Prop :=
  match assemble? vk ps ch with
  | some m => (hk ▸ m : Msm urs.k Fp G).eval urs = 0
  | none => False

/-- The `urs.k`↔`shape.k` transport: evaluating the `hk`-transported MSM against `urs` is the
same as evaluating `m` against the URS rebuilt at `shape.k` with `urs`'s (transported)
generators. -/
theorem eval_cast {shape : Shape} {urs : URS G} (hk : shape.k = urs.k) (m : Msm shape.k Fp G) :
    (hk ▸ m : Msm urs.k Fp G).eval urs = m.eval ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ := by
  -- With `urs` free, destructuring + `subst hk` collapses the cast to `rfl`. Isolating the
  -- transport here keeps `deployedAccepts_verifierEq` from destructuring the URS in place,
  -- which would tangle the accept hypothesis's own `hk`-cast.
  obtain ⟨k, g, w, u⟩ := urs
  change shape.k = k at hk
  subst hk
  rfl

/-- **The deployed accept entails the verifier equation.** From `DeployedAccepts`,
`assemble?_eq_some` identifies the accepted MSM with the non-rejecting `assembleFinalMsm`, and
`deployed_verification_eq` rewrites its evaluation to the explicit closed form — so
`DeployedIpaVerifierEq` holds for the proof's actual `(vk, ps, ch)`. An implication, not an
`Iff`: the converse is a completeness claim, not made here. This discharges the MSM↔equation
correspondence the Fiat–Shamir bridge used to absorb; what the bridge still supplies is
inventoried at `FiatShamirTree`. -/
theorem deployedAccepts_verifierEq [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (h : DeployedAccepts urs hk vk ps ch) :
    DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk ps ch := by
  unfold DeployedAccepts at h
  cases hm : assemble? vk ps ch with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some m =>
      rw [hm] at h
      simp only [] at h
      rw [eval_cast hk m] at h
      have hmeq := assemble?_eq_some vk ps ch hm
      unfold DeployedIpaVerifierEq
      rw [← deployed_verification_eq (hk ▸ urs.g) urs.w urs.u ps ch
            (constructIntermediateSets (assembleQueries vk ps ch)), ← hmeq]
      exact h

/-! ## `IpaRelation` is derived from the transcript tree, not assumed

`Zcash.Snark.ipa_soundV` derives the full opening relation — `commit g a = P` and `⟨a,b⟩ = v` —
from an accepting IPA transcript tree (`IpaAcceptV`), binding-free, by 3-special soundness. So the
bridge no longer assumes `IpaRelation`; the MSM↔equation correspondence and the `P`/`v` pinning it
used to also absorb are discharged (`deployedAccepts_verifierEq`), and the `g`/`U`/`W` separation
is derived — its failure computes a relation (`NontrivialRelation.ofDeployedTree`). What the
bridge still absorbs beyond the rewinding is inventoried at `FiatShamirTree` below. -/

/-- `IpaAcceptV` over the URS generators derives `IpaRelation`: the witness `ipa_soundV` extracts
opens `P` and gives the inner product. Derived, not assumed. -/
theorem ipaRelation_of_acceptV (urs : URS G) (b : Fin (2 ^ urs.k) → Fp) (P : G) (v : Fp)
    (t : IpaTreeV Fp G urs.k) (h : IpaAcceptV urs.g b P v t) :
    ∃ a, IpaRelation urs P b v a := by
  obtain ⟨a, hP, hv⟩ := ipa_soundV urs.g b P v t h
  refine ⟨a, hP, ?_⟩
  have hib : innerProduct a b = commitGen b a := by simp only [innerProduct, commitGen, smul_eq_mul]
  rw [hib]; exact hv

/-- The `Σ'`-data companion of `ipaRelation_of_acceptV`: the *computed* opening witness (from
`ipa_extractV`). The deployed reduction opens through this rather than the `∃`-shaped version, so the
opening is carried as data — at prime order `∃ a, IpaRelation …` is vacuously satisfiable (any point has
a `g`-preimage), while the computed witness cannot be produced without the accepting transcript. -/
def ipaRelation_extract (urs : URS G) (b : Fin (2 ^ urs.k) → Fp) (P : G) (v : Fp)
    (t : IpaTreeV Fp G urs.k) (h : IpaAcceptV urs.g b P v t) :
    Σ' a, IpaRelation urs P b v a :=
  let s := ipa_extractV urs.g b P v t h
  ⟨s.1, s.2.1, by
    have hib : innerProduct s.1 b = commitGen b s.1 := by simp only [innerProduct, commitGen, smul_eq_mul]
    rw [hib]; exact s.2.2⟩

/-- The deployed commitment the IPA verifier opens (`multiopenCommitment` with `urs`'s generators
transported to the proof's `shape.k`): the pinned `P`, read off `(vk, ps, ch)`. Reducible, so it
is defeq to its body for matching against `DeployedIpaVerifierEq`'s leading term. -/
abbrev deployedCommitment [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : G :=
  multiopenCommitment (hk ▸ urs.g) urs.w urs.u vk ps ch

/-! ## The tree opens the commitment up to declared `U`/`W` components

Every deployed commitment is blinded: `deployedCommitment` is an MSM over the proof's commitment
points, each carrying a `W`-blind, so as a group element it has a nonzero `W`-component. The
tree's commitment track, by contrast, ends in the pure `g`-span (the leaf's `P = ⟨aP, g⟩`), and
the accept forces the opened commitment's `U`/`W`-components to `0` — at each node the three
child equations at distinct challenges Vandermonde-pin them. Opening the raw `deployedCommitment`
would therefore be unsatisfiable for every real proof. So the bridge *declares* those components
(`ForkedTranscript.pU`/`pW`; honest values `0` and the aggregate blind), and the tree opens
`deployedCommitment − [pU]u − [pW]w`. The declaration is itself pinned up to a break: two
declarations for one commitment collide into a computed relation
(`NontrivialRelation.ofCombinationCollision`). Satisfiability is checked, not asserted:
`ForkedTranscript.nonempty_of_opening` builds a transcript from any blinded opening. -/

/-- A forked deployed transcript, as data: the tree the Fiat–Shamir forking would produce, with
its accept certificate. It opens the declared commitment `deployedCommitment − [pU]u − [pW]w`
(the section note above) to the pinned `multiopenValue`. Carried as data, not behind an `∃`, so
the peel can *compute* a discrete-log relation from it (see `The reduction form` in the module
docstring). -/
structure ForkedTranscript [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) (z blind : Fp) where
  tree : DeployedIpaTreeV Fp G urs.k
  /-- The declared `U`-component of the pinned commitment (honest value: `0`). -/
  pU : Fp
  /-- The declared `W`-component of the pinned commitment (honest value: the aggregate blind). -/
  pW : Fp
  accepts : DeployedIpaAcceptV urs.g b urs.u urs.w z
    (deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
    (multiopenValue vk ps ch) blind tree

/-- The commitment the transcript's tree opens: the pinned `deployedCommitment` with the declared
`U`/`W` components peeled off. Reducible, so it is defeq to `accepts`'s commitment argument. -/
abbrev ForkedTranscript.openedCommitment [DecidableEq G] [Inhabited G] {shape : Shape}
    {urs : URS G} {hk : shape.k = urs.k} {vk : VerifyingKey shape Fp G}
    {ps : ProofString shape Fp G} {ch : Challenges shape.k Fp} {b : Fin (2 ^ urs.k) → Fp}
    {z blind : Fp} (fs : ForkedTranscript urs hk vk ps ch b z blind) : G :=
  deployedCommitment urs hk vk ps ch - fs.pU • urs.u - fs.pW • urs.w

/-- **The interface admits real proofs (completeness gate).** A blinded opening of the pinned
commitment — `deployedCommitment = ⟨a, g⟩ + [pU]u + [pW]w` with `⟨a, b⟩` the pinned
`multiopenValue` — yields a forked transcript: declare `(pU, pW)` and build the tree from the
witness (`deployedIpaAcceptV_of_witness`). Honest proofs have exactly this shape (`pU = 0`,
`pW` the aggregate blind), so assuming `FiatShamirTree` does not exclude them. -/
theorem ForkedTranscript.nonempty_of_opening [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    (u₁ u₂ u₃ : Fp) (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0)
    (a : Fin (2 ^ urs.k) → Fp) (pU pW : Fp)
    (hP : deployedCommitment urs hk vk ps ch = commitGen urs.g a + pU • urs.u + pW • urs.w)
    (hv : multiopenValue vk ps ch = commitGen b a) :
    Nonempty (ForkedTranscript urs hk vk ps ch b z blind) := by
  obtain ⟨t, ht⟩ := deployedIpaAcceptV_of_witness u₁ u₂ u₃ h12 h13 h23 hu₁ hu₂ hu₃
    urs.g b urs.u urs.w z blind a
  refine ⟨⟨t, pU, pW, ?_⟩⟩
  have hcancel : deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w
      = commitGen urs.g a := by rw [hP]; abel
  rw [hcancel, hv]
  exact ht

/-- **The forking bridge — the residual assumption.** Its premise is halo2's explicit verifier
equation `DeployedIpaVerifierEq` (which `deployedAccepts_verifierEq` proves the deployed accept
entails); it produces a `ForkedTranscript`. It bundles the Fiat–Shamir *forking* with the
special-soundness *extraction* content the forked transcripts would pin by Vandermonde over the
augmented `(g, U, W)` basis, here arriving as bridge-supplied tree data:

(a) the rewinding producing three accepting continuations per node at distinct nonzero challenges;
(b) the node-level `L`/`R` ↦ value/blinding decomposition (`Lv`/`Rv`/`Lw`/`Rw` — each round
    point's `(g, U, W)`-representation, which must not depend on `z`);
(c) the leaf `g`-representation `aP` of the folded commitment (`DeployedIpaTreeV`'s leaf data);
    and
(d) the commitment's declared `U`/`W` components `pU`/`pW` (the section note above) and the
    adjusted-commitment identity `P' = P − [v]g₀ + [ξ]S`: re-expressing the value term and the
    `S`/`ξ` blinding poly against the declared opening needs a representation of the adversary
    point `S` (ξ-side rewinding or AGM), so it is not a deterministic rewrite.

This `FiatShamirTree` is the *legacy* bundled bridge; (a)–(c)'s content is now discharged on the live
forking path (`Soundness.Forking.Rewind`'s `deployed_forking_relation` — a *computable* reduction returning
the opening as data — assembled from `Forking.Extractor`/`Forking.Assembly`, and the Vesta
`_forking_*`/`_rewind` capstones), leaving only (d)'s `S`/`ξ` representation and the random-oracle rewinding
itself as the floor. The per-leaf `g`/`U`/`W` separation is *derived* — its failure computes a relation
(`NontrivialRelation.ofDeployedTree`) — but `S`/`ξ` is not peeled, it lives in (d). `b`/`z`/`blind` are
bridge-mediated (the protocol fixes `b = evalVector urs.k ch.x3`, telescoping at the leaf to
`b₀ = computeB ch.x3 ·`, and `z = ch.z`); `v` is pinned, and `P` is pinned up to the declared `pU`/`pW`. -/
def FiatShamirTree [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (b : Fin (2 ^ urs.k) → Fp) (z blind : Fp) : Type _ :=
  DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk ps ch →
    ForkedTranscript urs hk vk ps ch b z blind

/-- The forked transcript of an accepting proof: the bridge applied to the *proven* verifier
equation (`deployedAccepts_verifierEq`). -/
def ForkedTranscript.ofAccepts [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    (haccepts : DeployedAccepts urs hk vk ps ch)
    (hFS : FiatShamirTree urs hk vk ps ch b z blind) :
    ForkedTranscript urs hk vk ps ch b z blind :=
  hFS (deployedAccepts_verifierEq urs hk vk ps ch haccepts)

/-- **The Fiat–Shamir forking hypothesis — the genuine residual (random-oracle floor).** On halo2's
explicit verifier equation, rewinding the random oracle yields the 3-special-soundness forking *output*, as
data: the declared `U`/`W` components `pU`/`pW` of the pinned commitment (the section note above) and a
`DeployedIpaTreeV` whose every node records three accepting continuations at distinct nonzero per-round
challenges and whose every leaf carries the flat closed-form verifier equation (`ForkAccept`), opening the
declared commitment `deployedCommitment − [pU]u − [pW]w`. This is exactly the rewinding content that cannot be
discharged in Lean; everything downstream of having it is a theorem (`fiatShamirTree_of_forking`). -/
def FiatShamirForking [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (b : Fin (2 ^ urs.k) → Fp) (z blind : Fp) : Type _ :=
  DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk ps ch →
    Σ' (pU pW : Fp) (t : DeployedIpaTreeV Fp G urs.k),
      ForkAccept urs.g b urs.u urs.w z
        (deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w) (multiopenValue vk ps ch) blind t

/-- **The tree-assembly discharge.** The forking output (`FiatShamirForking`) *builds* the `FiatShamirTree`
bridge: the forking supplies the declared components `pU`/`pW` and the distinct-challenge accepting
transcripts, and the deterministic assembly `forkAccept_to_acceptV` (threading the per-round fold to the
leaves, reconciling each flat closed-form equation to the reformulated leaf check) turns them into the
`ForkedTranscript`'s `DeployedIpaAcceptV`. So the residual narrows from the handwave "an accepting verifier
equation yields the whole 3-ary tree" to the genuine random-oracle floor "the rewinding yields the forked
transcripts": the tree assembly itself — the node `L`/`R`↦value/blinding fold and the adjusted-commitment
and leaf reconciliation — is a theorem, `sorry`/`axiom`-free. -/
def fiatShamirTree_of_forking [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) (z blind : Fp)
    (hForking : FiatShamirForking urs hk vk ps ch b z blind) :
    FiatShamirTree urs hk vk ps ch b z blind := by
  intro hEq
  obtain ⟨pU, pW, t, hFork⟩ := hForking hEq
  exact ⟨t, pU, pW, forkAccept_to_acceptV _ _ _ _ _ t hFork⟩

/-! ## The constraint-side hypotheses are unsatisfiable at a prime-order curve

`hcirc` below (and `hquot`/`hgood` in the constraint variant) quantify over *every* mathematical
opening `a` of the pinned `(P, b, v)`. At a prime-order curve those openings form an affine
subspace of dimension `≥ 2^k − 2` (two linear conditions on `2^k` coordinates), so any
`circuitSat` that genuinely reads the witness fails on almost all of it: the hypotheses are
unsatisfiable for the intended instantiation, not merely undischarged.
`circuitSatViaGates_of_check` does not help — it derives `circuitSat` for *one* `a` from that
`a`'s own point-check, never the quantified premise.

The implication: the `_of_forked` theorems below currently carry no gate-level content — they
conclude `S` only for `circuitSat` instantiations that ignore the witness, so no soundness for
the deployed circuit's constraints follows from them yet. Their opening side stands on its own;
the constraint side is a scaffold until it is restated over the *extracted* witness via the
multiopen decode (`batch_open_soundV`), which is still open. -/

/-- **The deployed binding reduction, as a computed relation.** A forked transcript whose
projection is *not* cleanly accepted computes a nontrivial discrete-log relation among the
augmented generators — `NontrivialRelation.ofDeployedTree` at the declared opening
`fs.openedCommitment` and the pinned `multiopenValue`. Why this forces the clean accept — the
hypothesis of the `_of_forked` theorems below — is `The reduction form` in the module
docstring. -/
def NontrivialRelation.ofUnopenedFork [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp} (hz : z ≠ 0)
    (fs : ForkedTranscript urs hk vk ps ch b z blind)
    (hne : ¬ IpaAcceptV urs.g b fs.openedCommitment (multiopenValue vk ps ch)
      (projTree fs.tree)) :
    NontrivialRelation (F := Fp) urs.g urs.u urs.w :=
  NontrivialRelation.ofDeployedTree hz urs.g b fs.openedCommitment
    (multiopenValue vk ps ch) blind fs.tree fs.accepts hne

/-- **Deployed opening, given a clean fork.** From a forked transcript whose projection is
cleanly accepted, `ipa_soundV` extracts the opening witness for the declared opening
`fs.openedCommitment` — the blinded opening of the pinned commitment,
`deployedCommitment = ⟨a, g⟩ + [pU]u + [pW]w` with `⟨a, b⟩ = multiopenValue`; the circuit side
(`hcirc`) and VK-correctness (`hencodes`) conclude `S`. The clean-accept hypothesis `hclean` is
what DLR hardness forces — its failure computes a relation
(`NontrivialRelation.ofUnopenedFork`). `hcirc` has the unsatisfiable shape described in the
section note above. -/
theorem orchard_verifier_deployed_opening_of_forked [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop}
    (fs : ForkedTranscript urs hk vk ps ch b z blind)
    (hclean : IpaAcceptV urs.g b fs.openedCommitment (multiopenValue vk ps ch)
      (projTree fs.tree))
    (hcirc : ∀ a, IpaRelation urs fs.openedCommitment b (multiopenValue vk ps ch) a →
      circuitSat a)
    {S : Prop} (hencodes : ∀ a, SnarkRelation urs fs.openedCommitment b
      (multiopenValue vk ps ch) circuitSat a → S) :
    S := by
  obtain ⟨a, hrel⟩ := ipaRelation_of_acceptV urs b fs.openedCommitment
    (multiopenValue vk ps ch) (projTree fs.tree) hclean
  exact hencodes a ⟨hrel, hcirc a hrel⟩

/-! ## `circuitSat` is derived from the verifier's gate check + Schwartz–Zippel

The constraint side mirrors the opening side. The verifier checks the gate identity only at the
challenge `x` — a point check (`quotientCheck`: `numerator.eval x = h.eval x · (xⁿ−1)`).
`circuitSatViaGates_of_check` lifts that point check to the polynomial identity
`circuitSatViaGates` (the witness's decoded columns satisfy the gates) provided `x` avoids the
Schwartz–Zippel *bad set* — the roots of the difference polynomial when it is nonzero, which is
what `hgood` excludes. So `circuitSat`, instantiated to the concrete `circuitSatViaGates`, is
derived from the verifier's actual gate check rather than taken as an opaque hypothesis. -/

open Polynomial in
/-- **Deployed opening and constraint, given a clean fork.** As
`orchard_verifier_deployed_opening_of_forked`, with the circuit side derived too: `circuitSat` —
instantiated to `circuitSatViaGates` — from the verifier's gate point-check `hquot` at the
challenge `x`, lifted to the polynomial identity by Schwartz–Zippel (`hgood`), via
`circuitSatViaGates_of_check`. `hquot`/`hgood` share `hcirc`'s unsatisfiable shape (see the
section note above): the verifier's actual gate check constrains the *claimed* evaluations, not
every opening's decode. -/
theorem orchard_verifier_deployed_constraint_of_forked [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (fs : ForkedTranscript urs hk vk ps ch b z blind)
    (hclean : IpaAcceptV urs.g b fs.openedCommitment (multiopenValue vk ps ch)
      (projTree fs.tree))
    (hquot : ∀ a, IpaRelation urs fs.openedCommitment b (multiopenValue vk ps ch) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs fs.openedCommitment b (multiopenValue vk ps ch) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs fs.openedCommitment b (multiopenValue vk ps ch)
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S) :
    S := by
  obtain ⟨a, hrel⟩ := ipaRelation_of_acceptV urs b fs.openedCommitment
    (multiopenValue vk ps ch) (projTree fs.tree) hclean
  have hsat : circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg a :=
    circuitSatViaGates_of_check fixedCols decodeAdvice decodeInstance y gates hpoly deg a x
      (hquot a hrel) (hgood a hrel)
  exact hencodes a ⟨hrel, hsat⟩

end Zcash.Snark
