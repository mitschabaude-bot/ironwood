import Mathlib.Probability.Distributions.Uniform
import Zcash.Snark.Verifier.FiatShamir
import Zcash.Arithmetic

/-!
# Random-oracle model for Fiat–Shamir

`Verifier.FiatShamir` derives challenges with an abstract `squeeze`; the deployed verifier uses
Blake2b. The soundness proof models it as a random function with uniform answers, changeable at
one query. This module supplies the two primitives the forking development is framed with:
`reprogram`, which changes the answer at one transcript prefix, and `uniformChallenge` with
`uniformChallenge_badSet`, a fresh field challenge and its chance of landing in a finite bad set.

## Challenge-vector distribution

`Rewind.roChallenges_ipaRound_uniform` derives the uniform distribution on IPA challenge vectors
for a fixed proof from one assumption: the Blake2b squeeze is a uniform random function `O` over
its query domain. Each round reads `O` at a distinct prefix, so the answers are independent and
uniform. This also assumes injective transcript encoding and an exactly uniform
`Challenge255 → Fp` conversion. The distribution is therefore proved inside the model; the model
itself stays an assumption about Blake2b.

## The `Challenge255 → Fp` conversion bias

The deployed conversion is not exactly uniform. Halo2 reduces a fixed-width byte string modulo
`p`, which leaves each residue with probability `⌊2^w/p⌋/2^w` or `⌈2^w/p⌉/2^w`. Summed over `Fp`
that is a total-variation distance of at most `|Fp| / 2^w` per squeeze, so a `q`-squeeze run loses
at most `q · |Fp| / 2^w` — the same `q` that `Adversary.OracleComp` already charges query loss
against.

`PMFEventBiasLE` is the explicit boundary between that deployed distribution and an ideal
experiment.  The consensus-generic Action endpoints consume this relation in their final conjunct
and add its `ε` to the complete accepting-false-statement bound.  Instantiating `ε` still requires
pinning the conversion width and transcript implementation; their ideal `generatorRO` conjuncts
do not claim that implementation fact.

## What the adversary model still assumes

The querying-adversary experiment is present: `Adversary.OracleComp` models a bounded-query
adversary, `Adversary.Algebraic` decodes its deployed transcript into the representation-carrying
proof the AGM reduction reads, and the straight-line endpoints in
`Composition.StraightLineConstraint` price failure from the adversary's own advantage. Query loss
is charged explicitly: `(Q + 1) · (1/p)` per pinned squeeze and for the adaptive `z = 0` slice.
What remains is:

* **Efficiency modeling.** The deployed combined finder has a pointwise four-invocation bound
  (`straightLineConstraintRelationFinderCalls_le_four`), so no expected-runs analysis enters the
  accounting. PPT-ness of the adversary family is external to Lean.
* **The idealizations.** Blake2b as a random function, the conversion bias above, the AGM,
  plain-DL hardness, and the generator random-oracle model.

The `Fp`-squeeze exclusions — the Schwartz–Zippel `d / p`, the `z ≠ 0` and `ξ`-recovery `1 / p`
singletons, and any further point exclusions — combine into one subadditive bound by
`GoodChallenge.uniformChallenge_szBadSet_union`.
-/
namespace Zcash.Snark

open scoped ENNReal

variable {F G : Type*}

/-! ## Oracle-table reprogramming -/

open Classical in
/-- Change the oracle's answer at `t` to `c`, leaving all other answers unchanged. -/
noncomputable def reprogram (O : List (TranscriptElt F G) → F) (t : List (TranscriptElt F G)) (c : F) :
    List (TranscriptElt F G) → F :=
  fun t' => if t' = t then c else O t'

@[simp] theorem reprogram_self (O : List (TranscriptElt F G) → F) (t : List (TranscriptElt F G)) (c : F) :
    reprogram O t c t = c := by
  simp [reprogram]

theorem reprogram_ne {O : List (TranscriptElt F G) → F} {t t' : List (TranscriptElt F G)} {c : F}
    (h : t' ≠ t) : reprogram O t c t' = O t' := by
  simp [reprogram, h]

/-! ## The uniform-challenge idealization -/

/-- A fresh random-oracle squeeze, modeled as exactly uniform over `Fp`.

This is the ideal law used by the unsuffixed and `generatorRO` theorems.  Halo2's deployed
`Challenge255 → Fp` conversion is not definitionally this PMF; consumers making a deployed-law
claim must cross `PMFEventBiasLE` explicitly. -/
noncomputable def uniformChallenge : PMF Fp := PMF.uniformOfFintype Fp

/-- A uniform challenge lands in `bad` with probability `|bad| / |Fp|`. -/
theorem uniformChallenge_badSet (bad : Finset Fp) :
    uniformChallenge.toOuterMeasure bad = (bad.card : ℝ≥0∞) / Fintype.card Fp := by
  rw [uniformChallenge, PMF.toOuterMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- `actual` overshoots `ideal` by at most `ε` on every event.  This one-sided statistical-distance
interface is the exact premise needed to transport a soundness upper bound; it may represent one
squeeze or an entire adaptive transcript experiment. -/
def PMFEventBiasLE {Ω : Type*} (actual ideal : PMF Ω) (ε : ℝ≥0∞) : Prop :=
  ∀ S : Set Ω, actual.toOuterMeasure S ≤ ideal.toOuterMeasure S + ε

/-- Transport an ideal-experiment event bound to an explicitly related actual distribution. -/
theorem event_measure_le_of_bias {Ω : Type*} {actual ideal : PMF Ω} {ε bound : ℝ≥0∞}
    (hbias : PMFEventBiasLE actual ideal ε) (event : Set Ω)
    (hideal : ideal.toOuterMeasure event ≤ bound) :
    actual.toOuterMeasure event ≤ bound + ε := by
  exact (hbias event).trans (add_le_add hideal le_rfl)

end Zcash.Snark
