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

`badSet_measure_le_of_bias` is where the term attaches: it carries any bad-set bound proved
against `uniformChallenge` over to a biased law at an additive `ε`. Instantiating `ε` needs `w`
for the deployed transcript, a fact about halo2's transcript code recorded in the trust boundary
rather than proved here.

## What the adversary model still assumes

The querying-adversary experiment is present: `Adversary.OracleComp` models a bounded-query
adversary, `Adversary.Algebraic` runs the recursive extractor against it, and
`ComputedAlgebraicFSFamily.knowledgeSoundness_under_DL` and `.binding_under_DL` price extraction
failure from the adversary's own advantage. Query loss is charged explicitly: `(Q + k) · (3/p)`
for the extractor's escape slice and `(Q + 1) · (1/p)` for the adaptive `z = 0` slice. What
remains is:

* **Efficiency modeling.** The generic endpoints take `ReductionEfficient R`; their `_poly` forms
  discharge it unconditionally at `R = (8·Q+1)·10^k`, the Attema–Fehr–Klooß-style expected
  black-box call bound of the recursive extractor
  (`recursiveAlgebraicFork_oracle_tape_sum_runs_le_poly`, with `Q` the query bound and `k` the IPA
  depth). `reductionEfficient_of_forkSpread` is the conditional density-sensitive alternative.
  PPT-ness of the adversary family is external to Lean.
* **The idealizations.** Blake2b as a random function, the conversion bias above, the AGM,
  plain-DL hardness, and the generator random-oracle model.

The `Fp`-squeeze exclusions — the Schwartz–Zippel `d / p`, the `z ≠ 0` and `ξ`-recovery `1 / p`
singletons, and any further point exclusions — combine into one subadditive bound by
`GoodChallenge.uniformChallenge_szBadSet_union`. The `kerr` tree count lives over the
round-*vector* domain and is charged separately.
-/
namespace Zcash.Snark

open scoped ENNReal

variable {F G : Type*}

/-! ## Reprogramming — the rewinding primitive -/

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

/-- A fresh random-oracle squeeze, modeled as uniform over `Fp`.

Halo2's real `Challenge255 → Fp` conversion is a modular reduction of a fixed-width byte string and
so is only within total-variation distance `|Fp| / 2^w` of this law, for the conversion width `w`.
`badSet_measure_le_of_bias` charges that deviation; no bound in this development silently assumes
it away. -/
noncomputable def uniformChallenge : PMF Fp := PMF.uniformOfFintype Fp

/-- A uniform challenge lands in `bad` with probability `|bad| / |Fp|`. -/
theorem uniformChallenge_badSet (bad : Finset Fp) :
    uniformChallenge.toOuterMeasure bad = (bad.card : ℝ≥0∞) / Fintype.card Fp := by
  rw [uniformChallenge, PMF.toOuterMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

/-- Charge the deployed conversion's reduction bias against a bad-set budget.

If the real squeeze law `D` overshoots `uniformChallenge` by at most `ε` on every event — the
`ε = |Fp| / 2^w` of the module doc, for a `w`-bit conversion — then every bad-set bound proved in
the uniform model holds for `D` with `ε` added. The hypothesis is the assumption; the point of
stating it is that the term now has a name and a home instead of living in the word "negligible". -/
theorem badSet_measure_le_of_bias {D : PMF Fp} {ε : ℝ≥0∞}
    (hbias : ∀ S : Set Fp, D.toOuterMeasure S ≤ uniformChallenge.toOuterMeasure S + ε)
    (bad : Finset Fp) :
    D.toOuterMeasure bad ≤ (bad.card : ℝ≥0∞) / Fintype.card Fp + ε := by
  refine le_trans (hbias bad) (le_of_eq ?_)
  rw [uniformChallenge_badSet]

end Zcash.Snark
