import Mathlib.Probability.Distributions.Uniform
import Zcash.Snark.Verifier.FiatShamir
import Zcash.Snark.Core.Field

/-!
# Random-oracle model for the Fiat–Shamir squeeze

`Verifier.FiatShamir` derives challenges through an opaque `squeeze : List (TranscriptElt F G) → F`. The
deployed verifier instantiates it with Blake2b; discharging the Fiat–Shamir assumption models
that hash as a **random oracle** — a function whose answers are uniform and that we can **reprogram** at a
single query (the rewinding primitive the forking argument needs).

This module supplies the random-oracle primitives the forking development is framed with:

* `reprogram` — replace the oracle's answer at one transcript prefix, with `reprogram_self`/`reprogram_ne`.
  Rewinding re-runs the (oracle-deterministic) prover under `reprogram O t c`, diverging exactly at the
  forked query `t`.
* `uniformChallenge` / `uniformChallenge_badSet` — the idealization that a fresh squeeze is uniform over
  `Fp`, hence lands in a finite "bad" set of size `d` with probability `d / p`. This is the Schwartz–Zippel
  exclusion budget and the source of the forking-collision bounds.

## The distributional model: `hprob`'s measure is justified standalone; the adversary experiment is the floor

The forking probability (`Soundness.Forking.Probability`, `Soundness.Forking.Tree`) is stated over the uniform
measure `PMF.uniformOfFintype (Fin k → Fp)` on the IPA round-challenge vector. That a uniform random oracle
induces this measure is a theorem (`Soundness.Forking.Rewind.roChallenges_ipaRound_uniform`), replacing the old
uniformity axiom. It is a *standalone* justification — consumed by no capstone, over the fixed-`ps` marginal;
its precise scope is in that theorem's section — downstream of one standard assumption:

> **Random oracle.** The Blake2b squeeze is idealized as a *uniform random function* `O` over its query domain.

From that, challenge-vector uniformity follows (derivation in `Soundness.Forking.Rewind`): each round challenge
is `O` read at that round's transcript prefix, the `k` prefixes are distinct, so the `k` answers are
independent-uniform. Reprogramming (`reprogram`) resamples one prefix's answer — the rewinding primitive. Two
idealizations are part of "`O` is a uniform random function", not extra assumptions: the transcript encoding is
injective / self-delimiting, so distinct `TranscriptElt` sequences hit distinct Blake2b inputs (halo2 writes
fixed-width points and scalars behind domain-prefix bytes, so absorb-order collisions cannot occur); and the
`Challenge255 → F_p` decoding is taken as exactly uniform. halo2 reduces 64 hash bytes with
`FromUniformBytes<64>`, whose reduction bias is ≈ `p/2⁵¹² < 2⁻²⁵⁶` per squeeze — negligible but nonzero, and
not composed into any stated bound.

So the uniform measure of `hprob` is justified standalone, not posited — no `axiom`, no `sorry` — and its own
input, that `O` is a random oracle, is the standard Fiat–Shamir/ROM assumption (no concrete hash is provably a
random oracle).

The distributional floor left is the **adversary experiment above `hprob`**, not its measure. A full
knowledge-soundness reduction would model the Fiat–Shamir forger as a machine querying `O` and *derive* the
accept probability of `hprob` from its advantage `ε`, paying the query-loss `ε → ε/Q`. That is not modeled:
`hprob` is the hypothesis — the adversary's accept probability over the (now provably uniform, reprogrammable)
challenges — as any knowledge-soundness statement is conditional on the adversary succeeding. `hprob` cannot be
discharged outright (a soundness theorem with no accept-probability hypothesis is false); reducing it to a
querying adversary's advantage needs a probabilistic-oracle-machine, a lazily-sampled oracle, and a
forking-lemma-with-query-loss — foundations Mathlib does not provide. This is the out-of-Lean floor, with the
prover-as-oracle bridge (`deployed_forking_soundness_of_bridge`) and Blake2b-as-random-oracle. (Scope note: the
`_deployed` capstones instantiate the *fixed* proof string, so their `hprob` is that proof's accept measure over
the whole challenge space — the static dichotomy — while connecting a Fiat–Shamir forger to such a measure is
that out-of-Lean floor; see the quantifier-shape caveats there.) `uniformChallenge_badSet` is the one
directly-consumed uniformity consequence — it supplies the `1/p` `ξ`-randomization budget
(`blinder_shift_badSet_measure`, `Soundness.Vesta.blinder_value_recovery_badSet`).

Two scope notes, both part of that floor, not the derived uniformity. **Existence-only:** beating `kerr` proves
the extracted witness *exists* (a counting argument over the challenge space), not that an expected-polynomial-time
extractor computes it. **Uncomposed budgets:** the per-hypothesis exclusions (`z ≠ 0`, the `ξ`-recovery, `1/p`
each) and the `3k/p` tree threshold are stated separately, not composed into one end-to-end bound — the
composition belongs with the query-loss accounting.
-/

namespace Zcash.Snark

open scoped ENNReal

variable {F G : Type*}

/-! ## Reprogramming — the rewinding primitive -/

open Classical in
/-- Reprogram a Fiat–Shamir oracle at one transcript prefix `t`: answer `c` there, `O` everywhere else.
Forking reprograms the oracle at the forked round's query and re-runs the prover, producing a transcript
that agrees with the original on the prefix and diverges at `t`. -/
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

/-- The random-oracle idealization of a fresh squeeze: a uniform field challenge over `Fp`. -/
noncomputable def uniformChallenge : PMF Fp := PMF.uniformOfFintype Fp

/-- A fresh squeeze lands in a finite bad set of size `d` with probability `d / p` (`p = card Fp`) — the
Schwartz–Zippel exclusion budget the good-challenge arguments and the forking-collision bounds
draw on. -/
theorem uniformChallenge_badSet (bad : Finset Fp) :
    uniformChallenge.toOuterMeasure bad = (bad.card : ℝ≥0∞) / Fintype.card Fp := by
  rw [uniformChallenge, PMF.toOuterMeasure_apply_finset]
  simp only [PMF.uniformOfFintype_apply, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]

end Zcash.Snark
