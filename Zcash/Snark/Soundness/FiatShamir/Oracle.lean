import Mathlib.Probability.Distributions.Uniform
import Zcash.Snark.Verifier.FiatShamir
import Zcash.Arithmetic

/-!
# Random-oracle model for Fiat–Shamir

Models transcript squeezes as a reprogrammable random function. `PMFEventBiasLE` adds explicit
challenge-conversion bias when transporting ideal bounds. Blake2b randomness, transcript
injectivity, the AGM, generator random oracle, and DLOG hardness remain assumptions.
-/
namespace Zcash.Snark

open scoped ENNReal

variable {F G : Type*}

/-! ## Oracle-table reprogramming -/

/-- Change the oracle's answer at `t` to `c`, leaving all other answers unchanged. -/
def reprogram [DecidableEq F] [DecidableEq G]
    (O : List (TranscriptElt F G) → F) (t : List (TranscriptElt F G)) (c : F) :
    List (TranscriptElt F G) → F :=
  fun t' => if t' = t then c else O t'

@[simp] theorem reprogram_self [DecidableEq F] [DecidableEq G]
    (O : List (TranscriptElt F G) → F) (t : List (TranscriptElt F G)) (c : F) :
    reprogram O t c t = c := by
  simp [reprogram]

theorem reprogram_ne [DecidableEq F] [DecidableEq G]
    {O : List (TranscriptElt F G) → F} {t t' : List (TranscriptElt F G)} {c : F}
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
