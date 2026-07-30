import Mathlib.Tactic

/-!
# The verifier's challenges

The fingerprint MSM's coefficients are assembled from the proof's evaluation scalars and the
verifier's challenges; this module records the challenges: `θ, β, γ, y, x` (the main verifier),
`x₁…x₄` (the multiopen), and `ξ, z` plus the `k` round challenges `uⱼ` (the IPA opening).

This structure only records the sampled values. `Verifier.FiatShamir` separately models the exact
deployed transcript schedule, while `Soundness.FiatShamir` models its random-oracle execution and
query accounting. The soundness development uses these values in its Schwartz–Zippel and
represented-execution arguments.
-/

namespace Zcash.Snark

/-- The verifier's challenges, over a field carrier `F`, in squeeze order.

From the main verifier: `theta` (keeps the lookup columns linearly independent), `beta`, `gamma`,
`y` (keeps the gates linearly independent), and `x` (the evaluation point). From the multiopen:
`x1` (compresses same-point-set openings), `x2` (keeps the multi-point quotient terms independent),
`x3` (the opening point), and `x4` (collapses the remaining openings). From the IPA opening: `xi`
(blinds it), `z` (binds the inner product to the generator `u`), and the `k` round challenges
`ipaRound`. -/
structure Challenges (k : ℕ) (F : Type*) where
  theta : F
  beta : F
  gamma : F
  y : F
  x : F
  x1 : F
  x2 : F
  x3 : F
  x4 : F
  xi : F
  z : F
  ipaRound : Fin k → F
deriving DecidableEq

end Zcash.Snark
