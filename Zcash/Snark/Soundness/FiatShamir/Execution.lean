import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.FiatShamir.Oracle
import Zcash.Snark.Soundness.FiatShamir.Ordering

/-!
# Random-oracle execution and IPA splicing

`ofOracle` and `roChallenges` run the deployed schedule with a random oracle. `spliceIpa` replaces
the proof's IPA block while preserving its pre-IPA fields; the adaptive AGM development uses this
to assemble the proof returned by the algebraic adversary.

`Soundness.FiatShamir.Adversary` builds the querying-adversary reduction on top. Identifying Blake2b
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

private theorem Challenges.ext' {k : ℕ} {F : Type*} {c₁ c₂ : Challenges k F}
    (hθ : c₁.theta = c₂.theta) (hβ : c₁.beta = c₂.beta) (hγ : c₁.gamma = c₂.gamma)
    (hy : c₁.y = c₂.y) (hx : c₁.x = c₂.x) (h1 : c₁.x1 = c₂.x1) (h2 : c₁.x2 = c₂.x2)
    (h3 : c₁.x3 = c₂.x3) (h4 : c₁.x4 = c₂.x4) (hξ : c₁.xi = c₂.xi) (hz : c₁.z = c₂.z)
    (hu : c₁.ipaRound = c₂.ipaRound) : c₁ = c₂ := by
  cases c₁; cases c₂; simp_all

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
