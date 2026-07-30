import Mathlib.Tactic
import Zcash.Snark.Soundness.KnowledgeSoundness
import Zcash.Snark.Verifier.Assemble
import Zcash.Snark.Soundness.Consistency
import Zcash.Snark.Soundness.IpaSoundness
import Zcash.Snark.Soundness.Deployed.IpaPeel
import Zcash.Snark.Soundness.Deployed.Verification
import Zcash.Snark.Soundness.Forking.Assembly

/-!
# Deployed acceptance and IPA witness extraction

`DeployedAccepts` says that `assemble?` succeeds and the resulting MSM evaluates
to zero. `deployedAccepts_verifierEq` exposes halo2's IPA verifier equation, and
`ipaRelation_extract` computes the corresponding witness from an explicit
accepting IPA tree. The straight-line composition builds the terminal soundness
statement on top of these primitives.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm)

variable {G : Type*} [AddCommGroup G] [Module Fp G]

def DeployedAccepts [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : Prop :=
  match assemble? vk instanceCommitment ps ch with
  | some m => (hk ▸ m : Msm urs.k Fp G).eval urs = 0
  | none => False

/-- Transport MSM evaluation across the equality `shape.k = urs.k`. -/
theorem eval_cast {shape : Shape} {urs : URS G} (hk : shape.k = urs.k) (m : Msm shape.k Fp G) :
    (hk ▸ m : Msm urs.k Fp G).eval urs = m.eval ⟨shape.k, hk ▸ urs.g, urs.w, urs.u⟩ := by
  -- With `urs` free, destructuring + `subst hk` collapses the cast to `rfl`. Isolating the
  -- transport here keeps `deployedAccepts_verifierEq` from destructuring the URS in place,
  -- which would tangle the accept hypothesis's own `hk`-cast.
  obtain ⟨k, g, w, u⟩ := urs
  change shape.k = k at hk
  subst hk
  rfl

/-- Deployed acceptance implies halo2's explicit IPA verifier equation. -/
theorem deployedAccepts_verifierEq [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (h : DeployedAccepts urs hk vk instanceCommitment ps ch) :
    DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk instanceCommitment ps ch := by
  unfold DeployedAccepts at h
  cases hm : assemble? vk instanceCommitment ps ch with
  | none => rw [hm] at h; exact absurd h (by simp)
  | some m =>
      rw [hm] at h
      simp only [] at h
      rw [eval_cast hk m] at h
      have hmeq := assemble?_eq_some vk instanceCommitment ps ch hm
      unfold DeployedIpaVerifierEq
      rw [← deployed_verification_eq (hk ▸ urs.g) urs.w urs.u ps ch
            (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)), ← hmeq]
      exact h

/-- Compute the `IpaRelation` witness instead of hiding it behind an existential proposition. -/
def ipaRelation_extract (urs : URS G) (b : Fin (2 ^ urs.k) → Fp) (P : G) (v : Fp)
    (t : IpaTreeV Fp G urs.k) (h : IpaAcceptV urs.g b P v t) :
    Σ' a, IpaRelation urs P b v a :=
  let s := ipa_extractV urs.g b P v t h
  ⟨s.1, s.2.1, by
    have hib : innerProduct s.1 b = commitGen b s.1 := by simp only [innerProduct, commitGen, smul_eq_mul]
    rw [hib]; exact s.2.2⟩

/-- The proof's deployed multiopen commitment over the supplied URS. -/
abbrev deployedCommitment [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) : G :=
  multiopenCommitment (hk ▸ urs.g) urs.w urs.u vk instanceCommitment ps ch

/-! ## The tree opens the commitment up to declared `U`/`W` components

Real commitments include a `W` blinding component, while an IPA leaf opens a point in the `g` span.
The forked transcript therefore declares `U` and `W` components and opens the adjusted commitment
`deployedCommitment − [pU]u − [pW]w`.
-/

/-- A forked accepting IPA tree opening the deployed commitment after removing declared components. -/
structure ForkedTranscript [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) (z blind : Fp) where
  tree : DeployedIpaTreeV Fp G urs.k
  /-- The declared `U`-component of the pinned commitment (honest value: `0`). -/
  pU : Fp
  /-- The declared `W`-component of the pinned commitment (honest value: the aggregate blind). -/
  pW : Fp
  accepts : DeployedIpaAcceptV urs.g b urs.u urs.w z
    (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w)
    (multiopenValue vk instanceCommitment ps ch) blind tree

/-- The deployed commitment after removing the transcript's declared `U` and `W` components. -/
abbrev ForkedTranscript.openedCommitment [DecidableEq G] [Inhabited G] {shape : Shape}
    {urs : URS G} {hk : shape.k = urs.k} {vk : VerifyingKey shape Fp G} {instanceCommitment : Fin shape.numProofs → ℕ → G}
    {ps : ProofString shape Fp G} {ch : Challenges shape.k Fp} {b : Fin (2 ^ urs.k) → Fp}
    {z blind : Fp} (fs : ForkedTranscript urs hk vk instanceCommitment ps ch b z blind) : G :=
  deployedCommitment urs hk vk instanceCommitment ps ch - fs.pU • urs.u - fs.pW • urs.w

/-- Build a forked transcript from a blinded opening of the deployed commitment. -/
theorem ForkedTranscript.nonempty_of_opening [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    (u₁ u₂ u₃ : Fp) (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0)
    (a : Fin (2 ^ urs.k) → Fp) (pU pW : Fp)
    (hP : deployedCommitment urs hk vk instanceCommitment ps ch = commitGen urs.g a + pU • urs.u + pW • urs.w)
    (hv : multiopenValue vk instanceCommitment ps ch = commitGen b a) :
    Nonempty (ForkedTranscript urs hk vk instanceCommitment ps ch b z blind) := by
  obtain ⟨t, ht⟩ := deployedIpaAcceptV_of_witness u₁ u₂ u₃ h12 h13 h23 hu₁ hu₂ hu₃
    urs.g b urs.u urs.w z blind a
  refine ⟨⟨t, pU, pW, ?_⟩⟩
  have hcancel : deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w
      = commitGen urs.g a := by rw [hP]; abel
  rw [hcancel, hv]
  exact ht

/-- Legacy interface from the deployed verifier equation to a forked transcript.

It bundles random-oracle rewinding, round-point representations, leaf data, and declared commitment
components. The live forking path proves the deterministic extraction pieces separately. -/
def FiatShamirTree [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (b : Fin (2 ^ urs.k) → Fp) (z blind : Fp) : Type _ :=
  DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk instanceCommitment ps ch →
    ForkedTranscript urs hk vk instanceCommitment ps ch b z blind

/-- Apply the legacy fork bridge to a deployed accepting proof. -/
def ForkedTranscript.ofAccepts [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    (haccepts : DeployedAccepts urs hk vk instanceCommitment ps ch)
    (hFS : FiatShamirTree urs hk vk instanceCommitment ps ch b z blind) :
    ForkedTranscript urs hk vk instanceCommitment ps ch b z blind :=
  hFS (deployedAccepts_verifierEq urs hk vk instanceCommitment ps ch haccepts)

/-- Random-oracle forking output: declared commitment components and a ternary accepting tree. -/
def FiatShamirForking [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    (b : Fin (2 ^ urs.k) → Fp) (z blind : Fp) : Type _ :=
  DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk instanceCommitment ps ch →
    Σ' (pU pW : Fp) (t : DeployedIpaTreeV Fp G urs.k),
      ForkAccept urs.g b urs.u urs.w z
        (deployedCommitment urs hk vk instanceCommitment ps ch - pU • urs.u - pW • urs.w) (multiopenValue vk instanceCommitment ps ch) blind t

/-- Convert explicit forking output into the legacy `FiatShamirTree` interface. -/
def fiatShamirTree_of_forking [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (instanceCommitment : Fin shape.numProofs → ℕ → G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) (z blind : Fp)
    (hForking : FiatShamirForking urs hk vk instanceCommitment ps ch b z blind) :
    FiatShamirTree urs hk vk instanceCommitment ps ch b z blind := by
  intro hEq
  obtain ⟨pU, pW, t, hFork⟩ := hForking hEq
  exact ⟨t, pU, pW, forkAccept_to_acceptV _ _ _ _ _ t hFork⟩

end Zcash.Snark
