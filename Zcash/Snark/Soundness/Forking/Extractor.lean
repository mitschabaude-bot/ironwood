import Zcash.Snark.Soundness.IpaSoundness
import Zcash.Snark.Soundness.Deployed.IpaPeel
import Zcash.Snark.Soundness.Forking.Tree
import Zcash.Snark.Soundness.Forking.Probability

/-!
# Recover a deployed IPA tree from three forks

Three accepting continuations determine a parent commitment and its two round terms. The same
Vandermonde calculation recovers the parent value, blinding, and their round terms. This module uses
those recoveries to build a root-consistent deployed IPA tree.
-/

namespace Zcash.Snark

variable {F : Type*} [Field F]
variable {G : Type*} [AddCommGroup G] [Module F G]

/-- Recover a parent commitment and round terms from three folded commitments. -/
def vandermonde3_recover_group {u₁ u₂ u₃ : F}
    (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃) (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0)
    (P₁ P₂ P₃ : G) :
    Σ' (P L R : G), P + u₁⁻¹ • L + u₁ • R = P₁ ∧ P + u₂⁻¹ • L + u₂ • R = P₂
      ∧ P + u₃⁻¹ • L + u₃ • R = P₃ := by
  have d12 : u₁ - u₂ ≠ 0 := sub_ne_zero.mpr h12
  have d13 : u₁ - u₃ ≠ 0 := sub_ne_zero.mpr h13
  have d23 : u₂ - u₃ ≠ 0 := sub_ne_zero.mpr h23
  have d21 : u₂ - u₁ ≠ 0 := sub_ne_zero.mpr h12.symm
  have d31 : u₃ - u₁ ≠ 0 := sub_ne_zero.mpr h13.symm
  have d32 : u₃ - u₂ ≠ 0 := sub_ne_zero.mpr h23.symm
  refine ⟨(-(u₁ * (u₂ + u₃) / ((u₁ - u₂) * (u₁ - u₃)))) • P₁
            + (-(u₂ * (u₁ + u₃) / ((u₂ - u₁) * (u₂ - u₃)))) • P₂
            + (-(u₃ * (u₁ + u₂) / ((u₃ - u₁) * (u₃ - u₂)))) • P₃,
          (u₁ * (u₂ * u₃) / ((u₁ - u₂) * (u₁ - u₃))) • P₁
            + (u₂ * (u₁ * u₃) / ((u₂ - u₁) * (u₂ - u₃))) • P₂
            + (u₃ * (u₁ * u₂) / ((u₃ - u₁) * (u₃ - u₂))) • P₃,
          (u₁ / ((u₁ - u₂) * (u₁ - u₃))) • P₁
            + (u₂ / ((u₂ - u₁) * (u₂ - u₃))) • P₂
            + (u₃ / ((u₃ - u₁) * (u₃ - u₂))) • P₃, ?_, ?_, ?_⟩ <;>
    match_scalars <;> field_simp <;> ring

/-- Three distinct nonzero challenges uniquely determine the parent and round terms. -/
theorem fold_inj {u₁ u₂ u₃ : F} (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃)
    (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0) {P L R P' L' R' : G}
    (e₁ : P + u₁⁻¹ • L + u₁ • R = P' + u₁⁻¹ • L' + u₁ • R')
    (e₂ : P + u₂⁻¹ • L + u₂ • R = P' + u₂⁻¹ • L' + u₂ • R')
    (e₃ : P + u₃⁻¹ • L + u₃ • R = P' + u₃⁻¹ • L' + u₃ • R') :
    P = P' ∧ L = L' ∧ R = R' := by
  -- clear the inverses: fᵢ : uᵢ•(P-P') + (L-L') + (uᵢ*uᵢ)•(R-R') = 0
  have f : ∀ u : F, u ≠ 0 → (P + u⁻¹ • L + u • R = P' + u⁻¹ • L' + u • R') →
      u • (P - P') + (L - L') + (u * u) • (R - R') = 0 := by
    intro u hu e
    have h := congrArg (u • ·) (sub_eq_zero.mpr e)
    simp only [smul_zero, smul_sub, smul_add, smul_smul, mul_inv_cancel₀ hu, one_smul] at h
    rw [← h]; module
  have f₁ := f u₁ hu₁ e₁
  have f₂ := f u₂ hu₂ e₂
  have f₃ := f u₃ hu₃ e₃
  -- eliminate (L-L'): subtract pairs and factor out the nonzero difference
  have g : ∀ u v : F, u ≠ v →
      u • (P - P') + (u * u) • (R - R') = v • (P - P') + (v * v) • (R - R') →
      (P - P') + (u + v) • (R - R') = 0 := by
    intro u v huv e
    have hd : u - v ≠ 0 := sub_ne_zero.mpr huv
    have : (u - v) • ((P - P') + (u + v) • (R - R')) = 0 := by
      rw [← sub_eq_zero] at e; rw [← e]; module
    exact (smul_eq_zero.mp this).resolve_left hd
  have g12 : (P - P') + (u₁ + u₂) • (R - R') = 0 := g u₁ u₂ h12 (by linear_combination (norm := module) f₁ - f₂)
  have g13 : (P - P') + (u₁ + u₃) • (R - R') = 0 := g u₁ u₃ h13 (by linear_combination (norm := module) f₁ - f₃)
  -- (u₂ - u₃)•(R-R') = 0 ⟹ R = R'
  have hR : R - R' = 0 := by
    have hd : u₂ - u₃ ≠ 0 := sub_ne_zero.mpr h23
    have : (u₂ - u₃) • (R - R') = 0 := by linear_combination (norm := module) g12 - g13
    exact (smul_eq_zero.mp this).resolve_left hd
  have hP : P - P' = 0 := by linear_combination (norm := module) g12 - (u₁ + u₂) • hR
  have hL : L - L' = 0 := by linear_combination (norm := module) f₁ - u₁ • hP - (u₁ * u₁) • hR
  exact ⟨sub_eq_zero.mp hP, sub_eq_zero.mp hL, sub_eq_zero.mp hR⟩

/-- Recover a parent scalar and round terms from three folded scalars. -/
def vandermonde3_recover {u₁ u₂ u₃ : F}
    (h12 : u₁ ≠ u₂) (h13 : u₁ ≠ u₃) (h23 : u₂ ≠ u₃) (hu₁ : u₁ ≠ 0) (hu₂ : u₂ ≠ 0) (hu₃ : u₃ ≠ 0)
    (t₁ t₂ t₃ : F) :
    Σ' (v Lv Rv : F), v + u₁⁻¹ * Lv + u₁ * Rv = t₁ ∧ v + u₂⁻¹ * Lv + u₂ * Rv = t₂
      ∧ v + u₃⁻¹ * Lv + u₃ * Rv = t₃ := by
  have d12 : u₁ - u₂ ≠ 0 := sub_ne_zero.mpr h12
  have d13 : u₁ - u₃ ≠ 0 := sub_ne_zero.mpr h13
  have d23 : u₂ - u₃ ≠ 0 := sub_ne_zero.mpr h23
  have d21 : u₂ - u₁ ≠ 0 := sub_ne_zero.mpr h12.symm
  have d31 : u₃ - u₁ ≠ 0 := sub_ne_zero.mpr h13.symm
  have d32 : u₃ - u₂ ≠ 0 := sub_ne_zero.mpr h23.symm
  refine ⟨-(u₁ * t₁ * (u₂ + u₃) / ((u₁ - u₂) * (u₁ - u₃))
            + u₂ * t₂ * (u₁ + u₃) / ((u₂ - u₁) * (u₂ - u₃))
            + u₃ * t₃ * (u₁ + u₂) / ((u₃ - u₁) * (u₃ - u₂))),
          u₁ * t₁ * (u₂ * u₃) / ((u₁ - u₂) * (u₁ - u₃))
            + u₂ * t₂ * (u₁ * u₃) / ((u₂ - u₁) * (u₂ - u₃))
            + u₃ * t₃ * (u₁ * u₂) / ((u₃ - u₁) * (u₃ - u₂)),
          u₁ * t₁ / ((u₁ - u₂) * (u₁ - u₃))
            + u₂ * t₂ / ((u₂ - u₁) * (u₂ - u₃))
            + u₃ * t₃ / ((u₃ - u₁) * (u₃ - u₂)), ?_, ?_, ?_⟩ <;>
    field_simp <;> ring

/-! ## The root-consistent producer: threading the deployed commitment

`DForkCert` stores the prover's round points and three challenges at each node. `DeployedForkValid`
threads the deployed commitment through every path. `produceDeployed` recovers the tree bottom-up and
uses `fold_inj` to prove that its root is the original deployed commitment.
-/

/-- A fork tree containing each round point, three challenges, and each leaf opening. -/
inductive DForkCert (F G : Type*) : ℕ → Type _ where
  | leaf : F → F → DForkCert F G 0
  | node {d : ℕ} : G → G → F → F → F →
      DForkCert F G d → DForkCert F G d → DForkCert F G d → DForkCert F G (d + 1)

/-- Every path in a fork certificate satisfies the deployed flat verifier equation. -/
def DeployedForkValid : {d : ℕ} → (Fin (2 ^ d) → G) → (Fin (2 ^ d) → F) → (U W : G) → (z : F) → G →
    DForkCert F G d → Prop
  | 0, g, b, U, W, z, Pwhole, .leaf c f =>
      Pwhole = commitGen g (fun _ => c) + (z * commitGen b (fun _ => c)) • U + f • W
  | _ + 1, g, b, U, W, z, Pwhole, .node L R u₁ u₂ u₃ c₁ c₂ c₃ =>
      u₁ ≠ u₂ ∧ u₁ ≠ u₃ ∧ u₂ ≠ u₃ ∧ u₁ ≠ 0 ∧ u₂ ≠ 0 ∧ u₃ ≠ 0 ∧
        DeployedForkValid (foldGens g u₁) (foldGens b u₁) U W z (Pwhole + u₁⁻¹ • L + u₁ • R) c₁ ∧
        DeployedForkValid (foldGens g u₂) (foldGens b u₂) U W z (Pwhole + u₂⁻¹ • L + u₂ • R) c₂ ∧
        DeployedForkValid (foldGens g u₃) (foldGens b u₃) U W z (Pwhole + u₃⁻¹ • L + u₃ • R) c₃

/-- Build an accepting deployed IPA tree whose recovered root equals `Pwhole`. -/
def produceDeployed {U W : G} {z : F} : {d : ℕ} → (g : Fin (2 ^ d) → G) → (b : Fin (2 ^ d) → F) →
    (Pwhole : G) → (cert : DForkCert F G d) → DeployedForkValid g b U W z Pwhole cert →
    Σ' (P : G) (v blind : F) (t : DeployedIpaTreeV F G d),
      DeployedIpaAcceptV g b U W z P v blind t ∧ P + (z * v) • U + blind • W = Pwhole
  | 0, g, b, Pwhole, .leaf c f, hv =>
      ⟨commitGen g (fun _ => c), commitGen b (fun _ => c), f, .leaf c f (fun _ => c), ⟨rfl, rfl⟩, hv.symm⟩
  | d + 1, g, b, Pwhole, .node L R u₁ u₂ u₃ c₁ c₂ c₃, hv => by
      obtain ⟨h12, h13, h23, hu₁, hu₂, hu₃, hv₁, hv₂, hv₃⟩ := hv
      obtain ⟨P₁, v₁, bl₁, t₁, ha₁, hw₁⟩ := produceDeployed (foldGens g u₁) (foldGens b u₁) _ c₁ hv₁
      obtain ⟨P₂, v₂, bl₂, t₂, ha₂, hw₂⟩ := produceDeployed (foldGens g u₂) (foldGens b u₂) _ c₂ hv₂
      obtain ⟨P₃, v₃, bl₃, t₃, ha₃, hw₃⟩ := produceDeployed (foldGens g u₃) (foldGens b u₃) _ c₃ hv₃
      obtain ⟨P, L', R', eP₁, eP₂, eP₃⟩ := vandermonde3_recover_group h12 h13 h23 hu₁ hu₂ hu₃ P₁ P₂ P₃
      obtain ⟨v, Lv, Rv, ev₁, ev₂, ev₃⟩ := vandermonde3_recover h12 h13 h23 hu₁ hu₂ hu₃ v₁ v₂ v₃
      obtain ⟨blind, Lw, Rw, eb₁, eb₂, eb₃⟩ := vandermonde3_recover h12 h13 h23 hu₁ hu₂ hu₃ bl₁ bl₂ bl₃
      refine ⟨P, v, blind, .node L' R' Lv Rv Lw Rw u₁ u₂ u₃ t₁ t₂ t₃,
        ⟨h12, h13, h23, hu₁, hu₂, hu₃, ?_, ?_, ?_⟩, ?_⟩
      · simp only [smul_eq_mul]; rw [eP₁, ev₁, eb₁]; exact ha₁
      · simp only [smul_eq_mul]; rw [eP₂, ev₂, eb₂]; exact ha₂
      · simp only [smul_eq_mul]; rw [eP₃, ev₃, eb₃]; exact ha₃
      · -- the recovered root whole and `Pwhole` fold to the same three child wholes ⇒ equal (`fold_inj`)
        have key : ∀ (uu : F) (Pi : G) (vi bli : F),
            P + uu⁻¹ • L' + uu • R' = Pi → v + uu⁻¹ * Lv + uu * Rv = vi →
            blind + uu⁻¹ * Lw + uu * Rw = bli → Pi + (z * vi) • U + bli • W = Pwhole + uu⁻¹ • L + uu • R →
            (P + (z * v) • U + blind • W) + uu⁻¹ • (L' + (z * Lv) • U + Lw • W)
                + uu • (R' + (z * Rv) • U + Rw • W) = Pwhole + uu⁻¹ • L + uu • R := by
          intro uu Pi vi bli hP hvv hb hw
          rw [show (P + (z * v) • U + blind • W) + uu⁻¹ • (L' + (z * Lv) • U + Lw • W)
                + uu • (R' + (z * Rv) • U + Rw • W)
              = (P + uu⁻¹ • L' + uu • R') + (z * (v + uu⁻¹ * Lv + uu * Rv)) • U
                + (blind + uu⁻¹ * Lw + uu * Rw) • W from by match_scalars <;> ring,
            hP, hvv, hb, hw]
        exact (fold_inj h12 h13 h23 hu₁ hu₂ hu₃
          (key u₁ P₁ v₁ bl₁ eP₁ ev₁ eb₁ hw₁) (key u₂ P₂ v₂ bl₂ eP₂ ev₂ eb₂ hw₂)
          (key u₃ P₃ v₃ bl₃ eP₃ ev₃ eb₃ hw₃)).1

/-- Compute either an accepting deployed IPA tree or a nontrivial `(g, U, W)` relation.

The input certificate is explicit, and this definition uses no `Classical.choose`. -/
def deployed_forking_tree [DecidableEq F] [DecidableEq G] {U W : G} {z : F} (hz : z ≠ 0)
    {d : ℕ} (g : Fin (2 ^ d) → G) (b : Fin (2 ^ d) → F) (aDep : Fin (2 ^ d) → F) (vDep blindDep : F)
    (cert : DForkCert F G d)
    (hv : DeployedForkValid g b U W z (commitGen g aDep + (z * vDep) • U + blindDep • W) cert) :
    (Σ' (blind : F) (t : DeployedIpaTreeV F G d),
        DeployedIpaAcceptV g b U W z (commitGen g aDep) vDep blind t)
      ⊕' NontrivialRelation (F := F) g U W :=
  match produceDeployed g b _ cert hv with
  | ⟨P, v, blind, t, ha, hw⟩ =>
    if hclean : IpaAcceptV g b P v (projTree t) then
      match ipa_extractV g b P v (projTree t) hclean with
      | ⟨a, hPa, _hva⟩ =>
        if hcoord : a = aDep ∧ (z * v) = (z * vDep) ∧ blind = blindDep then
          PSum.inl ⟨blind, t, by
            obtain ⟨haa, hU, _⟩ := hcoord
            have hPP : P = commitGen g aDep := by rw [← hPa, haa]
            have hvv : v = vDep := mul_left_cancel₀ hz hU
            rw [hPP, hvv] at ha; exact ha⟩
        else
          PSum.inr (NontrivialRelation.ofCombinationCollision (by rw [← hPa] at hw; exact hw) hcoord)
    else
      PSum.inr (NontrivialRelation.ofDeployedTree hz g b P v blind t ha hclean)

/-! ## The prover-as-oracle-function model: from the abstract forking tree to `DeployedForkValid`

`extractable_of_prob` returns only a challenge tree. `Prover` supplies the round points and leaf
openings chosen along each prefix. `proverAccept_forkValid` combines them into a `DForkCert`.

Connecting a real Fiat–Shamir adversary to this strategy type remains outside this module.
-/

/-- A prefix-determined IPA prover strategy with round points and leaf openings. -/
inductive Prover (F G : Type*) : ℕ → Type _ where
  | leaf : F → F → Prover F G 0
  | node {d : ℕ} : G → G → (F → Prover F G d) → Prover F G (d + 1)

/-- The deployed accept condition along one challenge path through a prover strategy. -/
def proverAccept : {d : ℕ} → Prover F G d → (Fin (2 ^ d) → G) → (Fin (2 ^ d) → F) → (U W : G) → (z : F) → G →
    (Fin d → F) → Prop
  | 0, .leaf c f, g, b, U, W, z, Pwhole, _ =>
      Pwhole = commitGen g (fun _ => c) + (z * commitGen b (fun _ => c)) • U + f • W
  | _ + 1, .node L R cont, g, b, U, W, z, Pwhole, χ =>
      proverAccept (cont (χ 0)) (foldGens g (χ 0)) (foldGens b (χ 0)) U W z
        (Pwhole + (χ 0)⁻¹ • L + (χ 0) • R) (Fin.tail χ)

/-- Combine an `Extractable` challenge tree with a prover strategy to obtain a valid fork certificate. -/
theorem proverAccept_forkValid {U W : G} {z : F} : {d : ℕ} → (P : Prover F G d) → (g : Fin (2 ^ d) → G) →
    (b : Fin (2 ^ d) → F) → (Pwhole : G) → Extractable (proverAccept P g b U W z Pwhole) →
    ∃ cert : DForkCert F G d, DeployedForkValid g b U W z Pwhole cert
  | 0, .leaf c f, g, b, Pwhole, hext => ⟨.leaf c f, hext⟩
  | d + 1, .node L R cont, g, b, Pwhole, hext => by
      obtain ⟨u₁, u₂, u₃, h12, h13, h23, hu₁, hu₂, hu₃, e₁, e₂, e₃⟩ := hext
      obtain ⟨cert₁, hv₁⟩ := proverAccept_forkValid (cont u₁) (foldGens g u₁) (foldGens b u₁)
        (Pwhole + u₁⁻¹ • L + u₁ • R) e₁
      obtain ⟨cert₂, hv₂⟩ := proverAccept_forkValid (cont u₂) (foldGens g u₂) (foldGens b u₂)
        (Pwhole + u₂⁻¹ • L + u₂ • R) e₂
      obtain ⟨cert₃, hv₃⟩ := proverAccept_forkValid (cont u₃) (foldGens g u₃) (foldGens b u₃)
        (Pwhole + u₃⁻¹ • L + u₃ • R) e₃
      exact ⟨.node L R u₁ u₂ u₃ cert₁ cert₂ cert₃,
        h12, h13, h23, hu₁, hu₂, hu₃, hv₁, hv₂, hv₃⟩

end Zcash.Snark
