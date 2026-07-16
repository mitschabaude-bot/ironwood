import Zcash.Snark.Soundness.AGM.Adapter
import Zcash.Snark.Soundness.Forking.Extractor

/-!
# Algebraic prover and forking-certificate interfaces

An AGM prover does not return a bare group element: it returns the element together with coefficients
over the complete public basis it received. This module puts that rule in the operational types used
by the forking extractor.

`AlgebraicProver` is the prefix-determined prover strategy, with represented round points.
`AlgebraicDForkCert` is the corresponding explicit `(3, …, 3)` certificate. Both erase to the ordinary
forking types, while retaining the coefficient vectors needed to justify the AGM restriction.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- A prefix-determined prover whose every group output carries an AGM representation over `basis`. -/
inductive AlgebraicProver {ι : Type*} [Fintype ι] (basis : ι → G) : ℕ → Type _ where
  | leaf : F → F → AlgebraicProver basis 0
  | node {d : ℕ} : AlgebraicPoint (F := F) basis → AlgebraicPoint (F := F) basis →
      (F → AlgebraicProver basis d) → AlgebraicProver basis (d + 1)

namespace AlgebraicProver

/-- Forget the coefficient vectors, yielding the ordinary prover strategy consumed by the existing
forking predicate. -/
def toProver {ι : Type*} [Fintype ι] {basis : ι → G} :
    {d : ℕ} → AlgebraicProver (F := F) basis d → Prover F G d
  | 0, .leaf c f => .leaf c f
  | _ + 1, .node L R cont => .node L.point R.point (fun u => toProver (cont u))

end AlgebraicProver

/-- A deployed forking certificate whose round points retain their AGM representations. The basis is
fixed before the prover runs and is unchanged throughout all descendants of the fork tree. -/
inductive AlgebraicDForkCert {ι : Type*} [Fintype ι] (basis : ι → G) : ℕ → Type _ where
  | leaf : F → F → AlgebraicDForkCert basis 0
  | node {d : ℕ} : AlgebraicPoint (F := F) basis → AlgebraicPoint (F := F) basis → F → F → F →
      AlgebraicDForkCert basis d → AlgebraicDForkCert basis d → AlgebraicDForkCert basis d →
      AlgebraicDForkCert basis (d + 1)

namespace AlgebraicDForkCert

/-- Forget the coefficient vectors, preserving exactly the certificate checked by
`DeployedForkValid`. -/
def toDForkCert {ι : Type*} [Fintype ι] {basis : ι → G} :
    {d : ℕ} → AlgebraicDForkCert (F := F) basis d → DForkCert F G d
  | 0, .leaf c f => .leaf c f
  | _ + 1, .node L R u₁ u₂ u₃ c₁ c₂ c₃ =>
      .node L.point R.point u₁ u₂ u₃ (toDForkCert c₁) (toDForkCert c₂) (toDForkCert c₃)

end AlgebraicDForkCert

/-- Acceptance of an algebraic prover is the deployed path predicate for its erased strategy. The
algebraic restriction is carried by the strategy's type rather than added as a proposition. -/
def algebraicProverAccept {ι : Type*} [Fintype ι] {basis : ι → G} {d : ℕ}
    (P : AlgebraicProver (F := F) basis d) (g : Fin (2 ^ d) → G)
    (b : Fin (2 ^ d) → F) (U W : G) (z : F) (Pwhole : G) (χ : Fin d → F) : Prop :=
  proverAccept P.toProver g b U W z Pwhole χ

/-- Zip a propositional `Extractable` tree for an algebraic strategy into the existence of a
representation-carrying certificate. The round-point coefficient vectors come directly from the
strategy; only the challenge tree remains behind `Extractable`'s existential proposition. The
computed capstone therefore takes `AlgebraicDForkCert` itself as data rather than choosing this
witness. -/
theorem algebraicProverAccept_forkValid {ι : Type*} [Fintype ι] {basis : ι → G} {U W : G} {z : F} :
    {d : ℕ} → (P : AlgebraicProver (F := F) basis d) → (g : Fin (2 ^ d) → G) →
      (b : Fin (2 ^ d) → F) → (Pwhole : G) →
      Extractable (algebraicProverAccept P g b U W z Pwhole) →
      ∃ cert : AlgebraicDForkCert (F := F) basis d,
        DeployedForkValid g b U W z Pwhole cert.toDForkCert
  | 0, .leaf c f, g, b, Pwhole, hext => ⟨.leaf c f, hext⟩
  | d + 1, .node L R cont, g, b, Pwhole, hext => by
      obtain ⟨u₁, u₂, u₃, h12, h13, h23, hu₁, hu₂, hu₃, e₁, e₂, e₃⟩ := hext
      obtain ⟨cert₁, hv₁⟩ := algebraicProverAccept_forkValid (cont u₁)
        (foldGens g u₁) (foldGens b u₁)
        (Pwhole + u₁⁻¹ • L.point + u₁ • R.point) e₁
      obtain ⟨cert₂, hv₂⟩ := algebraicProverAccept_forkValid (cont u₂)
        (foldGens g u₂) (foldGens b u₂)
        (Pwhole + u₂⁻¹ • L.point + u₂ • R.point) e₂
      obtain ⟨cert₃, hv₃⟩ := algebraicProverAccept_forkValid (cont u₃)
        (foldGens g u₃) (foldGens b u₃)
        (Pwhole + u₃⁻¹ • L.point + u₃ • R.point) e₃
      exact ⟨.node L R u₁ u₂ u₃ cert₁ cert₂ cert₃,
        h12, h13, h23, hu₁, hu₂, hu₃, hv₁, hv₂, hv₃⟩

end Zcash.Snark
