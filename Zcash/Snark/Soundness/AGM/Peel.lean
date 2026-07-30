import Zcash.Snark.Soundness.AGM.Adapter

/-!
# Compare algebraic representations

`separateOrRelationWitness` compares two explicit representations over `(g, U, W)`. Equal
coordinates are returned on the left; otherwise their difference is returned as computed relation
data. The current straight-line and multiopen decoders use this small kernel directly.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G]

/-- Compare two representations, returning equality or their explicit difference as a relation. -/
def separateOrRelationWitness {n : ℕ} (g : Fin n → G) (U W : G)
    (a a' : Fin n → F) (α α' β β' : F)
    (e : commitGen g a + α • U + β • W = commitGen g a' + α' • U + β' • W) :
    (a = a' ∧ α = α' ∧ β = β') ⊕' AugmentedRelationWitness (F := F) g U W := by
  by_cases h : a = a' ∧ α = α' ∧ β = β'
  · exact PSum.inl h
  · exact PSum.inr (NontrivialRelation.ofCombinationCollision e h)

end Zcash.Snark
