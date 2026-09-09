/-!
# A satisfying witness, as data

`Satisfying R x` bundles a witness with the proof that it satisfies the relation `R`
at the instance `x`. It is Type-valued: under Curry–Howard the witness is data, and
that is what keeps knowledge-soundness statements constructive — `Classical.choice`
can conjure the truncated `∃ w, R x w` from mere soundness, but not this structure.

Modelled on `Satisfying` in zcash-lean's `Zcash/Proofs/Relations.lean`
(<https://github.com/daira/zcash-lean/blob/9065c356416e802a3b57cc54b26c8ac9b4165e4c/Zcash/Proofs/Relations.lean>),
which develops refinements between relations, with completeness, soundness, and
knowledge soundness as properties of the refinements rather than of individual
relations. Divergences a reader of that file should expect here: the instance and
witness types are universe-polymorphic rather than fixed at `Type`; the relation is a
curried `I → W → Prop` rather than Mathlib's `Rel`; and this development's
knowledge-soundness maps are fallible — they conclude `Satisfying … ⊕' Break` with
the break carried as computed data and priced by a hardness assumption, rather than
being total functions between satisfying witnesses.
-/

namespace Zcash.Common

universe u v

/-- A witness together with the proof that it satisfies the relation at the given
instance. -/
structure Satisfying {I : Type u} {W : Type v} (R : I → W → Prop) (x : I) where
  /-- The witness. -/
  w : W
  /-- The relation is satisfied by this witness at the given instance. -/
  satisfied : R x w

end Zcash.Common
