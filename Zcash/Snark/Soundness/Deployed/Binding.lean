import Zcash.Snark.Soundness.CommitFold
import Zcash.Common.DiscreteLogRelation

/-!
# Binding as a discrete-log-relation reduction over the augmented generators

`Zcash.Snark.Soundness.CommitFold` models commitment binding at the URS generators `g` as a
reduction to discrete-log-relation (DLR) hardness (`relation_of_collision`,
`commitmentBinding_iff_no_relation`). The deployed verifier additionally folds the inner-product
generator `U` and the blinding generator `W` into one group equation, so soundness there needs
binding over the *augmented* system `(g, U, W)`. That system is the shared `Zcash.NontrivialRelation`
(its `∑ i, a i • g i` is the Snark commitment `commitGen g a`); this module computes the relation per
the breaks-as-computed-data convention (`Zcash.Security.RandomOracle`):

* `NontrivialRelation.ofCombinationCollision` — a combined `(g, U, W)`-equation whose coordinates do
  not all agree *computes* a relation: the augmented analog of `relation_of_collision`, and the step
  used by the current AGM peel and canonical instance-commitment collision classifiers.

For why the reduction produces the relation as data — an ∃-closed `Prop` would be vacuous at the
concrete curve — see `The reduction form` in `Zcash.Snark.Soundness.Main`.
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

end Zcash.Snark
