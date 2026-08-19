import Zcash.Snark.Keygen.Certificate
import Zcash.Snark.Fixtures.MultiAction.Random.Fixture
import Zcash.Snark.Fixtures.PostNu63Random
import Mathlib.Util.AssertNoSorry

/-!
# The random two-action verifying key, certified derived

The captured verifying key of the random two-action capture equals the key derived end-to-end
from the ported `configure`/keygen at the captured URS — transported from the single-action
keygen certificate (`Keygen/Certificate.lean`) along the cross-capture point equalities of
`Fixtures/PostNu63Random.lean`, never re-evaluating keygen. Verifying keys are indexed only by
the circuit-owned shape, so the proof count does not enter this transport.
-/

namespace Zcash.Snark.FixtureRandom2

open Zcash.Snark
open Zcash.Snark.PostNu63Fixture
open Zcash.Circuits.Action (actionCircuit)

/-- The Action circuit shape is the circuit-owned part of this capture's proof shape. -/
theorem actionCircuitShape_eq : actionCircuit.shape = shape.toCircuitShape :=
  Keygen.actionCircuitShape_eq_fixtureCircuitShape

/-- The Action circuit's derived key at this capture's URS, transported to the fixture shape. -/
def derivedVk : VerifyingKey shape Fp G :=
  actionCircuitShape_eq ▸ actionCircuit.toVerifierKey capturedURS

/-- **The captured random two-action verifying key is fully derived.** -/
theorem vk_eq_derived : vk = derivedVk := by
  unfold derivedVk
  rw [randomMulti_uses_same_urs]
  have hshape : actionCircuitShape_eq = Keygen.actionCircuitShape_eq_fixtureCircuitShape :=
    Subsingleton.elim _ _
  rw [hshape]
  exact randomMulti_uses_same_vk.trans Keygen.vk_eq_toVerifierKey

assert_no_sorry vk_eq_derived

end Zcash.Snark.FixtureRandom2
