import Zcash.Meta.AxiomCheck

/-!
# Regression tests for native-axiom provenance

The negative cases deliberately declare axioms whose names imitate Lean's `native_decide`
auxiliaries. They live in this test-only library so the production `Zcash` library never imports
them.
-/

namespace Zcash.Meta.Tests.AxiomCheck

namespace Genuine

theorem owner : (123456 : Nat) < 123457 := by native_decide

assert_axioms Zcash.Meta.Tests.AxiomCheck.Genuine.owner +native(
  Zcash.Meta.Tests.AxiomCheck.Genuine.owner)

end Genuine

namespace GenuineAutoParam

/-- The certificate lives in an auto-param, so the axiom is emitted while elaborating the
structure instance below rather than a tactic block of its own. Lean then records the auxiliary's
end position at the start of the *next* token — past the end of the owning declaration — which is
why ownership is decided by the auxiliary's start position. `CompElliptic`'s Tonelli–Shanks data
(`pallasBase`, `vestaBase`) is the census entry with this shape. -/
structure Certified where
  value : Nat
  small : value < 123457 := by native_decide

def owner : Certified where
  value := 123456

assert_axioms Zcash.Meta.Tests.AxiomCheck.GenuineAutoParam.owner +native(
  Zcash.Meta.Tests.AxiomCheck.GenuineAutoParam.owner)

end GenuineAutoParam

namespace NonexistentOwner

axiom owner._native.native_decide.ax_1_1 : False
theorem target : False := owner._native.native_decide.ax_1_1

/-- error: Unknown constant `Zcash.Meta.Tests.AxiomCheck.NonexistentOwner.owner` -/
#guard_msgs (whitespace := lax) in
assert_axioms Zcash.Meta.Tests.AxiomCheck.NonexistentOwner.target +native(
  Zcash.Meta.Tests.AxiomCheck.NonexistentOwner.owner)

end NonexistentOwner

namespace UnrelatedOwner

theorem owner : True := True.intro
axiom owner._native.native_decide.ax_1_1 : False
theorem target : False := owner._native.native_decide.ax_1_1

/-- error: Zcash.Meta.Tests.AxiomCheck.UnrelatedOwner.target: '+native' names 'Zcash.Meta.Tests.AxiomCheck.UnrelatedOwner.owner', but that declaration owns no native_decide axiom -/
#guard_msgs (whitespace := lax) in
assert_axioms Zcash.Meta.Tests.AxiomCheck.UnrelatedOwner.target +native(
  Zcash.Meta.Tests.AxiomCheck.UnrelatedOwner.owner)

end UnrelatedOwner

namespace ForgedDependency

axiom owner._native.native_decide.ax_1_1 : False
theorem owner : False := owner._native.native_decide.ax_1_1

/-- error: 'Zcash.Meta.Tests.AxiomCheck.ForgedDependency.owner._native.native_decide.ax_1_1' looks like a native_decide axiom owned by 'Zcash.Meta.Tests.AxiomCheck.ForgedDependency.owner', but it was not emitted inside that declaration -/
#guard_msgs (whitespace := lax) in
assert_axioms Zcash.Meta.Tests.AxiomCheck.ForgedDependency.owner +native(
  Zcash.Meta.Tests.AxiomCheck.ForgedDependency.owner)

end ForgedDependency

end Zcash.Meta.Tests.AxiomCheck
