import Zcash.Meta.AxiomCheck

/-!
# Regression tests for native-axiom provenance

The negative cases deliberately impersonate Lean's `native_decide` auxiliaries: most declare an
axiom named like an auxiliary, and one instead names a *theorem* so that its own genuine auxiliary
imitates the marker path. They live in this test-only library so the production `Zcash` library
never imports them.
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

namespace MacroForged

/-! The forgery `ForgedDependency` cannot express. A top-level `axiom` command is necessarily its
own command, so its start lands *before* the owner's — which is what makes that case detectable.
Macro expansion removes exactly that tell: every declaration a macro emits inherits the macro
*invocation site* as its declaration range, so the axiom and the theorem using it share one
identical range. A non-strict start comparison accepts that automatically, and the census would
then certify an arbitrary axiom — here `False` — as a `native_decide` compiler-trust certificate.
`rangeStartsInside` therefore requires the auxiliary to start *strictly* after the owner, which no
macro-emitted sibling can do while both genuine shapes (`Genuine`, `GenuineAutoParam`) still can. -/

macro "forge " n:ident " : " t:term : command =>
  `(axiom $(Lean.mkIdent (n.getId ++ `_native ++ `native_decide ++ `ax_1_1)) : $t
    theorem $n : $t := $(Lean.mkIdent (n.getId ++ `_native ++ `native_decide ++ `ax_1_1)))

forge owner : False

/-- error: 'Zcash.Meta.Tests.AxiomCheck.MacroForged.owner._native.native_decide.ax_1_1' looks like a native_decide axiom owned by 'Zcash.Meta.Tests.AxiomCheck.MacroForged.owner', but it was not emitted inside that declaration -/
#guard_msgs (whitespace := lax) in
assert_axioms Zcash.Meta.Tests.AxiomCheck.MacroForged.owner +native(
  Zcash.Meta.Tests.AxiomCheck.MacroForged.owner)

end MacroForged

namespace SecondCertificate

/-! Two genuine certificates in one cone. The allowance compares the exact *set* of native axioms
reached against the set the named owners actually own, so an annotation that names only the first
owner goes stale the moment a second certificate enters the cone. Comparing owner sets alone would
not suffice: distinct axioms can share an owner name (see `AliasedOwner`). -/

theorem first : (234567 : Nat) < 234568 := by native_decide

theorem second : (345678 : Nat) < 345679 := by native_decide

theorem target : (234567 : Nat) < 234568 ∧ (345678 : Nat) < 345679 := ⟨first, second⟩

/-- error: Zcash.Meta.Tests.AxiomCheck.SecondCertificate.target: '+native' names [Zcash.Meta.Tests.AxiomCheck.SecondCertificate.first] but the native_decide axiom(s) present are owned by [Zcash.Meta.Tests.AxiomCheck.SecondCertificate.first, Zcash.Meta.Tests.AxiomCheck.SecondCertificate.second]; write '+native(Zcash.Meta.Tests.AxiomCheck.SecondCertificate.first, Zcash.Meta.Tests.AxiomCheck.SecondCertificate.second)' -/
#guard_msgs (whitespace := lax) in
assert_axioms Zcash.Meta.Tests.AxiomCheck.SecondCertificate.target +native(
  Zcash.Meta.Tests.AxiomCheck.SecondCertificate.first)

assert_axioms Zcash.Meta.Tests.AxiomCheck.SecondCertificate.target +native(
  Zcash.Meta.Tests.AxiomCheck.SecondCertificate.first,
  Zcash.Meta.Tests.AxiomCheck.SecondCertificate.second)

end SecondCertificate

namespace AliasedOwner

/-! A certifying declaration whose *own* name contains the marker components. Its auxiliary is
`owner.native_decide.smuggled._native.native_decide.ax_1_1`, so reading ownership off the prefix
before the *first* `_native`/`native_decide` component would credit it to `owner` — collapsing it
onto the legitimate certificate, where a pre-existing `+native(owner)` would cover both and admit
an undisclosed compiler-trust dependency. Ownership is decided by the *last* marker instead, so the
smuggled certificate keeps its own owner and the stale annotation fails the build. -/

theorem owner : (456789 : Nat) < 456790 := by native_decide

namespace owner.native_decide

theorem smuggled : (567890 : Nat) < 567891 := by native_decide

end owner.native_decide

theorem target : (456789 : Nat) < 456790 ∧ (567890 : Nat) < 567891 :=
  ⟨owner, owner.native_decide.smuggled⟩

/-- error: Zcash.Meta.Tests.AxiomCheck.AliasedOwner.target: '+native' names [Zcash.Meta.Tests.AxiomCheck.AliasedOwner.owner] but the native_decide axiom(s) present are owned by [Zcash.Meta.Tests.AxiomCheck.AliasedOwner.owner, Zcash.Meta.Tests.AxiomCheck.AliasedOwner.owner.native_decide.smuggled]; write '+native(Zcash.Meta.Tests.AxiomCheck.AliasedOwner.owner, Zcash.Meta.Tests.AxiomCheck.AliasedOwner.owner.native_decide.smuggled)' -/
#guard_msgs (whitespace := lax) in
assert_axioms Zcash.Meta.Tests.AxiomCheck.AliasedOwner.target +native(
  Zcash.Meta.Tests.AxiomCheck.AliasedOwner.owner)

/-! The disclosure the census demands: the smuggled certificate is attributed to its own
declaration, not aliased onto `owner`. -/
assert_axioms Zcash.Meta.Tests.AxiomCheck.AliasedOwner.target +native(
  Zcash.Meta.Tests.AxiomCheck.AliasedOwner.owner,
  Zcash.Meta.Tests.AxiomCheck.AliasedOwner.owner.native_decide.smuggled)

end AliasedOwner

end Zcash.Meta.Tests.AxiomCheck
