import Mathlib
import CompElliptic.Fields.Pasta

/-!
# The verifier's scalar field `F_p`

An Orchard proof is a halo2 proof over the Vesta curve (the verifier group `E_q`): commitments are
Vesta points; challenges and evaluations live in Vesta's scalar field `F_p`. By the Pasta
construction `F_p = vesta::Scalar = pallas::Base = ZMod p` with `p = PALLAS_BASE_CARD ≈ 2²⁵⁴` —
the Pallas *base* order, not the Pallas *scalar* order of the value commitment.

The development stays generic over `[Field F]`; this module pins the instantiation `F_p = ZMod p`
and records `|F_p| = p` (`card_Fp`), the cardinality the Schwartz–Zippel bound divides by. The
Pasta construction itself is not needed for soundness; the one curve-level fact that is — the
Vesta group order — is proven unconditionally in `Zcash.Snark.Soundness.Vesta` (`vestaOrder`, from
CompElliptic's `Pasta.Vesta.card_eq`), no longer an assumption.
-/

namespace Zcash.Snark

/-- The verifier's scalar field order `p = |E_q|` — the Vesta scalar order, equal to the Pallas
base order `PALLAS_BASE_CARD`. Imported from `CompElliptic.Fields.Pasta` with a machine-checked
Lucas/Pratt primality certificate. -/
@[reducible] def scalarFieldOrder : ℕ := CompElliptic.Fields.Pasta.PALLAS_BASE_CARD

/-- The verifier's scalar field `F_p = ZMod p` (the Vesta scalar field); a field, since `p` is
prime (CompElliptic's instance). -/
abbrev Fp := ZMod scalarFieldOrder

instance : Fact (Nat.Prime scalarFieldOrder) :=
  inferInstanceAs (Fact (Nat.Prime CompElliptic.Fields.Pasta.PALLAS_BASE_CARD))

instance : NeZero scalarFieldOrder :=
  ⟨(Fact.out : Nat.Prime scalarFieldOrder).pos.ne'⟩

/-- `F_p` is finite of cardinality `p` — the quantity the Schwartz–Zippel soundness bound divides by. -/
theorem card_Fp : Fintype.card Fp = scalarFieldOrder :=
  ZMod.card scalarFieldOrder

end Zcash.Snark
