import Zcash.Security.BindingSignature.Balance
import CompElliptic.Fields.Pasta

/-!
# Orchard no-overflow bound (spec §4.14)

The Orchard action count is bounded *directly* by a dedicated consensus rule `n ≤ 2^16 − 1`,
independent of the transaction size (the spec notes this is technically redundant given the
2 MB limit, but it stands on its own). Each action commits to the signed *net* value
`v = v_spend − v_output`, range-proven by the Action statement to lie in
`SignedValueDifferenceType = [−2^64+1, 2^64−1]`, i.e. `|v| ≤ 2^64 − 1`.

This module instantiates the generic `natAbs_lt_of_abs_le` from `Balance` at those concrete bounds,
discharging the `hbound` hypothesis of `bundle_integer_balances_reduction` for Orchard.
-/

namespace Zcash.Security.BindingSignature

/-- The Pallas scalar field order `r_ℙ` — the order of the Pallas group, which is the scalar field of
the Orchard value commitment (spec § Pallas and Vesta). Imported from `CompElliptic.Fields.Pasta`,
where it carries a Lucas/Pratt primality certificate. -/
@[reducible] def pallasScalarOrder : ℕ := CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD

/-- The Orchard `vSum` magnitude bound = the spec's `ValueCommitTypeOrchard` subrange endpoint
`(2^16 − 1)·(2^64 − 1) + 2^63`, from `|v| ≤ 2^64 − 1` per action, the consensus rule `n ≤ 2^16 − 1`,
and the signed-64-bit `vBalance`. -/
def orchardVSumBound : ℤ := vSumBound (2^16 - 1)

/-- The bound equals the spec's quoted endpoint. -/
example : orchardVSumBound = 1208916596242592319864833 := by norm_num [orchardVSumBound, vSumBound]

/-- **Orchard no-overflow bound.** With `|v| ≤ 2^64 − 1` per action, `n ≤ 2^16 − 1` actions, and
`|vBalance| ≤ 2^63`, the net sum `vSum = ∑ v − vBalance` has `vSum.natAbs < r` once
`orchardVSumBound < r` — directly from the shared `natAbs_lt_of_vSumBound`. This is the `hbound` of
`NontrivialRelation.ofBundleIntImbalance` for Orchard. -/
theorem orchard_natAbs_lt {r : ℕ} (vs : List ℤ) (vBalance : ℤ)
    (hv : ∀ v ∈ vs, |v| ≤ 2^64 - 1)
    (hn : vs.length ≤ 2^16 - 1)
    (hvBalance : |vBalance| ≤ 2^63)
    (hr : orchardVSumBound < (r : ℤ)) :
    (vs.sum - vBalance).natAbs < r :=
  natAbs_lt_of_vSumBound vs vBalance (2^16 - 1) hv hn hvBalance hr

/-- The bound fits the Pallas scalar field: the `hr` that instantiates `orchard_natAbs_lt` at
`r = pallasScalarOrder` (and witnesses that the lemma is not vacuous). -/
theorem orchardVSumBound_lt_pallasScalarOrder : orchardVSumBound < (pallasScalarOrder : ℤ) := by
  norm_num [orchardVSumBound, vSumBound, pallasScalarOrder]

/-- **Orchard integer balance reduction (§4.14), as a computed relation.** A verifying Orchard
bundle of `≤ 2^16 − 1` actions — each committing a net value `v ∈ [−2^64+1, 2^64−1]`, with
signed-64-bit `vBalance` — that does not balance over ℤ (`∑ v_net − vBalance ≠ 0`) yields an
explicit nontrivial discrete-log relation between `Vbase` and `Rbase`, as data. The no-overflow bound is
discharged here by `orchard_natAbs_lt`; there is no binding assumption (RedDSA extractability
`hExtract` is the only cryptographic input). The computed relation is discharged against DLR
hardness at the computational layer, and Orchard bundle balance is the contrapositive. -/
def NontrivialRelation.ofOrchardImbalance {M : Type*} [AddCommGroup M]
    [Module (ZMod pallasScalarOrder) M]
    (Vbase Rbase : M) (actions : List (ℤ × ZMod pallasScalarOrder)) (vBalance : ℤ)
    (bsk : ZMod pallasScalarOrder)
    (hne : (actions.map Prod.fst).sum - vBalance ≠ 0)
    (hv : ∀ v ∈ actions.map Prod.fst, |v| ≤ 2^64 - 1)
    (hn : actions.length ≤ 2^16 - 1)
    (hvBalance : |vBalance| ≤ 2^63)
    (hExtract : bindingVK Vbase Rbase (castBundle actions) (castBundle []) (vBalance : ZMod pallasScalarOrder)
      = bsk • Rbase) :
    NontrivialRelation (F := ZMod pallasScalarOrder) Vbase Rbase :=
  have hbound := orchard_natAbs_lt (actions.map Prod.fst) vBalance hv (by simpa using hn) hvBalance
    orchardVSumBound_lt_pallasScalarOrder
  NontrivialRelation.ofBundleIntImbalance Vbase Rbase actions [] vBalance bsk (by simpa using hne)
    (by simpa using hbound) hExtract

end Zcash.Security.BindingSignature
