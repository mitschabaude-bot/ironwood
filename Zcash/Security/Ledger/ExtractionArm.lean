import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Probability.Distributions.Uniform
import Zcash.Security.Ledger.Capstone
import Zcash.Security.Ledger.Value
import Zcash.Security.RedDSA.Extraction

/-!
# The transaction-balance premiss with a fallible extractor

The transaction-balance premiss discharge, in extractor-plus-knowledge-error form:
the extractor is an arbitrary *function*, its failures are *exhibited*, and the
capstones bound the violation probability by `ε_dlr + κ` — equivalently, a violation
yields a computed `(Vbase, Rbase)` relation with probability at least `Pr[violation] − κ`.
A total extraction hypothesis would be classically satisfiable and carry no
computational content (see the module doc of `Zcash.Security.Ledger.Value`).

* `BindingSigShape` pins `Primitives.bindingVerify` to an abstract RedDSA scheme
  based at the randomness base `Rbase` (`Zcash.Security.RedDSA.Basic`) — the spec's
  demand that a binding signature "prove knowledge of the discrete logarithm of the
  validating key with respect to the base ℛ" (§5.4.7.2) is then a statement about
  this scheme.
* `ValueShape.premissOrBreakFallible` decides the per-transaction net-value equation
  and, on failure, runs the extractor: *either* it pins `bvk` and the witnessed
  bundle computes the nontrivial `(Vbase, Rbase)` relation, *or* the transaction's verifying
  binding signature is an exhibited `RedDSA.ExtractionFailure` — the knowledge-error
  event, as data.
* `balanceConservation_measure_le_kerr` / `shieldedBalanceCap_measure_le_kerr`
  compose the three-way premiss into the probabilistic capstones:
  violation ≤ `ε_dlr + κ`, with `ε_dlr` bounding the relation arm (discharged onward
  against DL hardness via the AGM layer) and `κ` bounding the extraction-failure
  arm.

What stays named: `κ` itself — the RedDSA knowledge error, a bound on the probability that
an adversary produces a verifying signature that the extractor misses. The known
discharge routes and their losses are described in the module doc of
`Zcash.Security.RedDSA.Basic`. None is chosen here. The `Extractor` interface
consumes only the verifying triple `(vk, m, σ)`: a straight-line AGM discharge
extracts from an algebraic adversary's representations and a rewinding discharge
re-runs the adversary, so a discharge would widen the interface or restate the
bound per adversary.
-/

namespace Zcash.Security.Ledger.Model

open Zcash.Security.BindingSignature
open scoped ENNReal

variable {r : ℕ} [Fact (Nat.Prime r)]
variable {G : Type*} [AddCommGroup G] [Module (ZMod r) G]
variable {IVK NK RHO PSI MHASH MENC MSG SIG : Type*} {KW : Type*}
variable {P : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG}
variable {kv : KeyBindingInterface KW G IVK NK}
variable {issuance : ℕ → ℕ} {maxActions : ℕ}

/-- The RedDSA shape of the binding-signature primitive: an abstract scheme based at
the value-commitment randomness base `Rbase` whose verification equation is what
`bindingVerify` computes, with `toSig` decoding the model's opaque signature type.
The signature-side counterpart of the same shape's `ValueShape` commitment side. -/
structure BindingSigShape (P : Primitives (ZMod r) G IVK NK RHO PSI MHASH MENC MSG SIG)
    (shape : ValueShape P) where
  sch : RedDSA.Scheme (ZMod r) G MSG
  toSig : SIG → RedDSA.Sig (ZMod r) G
  base_eq : sch.base = shape.Rbase
  verify_iff : ∀ (bvk : G) (m : MSG) (σ : SIG),
    P.bindingVerify bvk m σ ↔ sch.Verify bvk m (toSig σ)

/-- **The valid imbalance fits the field.** A valid transaction's integer imbalance has
magnitude at most the `vSum` shape `maxActions · (valueBound − 1) + vBalanceBound` —the
statement's strict value ranges bound each action's net value, validity bounds the action
count and the declared balance— which the no-overflow hypothesis places below `r`. The
shared discharge of both conservation arms' `natAbs < r` obligations. -/
theorem ValidLedger.imbalance_natAbs_lt
    {ledger : Ledger KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth}
    (hval : ValidLedger P kv issuance maxActions ledger)
    (hr : maxActions * (P.valueBound - 1) + P.vBalanceBound < r)
    {tx : Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth} (htx : tx ∈ ledger) :
    (txNetValue tx - tx.vBalance).natAbs < r :=
  calc (txNetValue tx - tx.vBalance).natAbs
      ≤ (txNetValue tx).natAbs + tx.vBalance.natAbs := Int.natAbs_sub_le _ _
    _ ≤ maxActions * (P.valueBound - 1) + P.vBalanceBound :=
        Nat.add_le_add
          (le_trans (txNetValue_natAbs_le (P := P) (kv := kv) (hval.satisfied tx htx))
            (Nat.mul_le_mul_right _ (hval.action_bound tx htx)))
          (hval.vbalance_bound tx htx)
    _ < r := hr

/-- **The transaction-balance premiss discharge, with a fallible extractor.** Decide the
per-transaction net-value equation. On failure, run `extractor` on the transaction's
verifying binding signature. If `extractor` pins `bvk = [bsk] Rbase`, the witnessed bundle
computes the nontrivial `(Vbase, Rbase)` relation, with the no-overflow bound `hr`.
Otherwise the failure is exhibited as a `RedDSA.ExtractionFailure`: a verifying signature
whose key the extractor misses — the event that the knowledge error `κ` bounds. Nothing is
assumed of `extractor`. -/
def ValueShape.premissOrBreakFallible [DecidableEq G]
    {ledger : Ledger KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth}
    (shape : ValueShape P) (binding : BindingSigShape P shape)
    (hval : ValidLedger P kv issuance maxActions ledger)
    (hr : maxActions * (P.valueBound - 1) + P.vBalanceBound < r)
    (extractor : RedDSA.Extractor (ZMod r) G MSG)
    (tx : Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth) (htx : tx ∈ ledger) :
    (txNetValue tx = tx.vBalance)
      ⊕' (BindingSignature.NontrivialRelation (F := ZMod r) shape.Vbase shape.Rbase
          ⊕' RedDSA.ExtractionFailure binding.sch extractor) :=
  if heq : txNetValue tx = tx.vBalance then .inl heq
  else if hex : tx.bvk P
      = extractor (tx.bvk P) tx.sighash (binding.toSig tx.bindingSig) • shape.Rbase then
    .inr (.inl (NontrivialRelation.ofBundleIntImbalance shape.Vbase shape.Rbase (txBundle tx) []
      tx.vBalance
      (extractor (tx.bvk P) tx.sighash (binding.toSig tx.bindingSig))
      (by
        simp only [List.map_nil, List.sum_nil, sub_zero, txBundle_fst_sum]
        exact sub_ne_zero.mpr heq)
      (by
        simp only [List.map_nil, List.sum_nil, sub_zero, txBundle_fst_sum]
        exact hval.imbalance_natAbs_lt hr htx)
      ((bvk_eq shape (hval.satisfied tx htx)).symm.trans hex)))
  else
    .inr (.inr ⟨tx.bvk P, tx.sighash, binding.toSig tx.bindingSig,
      (binding.verify_iff _ _ _).mp (hval.binding_verified tx htx),
      by rw [binding.base_eq]; exact hex⟩)

section Capstone

variable [DecidableEq G]

variable (kv) in
/-- `premissOrBreakFallible` as the per-sample premiss the probabilistic capstones
consume, at the break type `NontrivialRelation ⊕' ExtractionFailure`. -/
def txBalancePremissFallible (shape : ValueShape P) (binding : BindingSigShape P shape)
    (hr : maxActions * (P.valueBound - 1) + P.vBalanceBound < r)
    (extractor : RedDSA.Extractor (ZMod r) G MSG)
    (ω : ValidAnnotated P kv issuance maxActions)
    (tx : Tx KW (ZMod r) G RHO PSI MHASH MENC MSG SIG P.depth) (htx : tx ∈ ω.1) :
    (txNetValue tx = tx.vBalance)
      ⊕' (BindingSignature.NontrivialRelation (F := ZMod r) shape.Vbase shape.Rbase
          ⊕' RedDSA.ExtractionFailure binding.sch extractor) :=
  shape.premissOrBreakFallible binding ω.2 hr extractor tx htx

variable (kv) in
/-- The relation arm: the samples on which the conservation reduction computes a
nontrivial `(Vbase, Rbase)` relation. Bounded onward by DL hardness (via the AGM layer's
relation-to-DL handoff); its named bound is the `ε_dlr` slot. -/
def valueRelationEvent (shape : ValueShape P) (binding : BindingSigShape P shape)
    (hr : maxActions * (P.valueBound - 1) + P.vBalanceBound < r)
    (extractor : RedDSA.Extractor (ZMod r) G MSG) (i : ℕ) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ b, balanceConservationOrBreak (issuance := issuance)
    (txBalancePremissFallible kv shape binding hr extractor ω) i = .inr (.inl b)}

variable (kv) in
/-- The extraction-failure arm: the samples on which the reduction exhibits a
verifying binding signature whose key the extractor misses
(`RedDSA.ExtractionFailure`, carried as data in the branch). Its named bound is the
knowledge error `κ`. -/
def extractFailEvent (shape : ValueShape P) (binding : BindingSigShape P shape)
    (hr : maxActions * (P.valueBound - 1) + P.vBalanceBound < r)
    (extractor : RedDSA.Extractor (ZMod r) G MSG) (i : ℕ) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ failure, balanceConservationOrBreak (issuance := issuance)
    (txBalancePremissFallible kv shape binding hr extractor ω) i = .inr (.inr failure)}

variable (kv) in
/-- The extraction failure computed on a sample: the branch value of the conservation
reduction, when it lands in the extraction-failure arm. -/
def extractFailureOf (shape : ValueShape P) (binding : BindingSigShape P shape)
    (hr : maxActions * (P.valueBound - 1) + P.vBalanceBound < r)
    (extractor : RedDSA.Extractor (ZMod r) G MSG)
    (ω : ValidAnnotated P kv issuance maxActions) (i : ℕ) :
    Option (RedDSA.ExtractionFailure binding.sch extractor) :=
  match balanceConservationOrBreak (issuance := issuance)
    (txBalancePremissFallible kv shape binding hr extractor ω) i with
  | .inr (.inr failure) => some failure
  | _ => none

/-- On the extraction-failure arm the computed failure is defined: the arm's named
`κ` is a bound on the adversary's probability of beating the extractor, and nothing
else. -/
theorem extractFailureOf_isSome (shape : ValueShape P) (binding : BindingSigShape P shape)
    (hr : maxActions * (P.valueBound - 1) + P.vBalanceBound < r)
    (extractor : RedDSA.Extractor (ZMod r) G MSG) (i : ℕ)
    {ω : ValidAnnotated P kv issuance maxActions}
    (hω : ω ∈ extractFailEvent kv shape binding hr extractor i) :
    (extractFailureOf kv shape binding hr extractor ω i).isSome := by
  obtain ⟨failure, hfailure⟩ := hω
  simp only [extractFailureOf, hfailure, Option.isSome_some]

/-- The transaction-balance premiss arm splits into the relation arm and the
extraction-failure arm. -/
theorem txBalanceBreakEvent_fallible_subset (shape : ValueShape P)
    (binding : BindingSigShape P shape)
    (hr : maxActions * (P.valueBound - 1) + P.vBalanceBound < r)
    (extractor : RedDSA.Extractor (ZMod r) G MSG) (i : ℕ) :
    txBalanceBreakEvent
        (txBalancePremissFallible (issuance := issuance) kv shape binding hr extractor) i
      ⊆ valueRelationEvent kv shape binding hr extractor i
        ∪ extractFailEvent kv shape binding hr extractor i := by
  rintro ω ⟨b, hb⟩
  cases b with
  | inl rel => exact Or.inl ⟨rel, hb⟩
  | inr failure => exact Or.inr ⟨failure, hb⟩

/-- **Value conservation in extractor-plus-knowledge-error form.** For any adversary
and any `extractor`, the probability that the value ledger fails to balance
is at most `ε_dlr + κ`: the relation arm's bound plus the knowledge error. Read
contrapositively, a violation computes a nontrivial `(Vbase, Rbase)` relation with
probability at least `Pr[violation] − κ` — the extraction succeeds up to the
knowledge error, which is the form a forking discharge of `κ` composes with. -/
theorem balanceConservation_measure_le_kerr
    (A : PMF (ValidAnnotated P kv issuance maxActions))
    (shape : ValueShape P) (binding : BindingSigShape P shape)
    (hr : maxActions * (P.valueBound - 1) + P.vBalanceBound < r)
    (extractor : RedDSA.Extractor (ZMod r) G MSG) (i : ℕ) {ε_dlr κ : ℝ≥0∞}
    (hdlr : A.toOuterMeasure (valueRelationEvent kv shape binding hr extractor i) ≤ ε_dlr)
    (hκ : A.toOuterMeasure (extractFailEvent kv shape binding hr extractor i) ≤ κ) :
    A.toOuterMeasure (balanceConservationViolation i) ≤ ε_dlr + κ :=
  le_trans
    (toOuterMeasure_le_add₂ A
      (le_trans
        (balanceConservationViolation_subset
          (txBalancePremissFallible kv shape binding hr extractor) i)
        (txBalanceBreakEvent_fallible_subset shape binding hr extractor i)))
    (add_le_add hdlr hκ)

/-- **Balance-value in extractor-plus-knowledge-error form.** As
`balanceConservation_measure_le_kerr`, for the shielded pool exceeding the minted
issuance. -/
theorem shieldedBalanceCap_measure_le_kerr
    (A : PMF (ValidAnnotated P kv issuance maxActions))
    (shape : ValueShape P) (binding : BindingSigShape P shape)
    (hr : maxActions * (P.valueBound - 1) + P.vBalanceBound < r)
    (extractor : RedDSA.Extractor (ZMod r) G MSG) (i : ℕ) {ε_dlr κ : ℝ≥0∞}
    (hdlr : A.toOuterMeasure (valueRelationEvent kv shape binding hr extractor i) ≤ ε_dlr)
    (hκ : A.toOuterMeasure (extractFailEvent kv shape binding hr extractor i) ≤ κ) :
    A.toOuterMeasure (shieldedBalanceCapViolation i) ≤ ε_dlr + κ :=
  le_trans
    (toOuterMeasure_le_add₂ A
      (le_trans
        (shieldedBalanceCapViolation_subset
          (txBalancePremissFallible kv shape binding hr extractor) i)
        (txBalanceBreakEvent_fallible_subset shape binding hr extractor i)))
    (add_le_add hdlr hκ)

/-! ### All prefixes -/

variable (kv) in
/-- The all-prefixes relation arm: at some prefix `i < k`, the conservation reduction
computes a nontrivial `(Vbase, Rbase)` relation. -/
def valueRelationEventBefore (shape : ValueShape P) (binding : BindingSigShape P shape)
    (hr : maxActions * (P.valueBound - 1) + P.vBalanceBound < r)
    (extractor : RedDSA.Extractor (ZMod r) G MSG) (k : ℕ) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ i, i < k ∧ ω ∈ valueRelationEvent kv shape binding hr extractor i}

variable (kv) in
/-- The all-prefixes extraction-failure arm: at some prefix `i < k`, the reduction
exhibits a verifying binding signature whose key the extractor misses. -/
def extractFailEventBefore (shape : ValueShape P) (binding : BindingSigShape P shape)
    (hr : maxActions * (P.valueBound - 1) + P.vBalanceBound < r)
    (extractor : RedDSA.Extractor (ZMod r) G MSG) (k : ℕ) :
    Set (ValidAnnotated P kv issuance maxActions) :=
  {ω | ∃ i, i < k ∧ ω ∈ extractFailEvent kv shape binding hr extractor i}

/-- A conservation violation at some prefix lands in the all-prefixes relation arm or
the all-prefixes extraction-failure arm, at that same prefix. -/
theorem balanceConservationViolationBefore_subset_fallible (shape : ValueShape P)
    (binding : BindingSigShape P shape) (hr : maxActions * (P.valueBound - 1) + P.vBalanceBound < r)
    (extractor : RedDSA.Extractor (ZMod r) G MSG) (k : ℕ) :
    balanceConservationViolationBefore (P := P) (kv := kv) (issuance := issuance)
        (maxActions := maxActions) k
      ⊆ valueRelationEventBefore kv shape binding hr extractor k
        ∪ extractFailEventBefore kv shape binding hr extractor k := by
  rintro ω ⟨i, hik, hω⟩
  rcases txBalanceBreakEvent_fallible_subset shape binding hr extractor i
      (balanceConservationViolation_subset
        (txBalancePremissFallible kv shape binding hr extractor) i hω)
    with h | h
  · exact Or.inl ⟨i, hik, h⟩
  · exact Or.inr ⟨i, hik, h⟩

/-- A cap violation at some prefix lands in the same two all-prefixes arms. -/
theorem shieldedBalanceCapViolationBefore_subset_fallible (shape : ValueShape P)
    (binding : BindingSigShape P shape) (hr : maxActions * (P.valueBound - 1) + P.vBalanceBound < r)
    (extractor : RedDSA.Extractor (ZMod r) G MSG) (k : ℕ) :
    shieldedBalanceCapViolationBefore (P := P) (kv := kv) (issuance := issuance)
        (maxActions := maxActions) k
      ⊆ valueRelationEventBefore kv shape binding hr extractor k
        ∪ extractFailEventBefore kv shape binding hr extractor k := by
  rintro ω ⟨i, hik, hω⟩
  rcases txBalanceBreakEvent_fallible_subset shape binding hr extractor i
      (shieldedBalanceCapViolation_subset
        (txBalancePremissFallible kv shape binding hr extractor) i hω)
    with h | h
  · exact Or.inl ⟨i, hik, h⟩
  · exact Or.inr ⟨i, hik, h⟩

/-- **All-prefixes value conservation in extractor-plus-knowledge-error form.** The
probability that the ledger fails to balance at some prefix `i < k` is at most
`ε_dlr + κ`, with no factor of `k`: every prefix's violation lands in the one
all-prefixes relation arm or the one all-prefixes extraction-failure arm. -/
theorem balanceConservationBefore_measure_le_kerr
    (A : PMF (ValidAnnotated P kv issuance maxActions))
    (shape : ValueShape P) (binding : BindingSigShape P shape)
    (hr : maxActions * (P.valueBound - 1) + P.vBalanceBound < r)
    (extractor : RedDSA.Extractor (ZMod r) G MSG) (k : ℕ) {ε_dlr κ : ℝ≥0∞}
    (hdlr : A.toOuterMeasure (valueRelationEventBefore kv shape binding hr extractor k) ≤ ε_dlr)
    (hκ : A.toOuterMeasure (extractFailEventBefore kv shape binding hr extractor k) ≤ κ) :
    A.toOuterMeasure (balanceConservationViolationBefore (P := P) (kv := kv)
        (issuance := issuance) (maxActions := maxActions) k) ≤ ε_dlr + κ :=
  le_trans
    (toOuterMeasure_le_add₂ A
      (balanceConservationViolationBefore_subset_fallible shape binding hr extractor k))
    (add_le_add hdlr hκ)

/-- **All-prefixes shielded-balance cap in extractor-plus-knowledge-error form.** As
`balanceConservationBefore_measure_le_kerr`, for the shielded pool exceeding the
minted issuance at some prefix. -/
theorem shieldedBalanceCapBefore_measure_le_kerr
    (A : PMF (ValidAnnotated P kv issuance maxActions))
    (shape : ValueShape P) (binding : BindingSigShape P shape)
    (hr : maxActions * (P.valueBound - 1) + P.vBalanceBound < r)
    (extractor : RedDSA.Extractor (ZMod r) G MSG) (k : ℕ) {ε_dlr κ : ℝ≥0∞}
    (hdlr : A.toOuterMeasure (valueRelationEventBefore kv shape binding hr extractor k) ≤ ε_dlr)
    (hκ : A.toOuterMeasure (extractFailEventBefore kv shape binding hr extractor k) ≤ κ) :
    A.toOuterMeasure (shieldedBalanceCapViolationBefore (P := P) (kv := kv)
        (issuance := issuance) (maxActions := maxActions) k) ≤ ε_dlr + κ :=
  le_trans
    (toOuterMeasure_le_add₂ A
      (shieldedBalanceCapViolationBefore_subset_fallible shape binding hr extractor k))
    (add_le_add hdlr hκ)

end Capstone

end Zcash.Security.Ledger.Model
