import Zcash.Common.Satisfying
import Zcash.Security.Ledger.SinsemillaDLR
import Zcash.Snark.Soundness.Action.AdaptiveStatementKnowledge

/-!
# The bundle-level Action-to-ledger bridge

Lift the per-Action data bridge across an accepted bundle. Each extracted member
witness (`TopLevelSemanticWitness`) is a satisfying witness of the circuit-facing
`ActionSpec` (`Zcash.Common.Satisfying`), and `actionSpecToLedgerData` refines it to
the member's ledger data —the full extracted witness together with its refined
ledger action— or the computed discrete-log relation of its first Sinsemilla
escape. The bundle traversal returns every member's data or the first escape
(`finForallOrRelationWitness`): knowledge soundness composed at the reduction layer,
with everything carried as data.
-/

namespace Zcash.Security.Ledger.ActionBundleBridge

open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Common
open Zcash.Security.Concrete
open Zcash.Security.Ledger.Bridge
open Zcash.Snark
open Zcash.Snark.ActionTerminal

variable {MSG SIG : Type*}

/-- An extracted bundle member as a satisfying witness of the circuit-facing
`ActionSpec`: the private witness transported across the circuit boundary, with its
specification proof. -/
def memberSatisfying {input : PublicInputs Fp}
    (w : TopLevelSemanticWitness actionCircuit input) :
    Satisfying ActionSpec input where
  w := actionCircuit_privateWitness_eq ▸ w.w
  satisfied := by
    rw [actionCircuit_spec_iff]
    simp only [eqRec_eq_cast, cast_cast, cast_eq]
    exact w.satisfied

/-- The ledger data of one accepted bundle member. -/
structure MemberLedgerData
    (spendAuthVerify bindingVerify : PallasGroup → MSG → SIG → Prop)
    (input : PublicInputs Fp) where
  /-- The member's extracted private witness — the chain's genuinely free value,
  carried in full. -/
  wit : PrivateWitness
  /-- The member's refined ledger action. -/
  success : ActionLedgerSuccess spendAuthVerify bindingVerify (combine input wit)

/-- Refine one extracted bundle member to its ledger data, or the computed
discrete-log relation of its first Sinsemilla escape. -/
def memberLedgerData
    (spendAuthVerify bindingVerify : PallasGroup → MSG → SIG → Prop)
    {input : PublicInputs Fp}
    (w : TopLevelSemanticWitness actionCircuit input) :
    MemberLedgerData spendAuthVerify bindingVerify input ⊕' ActionDLBreak :=
  let sat := memberSatisfying w
  bindOrRelationWitness
    (actionSpecToLedgerData spendAuthVerify bindingVerify input sat.w sat.satisfied)
    fun success => { wit := sat.w, success := success }

/-- Refine every member of an accepted bundle, or return the first member's computed
escape relation. -/
def bundleLedgerData
    (spendAuthVerify bindingVerify : PallasGroup → MSG → SIG → Prop)
    {numProofs : ℕ} {inputs : Fin numProofs → PublicInputs Fp}
    (witness : ActionBundleWitness inputs) :
    (∀ i, MemberLedgerData spendAuthVerify bindingVerify (inputs i)) ⊕' ActionDLBreak :=
  finForallOrRelationWitness fun i =>
    memberLedgerData spendAuthVerify bindingVerify (witness i)

section Extraction

open Zcash.Arithmetic (scalarFieldOrder)

variable {pp : ProofParams} (family : ComputedAdaptiveActionStatementFSFamily pp)
  (hchar : ∀ basis O, deployedX4PairCount (adaptiveActionStatementVk pp basis)
    (adaptiveActionStatementInstanceCommitment pp basis (family.runOutput basis O).inputs)
    (family.runProof basis O).proof.1 (family.runRecord basis O) < scalarFieldOrder)
  (spendAuthVerify bindingVerify : PallasGroup → MSG → SIG → Prop)

/-- The ledger-level outcome of one adaptive-statement run: every member's ledger data, a
ledger Sinsemilla escape, or the circuit-side algebraic relation over the run's own basis.
`none` is exactly the runs on which the shared knowledge outcome is undefined
(`actionLedgerOutcome_isSome_iff`). The routing is deliberate: circuit-side relations
stay in their own arm —on accepting runs, that arm and `none` together are the
knowledge-failure event that the knowledge-error endpoint bounds— and only the
bridge's Sinsemilla escapes surface as ledger breaks. -/
def actionLedgerOutcome
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    Option ((∀ i, MemberLedgerData spendAuthVerify bindingVerify
        ((family.runOutput basis O).inputs i))
      ⊕ (ActionDLBreak ⊕ AlgebraicRelationWitness (F := Fp) basis)) :=
  (family.adaptiveStatementKnowledgeOutcome hchar basis O).map fun
    | Sum.inl witness =>
        match bundleLedgerData spendAuthVerify bindingVerify witness with
        | PSum.inl members => Sum.inl members
        | PSum.inr dlb => Sum.inr (Sum.inl dlb)
    | Sum.inr relation => Sum.inr (Sum.inr relation)

/-- The composed ledger-level extractor: every member's ledger data, on the runs
where the witness extraction succeeds and no member escapes. -/
def actionLedgerExtractor
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) :
    Option (∀ i, MemberLedgerData spendAuthVerify bindingVerify
      ((family.runOutput basis O).inputs i)) :=
  match actionLedgerOutcome family hchar spendAuthVerify bindingVerify basis O with
  | some (Sum.inl members) => some members
  | _ => none

/-- The ledger outcome is defined exactly where the shared knowledge outcome is:
the composition adds no new failure. -/
theorem actionLedgerOutcome_isSome_iff (basis) (O) :
    (actionLedgerOutcome family hchar spendAuthVerify bindingVerify basis O).isSome ↔
      (family.adaptiveStatementKnowledgeOutcome hchar basis O).isSome := by
  unfold actionLedgerOutcome
  simp

/-- The computed ledger escape of one run: the discrete-log relation data of the first
member's Sinsemilla escape, on the runs where the extracted bundle escapes the bridge. -/
def actionLedgerEscapeFinder
    (basis : AugmentedIndex (2 ^ (AdaptiveActionStatementShape pp).k) → VestaG)
    (O : family.Coins) : Option ActionDLBreak :=
  match actionLedgerOutcome family hchar spendAuthVerify bindingVerify basis O with
  | some (Sum.inr (Sum.inl dlb)) => some dlb
  | _ => none

/-- The composed `actionLedgerExtractor` fails iff either:
* the shared knowledge outcome carries no witness — i.e. on its undefined and relation arms; or
* a member of the extracted bundle escapes the bridge (`actionLedgerEscapeFinder` returns
  something). -/
theorem actionLedgerExtractor_eq_none_iff (basis) (O) :
    actionLedgerExtractor family hchar spendAuthVerify bindingVerify basis O = none ↔
      (family.adaptiveStatementKnowledgeExtractor hchar basis O = none ∨
        (actionLedgerEscapeFinder family hchar spendAuthVerify bindingVerify
          basis O).isSome) := by
  rw [ComputedAdaptiveActionStatementFSFamily.adaptiveStatementKnowledgeExtractor_eq_none_iff]
  have houtEq : actionLedgerOutcome family hchar spendAuthVerify bindingVerify basis O =
      (family.adaptiveStatementKnowledgeOutcome hchar basis O).map _ := rfl
  unfold actionLedgerExtractor actionLedgerEscapeFinder
  rw [houtEq]
  cases houtcome : family.adaptiveStatementKnowledgeOutcome hchar basis O with
  | none => simp
  | some outcome =>
      cases outcome with
      | inl witness =>
          cases hb : bundleLedgerData spendAuthVerify bindingVerify witness with
          | inl members =>
              refine iff_of_false (by simp [hb]) ?_
              rintro (hforall | hesc)
              · exact hforall witness rfl
              · simp [hb] at hesc
          | inr dlb => simp [hb]
      | inr relation => simp

end Extraction

end Zcash.Security.Ledger.ActionBundleBridge
