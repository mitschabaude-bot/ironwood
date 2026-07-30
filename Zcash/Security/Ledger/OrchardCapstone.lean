import Mathlib.Tactic
import Zcash.Security.Ledger.Capstone
import Zcash.Security.Ledger.KeyBindingDLR
import Zcash.Security.Ledger.NoteCommitDLR
import Zcash.Security.Ledger.MerkleDLR

/-!
# The Orchard instantiation: every Balance-subset arm computes a discrete-log relation

These are the instantiations that use the Orchard-protocol bases and parameters. At
them, each of the three Balance-subset break arms reduces to a nontrivial discrete-log
relation among the fixed Sinsemilla bases. Each reducer is a total, hypothesis-free
function from the arm's break to its relation, so it needs no random-oracle model.
`orchardBalanceSubsetOrRelation` runs all three: from a valid Orchard ledger it
computes either the Balance-subset containment or a nontrivial relation among the
fixed bases.

This is the deterministic core of the Orchard ε discharge. The probability that a
sampled ledger produces a relation is the discrete-log-relation advantage for the
fixed bases, under their pre-quantum hardness (their independence, spec Theorems 5.4.3
and 5.4.4). That is the same terminal as the Merkle and note-commitment arms, and the
key-binding arm reaches it here without the oracle model. Turning this deterministic
reduction into a bound on the capstone's named ε — composing it with
`balanceSubset_measure_le` over a `PMF` of Orchard ledgers — is not yet formalized.
-/

namespace Zcash.Security.Ledger.Bridge

open Zcash.Circuits
open Zcash.Security.Concrete
open Zcash.Security.Ledger.Pool
open Zcash.Security.Ledger.Model

variable {MSG SIG : Type*}
  (verify bverify : PallasGroup → MSG → SIG → Prop)
  (issuance : ℕ → ℕ) (maxActions : ℕ)

/-- The Orchard instantiation's sample space. -/
abbrev OrchardAnnotated :=
  ValidAnnotated (primitives (MSG := MSG) (SIG := SIG) verify bverify) keyBinding
    issuance maxActions

/-- The three Orchard Balance-subset relation targets: the key-binding and
note-commitment arms land in two-generator relations at their domain points, the
Merkle arm in a one-generator relation. -/
inductive OrchardBalanceRelation where
  | keyBinding (r : NontrivialRelation (F := Fq) pallasS ivkQpt commitIvkRpt)
  | noteCommit (r : NontrivialRelation (F := Fq) pallasS noteQpt noteCommitRpt)
  | merkle (r : NontrivialRelationOne (F := Fq) pallasS merkleQpt)

/-- **The Orchard Balance-subset reduction.** In a valid Orchard ledger, either the
nonzero spends of the first `i + 1` transactions are covered by the positioned outputs
of the first `i`, or the ledger's own data computes a nontrivial discrete-log relation
among the fixed Sinsemilla bases. Each Balance-subset break arm is routed through its
Orchard reducer, so a break in any arm becomes a nontrivial relation among the fixed
bases, with no random-oracle model. -/
def orchardBalanceSubsetOrRelation {ledger : Ledger _ Fq PallasGroup Fp Fp Fp Encoding MSG SIG _}
    (hval : ValidLedger (primitives (MSG := MSG) (SIG := SIG) verify bverify) keyBinding
      issuance maxActions ledger) (i : ℕ) :
    (nonZeroSpends ledger (i + 1) ≤ ↑(positionedOutputs ledger i))
      ⊕' OrchardBalanceRelation :=
  match balanceSubsetOrBreak hval i with
  | .inl hsub => .inl hsub
  | .inr (.keyBinding _ _ h) => .inr (.keyBinding (relationOfKeyBindingBreak h))
  | .inr (.noteCommit nb) => .inr (.noteCommit (relationOfNoteCommitBreak verify bverify nb))
  | .inr (.merkle c) => .inr (.merkle (relationOfMerkleCollision c.2))

end Zcash.Security.Ledger.Bridge
