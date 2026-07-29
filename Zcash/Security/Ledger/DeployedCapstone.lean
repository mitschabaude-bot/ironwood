import Mathlib
import Zcash.Security.Ledger.Capstone
import Zcash.Security.Ledger.KeyBindingDLR
import Zcash.Security.Ledger.NoteCommitDLR
import Zcash.Security.Ledger.MerkleDLR

/-!
# The deployed instantiation: every Balance-subset arm computes a discrete-log relation

At the deployed Orchard primitives, each of the three Balance-subset break arms reduces
to a nontrivial discrete-log relation among the fixed Sinsemilla bases. These are the
event-level reductions that discharge the capstone's three named ε hypotheses at the
deployed instantiation. Each takes a sample on which the reduction lands in one arm and
returns the arm's relation, so the arm's probability is the probability that the
composite produces a relation. Under the pre-quantum hardness of the deployed bases
(their independence, spec Theorems 5.4.3 and 5.4.4), that probability is the
discrete-log-relation advantage — the same terminal the Merkle and note-commitment arms
already share, with no random-oracle model.

Composing these with `balanceSubset_measure_le` replaces the three opaque arm ε's with
one discrete-log-relation assumption per domain point, and the key-binding arm no longer
needs the oracle model at the deployed instantiation.
-/

namespace Zcash.Security.Ledger.Bridge

open Zcash.Circuits
open Zcash.Security.Concrete
open Zcash.Security.Ledger.Pool
open Zcash.Security.Ledger.Model

variable {MSG SIG : Type*}
  (verify bverify : PallasGroup → MSG → SIG → Prop)
  (issuance : ℕ → ℕ) (maxActions : ℕ)

/-- The deployed instantiation's sample space. -/
abbrev DeployedAnnotated :=
  ValidAnnotated (primitives (MSG := MSG) (SIG := SIG) verify bverify) keyBinding
    issuance maxActions

/-- The three deployed Balance-subset relation targets: the key-binding and
note-commitment arms land in two-generator relations at their domain points, the
Merkle arm in a one-generator relation. -/
inductive DeployedBalanceRelation where
  | keyBinding (r : NontrivialRelation (F := Fq) pallasS ivkQpt commitIvkRpt)
  | noteCommit (r : NontrivialRelation (F := Fq) pallasS noteQpt noteCommitRpt)
  | merkle (r : NontrivialRelationOne (F := Fq) pallasS merkleQpt)

/-- **The deployed Balance-subset reduction.** In a valid deployed ledger, either the
nonzero spends of the first `i + 1` transactions are covered by the positioned outputs
of the first `i`, or the ledger's own data computes a nontrivial discrete-log relation
among the fixed Sinsemilla bases. Each Balance-subset break arm is routed through its
deployed reducer, so the three named ε hypotheses collapse to one discrete-log-relation
assumption per domain point, with no random-oracle model. -/
def deployedBalanceSubsetOrRelation {ledger : Ledger _ Fq PallasGroup Fp Fp Fp Encoding MSG SIG _}
    (hval : ValidLedger (primitives (MSG := MSG) (SIG := SIG) verify bverify) keyBinding
      issuance maxActions ledger) (i : ℕ) :
    (nonZeroSpends ledger (i + 1) ≤ ↑(positionedOutputs ledger i))
      ⊕' DeployedBalanceRelation :=
  match balanceSubsetOrBreak hval i with
  | .inl hsub => .inl hsub
  | .inr (.keyBinding _ _ h) => .inr (.keyBinding (relationOfKeyBindingBreak h))
  | .inr (.noteCommit nb) => .inr (.noteCommit (relationOfNoteCommitBreak verify bverify nb))
  | .inr (.merkle c) => .inr (.merkle (relationOfMerkleCollision c.2))

end Zcash.Security.Ledger.Bridge
