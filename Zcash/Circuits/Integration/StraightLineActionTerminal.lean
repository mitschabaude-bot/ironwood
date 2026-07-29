import Zcash.Circuits.Integration.ActionTerminal
import Zcash.Snark.Soundness.AGM.DecodeToOpened
import Zcash.Snark.Soundness.Composition.StraightLineDecodeSupply

/-!
# The rewind-free decode at the Action terminal

`ActionTerminal` concludes the concrete Action bundle statement from the historical opened-batch
interface: an `OpenedBatchOpenings`, a per-set `OpenedMemberDecode`, deployed acceptance, the
canonical quotient, and the member-binding premise.  That interface was written for the rewinding
route.

`AGM.DecodeToOpened` presents a rewind-free `DeployedAlgebraicDecode` in exactly that shape, so the
straight-line route reaches the same terminal from one accepting execution.  This module ties the
two together: a decoding run supplies its own decode and acceptance, both at the run's complete
challenge record, and what remains are the challenge exclusions — `hxgood`, `hgoodY`, and the
permutation and lookup exclusions — which `StraightLineActionEvent` prices, not this module.

The rewind-based route to the same conclusion is `Soundness.ActionVesta` (generic) and
`Soundness.Deployed.ActionVesta` (at the captured artifacts), which take an `OpenedBatchOpenings`
supplied by `x₄` rewinding and pay accept-measure premises for it.  Neither supersedes the other:
that route assumes rewinds and measures, this one assumes a represented decode.

The terminal is used unchanged.  Nothing in this module weakens its statement: the verifying key
is still `actionCircuit.toVerifierKey`, and no free semantic proposition, `hencodes`, or decoded
column feed is reintroduced.
-/

namespace Zcash.Snark

namespace ActionTerminal

open Halo2 Polynomial Keygen
open Zcash.Circuits
open Zcash.Circuits.Action
open Zcash.Arithmetic (scalarFieldOrder)

variable {G : Type} [AddCommGroup G] [Module Fp G] [DecidableEq G] [Inhabited G]

local instance vestaInhabitedStraightLineActionTerminal : Inhabited VestaG := ⟨0⟩

/-- **The Action bundle statement from a rewind-free decode.**  The decode supplies the batch
openings, the member decodes, the `x₄` designation and the member-binding premise; the caller
supplies acceptance and the challenge exclusions.

The member-binding premise never takes its relation branch here: a decode already carries the
value equations, so `memberBinding` lands on the left for every slot and point. -/
noncomputable def action_bundleStatement_or_relation_of_decode
    (pp : ProofParams) (urs : URS G)
    (hk : (pp.mergeDerived actionCircuit).k = urs.k)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (ps : ProofString (pp.mergeDerived actionCircuit) Fp G)
    (ch : Challenges (pp.mergeDerived actionCircuit).k Fp)
    (pU pW : Fp) (a : Fin (2 ^ urs.k) → Fp)
    (decode : DeployedAlgebraicDecode urs hk
      (actionCircuit.toVerifierKey pp urs)
      (actionCircuit.instanceCommitment pp urs inputs) ps ch a pU pW)
    (hchar : deployedX4PairCount
      (actionCircuit.toVerifierKey pp urs)
      (actionCircuit.instanceCommitment pp urs inputs) ps ch < scalarFieldOrder)
    (haccepts :
      DeployedAccepts urs hk
        (actionCircuit.toVerifierKey pp urs)
        (actionCircuit.instanceCommitment pp urs inputs) ps ch) :=
  action_bundleStatement_or_relation_of_decodedMemberPolynomial_eq
    pp urs hk inputs ps ch pU pW a
    (decode.toOpenedBatch hchar)
    (fun i hi => decode.toMemberDecode hchar i hi)
    haccepts _ rfl
    (fun slot point hpoint => PSum.inl (decode.memberBinding hchar slot point hpoint))

/-- The run's decode at the Action circuit's artifacts: extracted from the event, re-rounded to
the run's complete challenge record, and transported along the key and instance identifications. -/
noncomputable def actionRunDecode
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (pp.mergeDerived actionCircuit))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (hvk : family.vk basis =
      actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
    (hI : family.instanceCommitment basis =
      actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
    (hdecoded : family.straightLineConstraintDecoded static basis O) :
    DeployedAlgebraicDecode
      (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) rfl
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O)
      ((straightLineRunOutput family basis O).1.aMulti
        (wrappedPreIpaReads (straightLineRunOutput family basis O)))
      ((straightLineRunOutput family basis O).1.multiU
        (wrappedPreIpaReads (straightLineRunOutput family basis O)))
      ((straightLineRunOutput family basis O).1.multiBlind
        (wrappedPreIpaReads (straightLineRunOutput family basis O))) :=
  hI ▸ hvk ▸ (straightLineDecode family static basis O hdecoded).reRound
    (runRounds family.toFamily basis O)

/-- The run's acceptance at the Action circuit's artifacts. -/
theorem actionRunAccepts
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (pp.mergeDerived actionCircuit))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (hvk : family.vk basis =
      actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
    (hI : family.instanceCommitment basis =
      actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
    (hdecoded : family.straightLineConstraintDecoded static basis O) :
    DeployedAccepts (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) rfl
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) :=
  hI ▸ hvk ▸ straightLineAccepts_of_decoded family static basis O hdecoded

/-- **The Action terminal reached from the straight-line constraint event.**  A family at the
Action shape supplies the decode and the acceptance from its own accepting run, so the terminal
is reached without a rewind.

`hvk` and `hI` identify the family's verifying key and instance commitment with the Action
circuit's, and the run data is transported along them.  Everything is stated at the run's
complete challenge record — acceptance reads the IPA rounds, so the root layer's zero-round
record cannot carry it.  The challenge exclusions are still open, exactly as in
`action_bundleStatement_or_relation_of_decode`. -/
noncomputable def action_bundleStatement_or_relation_of_straightLineDecoded
    (pp : ProofParams)
    (family : ComputedStraightLineDeployedFSFamily (pp.mergeDerived actionCircuit))
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ (pp.mergeDerived actionCircuit).k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen (pp.mergeDerived actionCircuit) family.init.length 10
        + 3 * (pp.mergeDerived actionCircuit).k) → Fp)
    (inputs : Fin (pp.mergeDerived actionCircuit).numProofs → PublicInputs Fp)
    (hvk : family.vk basis =
      actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
    (hI : family.instanceCommitment basis =
      actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
    (hdecoded : family.straightLineConstraintDecoded static basis O)
    (hchar : deployedX4PairCount
      (actionCircuit.toVerifierKey pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis))
      (actionCircuit.instanceCommitment pp
        (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) inputs)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) < scalarFieldOrder) :=
  action_bundleStatement_or_relation_of_decode pp
    (ursOfAugmentedBasis (pp.mergeDerived actionCircuit).k basis) rfl inputs
    (straightLineRunOutput family basis O).1.proof.1
    (straightLineRunRecord family basis O)
    ((straightLineRunOutput family basis O).1.multiU
      (wrappedPreIpaReads (straightLineRunOutput family basis O)))
    ((straightLineRunOutput family basis O).1.multiBlind
      (wrappedPreIpaReads (straightLineRunOutput family basis O)))
    ((straightLineRunOutput family basis O).1.aMulti
      (wrappedPreIpaReads (straightLineRunOutput family basis O)))
    (actionRunDecode pp family static basis O inputs hvk hI hdecoded)
    hchar
    (actionRunAccepts pp family static basis O inputs hvk hI hdecoded)

end ActionTerminal

end Zcash.Snark
