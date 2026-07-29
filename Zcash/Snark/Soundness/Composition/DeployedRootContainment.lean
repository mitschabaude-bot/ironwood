import Zcash.Snark.Soundness.AGM.DeployedPinnedRoots
import Zcash.Snark.Soundness.Composition.DeployedRuntime

/-!
# The retained deployed AGM root decode

`DeployedRootDecodeWitness` is the data a successful deployed root decode keeps: the batch witness
together with its equality to the decoded batches, so the constraint layer can reuse the run's own
online AGM coordinates rather than choose a fresh existential decode.  `deployedRootDecoded` is the
proposition that such a witness exists.
-/

namespace Zcash.Snark

open Classical
open ComputedAlgebraicFSFamily
open ComputedDeployedRootFSFamily
open scoped ENNReal

local instance vestaInhabitedDeployedRootContainment : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

/-- The wrapped online output for one sampled basis and random-oracle table. -/
abbrev deployedRootRunOutput (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (coins : family.toFamily.Coins) :=
  (wrappedAdversary family.toFamily basis).run coins

/-- Data retained by a successful deployed root decode.  Keeping the batch witness and its
equality to the decoded batches is what lets the constraint layer reuse the exact online AGM
coordinates instead of choosing a fresh existential decode. -/
structure DeployedRootDecodeWitness (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (coins : family.toFamily.Coins) where
  batchWitness : DeployedBatchWitness family.toFamily basis
    (deployedRootRunOutput family basis coins)
  outcome_eq : family.outcome basis coins = PSum.inl batchWitness
  decoded : DeployedAlgebraicDecode (ursOfAugmentedBasis shape.k basis) rfl
    (family.vk basis) (family.instanceCommitment basis)
    (deployedRootRunOutput family basis coins).1.proof.1
    (wrappedPreIpaRecord (deployedRootRunOutput family basis coins))
    ((deployedRootRunOutput family basis coins).1.aMulti
      (wrappedPreIpaReads (deployedRootRunOutput family basis coins)))
    ((deployedRootRunOutput family basis coins).1.multiU
      (wrappedPreIpaReads (deployedRootRunOutput family basis coins)))
    ((deployedRootRunOutput family basis coins).1.multiBlind
      (wrappedPreIpaReads (deployedRootRunOutput family basis coins)))
  batches_eq : decoded.batches = batchWitness.batches

/-- Retained root-decode provenance is unique.  Its batch data is pinned by `family.outcome`; the
remaining decode fields are proofs about those same batches.  Thus the later proof-only use of
`Classical.choice` cannot choose different relation coefficients. -/
theorem DeployedRootDecodeWitness.unique
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (coins : family.toFamily.Coins)
    (a b : DeployedRootDecodeWitness family basis coins) : a = b := by
  have hw : a.batchWitness = b.batchWitness := by
    exact PSum.inl.inj (a.outcome_eq.symm.trans b.outcome_eq)
  cases a with
  | mk aBatch aOutcome aDecoded aBatchesEq =>
      cases b with
      | mk bBatch bOutcome bDecoded bBatchesEq =>
          dsimp only at hw
          subst bBatch
          have hd : aDecoded = bDecoded := by
            cases aDecoded with
            | mk aBatches aX4 aMembers =>
                cases bDecoded with
                | mk bBatches bX4 bMembers =>
                    have hbatches : aBatches = bBatches :=
                      aBatchesEq.trans bBatchesEq.symm
                    cases hbatches
                    rfl
          subst bDecoded
          rfl

instance deployedRootDecodeWitnessSubsingleton
    (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG) (coins : family.toFamily.Coins) :
    Subsingleton (DeployedRootDecodeWitness family basis coins) :=
  ⟨DeployedRootDecodeWitness.unique family basis coins⟩

/-- All deployed member-polynomial values decoded from the AGM coordinates at the run's own
record. -/
def deployedRootDecoded (family : ComputedDeployedRootFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (coins : family.toFamily.Coins) : Prop :=
  Nonempty (DeployedRootDecodeWitness family basis coins)

end Zcash.Snark
