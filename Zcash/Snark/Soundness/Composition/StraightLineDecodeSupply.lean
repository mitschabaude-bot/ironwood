import Zcash.Snark.Soundness.Composition.StraightLineConstraint

/-!
# The algebraic decode behind the straight-line constraint event

`straightLineConstraintDecoded` is proposition-only: it says the root decode succeeded and yielded
a constraint witness, but hands out no data.  The Action terminal needs the data — a
`DeployedAlgebraicDecode` at the run's own artifacts.

`straightLineConstraintDecoded_nonempty_decode` recovers the decode as a `Nonempty`, and
`straightLineDecode` picks one.  The decode is pinned by `family.outcome`, so the choice cannot
invent different AGM coordinates — `DeployedRootDecodeWitness.unique`.

The artifacts are the run's, not the Action circuit's.  Identifying the two is the caller's job;
`ActionTerminal.action_bundleStatement_or_relation_of_straightLineDecoded` does it with the keygen
certificate equalities.
-/

namespace Zcash.Snark

open Classical
open ComputedStraightLineDeployedFSFamily (straightLineDummyTape)

local instance vestaInhabitedStraightLineDecodeSupply : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

/-- Re-round a decode.  No decode field reads the record's IPA rounds, so a decode at one round
vector is a decode at any other; every field transports by `rfl`.  Deployed acceptance is *not*
round-blind — the final IPA equation reads `ch.ipaRound` — which is why the root layer's
zero-round record and an accepting run's true record need this bridge at all. -/
def DeployedAlgebraicDecode.reRound {G : Type*} [AddCommGroup G] [Module Fp G]
    [DecidableEq G] [Inhabited G]
    {urs : URS G} {hk : shape.k = urs.k} {vk : VerifyingKey shape Fp G}
    {ic : Fin shape.numProofs → Nat → G} {ps : ProofString shape Fp G}
    {nu : Fin 11 → Fp} {r₁ : Fin shape.k → Fp}
    {a : Fin (2 ^ urs.k) → Fp} {aU aW : Fp}
    (d : DeployedAlgebraicDecode urs hk vk ic ps (chRecord nu r₁) a aU aW)
    (r₂ : Fin shape.k → Fp) :
    DeployedAlgebraicDecode urs hk vk ic ps (chRecord nu r₂) a aU aW where
  batches := ⟨d.batches.x4, d.batches.x1⟩
  x4Values := d.x4Values
  memberValues := d.memberValues

/-- The one-run wrapped output: the straight-line event's run at `basis` and the oracle table `O`.
The dummy tape is the fixed index the root-decode witness type is reused at. -/
noncomputable abbrev straightLineRunOutput
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) :=
  deployedRootRunOutput family.toRootFamily basis (O, straightLineDummyTape)

/-- The run's own algebraic decode exists whenever the straight-line constraint event decodes.

Stepped through in the body: the event's nested existentials carry a `DeployedRootDecodeWitness`,
whose `decoded` field is the decode. -/
theorem straightLineConstraintDecoded_nonempty_decode
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (h : family.straightLineConstraintDecoded static basis O) :
    Nonempty (DeployedAlgebraicDecode (ursOfAugmentedBasis shape.k basis) rfl
      (family.vk basis) (family.instanceCommitment basis)
      (deployedRootRunOutput family.toRootFamily basis (O, straightLineDummyTape)).1.proof.1
      (wrappedPreIpaRecord
        (deployedRootRunOutput family.toRootFamily basis (O, straightLineDummyTape)))
      ((deployedRootRunOutput family.toRootFamily basis (O, straightLineDummyTape)).1.aMulti
        (wrappedPreIpaReads
          (deployedRootRunOutput family.toRootFamily basis (O, straightLineDummyTape))))
      ((deployedRootRunOutput family.toRootFamily basis (O, straightLineDummyTape)).1.multiU
        (wrappedPreIpaReads
          (deployedRootRunOutput family.toRootFamily basis (O, straightLineDummyTape))))
      ((deployedRootRunOutput family.toRootFamily basis (O, straightLineDummyTape)).1.multiBlind
        (wrappedPreIpaReads
          (deployedRootRunOutput family.toRootFamily basis (O, straightLineDummyTape))))) := by
  -- The event is `deployedConstraintDecodedOfRoot` at the one-run coins: acceptance, a root
  -- decode witness, the pre-`x` exclusion, and the constraint witness it produces.
  obtain ⟨_haccept, root, _hxgood, _witness, _hw⟩ := h
  exact ⟨root.decoded⟩

/-- The decode picked out of the straight-line constraint event. -/
noncomputable def straightLineDecode
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (h : family.straightLineConstraintDecoded static basis O) :=
  Classical.choice (straightLineConstraintDecoded_nonempty_decode family static basis O h)

/-- The run's complete challenge record: the squeezed pre-IPA reads and the true IPA rounds.
The root layer's `wrappedPreIpaRecord` zeroes the rounds; acceptance holds at this record. -/
noncomputable abbrev straightLineRunRecord
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) :
    Challenges shape.k Fp :=
  chRecord (wrappedPreIpaReads (straightLineRunOutput family basis O))
    (runRounds family.toFamily basis O)

/-- The run's pre-IPA reads are the oracle's answers at the squeeze prefixes.  This is what lets
a per-challenge event embed into the index-generic squeeze surface. -/
theorem straightLineRunReads_eq
    (family : ComputedStraightLineDeployedFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) :
    wrappedPreIpaReads (straightLineRunOutput family basis O) =
      fun i => O (algebraicFullPrefixesPre family.init
        ((family.adversary basis).run O) i) := by
  simpa [runReads, runProof] using wrappedPreIpaReads_run family.toFamily basis O

/-- A decoding run is an accepting run: the event's own acceptance component, restated at the
run's proof string and complete challenge record. -/
theorem straightLineAccepts_of_decoded
    (family : ComputedStraightLineDeployedFSFamily shape)
    (static : DeployedConstraintStaticChecks family.toRootFamily)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)
    (h : family.straightLineConstraintDecoded static basis O) :
    DeployedAccepts (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
      (family.instanceCommitment basis)
      (straightLineRunOutput family basis O).1.proof.1
      (straightLineRunRecord family basis O) := by
  obtain ⟨haccept, -⟩ := h
  have hdeployed := deployedAccepts_of_fsWinsFull family.toFamily basis O haccept
  simpa [straightLineRunOutput, straightLineRunRecord, deployedRootRunOutput,
    wrappedAdversary_run_fst, wrappedPreIpaReads_run] using hdeployed

end Zcash.Snark
