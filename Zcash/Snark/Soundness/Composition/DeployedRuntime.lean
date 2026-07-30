import Zcash.Snark.Soundness.Composition.DeployedAcceptance
import Zcash.Snark.Soundness.FiatShamir.WithReads

/-!
# Runtime helpers for deployed algebraic extraction

This module contains the challenge-read wrapper and deployed-acceptance bookkeeping shared by the
straight-line root containment.
-/

namespace Zcash.Snark

open Classical
open ComputedAlgebraicFSFamily

local instance vestaInhabitedDeployedRuntime : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

/-- A fiber bound for an arbitrary independent product. -/
theorem independentProductPMF_fiber_bound {A B : Type*} (p : PMF A) (q : PMF B)
    (S : A → Set B) {beta : ENNReal} (hS : ∀ a, q.toOuterMeasure (S a) ≤ beta) :
    (independentProductPMF p q).toOuterMeasure {x : A × B | x.2 ∈ S x.1} ≤ beta := by
  rw [independentProductPMF, PMF.toOuterMeasure_bind_apply]
  calc ∑' a, p a * (q.map (Prod.mk a)).toOuterMeasure {x : A × B | x.2 ∈ S x.1}
      = ∑' a, p a * q.toOuterMeasure (S a) := by
        refine tsum_congr fun a => ?_
        have hpre : (Prod.mk a) ⁻¹' {x : A × B | x.2 ∈ S x.1} = S a := by
          ext b
          simp only [Set.mem_preimage, Set.mem_setOf_eq]
        rw [PMF.toOuterMeasure_map_apply, hpre]
    _ ≤ ∑' a, p a * beta := ENNReal.tsum_le_tsum fun a => mul_le_mul_right (hS a) _
    _ = (∑' a, p a) * beta := by rw [ENNReal.tsum_mul_right]
    _ = beta := by rw [PMF.tsum_coe, one_mul]

/-- The algebraic adversary together with all eleven pre-IPA and `k` IPA-round oracle reads.
Irreducibility keeps dependent witness indices stable during equality elimination; proofs that need
the implementation unfold it explicitly. -/
@[irreducible] def wrappedAdversary (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) :
    OracleComp (BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis) ×
        (Fin (11 + shape.k) → Fp)) :=
  (family.adversary basis).withReads
    (fun p => Fin.append (algebraicFullPrefixesPre family.init p)
      (algebraicFullPrefixes family.init p))

/-- The challenge record encoded by a wrapped output. -/
def wrappedRecord {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs → Nat → VestaG}
    (pnu : AlgebraicWfProof basis vk instanceCommitment × (Fin (11 + shape.k) → Fp)) :
    Challenges shape.k Fp :=
  chRecord (fun i => pnu.2 (Fin.castAdd shape.k i))
    (fun j => pnu.2 (Fin.natAdd 11 j))

/-- The underlying proof produced on one oracle table. -/
def runProof (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    AlgebraicWfProof basis (family.vk basis) (family.instanceCommitment basis) :=
  (family.adversary basis).run O

/-- The eleven pre-IPA reads of one run. -/
def runReads (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    Fin 11 → Fp :=
  fun i => O (algebraicFullPrefixesPre family.init (runProof family basis O) i)

/-- The `k` IPA-round reads of one run. -/
def runRounds (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    Fin shape.k → Fp :=
  fun j => O (algebraicFullPrefixes family.init (runProof family basis O) j)

/-- The complete challenge record of one run. -/
def runRecord (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    Challenges shape.k Fp :=
  chRecord (runReads family basis O) (runRounds family basis O)

/-- Wrapping preserves the underlying adversary output. -/
theorem wrappedAdversary_run_fst (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    ((wrappedAdversary family basis).run O).1 = (family.adversary basis).run O := by
  simp only [wrappedAdversary, OracleComp.run_withReads]

/-- Wrapping adds one query per re-read squeeze point: eleven pre-IPA and `shape.k` IPA rounds.
Stated here so callers never unfold the irreducible wrapper. -/
theorem queryBound_wrappedAdversary (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) :
    (wrappedAdversary family basis).QueryBound (family.Q + (11 + shape.k)) := by
  rw [wrappedAdversary]
  exact OracleComp.queryBound_withReads _ (family.queryBound basis)

/-- The wrapped reads reconstruct the run's challenge record. -/
theorem wrappedRecord_run (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    wrappedRecord ((wrappedAdversary family basis).run O) = runRecord family basis O := by
  simp only [wrappedAdversary, OracleComp.run_withReads, wrappedRecord, runRecord]
  exact congrArg₂ chRecord
    (funext fun i => congrArg O (Fin.append_left _ _ i))
    (funext fun j => congrArg O (Fin.append_right _ _ j))

open ComputedAlgebraicFSFamily in
/-- Deployed acceptance at the Fiat-Shamir game is verifier acceptance at the run's record. -/
theorem deployedAccepts_of_fsWinsFull (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)
    (hwin : fsWinsFull (family.adversary basis)
      (fullAlgebraicAcceptDeployed basis (family.vk basis)
        (family.instanceCommitment basis))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) O) :
    DeployedAccepts (ursOfAugmentedBasis shape.k basis) rfl (family.vk basis)
      (family.instanceCommitment basis) (runProof family basis O).proof.1
      (runRecord family basis O) :=
  hwin

end Zcash.Snark
