import Zcash.Snark.Soundness.Vesta
import Zcash.Snark.Soundness.AGM.ProbabilityVesta
import Zcash.Snark.Soundness.AGM.ProbabilityCoins
import Zcash.Snark.Soundness.Forking.Adversary.PreIpa
import Zcash.Snark.Soundness.Forking.Adversary.Recursive

/-!
# Fiat–Shamir to AGM handoff

This module connects the bounded-query Fiat–Shamir adversary to the AGM data consumed by the
reduction.

## Proof route

1. `AlgebraicWfProof` carries the multiopen, `S`, and IPA-round representations.
2. The recursive extractor computes and validates an `AlgebraicDForkCert`.
3. `DeployedAlgebraicForkingInstance.runRelation` computes a relation from either kernel output.
4. The probability theorem charges query loss, the `z = 0` slice, and the fixed-slot DL loss.

## Binding event

A binding attack is verifier acceptance with a value mismatch against the carried aggregate
opening. It is not nonexistence of an opening, which would be nearly vacuous in a prime-order group
(see `Zcash.Security.BindingSignature.Balance`). A clean extracted opening on a mismatch run gives
a commitment collision; the other kernel branch already gives a relation.
-/

namespace Zcash.Snark

open scoped ENNReal

local instance : Inhabited VestaG := ⟨0⟩

/-! ## Minimal deployed transcript interface -/

/-- A deployed proof string together with the reader's shape checks. -/
def WfProof (shape : Shape) : Type _ := {ps' : ProofString shape Fp VestaG // PsWellFormed ps'}

/-- The proof's eleven pre-IPA squeeze points, embedded in the bounded oracle domain. -/
def fullPrefixesPre {shape : Shape} (init : List (TranscriptElt Fp VestaG)) (p : WfProof shape) :
    Fin 11 → BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) :=
  fun i => ⟨preIpaSqueezePoints init p.1 i, by
    have h := (preIpaSqueezePoints_length_le init p.1 i).trans
      (le_of_eq (preIpaTranscript_length_eq init p.1 p.2))
    omega⟩

/-- The proof's IPA round transcripts, embedded in the bounded oracle domain. -/
def fullPrefixes {shape : Shape} (init : List (TranscriptElt Fp VestaG)) (p : WfProof shape) :
    Fin shape.k → BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) :=
  fun j => ⟨roundTranscriptFin (preIpaTranscript init p.1) p.1.ipaRounds j, by
    rw [roundTranscriptFin_length, preIpaTranscript_length_eq init p.1 p.2]
    have := j.isLt
    omega⟩

/-- Read the two round points from the final absorb block before a challenge squeeze. -/
def grindDecode [Inhabited VestaG] {L : ℕ} (t : BTranscript Fp VestaG L) : VestaG × VestaG :=
  ((match t.val[t.val.length - 3]? with | some (.point g) => g | _ => default),
   (match t.val[t.val.length - 2]? with | some (.point g) => g | _ => default))

/-- Decoding a deployed round transcript returns that round's two points. -/
theorem grindDecode_round {L : ℕ} [Inhabited VestaG] {shape : Shape}
    (t₀ : List (TranscriptElt Fp VestaG)) (R : Fin shape.k → VestaG × VestaG) (j : Fin shape.k)
    (hb : (roundTranscriptFin t₀ R j).length ≤ L) :
    grindDecode (⟨roundTranscriptFin t₀ R j, hb⟩ : BTranscript Fp VestaG L) = R j := by
  have hlen : (roundTranscriptFin t₀ R j).length = t₀.length + 3 * (j.val + 1) :=
    roundTranscriptFin_length t₀ R j
  show ((match (roundTranscriptFin t₀ R j)[(roundTranscriptFin t₀ R j).length - 3]? with
      | some (.point g) => g | _ => default),
    (match (roundTranscriptFin t₀ R j)[(roundTranscriptFin t₀ R j).length - 2]? with
      | some (.point g) => g | _ => default)) = R j
  rw [show (roundTranscriptFin t₀ R j).length - 3 = t₀.length + 3 * j.val from by omega,
    show (roundTranscriptFin t₀ R j).length - 2 = t₀.length + 3 * j.val + 1 from by omega,
    roundTranscriptFin_getElem?_fst, roundTranscriptFin_getElem?_snd]

/-- Multiopen values do not depend on the IPA round challenges. -/
theorem multiopenValue_ipaRound [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (vk : VerifyingKey shape Fp VestaG)
    (ps : ProofString shape Fp VestaG) (c : Challenges shape.k Fp) (χ : Fin shape.k → Fp) :
    multiopenValue vk ps {c with ipaRound := χ} = multiopenValue vk ps c := rfl

/-- Replacing the IPA proof suffix does not change the multiopen value. -/
theorem multiopenValue_spliceIpa [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (vk : VerifyingKey shape Fp VestaG)
    (ps : ProofString shape Fp VestaG) (R : Fin shape.k → VestaG × VestaG) (cc ff : Fp)
    (c : Challenges shape.k Fp) :
    multiopenValue vk (spliceIpa ps R cc ff) c = multiopenValue vk ps c := rfl

/-- Multiopen commitments do not depend on the IPA round challenges. -/
theorem multiopenCommitment_ipaRound [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (g : Fin (2 ^ shape.k) → VestaG)
    (w u : VestaG) (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG)
    (c : Challenges shape.k Fp) (χ : Fin shape.k → Fp) :
    multiopenCommitment g w u vk ps {c with ipaRound := χ}
      = multiopenCommitment g w u vk ps c := rfl

/-- Replacing the IPA proof suffix does not change the multiopen commitment. -/
theorem multiopenCommitment_spliceIpa [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (g : Fin (2 ^ shape.k) → VestaG)
    (w u : VestaG) (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG)
    (R : Fin shape.k → VestaG × VestaG) (cc ff : Fp) (c : Challenges shape.k Fp) :
    multiopenCommitment g w u vk (spliceIpa ps R cc ff) c
      = multiopenCommitment g w u vk ps c := rfl

/-- Every pre-IPA squeeze position is no later than the final one. -/
private theorem preIpaLen_le_last (shape : Shape) (n₀ : ℕ) (i : Fin 11) :
    preIpaLen shape n₀ i ≤ preIpaLen shape n₀ 10 := by
  fin_cases i <;> simp [preIpaLen] <;> omega

attribute [local irreducible] preIpaTranscript preIpaLen

/-- Decode the deployed pre-IPA chain and IPA round chain from an adaptive proof output. -/
def fullDecodeDeployed [Inhabited VestaG] (shape : Shape)
    (init : List (TranscriptElt Fp VestaG)) :
    FullDecode (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) 11 shape.k
      (fullPrefixesPre init) (fullPrefixes init) :=
  { roundOf := fun t => (t.val.length - preIpaLen shape init.length 10) / 3 - 1
    chainAt := fun t i =>
      ⟨t.val.take (preIpaLen shape init.length 10 + 3 * (i.val + 1)), by
        rw [List.length_take]
        exact le_trans (min_le_right _ _) t.prop⟩
    roundOf_prefixes := by
      intro p j
      show (((roundTranscriptFin (preIpaTranscript init p.1) p.1.ipaRounds j).length
          - preIpaLen shape init.length 10)) / 3 - 1 = j.val
      rw [roundTranscriptFin_length, preIpaTranscript_length_eq init p.1 p.2]
      omega
    chainAt_prefixes := by
      intro p j i hij
      apply Subtype.ext
      show (roundTranscriptFin (preIpaTranscript init p.1) p.1.ipaRounds j).take
          (preIpaLen shape init.length 10 + 3 * (i.val + 1))
          = roundTranscriptFin (preIpaTranscript init p.1) p.1.ipaRounds i
      rw [← preIpaTranscript_length_eq init p.1 p.2]
      exact roundTranscriptFin_take (preIpaTranscript init p.1) p.1.ipaRounds hij
    chainAt_ne := by
      intro t i hi hEq
      have hi' : i.val < (t.val.length - preIpaLen shape init.length 10) / 3 - 1 := hi
      have hlen : (t.val.take (preIpaLen shape init.length 10 + 3 * (i.val + 1))).length
          = t.val.length :=
        congrArg (fun x : BTranscript Fp VestaG
          (preIpaLen shape init.length 10 + 3 * shape.k) => x.val.length) hEq
      rw [List.length_take] at hlen
      omega
    chainPre := fun t i =>
      ⟨t.val.take (preIpaLen shape init.length i), by
        rw [List.length_take]
        exact le_trans (min_le_right _ _) t.prop⟩
    guard := fun t => preIpaLen shape init.length 10 < t.val.length
    guard_prefixes := by
      intro p j
      show preIpaLen shape init.length 10
          < (roundTranscriptFin (preIpaTranscript init p.1) p.1.ipaRounds j).length
      rw [roundTranscriptFin_length, preIpaTranscript_length_eq init p.1 p.2]
      omega
    chainPre_prefixes := by
      intro p j i
      apply Subtype.ext
      show (roundTranscriptFin (preIpaTranscript init p.1) p.1.ipaRounds j).take
          (preIpaLen shape init.length i) = preIpaSqueezePoints init p.1 i
      have hpre : preIpaSqueezePoints init p.1 i
          <+: roundTranscriptFin (preIpaTranscript init p.1) p.1.ipaRounds j :=
        (preIpaSqueezePoints_prefix init p.1 i).trans
          (by rw [roundTranscriptFin]; exact List.prefix_append _ _)
      have h := List.prefix_iff_eq_take.mp hpre
      rw [preIpaSqueezePoints_length_eq init p.1 p.2] at h
      exact h.symm
    chainPre_ne := by
      intro t hg i hEq
      have hlen : (t.val.take (preIpaLen shape init.length i)).length = t.val.length :=
        congrArg (fun x : BTranscript Fp VestaG
          (preIpaLen shape init.length 10 + 3 * shape.k) => x.val.length) hEq
      rw [List.length_take] at hlen
      have := preIpaLen_le_last shape init.length i
      have hg' : preIpaLen shape init.length 10 < t.val.length := hg
      omega }

/-! ## Algebraic output of the fully adaptive deployed adversary -/

/-- A proof string in which every prover-emitted group element carries its AGM representation. -/
abbrev AlgebraicProofString (shape : Shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) :=
  ProofString shape Fp (AlgebraicPoint (F := Fp) basis)

namespace AlgebraicProofString

/-- Erase every group representation to obtain the deployed proof string. -/
def erase {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (ps : AlgebraicProofString shape basis) : ProofString shape Fp VestaG :=
  { adviceCommitments := fun p i => (ps.adviceCommitments p i).point
    lookupPermutedInput := fun p i => (ps.lookupPermutedInput p i).point
    lookupPermutedTable := fun p i => (ps.lookupPermutedTable p i).point
    permutationProduct := fun p i => (ps.permutationProduct p i).point
    lookupProduct := fun p i => (ps.lookupProduct p i).point
    vanishingRandom := ps.vanishingRandom.point
    hPieces := fun i => (ps.hPieces i).point
    instanceEvals := ps.instanceEvals
    adviceEvals := ps.adviceEvals
    fixedEvals := ps.fixedEvals
    vanishingRandomEval := ps.vanishingRandomEval
    permutationCommonEvals := ps.permutationCommonEvals
    permutationSetEvals := ps.permutationSetEvals
    lookupEvals := ps.lookupEvals
    multiopenQPrime := ps.multiopenQPrime.point
    multiopenU := ps.multiopenU
    ipaS := ps.ipaS.point
    ipaRounds := fun j => ((ps.ipaRounds j).1.point, (ps.ipaRounds j).2.point)
    ipaC := ps.ipaC
    ipaF := ps.ipaF }

end AlgebraicProofString

/-- The algebraic proof and its aggregate `(g,U,W)` coordinates after transcript assembly.
`AlgebraicProofString` represents each emitted point; `aMulti` and `s` aggregate those coordinates.
Honest proofs have `multiU = sU = 0`. -/
structure AlgebraicWfProof {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) where
  algebraicProof : AlgebraicProofString shape basis
  wellFormed : PsWellFormed algebraicProof.erase
  aMulti : (Fin 11 → Fp) → Fin (2 ^ shape.k) → Fp
  multiU : (Fin 11 → Fp) → Fp
  multiBlind : (Fin 11 → Fp) → Fp
  multiopen_repr : ∀ ν,
    commit (ursOfAugmentedBasis shape.k basis) (aMulti ν) +
        multiU ν • (ursOfAugmentedBasis shape.k basis).u +
        multiBlind ν • (ursOfAugmentedBasis shape.k basis).w =
      multiopenCommitment (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).w (ursOfAugmentedBasis shape.k basis).u
        vk algebraicProof.erase (chRecord ν (fun _ => 0))
  s : Fin (2 ^ shape.k) → Fp
  sU : Fp
  sBlind : Fp
  ipaS_repr : commit (ursOfAugmentedBasis shape.k basis) s +
      sU • (ursOfAugmentedBasis shape.k basis).u +
      sBlind • (ursOfAugmentedBasis shape.k basis).w = algebraicProof.ipaS.point

namespace AlgebraicWfProof

/-- The ordinary well-formed proof used by the deployed transcript schedule. -/
def proof {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG} (p : AlgebraicWfProof basis vk) : WfProof shape :=
  ⟨p.algebraicProof.erase, p.wellFormed⟩

/-- Representation-carrying IPA round points. -/
def rounds {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG} (p : AlgebraicWfProof basis vk) (j : Fin shape.k) :
    AlgebraicPoint (F := Fp) basis × AlgebraicPoint (F := Fp) basis :=
  p.algebraicProof.ipaRounds j

end AlgebraicWfProof

/-- Precompose a fully adaptive decode with an erasure map on adversary outputs. -/
def FullDecode.precomp {T P P' : Type*} {m k : ℕ}
    {prefixesPre : P → Fin m → T} {prefixes : P → Fin k → T}
    (D : FullDecode T m k prefixesPre prefixes) (erase : P' → P) :
    FullDecode T m k (fun p => prefixesPre (erase p)) (fun p => prefixes (erase p)) :=
  { roundOf := D.roundOf
    chainAt := D.chainAt
    roundOf_prefixes := fun p j => D.roundOf_prefixes (erase p) j
    chainAt_prefixes := fun p j i h => D.chainAt_prefixes (erase p) j i h
    chainAt_ne := D.chainAt_ne
    chainPre := D.chainPre
    guard := D.guard
    guard_prefixes := fun p j => D.guard_prefixes (erase p) j
    chainPre_prefixes := fun p j i => D.chainPre_prefixes (erase p) j i
    chainPre_ne := D.chainPre_ne }

/-- The algebraic output's pre-IPA squeeze points. -/
def algebraicFullPrefixesPre {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG} (init : List (TranscriptElt Fp VestaG))
    (p : AlgebraicWfProof basis vk) :=
  fullPrefixesPre init p.proof

/-- The algebraic output's IPA round squeeze points. -/
def algebraicFullPrefixes {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG} (init : List (TranscriptElt Fp VestaG))
    (p : AlgebraicWfProof basis vk) :=
  fullPrefixes init p.proof

/-- Equality of one deployed IPA squeeze point fixes the complete pre-IPA transcript. -/
theorem preIpaTranscript_eq_of_fullPrefix_eq {shape : Shape}
    (init : List (TranscriptElt Fp VestaG)) (p q : WfProof shape) (j : Fin shape.k)
    (h : fullPrefixes init p j = fullPrefixes init q j) :
    preIpaTranscript init p.1 = preIpaTranscript init q.1 := by
  have hval := congrArg Subtype.val h
  change roundTranscriptFin (preIpaTranscript init p.1) p.1.ipaRounds j =
    roundTranscriptFin (preIpaTranscript init q.1) q.1.ipaRounds j at hval
  have hp := preIpaTranscript_length_eq init p.1 p.2
  have hq := preIpaTranscript_length_eq init q.1 q.2
  rw [roundTranscriptFin, roundTranscriptFin] at hval
  calc
    preIpaTranscript init p.1 =
        (preIpaTranscript init p.1 ++
          (((List.finRange shape.k).take (j.val + 1)).map (fun i =>
            [TranscriptElt.point (p.1.ipaRounds i).1,
              TranscriptElt.point (p.1.ipaRounds i).2,
              TranscriptElt.challenge])).flatten).take (preIpaLen shape init.length 10) := by
          rw [← hp, List.take_append_of_le_length (le_refl _)]
          simp
    _ = (preIpaTranscript init q.1 ++
          (((List.finRange shape.k).take (j.val + 1)).map (fun i =>
            [TranscriptElt.point (q.1.ipaRounds i).1,
              TranscriptElt.point (q.1.ipaRounds i).2,
              TranscriptElt.challenge])).flatten).take (preIpaLen shape init.length 10) :=
        congrArg (List.take (preIpaLen shape init.length 10)) hval
    _ = preIpaTranscript init q.1 := by
          rw [← hq, List.take_append_of_le_length (le_refl _)]
          simp

/-- The deployed binding attack: verifier acceptance while the accepted value, including the
declared `U` shift, differs from the value of `aMulti`. See the module's binding-event note. -/
def fullAlgebraicBindingAttack {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (p : AlgebraicWfProof basis vk)
    (ν : Fin 11 → Fp) (χ : Fin shape.k → Fp) : Prop :=
  DeployedIpaVerifierEq (ursOfAugmentedBasis shape.k basis).g
      (ursOfAugmentedBasis shape.k basis).w (ursOfAugmentedBasis shape.k basis).u
      vk p.proof.1 (chRecord ν χ) ∧
    innerProduct (p.aMulti ν) (evalVector shape.k (ν 7)) ≠
      multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0)) +
        (ν 10)⁻¹ * (p.multiU ν + ν 9 * p.sU) -
        ν 9 * innerProduct p.s (evalVector shape.k (ν 7))

/-- The binding attack with the `z ≠ 0` guard required by the fork kernel. -/
def fullAlgebraicBindingAttackZ {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (p : AlgebraicWfProof basis vk)
    (ν : Fin 11 → Fp) (χ : Fin shape.k → Fp) : Prop :=
  fullAlgebraicBindingAttack basis vk p ν χ ∧ ν 10 ≠ 0

/-- Verifier acceptance with the nonzero folding challenge required by the IPA extractor. The
binding mismatch is checked only when converting the extracted instance to a relation. -/
def fullAlgebraicAcceptZ {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (p : AlgebraicWfProof basis vk)
    (ν : Fin 11 → Fp) (χ : Fin shape.k → Fp) : Prop :=
  DeployedIpaVerifierEq (ursOfAugmentedBasis shape.k basis).g
      (ursOfAugmentedBasis shape.k basis).w (ursOfAugmentedBasis shape.k basis).u
      vk p.proof.1 (chRecord ν χ) ∧ ν 10 ≠ 0

/-- The accepting-transcript test read directly from one oracle table. -/
def algebraicTableAcceptZ {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (init : List (TranscriptElt Fp VestaG))
    (O : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)
    (p : AlgebraicWfProof basis vk) : Prop :=
  fullAlgebraicAcceptZ basis vk p
    (fun i => O (algebraicFullPrefixesPre init p i))
    (fun j => O (algebraicFullPrefixes init p j))

/-- Run the recursive extractor against the deployed algebraic Fiat–Shamir adversary. The oracle
table and extractor coins determine the returned certificate. -/
def algebraicForkCertAttempt {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk))
    (O : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)
    (coins : RecursiveForkCoins Fp shape.k) :
    RecursiveForkAttempt (AlgebraicDForkCert (F := Fp) basis shape.k) :=
  recursiveAlgebraicFork basis shape.k A (algebraicFullPrefixes init)
    (fun p => p.rounds) (fun p => (p.proof.1.ipaC, p.proof.1.ipaF))
    (algebraicTableAcceptZ basis vk init) (fun O p => by
      unfold algebraicTableAcceptZ fullAlgebraicAcceptZ DeployedIpaVerifierEq
      infer_instance) O coins

/-- Accepted deployed algebraic FS runs on which the executable recursive extractor fails to
return a certificate. -/
noncomputable def algebraicForkCertFailureSet {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk))
    (coins : RecursiveForkCoins Fp shape.k) :
    Set (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp) :=
  {O | fsWinsFull A (fullAlgebraicAcceptZ basis vk)
      (algebraicFullPrefixesPre init) (algebraicFullPrefixes init) O ∧
    ¬ (algebraicForkCertAttempt basis vk init A O coins).output.isSome}

/-- The concrete recursive certificate producer loses only the bounded-query escape slice. -/
theorem algebraicForkCertFailure_measure_le {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk))
    (tape : RecursiveForkTape Fp shape.k) {Q : ℕ} (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)).toOuterMeasure
        (algebraicForkCertFailureSet basis vk init A tape.toCoins)
      ≤ (Q + shape.k) * (3 / Fintype.card Fp) := by
  let D : PrefixDecode
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) shape.k
      (algebraicFullPrefixes (basis := basis) (vk := vk) init) :=
    ((fullDecodeDeployed shape init).precomp
      (fun p : AlgebraicWfProof basis vk => p.proof)).toPrefixDecode
  have h := recursiveForkFailure_measure_le basis shape.k A (algebraicFullPrefixes init)
    (fun p => p.rounds) (fun p => (p.proof.1.ipaC, p.proof.1.ipaF))
    (algebraicTableAcceptZ basis vk init) (fun O p => by
      unfold algebraicTableAcceptZ fullAlgebraicAcceptZ DeployedIpaVerifierEq
      infer_instance) D tape.toCoins tape.toCoins_complete hQ
  simpa only [recursiveForkFailureSet, algebraicForkCertFailureSet, algebraicForkCertAttempt,
    algebraicTableAcceptZ, fsWinsFull] using h

/-- Every certificate returned by the deployed extractor satisfies `DeployedForkValid`. -/
theorem algebraicForkCertAttempt_valid {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk))
    (O : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)
    (coins : RecursiveForkCoins Fp shape.k)
    (cert : AlgebraicDForkCert (F := Fp) basis shape.k)
    (hout : (algebraicForkCertAttempt basis vk init A O coins).output = some cert) :
    let p₀ := A.run O
    let ν₀ : Fin 11 → Fp := fun i => O (algebraicFullPrefixesPre init p₀ i)
    let urs := ursOfAugmentedBasis shape.k basis
    DeployedForkValid urs.g (evalVector shape.k (ν₀ 7)) urs.u urs.w (ν₀ 10)
      (commit urs
          (adjustedWitness (p₀.aMulti ν₀) p₀.s
            (multiopenValue vk p₀.proof.1 (chRecord ν₀ (fun _ => 0))) (ν₀ 9)) +
        (p₀.multiU ν₀ + ν₀ 9 * p₀.sU) • urs.u +
        (p₀.multiBlind ν₀ + ν₀ 9 * p₀.sBlind) • urs.w)
      cert.toDForkCert := by
  let p₀ := A.run O
  let ν₀ : Fin 11 → Fp := fun i => O (algebraicFullPrefixesPre init p₀ i)
  let urs := ursOfAugmentedBasis shape.k basis
  let FD : FullDecode
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k))
      11 shape.k (algebraicFullPrefixesPre init) (algebraicFullPrefixes init) :=
    (fullDecodeDeployed shape init).precomp
      (fun p : AlgebraicWfProof basis vk => p.proof)
  let D := FD.toPrefixDecode
  let stable := fun
      (O' : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)
      (p' : AlgebraicWfProof basis vk) =>
    preIpaTranscript init p'.proof.1 = preIpaTranscript init p₀.proof.1 ∧
      ∀ i, O' (algebraicFullPrefixesPre init p' i) = ν₀ i
  have hstable₀ : stable O p₀ := by
    refine ⟨rfl, ?_⟩
    intro i
    rfl
  have hstableUpdate : ∀ (m : ℕ) (hm : m < shape.k)
      (O' : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)
      (p' : AlgebraicWfProof basis vk) (u : Fp), stable O' p' →
      let t := algebraicFullPrefixes init p' ⟨m, hm⟩
      let O'' := Function.update O' t u
      let p'' := A.run O''
      algebraicFullPrefixes init p'' ⟨m, hm⟩ = t → stable O'' p'' := by
    intro m hm O' p' u hs t O'' p'' ht
    change (preIpaTranscript init p'.proof.1 = preIpaTranscript init p₀.proof.1 ∧
      ∀ i, O' (algebraicFullPrefixesPre init p' i) = ν₀ i) at hs
    change preIpaTranscript init p''.proof.1 = preIpaTranscript init p₀.proof.1 ∧
      ∀ i, O'' (algebraicFullPrefixesPre init p'' i) = ν₀ i
    have hpre : preIpaTranscript init p''.proof.1 = preIpaTranscript init p'.proof.1 := by
      exact preIpaTranscript_eq_of_fullPrefix_eq init p''.proof p'.proof ⟨m, hm⟩ ht
    have hsplice : p''.proof.1 =
        spliceIpa p'.proof.1 p''.proof.1.ipaRounds p''.proof.1.ipaC p''.proof.1.ipaF :=
      preIpaTranscript_inj init p''.proof.2 p'.proof.2 hpre
    refine ⟨hpre.trans hs.1, ?_⟩
    intro i
    have hprePoint : algebraicFullPrefixesPre init p'' i =
        algebraicFullPrefixesPre init p' i := by
      apply Subtype.ext
      change preIpaSqueezePoints init p''.proof.1 i = preIpaSqueezePoints init p'.proof.1 i
      rw [hsplice, preIpaSqueezePoints_spliceIpa]
    have hne : algebraicFullPrefixesPre init p'' i ≠ t := by
      intro heq
      have hle := (preIpaSqueezePoints_length_le init p''.proof.1 i).trans
        (le_of_eq (preIpaTranscript_length_eq init p''.proof.1 p''.proof.2))
      have hround := roundTranscriptFin_length
        (preIpaTranscript init p'.proof.1) p'.proof.1.ipaRounds ⟨m, hm⟩
      rw [preIpaTranscript_length_eq init p'.proof.1 p'.proof.2] at hround
      have hlen := congrArg (fun x => x.val.length) heq
      change (preIpaSqueezePoints init p''.proof.1 i).length =
        (roundTranscriptFin (preIpaTranscript init p'.proof.1)
          p'.proof.1.ipaRounds ⟨m, hm⟩).length at hlen
      omega
    change Function.update O' t u (algebraicFullPrefixesPre init p'' i) = ν₀ i
    rw [Function.update_apply, if_neg hne, hprePoint]
    exact hs.2 i
  have hdecode : ∀ (p : AlgebraicWfProof basis vk) (j : Fin shape.k),
      ((p.rounds j).1.point, (p.rounds j).2.point) =
        grindDecode (algebraicFullPrefixes init p j) := by
    intro p j
    exact (grindDecode_round (preIpaTranscript init p.proof.1) p.proof.1.ipaRounds j _).symm
  have hreal : AlgebraicForkRealizes basis grindDecode
      (RecursiveRunSuffix shape.k 0 shape.k (by omega) A (algebraicFullPrefixes init)
        (fun p => (p.proof.1.ipaC, p.proof.1.ipaF))
        (algebraicTableAcceptZ basis vk init) stable Fin.elim0) cert := by
    apply recursiveAlgebraicForkFrom_realizes basis shape.k A (algebraicFullPrefixes init)
      (fun p => p.rounds) (fun p => (p.proof.1.ipaC, p.proof.1.ipaF))
      (algebraicTableAcceptZ basis vk init) _ grindDecode D stable hstableUpdate hdecode
      0 (by omega) O p₀ coins cert Fin.elim0 rfl hstable₀
    · intro i
      exact Fin.elim0 i
    · simpa only [algebraicForkCertAttempt, recursiveAlgebraicFork] using hout
  have hPwhole : ∀ (chi : Fin shape.k → Fp),
      (multiopenCommitment urs.g urs.w urs.u vk p₀.proof.1 (chRecord ν₀ chi)
        + (∑ i, ([-(multiopenValue vk p₀.proof.1 (chRecord ν₀ chi))].getD i.val 0) • urs.g i)
        + (chRecord ν₀ chi : Challenges shape.k Fp).xi • p₀.proof.1.ipaS)
      = (commit urs
            (adjustedWitness (p₀.aMulti ν₀) p₀.s
              (multiopenValue vk p₀.proof.1 (chRecord ν₀ (fun _ => 0))) (ν₀ 9))
          + (p₀.multiU ν₀ + ν₀ 9 * p₀.sU) • urs.u
          + (p₀.multiBlind ν₀ + ν₀ 9 * p₀.sBlind) • urs.w) := by
    intro chi
    dsimp only [urs]
    dsimp only [AlgebraicWfProof.proof]
    rw [← chRecord_update ν₀ chi, multiopenValue_ipaRound, multiopenCommitment_ipaRound,
      show ({chRecord ν₀ (fun _ => (0 : Fp)) with ipaRound := chi} :
        Challenges shape.k Fp).xi = ν₀ 9 from rfl,
      ← p₀.multiopen_repr ν₀,
      show p₀.algebraicProof.erase.ipaS = p₀.algebraicProof.ipaS.point from rfl,
      ← p₀.ipaS_repr,
      sum_getD_single urs.g
        (multiopenValue vk p₀.algebraicProof.erase (chRecord ν₀ (fun _ => 0))),
      commit_adjustedWitness]
    module
  apply AlgebraicForkRealizes.deployedForkValid basis grindDecode urs.u urs.w (ν₀ 10)
    urs.g (evalVector shape.k (ν₀ 7)) _ _ cert hreal
  rintro ts cs c f ⟨O', p', hp', hwin, hs, -, hts, hcs, hfinal⟩
  change flatAccept (proverOfRounds (fun j => grindDecode (ts j)) c f)
    urs.g (evalVector shape.k (ν₀ 7)) urs.u urs.w (ν₀ 10)
      (commit urs
          (adjustedWitness (p₀.aMulti ν₀) p₀.s
            (multiopenValue vk p₀.proof.1 (chRecord ν₀ (fun _ => 0))) (ν₀ 9)) +
        (p₀.multiU ν₀ + ν₀ 9 * p₀.sU) • urs.u +
        (p₀.multiBlind ν₀ + ν₀ 9 * p₀.sBlind) • urs.w) cs
  have hsplice : p'.proof.1 =
      spliceIpa p₀.proof.1 p'.proof.1.ipaRounds p'.proof.1.ipaC p'.proof.1.ipaF :=
    preIpaTranscript_inj init p'.proof.2 p₀.proof.2 hs.1
  have hnu : (fun i => O' (algebraicFullPrefixesPre init p' i)) = ν₀ := funext hs.2
  have hchi : (fun j => O' (algebraicFullPrefixes init p' j)) = cs := by
    funext j
    rw [show algebraicFullPrefixes init p' j = ts j by simpa using hts j]
    exact hcs j
  rw [algebraicTableAcceptZ, hnu, hchi] at hwin
  have hacc := hwin.1
  rw [deployedVerifierEq_iff_flatAccept] at hacc
  rw [hsplice, multiopenValue_spliceIpa, multiopenCommitment_spliceIpa] at hacc
  have hrounds : (fun j => grindDecode (ts j)) = p'.proof.1.ipaRounds := by
    funext j
    calc
      grindDecode (ts j) = grindDecode (algebraicFullPrefixes init p' j) :=
        congrArg grindDecode (by simpa using (hts j).symm)
      _ = p'.proof.1.ipaRounds j := (hdecode p' j).symm
  have hc : p'.proof.1.ipaC = c := congrArg Prod.fst hfinal
  have hf : p'.proof.1.ipaF = f := congrArg Prod.snd hfinal
  rw [hrounds, ← hc, ← hf, ← hPwhole cs]
  rw [show (spliceIpa p₀.proof.1 p'.proof.1.ipaRounds p'.proof.1.ipaC
    p'.proof.1.ipaF).ipaS = p₀.proof.1.ipaS from rfl] at hacc
  exact hacc

/-- Rewrite a certificate onto the canonical augmented basis of the deployed AGM instance. -/
def AlgebraicDForkCert.toCanonicalBasis {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (cert : AlgebraicDForkCert (F := Fp) basis shape.k) :
    AlgebraicDForkCert (F := Fp)
      (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k := by
  exact Eq.mpr (congrArg (fun b => AlgebraicDForkCert (F := Fp) b shape.k)
    (augmentedBasis_ursOfAugmentedBasis shape.k basis)) cert

/-- Transporting an algebraic certificate across an equality of basis functions leaves its
ordinary certificate unchanged. -/
theorem AlgebraicDForkCert.toDForkCert_eq_mpr_basis {shape : Shape}
    {basis basis' : AugmentedIndex (2 ^ shape.k) → VestaG} (h : basis' = basis)
    (cert : AlgebraicDForkCert (F := Fp) basis shape.k) :
    (Eq.mpr (congrArg (fun b => AlgebraicDForkCert (F := Fp) b shape.k) h) cert).toDForkCert =
      cert.toDForkCert := by
  subst basis'
  rfl

/-- Changing only the type-level name of the augmented basis does not change the erased tree. -/
theorem AlgebraicDForkCert.toCanonicalBasis_toDForkCert {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    (cert : AlgebraicDForkCert (F := Fp) basis shape.k) :
    cert.toCanonicalBasis.toDForkCert = cert.toDForkCert := by
  exact AlgebraicDForkCert.toDForkCert_eq_mpr_basis
    (augmentedBasis_ursOfAugmentedBasis shape.k basis) cert

/-- Transport certificate validity to the canonical basis used by the deployed AGM instance. -/
theorem algebraicForkCertAttempt_valid_canonical {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk))
    (O : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)
    (coins : RecursiveForkCoins Fp shape.k)
    (cert : AlgebraicDForkCert (F := Fp) basis shape.k)
    (hout : (algebraicForkCertAttempt basis vk init A O coins).output = some cert) :
    let p := A.run O
    let ν : Fin 11 → Fp := fun i => O (algebraicFullPrefixesPre init p i)
    let urs := ursOfAugmentedBasis shape.k basis
    DeployedForkValid urs.g (evalVector shape.k (ν 7)) urs.u urs.w (ν 10)
      (commit urs
          (adjustedWitness (p.aMulti ν) p.s
            (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
        (p.multiU ν + ν 9 * p.sU) • urs.u +
        (p.multiBlind ν + ν 9 * p.sBlind) • urs.w)
      cert.toCanonicalBasis.toDForkCert := by
  rw [AlgebraicDForkCert.toCanonicalBasis_toDForkCert]
  exact algebraicForkCertAttempt_valid basis vk init A O coins cert hout

/-- Package one checked certificate with the algebraic data from its root FS run. -/
def deployedAlgebraicInstanceOfCert {shape : Shape}
    {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    (p : AlgebraicWfProof basis vk) (ν : Fin 11 → Fp)
    (cert : AlgebraicDForkCert (F := Fp)
      (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
    (hz : ν 10 ≠ 0)
    (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
      (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w (ν 10)
      (commit (ursOfAugmentedBasis shape.k basis)
          (adjustedWitness (p.aMulti ν) p.s
            (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
        (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
        (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
      cert.toDForkCert) :
    DeployedAlgebraicForkingInstance (G := VestaG) shape.k basis :=
  { b := evalVector shape.k (ν 7)
    v := multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0))
    ξ := ν 9
    z := ν 10
    vU := p.multiU ν + ν 9 * p.sU
    blind := p.multiBlind ν + ν 9 * p.sBlind
    aMulti := p.aMulti ν
    aDep := adjustedWitness (p.aMulti ν) p.s
      (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)
    s := p.s
    cert := cert
    hz := hz
    hb0 := evalVector_zero shape.k (ν 7)
    hP := commit_adjustedWitness (ursOfAugmentedBasis shape.k basis) (p.aMulti ν) p.s
      (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)
    hvalid := hvalid }

/-- On a mismatch run, a checked instance always yields an explicit relation: the kernel's
relation branch directly, or the commitment collision between its clean opening and the carried
aggregate opening `aMulti`. -/
theorem deployedAlgebraicInstanceOfCert_runRelation_isSome
    {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    (p : AlgebraicWfProof basis vk) (ν : Fin 11 → Fp)
    (cert : AlgebraicDForkCert (F := Fp)
      (augmentedBasis (ursOfAugmentedBasis shape.k basis).g
        (ursOfAugmentedBasis shape.k basis).u (ursOfAugmentedBasis shape.k basis).w) shape.k)
    (hz : ν 10 ≠ 0)
    (hvalid : DeployedForkValid (ursOfAugmentedBasis shape.k basis).g
      (evalVector shape.k (ν 7)) (ursOfAugmentedBasis shape.k basis).u
      (ursOfAugmentedBasis shape.k basis).w (ν 10)
      (commit (ursOfAugmentedBasis shape.k basis)
          (adjustedWitness (p.aMulti ν) p.s
            (multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0))) (ν 9)) +
        (p.multiU ν + ν 9 * p.sU) • (ursOfAugmentedBasis shape.k basis).u +
        (p.multiBlind ν + ν 9 * p.sBlind) • (ursOfAugmentedBasis shape.k basis).w)
      cert.toDForkCert)
    (hmm : innerProduct (p.aMulti ν) (evalVector shape.k (ν 7)) ≠
      multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0)) +
        (ν 10)⁻¹ * (p.multiU ν + ν 9 * p.sU) -
        ν 9 * innerProduct p.s (evalVector shape.k (ν 7))) :
    (deployedAlgebraicInstanceOfCert p ν cert hz hvalid).runRelation.isSome :=
  DeployedAlgebraicForkingInstance.runRelation_isSome_of_mismatch
    (deployedAlgebraicInstanceOfCert p ν cert hz hvalid) hmm

/-- Compute a deployed AGM instance from one Fiat–Shamir oracle table and extractor coins.
Failure to find a valid tree, or `z = 0`, returns `none`. -/
def computedDeployedAlgebraicInstance {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk))
    (O : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)
    (coins : RecursiveForkCoins Fp shape.k) :
    RecursiveForkAttempt
      (DeployedAlgebraicForkingInstance (G := VestaG) shape.k basis) := by
  let urs := ursOfAugmentedBasis shape.k basis
  let p := A.run O
  let ν : Fin 11 → Fp := fun i => O (algebraicFullPrefixesPre init p i)
  let certAttempt := algebraicForkCertAttempt basis vk init A O coins
  match hcert : certAttempt.output with
  | none => exact { output := none, runs := certAttempt.runs }
  | some cert =>
    if hz : ν 10 ≠ 0 then
      let canonicalCert := cert.toCanonicalBasis
      let b := evalVector shape.k (ν 7)
      let v := multiopenValue vk p.proof.1 (chRecord ν (fun _ => 0))
      let aDep := adjustedWitness (p.aMulti ν) p.s v (ν 9)
      let vU := p.multiU ν + ν 9 * p.sU
      let blind := p.multiBlind ν + ν 9 * p.sBlind
      have hvalid : DeployedForkValid urs.g b urs.u urs.w (ν 10)
          (commit urs aDep + vU • urs.u + blind • urs.w)
          canonicalCert.toDForkCert := by
        have hcert' : (algebraicForkCertAttempt basis vk init A O coins).output = some cert := by
          simpa only [certAttempt] using hcert
        exact algebraicForkCertAttempt_valid_canonical basis vk init A O coins cert hcert'
      exact
        { output := some (deployedAlgebraicInstanceOfCert p ν canonicalCert hz hvalid)
          runs := certAttempt.runs }
    else
      exact { output := none, runs := certAttempt.runs }

/-- The computed producer on the finite tape used by the probability experiment. -/
def computedDeployedAlgebraicInstanceFromTape {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk))
    (O : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)
    (tape : RecursiveForkTape Fp shape.k) :
    RecursiveForkAttempt
      (DeployedAlgebraicForkingInstance (G := VestaG) shape.k basis) :=
  computedDeployedAlgebraicInstance basis vk init A O tape.toCoins

/-- Accepting oracle tables on which the certified operational producer returns no AGM instance. -/
noncomputable def computedAlgebraicInstanceFailureSet {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk))
    (tape : RecursiveForkTape Fp shape.k) :
    Set (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp) :=
  {O | fsWinsFull A (fullAlgebraicAcceptZ basis vk)
      (algebraicFullPrefixesPre init) (algebraicFullPrefixes init) O ∧
    ¬ (computedDeployedAlgebraicInstanceFromTape basis vk init A O tape).output.isSome}

/-- On an accepting run, failure of the checked instance producer implies failure of the raw
certificate producer. -/
theorem computedAlgebraicInstanceFailureSet_subset_certFailure {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk))
    (tape : RecursiveForkTape Fp shape.k) :
    computedAlgebraicInstanceFailureSet basis vk init A tape ⊆
      algebraicForkCertFailureSet basis vk init A tape.toCoins := by
  intro O hfail
  refine ⟨hfail.1, ?_⟩
  intro hsome
  obtain ⟨cert, hcert⟩ := Option.isSome_iff_exists.mp hsome
  apply hfail.2
  unfold computedDeployedAlgebraicInstanceFromTape computedDeployedAlgebraicInstance
  dsimp only
  split
  · rename_i hnone
    rw [hnone] at hcert
    simp at hcert
  · rename_i cert' hcert'
    have hz : O (algebraicFullPrefixesPre init (A.run O) 10) ≠ 0 := hfail.1.2
    simp [hz]

/-- The executable, validity-certified producer loses no more probability than the recursive
certificate extractor itself. -/
theorem computedAlgebraicInstanceFailure_measure_le {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk))
    (tape : RecursiveForkTape Fp shape.k) {Q : ℕ} (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)).toOuterMeasure
        (computedAlgebraicInstanceFailureSet basis vk init A tape)
      ≤ (Q + shape.k) * (3 / Fintype.card Fp) := by
  refine le_trans (MeasureTheory.measure_mono
    (computedAlgebraicInstanceFailureSet_subset_certFailure basis vk init A tape)) ?_
  exact algebraicForkCertFailure_measure_le basis vk init A tape hQ

/-- A computed instance obtained on a real binding-attack run always returns an explicit
relation: the kernel's relation branch, or the collision of its clean opening with the carried
aggregate opening. -/
theorem computedDeployedAlgebraicInstance_runRelation_isSome
    {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk))
    (O : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)
    (coins : RecursiveForkCoins Fp shape.k)
    {x : DeployedAlgebraicForkingInstance (G := VestaG) shape.k basis}
    (hwin : fsWinsFull A (fullAlgebraicBindingAttack basis vk)
      (algebraicFullPrefixesPre init) (algebraicFullPrefixes init) O)
    (hinst : (computedDeployedAlgebraicInstance basis vk init A O coins).output = some x) :
    x.runRelation.isSome := by
  rw [fsWinsFull] at hwin
  unfold computedDeployedAlgebraicInstance at hinst
  dsimp only at hinst
  split at hinst
  · simp at hinst
  · rename_i cert hcert
    split at hinst
    · rename_i hz
      injection hinst with hx
      subst x
      apply deployedAlgebraicInstanceOfCert_runRelation_isSome
      exact hwin.2
    · simp at hinst

/-- Tape-form specialization of `computedDeployedAlgebraicInstance_runRelation_isSome`. -/
theorem computedDeployedAlgebraicInstanceFromTape_runRelation_isSome
    {shape : Shape}
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (vk : VerifyingKey shape Fp VestaG) (init : List (TranscriptElt Fp VestaG))
    (A : OracleComp
      (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
      (AlgebraicWfProof basis vk))
    (O : BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k) → Fp)
    (tape : RecursiveForkTape Fp shape.k)
    {x : DeployedAlgebraicForkingInstance (G := VestaG) shape.k basis}
    (hwin : fsWinsFull A (fullAlgebraicBindingAttack basis vk)
      (algebraicFullPrefixesPre init) (algebraicFullPrefixes init) O)
    (hinst : (computedDeployedAlgebraicInstanceFromTape basis vk init A O tape).output = some x) :
    x.runRelation.isSome :=
  computedDeployedAlgebraicInstance_runRelation_isSome basis vk init A O tape.toCoins hwin hinst

/-! ## Computed basis-indexed producer -/

/-- A basis-indexed family with one common transcript prefix, so every basis uses the same extractor
coin type. -/
structure ComputedAlgebraicFSFamily (shape : Shape) where
  init : List (TranscriptElt Fp VestaG)
  vk : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → VerifyingKey shape Fp VestaG
  adversary : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → OracleComp
    (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
    (AlgebraicWfProof basis (vk basis))
  Q : ℕ
  queryBound : ∀ basis, (adversary basis).QueryBound Q

namespace ComputedAlgebraicFSFamily

variable {shape : Shape}

/-- Independent random-oracle and recursive-extractor coins. -/
abbrev Coins (family : ComputedAlgebraicFSFamily shape) :=
  (BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) ×
    RecursiveForkTape Fp shape.k

/-- Run the computed FS-to-AGM producer on one basis and one set of extractor coins. -/
def instanceAttempt (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (coins : family.Coins) :
    RecursiveForkAttempt
      (DeployedAlgebraicForkingInstance (G := VestaG) shape.k basis) :=
  computedDeployedAlgebraicInstanceFromTape basis (family.vk basis) family.init
    (family.adversary basis) coins.1 coins.2

/-- Run the produced instance and return its explicit relation. `runRelation` handles both the
kernel relation branch and a clean-opening commitment collision. -/
def relationFinder (family : ComputedAlgebraicFSFamily shape) :
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → family.Coins →
      Option (AlgebraicRelationWitness (F := Fp) basis) :=
  fun basis coins =>
    match (family.instanceAttempt basis coins).output with
    | none => none
    | some x => x.runRelation

/-- The real binding-attack event for one oracle table. -/
def bindingWin (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (O : family.Coins) : Prop :=
  fsWinsFull (family.adversary basis) (fullAlgebraicBindingAttack basis (family.vk basis))
    (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) O.1

/-- Binding runs on which the operational producer returns no instance. -/
def failedBinding (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) : Set family.Coins :=
  {coins | family.bindingWin basis coins ∧
    ¬ (family.instanceAttempt basis coins).output.isSome}

/-- For one sampled basis, failed binding extraction is bounded by the recursive query loss and
the adaptive `z = 0` slice. -/
theorem failedBinding_measure_le (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) :
    (PMF.uniformOfFintype family.Coins).toOuterMeasure (family.failedBinding basis)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) := by
  let acceptFailure : Set family.Coins := {coins |
    fsWinsFull (family.adversary basis) (fullAlgebraicAcceptZ basis (family.vk basis))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) coins.1 ∧
    ¬ (family.instanceAttempt basis coins).output.isSome}
  let zeroFailure : Set family.Coins := {coins |
    family.bindingWin basis coins ∧
      coins.1 (algebraicFullPrefixesPre family.init
        ((family.adversary basis).run coins.1) 10) = 0}
  have haccept : (PMF.uniformOfFintype family.Coins).toOuterMeasure acceptFailure ≤
      (family.Q + shape.k) * (3 / Fintype.card Fp) := by
    apply uniformOfFintype_prod_fiber_bound
      (fun tape => computedAlgebraicInstanceFailureSet basis (family.vk basis) family.init
        (family.adversary basis) tape)
    intro tape
    exact computedAlgebraicInstanceFailure_measure_le basis (family.vk basis) family.init
      (family.adversary basis) tape (family.queryBound basis)
  have hzero : (PMF.uniformOfFintype family.Coins).toOuterMeasure zeroFailure ≤
      (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) := by
    apply uniformOfFintype_prod_fiber_bound
      (fun _tape : RecursiveForkTape Fp shape.k =>
        {O | fsWinsFull (family.adversary basis)
            (fullAlgebraicBindingAttack basis (family.vk basis))
            (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) O ∧
          O (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 10) = 0})
    intro _
    exact fsAdvantageFull_zero_slice_le (family.adversary basis)
      (fullAlgebraicBindingAttack basis (family.vk basis))
      (algebraicFullPrefixesPre family.init) (algebraicFullPrefixes family.init) 10
      (family.queryBound basis)
  have hsub : family.failedBinding basis ⊆ acceptFailure ∪ zeroFailure := by
    intro coins hfail
    by_cases hz : coins.1 (algebraicFullPrefixesPre family.init
        ((family.adversary basis).run coins.1) 10) = 0
    · exact Or.inr ⟨hfail.1, hz⟩
    · refine Or.inl ⟨?_, hfail.2⟩
      exact ⟨hfail.1.1, hz⟩
  refine le_trans (MeasureTheory.measure_mono hsub)
    (le_trans (MeasureTheory.measure_union_le _ _) ?_)
  exact add_le_add haccept hzero

/-- On a binding-attack run, every returned instance is retained by the relation finder: the
mismatch with the carried aggregate opening turns even a clean extracted opening into a
commitment-collision relation. -/
theorem relationFinder_isSome_of_bindingWin
    (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (coins : family.Coins)
    (hwin : family.bindingWin basis coins)
    (hsome : (family.instanceAttempt basis coins).output.isSome) :
    (family.relationFinder basis coins).isSome := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
  have hrel := computedDeployedAlgebraicInstanceFromTape_runRelation_isSome basis
    (family.vk basis) family.init (family.adversary basis) coins.1 coins.2 hwin hx
  unfold relationFinder
  rw [hx]
  exact hrel

/-- Basis/coin pairs on which the real binding attack occurs and the recursive extractor returns an
instance. -/
noncomputable def successfulBindingSet
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape) :
    Finset ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins) := by
  classical
  exact Finset.univ.filter fun p =>
    family.bindingWin (scalarBasis B p.1) p.2 ∧
      (family.instanceAttempt (scalarBasis B p.1) p.2).output.isSome

/-- All real binding runs, before extraction success is required. -/
noncomputable def bindingSet
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape) :
    Finset ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins) := by
  classical
  exact Finset.univ.filter fun p => family.bindingWin (scalarBasis B p.1) p.2

/-- The binding event on an explicit augmented basis and extractor coins. -/
def bindingEvent (family : ComputedAlgebraicFSFamily shape) :
    Set ((AugmentedIndex (2 ^ shape.k) → VestaG) × family.Coins) :=
  {p | family.bindingWin p.1 p.2}

/-- Real binding runs lost by the executable producer. -/
noncomputable def failedBindingSet
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape) :
    Finset ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins) := by
  classical
  exact Finset.univ.filter fun p => p.2 ∈ family.failedBinding (scalarBasis B p.1)

/-- Averaging over the sampled basis does not increase the uniform extractor-loss bound. -/
theorem failedBindingSet_prob_le
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape) :
    (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)).toOuterMeasure
        (failedBindingSet B family)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) := by
  have hset : (↑(failedBindingSet B family) :
      Set ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)) =
      {p | p.2 ∈ family.failedBinding (scalarBasis B p.1)} := by
    ext p
    simp only [failedBindingSet, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and, Set.mem_setOf_eq]
  rw [hset]
  apply uniformOfFintype_prod_fiber_bound_right
    (β := (family.Q + shape.k) * (3 / Fintype.card Fp) +
      (family.Q + 1 : ℕ) * (1 / Fintype.card Fp))
    (fun coeffs : AugmentedIndex (2 ^ shape.k) → Fp =>
      family.failedBinding (scalarBasis B coeffs))
  intro coeffs
  exact failedBinding_measure_le (shape := shape) family (scalarBasis B coeffs)

/-- Every binding run either produces an instance or lies in the explicitly bounded failure set. -/
theorem bindingSet_subset_success_union_failure
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape) :
    (↑(bindingSet B family) :
        Set ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)) ⊆
      (↑(successfulBindingSet B family) :
          Set ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)) ∪
      (↑(failedBindingSet B family) :
          Set ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)) := by
  intro p hp
  simp only [bindingSet, successfulBindingSet, failedBindingSet, Finset.mem_coe,
    Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_union] at hp ⊢
  by_cases hsome : (family.instanceAttempt (scalarBasis B p.1) p.2).output.isSome
  · exact Or.inl ⟨hp, hsome⟩
  · exact Or.inr ⟨hp, hsome⟩

/-- Every successfully extracted binding run is a relation-producing run of the computed finder. -/
theorem successfulBindingSet_subset_relSet
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape) :
    successfulBindingSet B family ⊆ relSetWithCoins B family.relationFinder := by
  intro p hp
  simp only [successfulBindingSet, Finset.mem_filter, Finset.mem_univ, true_and] at hp
  simp only [relSetWithCoins, Finset.mem_filter, Finset.mem_univ, true_and]
  exact family.relationFinder_isSome_of_bindingWin (scalarBasis B p.1) p.2 hp.1 hp.2

/-- Plain-DL hardness bounds the probability of real binding runs on which the executable extractor
returns an AGM instance. -/
theorem successfulBinding_prob_le_of_textbookDL
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.relationFinder bound) :
    (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)).toOuterMeasure
        (successfulBindingSet B family)
      ≤ Fintype.card (AugmentedIndex (2 ^ shape.k)) * bound := by
  refine le_trans (MeasureTheory.measure_mono (successfulBindingSet_subset_relSet B family)) ?_
  exact relationWithCoins_prob_le_of_textbookDL B family.relationFinder hDL

/-- End-to-end computed probability bound: the real deployed binding event is at most the
recursive query loss, the adaptive `z = 0` loss, and the fixed-slot plain-DL term. -/
theorem binding_prob_le_of_textbookDL
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.relationFinder bound) :
    (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)).toOuterMeasure
        (bindingSet B family)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        Fintype.card (AugmentedIndex (2 ^ shape.k)) * bound := by
  refine le_trans (MeasureTheory.measure_mono
    (bindingSet_subset_success_union_failure B family)) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  have hsuccess := successfulBinding_prob_le_of_textbookDL B family hDL
  have hfailure := failedBindingSet_prob_le B family
  exact add_le_add hsuccess hfailure |>.trans_eq (by ac_rfl)

/-- Transfer the computed binding experiment from an explicit uniform-URS setup to the sampled
scalar basis used by the fixed-slot reduction. Extractor coins remain independent on both sides. -/
theorem binding_prob_eq_of_uniformURS {Ω : Type*} (setup : PMF Ω)
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape)
    (basisOf : Ω → AugmentedIndex (2 ^ shape.k) → VestaG)
    (hURS : OrchardUniformURSIdentification setup shape.k B basisOf) :
    (independentProductPMF setup (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (basisOf p.1, p.2)) ⁻¹' family.bindingEvent) =
      (PMF.uniformOfFintype
        ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)).toOuterMeasure
        (bindingSet B family) := by
  let coinPMF := PMF.uniformOfFintype family.Coins
  have hprod :
      (independentProductPMF setup coinPMF).map (fun p => (basisOf p.1, p.2)) =
        (independentProductPMF
          (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) → Fp)) coinPMF).map
            (fun p => (scalarBasis B p.1, p.2)) := by
    calc
      _ = independentProductPMF (setup.map basisOf) coinPMF :=
        independentProductPMF_map_left setup coinPMF basisOf
      _ = independentProductPMF
          ((PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) → Fp)).map (scalarBasis B))
          coinPMF := congrArg (fun p => independentProductPMF p coinPMF) hURS
      _ = _ := (independentProductPMF_map_left
        (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) → Fp)) coinPMF
        (scalarBasis B)).symm
  have hmeasure := congrArg
    (fun p : PMF ((AugmentedIndex (2 ^ shape.k) → VestaG) × family.Coins) =>
      p.toOuterMeasure family.bindingEvent) hprod
  change ((independentProductPMF setup coinPMF).map
      (fun p => (basisOf p.1, p.2))).toOuterMeasure family.bindingEvent =
    ((independentProductPMF
      (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) → Fp)) coinPMF).map
        (fun p => (scalarBasis B p.1, p.2))).toOuterMeasure family.bindingEvent at hmeasure
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply] at hmeasure
  calc
    _ = (independentProductPMF
          (PMF.uniformOfFintype (AugmentedIndex (2 ^ shape.k) → Fp)) coinPMF).toOuterMeasure
          ((fun p => (scalarBasis B p.1, p.2)) ⁻¹' family.bindingEvent) := hmeasure
    _ = (PMF.uniformOfFintype
          ((AugmentedIndex (2 ^ shape.k) → Fp) × family.Coins)).toOuterMeasure
          (bindingSet B family) := by
      rw [independentProductPMF_uniform]
      congr 1
      ext p
      simp only [Set.mem_preimage, bindingEvent, Set.mem_setOf_eq, bindingSet,
        Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]

/-- End-to-end computed bound under an explicit uniform-URS setup distribution. -/
theorem binding_prob_le_of_uniformURS_textbookDL {Ω : Type*} (setup : PMF Ω)
    (B : VestaG) (family : ComputedAlgebraicFSFamily shape)
    (basisOf : Ω → AugmentedIndex (2 ^ shape.k) → VestaG)
    {bound : ℝ≥0∞} (hURS : OrchardUniformURSIdentification setup shape.k B basisOf)
    (hDL : TextbookDLWithCoinsAdvantageLE B family.relationFinder bound) :
    (independentProductPMF setup (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (basisOf p.1, p.2)) ⁻¹' family.bindingEvent)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        Fintype.card (AugmentedIndex (2 ^ shape.k)) * bound := by
  rw [binding_prob_eq_of_uniformURS setup B family basisOf hURS]
  exact binding_prob_le_of_textbookDL B family hDL

/-- End-to-end computed bound in the uniform generator-random-oracle setup model. -/
theorem binding_prob_le_of_generatorRO_textbookDL
    {T : Type*} [DecidableEq T] (B : VestaG) (hB : B ≠ 0)
    (query : AugmentedIndex (2 ^ shape.k) → T) (hquery : Function.Injective query)
    (family : ComputedAlgebraicFSFamily shape) {bound : ℝ≥0∞}
    (hDL : TextbookDLWithCoinsAdvantageLE B family.relationFinder bound) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' family.bindingEvent)
      ≤ (family.Q + shape.k) * (3 / Fintype.card Fp) +
        (family.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        Fintype.card (AugmentedIndex (2 ^ shape.k)) * bound :=
  binding_prob_le_of_uniformURS_textbookDL (orchardGeneratorROSetup query) B family
    (orchardGeneratorROBasis query)
    (orchard_uniformURSIdentification_of_generatorRO shape.k B hB query hquery) hDL

end ComputedAlgebraicFSFamily

/-! ## Randomized adversaries

Private coins form a uniform mixture of deterministic adversaries. The binding bound averages over
that mixture when the DL hypothesis holds for every member. `fsWinsFull_restrictSum_le` handles
finite junk oracle points without changing the query budget. -/

/-- A basis-indexed family whose adversary additionally draws private coins from a finite type
`R`, independent of the oracle table and the extractor tape. All members share one transcript
prefix, so they share one oracle-and-tape coin type. -/
structure ComputedAlgebraicFSFamilyRand (shape : Shape) (R : Type*) where
  init : List (TranscriptElt Fp VestaG)
  vk : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → VerifyingKey shape Fp VestaG
  adversary : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → R → OracleComp
    (BTranscript Fp VestaG (preIpaLen shape init.length 10 + 3 * shape.k)) Fp
    (AlgebraicWfProof basis (vk basis))
  Q : ℕ
  queryBound : ∀ basis r, (adversary basis r).QueryBound Q

namespace ComputedAlgebraicFSFamilyRand

variable {shape : Shape} {R : Type*}

/-- The deterministic member obtained by fixing the private coins. -/
abbrev determinize (fam : ComputedAlgebraicFSFamilyRand shape R) (r : R) :
    ComputedAlgebraicFSFamily shape :=
  { init := fam.init
    vk := fam.vk
    adversary := fun basis => fam.adversary basis r
    Q := fam.Q
    queryBound := fun basis => fam.queryBound basis r }

/-- The oracle-table and extractor-tape coins, shared by every member. -/
abbrev Coins (fam : ComputedAlgebraicFSFamilyRand shape R) :=
  (BTranscript Fp VestaG (preIpaLen shape fam.init.length 10 + 3 * shape.k) → Fp) ×
    RecursiveForkTape Fp shape.k

open Classical in
/-- **Randomized-adversary bound.** Averaging deterministic members over uniform private coins
preserves the query loss, `z = 0` loss, and DL bound. -/
theorem binding_prob_le_of_textbookDL_rand [Fintype R] [Nonempty R]
    (B : VestaG) (fam : ComputedAlgebraicFSFamilyRand shape R) {bound : ℝ≥0∞}
    (hDL : ∀ r, TextbookDLWithCoinsAdvantageLE B (fam.determinize r).relationFinder bound) :
    (PMF.uniformOfFintype
        (((AugmentedIndex (2 ^ shape.k) → Fp) × fam.Coins) × R)).toOuterMeasure
        {p : ((AugmentedIndex (2 ^ shape.k) → Fp) × fam.Coins) × R |
          p.1 ∈ (ComputedAlgebraicFSFamily.bindingSet B (fam.determinize p.2) :
            Set ((AugmentedIndex (2 ^ shape.k) → Fp) × fam.Coins))}
      ≤ (fam.Q + shape.k) * (3 / Fintype.card Fp) +
        (fam.Q + 1 : ℕ) * (1 / Fintype.card Fp) +
        Fintype.card (AugmentedIndex (2 ^ shape.k)) * bound := by
  apply uniformOfFintype_prod_fiber_bound
    (fun r => (ComputedAlgebraicFSFamily.bindingSet B (fam.determinize r) :
      Set ((AugmentedIndex (2 ^ shape.k) → Fp) × fam.Coins)))
  intro r
  exact ComputedAlgebraicFSFamily.binding_prob_le_of_textbookDL B (fam.determinize r) (hDL r)

end ComputedAlgebraicFSFamilyRand

/-! ## Standard AGM adapter

`AlgebraicWfProof.ofRepresented` computes the multiopen and `S` coordinates from per-point AGM
representations. `Provenance.AlgebraicWfProof.ofStandard` proves that the deployed assembly uses
only represented proof and verifying-key points, discharging the coverage premise below. -/

/-- Decompose an augmented-basis representation into its generator, `U`, and `W` components. -/
theorem representationEval_augmented_components {n : ℕ}
    (basis : AugmentedIndex n → VestaG) (c : AugmentedIndex n → Fp) :
    representationEval basis c
      = (∑ i : Fin n, c (AugmentedIndex.gen i) • basis (AugmentedIndex.gen i))
        + c AugmentedIndex.u • basis AugmentedIndex.u
        + c AugmentedIndex.w • basis AugmentedIndex.w := by
  rw [representationEval, Fintype.sum_sum_type, Fin.sum_univ_two, ← add_assoc]
  rfl

section Adapter

variable {shape : Shape} {basis : AugmentedIndex (2 ^ shape.k) → VestaG}

/-- The generator components of an augmented-basis representation. -/
def AlgebraicPoint.gPart (P : AlgebraicPoint (F := Fp) basis) : Fin (2 ^ shape.k) → Fp :=
  fun i => P.coeffs (AugmentedIndex.gen i)

/-- An augmented-basis point is its generator commitment plus its declared `U` and `W`
components. -/
theorem AlgebraicPoint.point_eq_components (P : AlgebraicPoint (F := Fp) basis) :
    P.point = commit (ursOfAugmentedBasis shape.k basis) P.gPart
      + P.coeffs AugmentedIndex.u • (ursOfAugmentedBasis shape.k basis).u
      + P.coeffs AugmentedIndex.w • (ursOfAugmentedBasis shape.k basis).w := by
  rw [← P.hEq, representationEval_augmented_components]
  rfl

private theorem commitA_add (a b : Fin (2 ^ shape.k) → Fp) :
    commit (ursOfAugmentedBasis shape.k basis) (a + b)
      = commit (ursOfAugmentedBasis shape.k basis) a
        + commit (ursOfAugmentedBasis shape.k basis) b :=
  commit_add _ _ _

private theorem commitA_smul (c : Fp) (a : Fin (2 ^ shape.k) → Fp) :
    commit (ursOfAugmentedBasis shape.k basis) (c • a)
      = c • commit (ursOfAugmentedBasis shape.k basis) a :=
  commit_smul _ _ _

/-- The aggregated generator coordinates of a represented term list. -/
def repsGPart (reps : List (Fp × AlgebraicPoint (F := Fp) basis)) : Fin (2 ^ shape.k) → Fp :=
  fun i => (reps.map (fun t => t.1 * t.2.coeffs (AugmentedIndex.gen i))).sum

/-- The aggregated `U` coordinate of a represented term list. -/
def repsU (reps : List (Fp × AlgebraicPoint (F := Fp) basis)) : Fp :=
  (reps.map (fun t => t.1 * t.2.coeffs AugmentedIndex.u)).sum

/-- The aggregated `W` coordinate of a represented term list. -/
def repsW (reps : List (Fp × AlgebraicPoint (F := Fp) basis)) : Fp :=
  (reps.map (fun t => t.1 * t.2.coeffs AugmentedIndex.w)).sum

theorem repsGPart_cons (t : Fp × AlgebraicPoint (F := Fp) basis)
    (reps : List (Fp × AlgebraicPoint (F := Fp) basis)) :
    repsGPart (t :: reps) = t.1 • t.2.gPart + repsGPart reps := by
  funext i
  simp [repsGPart, AlgebraicPoint.gPart, smul_eq_mul]

theorem repsU_cons (t : Fp × AlgebraicPoint (F := Fp) basis)
    (reps : List (Fp × AlgebraicPoint (F := Fp) basis)) :
    repsU (t :: reps) = t.1 * t.2.coeffs AugmentedIndex.u + repsU reps := by
  simp [repsU]

theorem repsW_cons (t : Fp × AlgebraicPoint (F := Fp) basis)
    (reps : List (Fp × AlgebraicPoint (F := Fp) basis)) :
    repsW (t :: reps) = t.1 * t.2.coeffs AugmentedIndex.w + repsW reps := by
  simp [repsW]

/-- Represented `(scalar, point)` terms sum to the commitment of their aggregated generator
coordinates plus the aggregated `U` and `W` components: appended terms are linear, so
representations aggregate coordinatewise. -/
theorem sum_map_smul_point_repr (reps : List (Fp × AlgebraicPoint (F := Fp) basis)) :
    ((reps.map (fun t => (t.1, t.2.point))).map (fun t => t.1 • t.2)).sum
      = commit (ursOfAugmentedBasis shape.k basis) (repsGPart reps)
        + repsU reps • (ursOfAugmentedBasis shape.k basis).u
        + repsW reps • (ursOfAugmentedBasis shape.k basis).w := by
  induction reps with
  | nil =>
      simp [repsGPart, repsU, repsW, commit]
  | cons t reps ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, t.2.point_eq_components, repsGPart_cons, repsU_cons, repsW_cons,
        commitA_add, commitA_smul]
      module

/-- Evaluating an MSM whose appended points carry representations: the aggregate `(g,U,W)`
coordinates are the MSM's own scalars plus the coordinatewise linear combination of the
representations. -/
theorem Msm.eval_repr (m : Msm shape.k Fp VestaG)
    (reps : List (Fp × AlgebraicPoint (F := Fp) basis))
    (hcov : m.other = reps.map (fun t => (t.1, t.2.point))) :
    m.eval (ursOfAugmentedBasis shape.k basis)
      = commit (ursOfAugmentedBasis shape.k basis) (m.gScalars + repsGPart reps)
        + (m.uScalar + repsU reps) • (ursOfAugmentedBasis shape.k basis).u
        + (m.wScalar + repsW reps) • (ursOfAugmentedBasis shape.k basis).w := by
  have heval : ∀ (urs : URS VestaG) (m' : Msm urs.k Fp VestaG),
      m'.eval urs = commit urs m'.gScalars + m'.wScalar • urs.w + m'.uScalar • urs.u
        + (m'.other.map fun t => t.1 • t.2).sum := fun _ _ => rfl
  rw [heval, hcov, sum_map_smul_point_repr, commitA_add]
  module

/-- The multiopen assembly MSM whose evaluation is `multiopenCommitment`. -/
def multiopenMsm (vk : VerifyingKey shape Fp VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp) :
    Msm shape.k Fp VestaG :=
  (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
    (constructIntermediateSets (assembleQueries vk ps ch)) (Msm.zero shape.k Fp VestaG)).1

/-- `multiopenCommitment` is the assembly MSM's evaluation. -/
theorem multiopenCommitment_eq_eval
    (g' : Fin (2 ^ shape.k) → VestaG) (w' u' : VestaG)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG)
    (ch : Challenges shape.k Fp) :
    multiopenCommitment g' w' u' vk ps ch
      = (multiopenMsm vk ps ch).eval ⟨shape.k, g', w', u'⟩ := by
  unfold multiopenCommitment multiopenMsm
  rfl

attribute [local irreducible] multiopenMsm

/-- Evaluating against the reconstructed URS is evaluating against its literal components: the
`URS` structure eta step, stated for an abstract MSM so nothing large is ever normalized. -/
private theorem eval_urs_eta (m : Msm shape.k Fp VestaG) :
    m.eval (⟨shape.k, (ursOfAugmentedBasis shape.k basis).g,
        (ursOfAugmentedBasis shape.k basis).w,
        (ursOfAugmentedBasis shape.k basis).u⟩ : URS VestaG)
      = m.eval (ursOfAugmentedBasis shape.k basis) := rfl

attribute [local irreducible] multiopenCommitment Msm.eval

/-- A represented multiopen assembly: the assembled MSM's appended points, each carrying its
`(g,U,W)` representation. A standard AGM adversary supplies this from the representations of the
proof and verifying-key commitments it feeds the verifier
(`RepresentedMultiopen.ofCoveredList`). -/
structure RepresentedMultiopen
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (ν : Fin 11 → Fp) where
  reps : List (Fp × AlgebraicPoint (F := Fp) basis)
  covers : (multiopenMsm vk ps (chRecord ν (fun _ => 0))).other
    = reps.map (fun t => (t.1, t.2.point))

/-- Rebuild a scalar–point list from lookups into a covering list of represented points. -/
private theorem list_eq_map_pmap_lookup {β : Type*} (point : β → VestaG)
    (L : List β) : (l : List (Fp × VestaG)) →
    (H : ∀ pr ∈ l, (L.find? (fun ap => point ap = pr.2)).isSome) →
    l = (l.pmap (fun pr h => (pr.1, (L.find? (fun ap => point ap = pr.2)).get h)) H).map
        (fun t => (t.1, point t.2))
  | [], _ => rfl
  | pr :: l, H => by
      simp only [List.pmap, List.map_cons]
      refine congrArg₂ List.cons ?_ (list_eq_map_pmap_lookup point L l
        (fun a ha => H a (List.mem_cons_of_mem _ ha)))
      have hp := List.find?_some
        ((Option.some_get (H pr (List.mem_cons_self ..))).symm)
      have hpt : point ((L.find? (fun ap => point ap = pr.2)).get
          (H pr (List.mem_cons_self ..))) = pr.2 := by
        simpa using hp
      exact Prod.ext rfl hpt.symm

/-- Build the represented assembly by lookup: any list of represented points containing every
point the assembly appends suffices. The hypothesis is representation-free — it speaks only about
which group elements the deployed assembly touches. -/
def RepresentedMultiopen.ofCoveredList
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG)
    (ν : Fin 11 → Fp) (L : List (AlgebraicPoint (F := Fp) basis))
    (hcover : ∀ pr ∈ (multiopenMsm vk ps (chRecord ν (fun _ => 0))).other,
      ∃ ap ∈ L, ap.point = pr.2) :
    RepresentedMultiopen vk ps basis ν :=
  have H : ∀ pr ∈ (multiopenMsm vk ps (chRecord ν (fun _ => 0))).other,
      (L.find? (fun ap => ap.point = pr.2)).isSome := by
    intro pr hpr
    rw [List.find?_isSome]
    obtain ⟨ap, hapL, hap⟩ := hcover pr hpr
    exact ⟨ap, hapL, by simp [hap]⟩
  { reps := (multiopenMsm vk ps (chRecord ν (fun _ => 0))).other.pmap
      (fun pr h => (pr.1, (L.find? (fun ap => ap.point = pr.2)).get h)) H
    covers := list_eq_map_pmap_lookup AlgebraicPoint.point L _ H }

/-- **Standard AGM adapter.** Compute the packaged proof from represented emitted points and a
represented multiopen assembly. No aggregate representation equality is assumed. -/
def AlgebraicWfProof.ofRepresented {vk : VerifyingKey shape Fp VestaG}
    (aps : AlgebraicProofString shape basis) (hwf : PsWellFormed aps.erase)
    (rm : ∀ ν : Fin 11 → Fp, RepresentedMultiopen vk aps.erase basis ν) :
    AlgebraicWfProof basis vk :=
  { algebraicProof := aps
    wellFormed := hwf
    aMulti := fun ν =>
      (multiopenMsm vk aps.erase (chRecord ν (fun _ => 0))).gScalars + repsGPart (rm ν).reps
    multiU := fun ν =>
      (multiopenMsm vk aps.erase (chRecord ν (fun _ => 0))).uScalar + repsU (rm ν).reps
    multiBlind := fun ν =>
      (multiopenMsm vk aps.erase (chRecord ν (fun _ => 0))).wScalar + repsW (rm ν).reps
    multiopen_repr := fun ν =>
      (Msm.eval_repr (multiopenMsm vk aps.erase (chRecord ν (fun _ => 0)))
        (rm ν).reps (rm ν).covers).symm.trans
        ((eval_urs_eta (multiopenMsm vk aps.erase (chRecord ν (fun _ => 0)))).symm.trans
          (multiopenCommitment_eq_eval _ _ _ vk aps.erase _).symm)
    s := aps.ipaS.gPart
    sU := aps.ipaS.coeffs AugmentedIndex.u
    sBlind := aps.ipaS.coeffs AugmentedIndex.w
    ipaS_repr := (AlgebraicPoint.point_eq_components aps.ipaS).symm }

end Adapter

end Zcash.Snark
