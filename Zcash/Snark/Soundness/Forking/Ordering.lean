import Zcash.Snark.Verifier.FiatShamir
import Zcash.Snark.Soundness.Forking.Extractor

/-!
# Fiat–Shamir round ordering

`deriveChallenges` appends each IPA round point `(Lⱼ, Rⱼ)` before squeezing its challenge `uⱼ`:

    (List.finRange shape.k).foldl (fun (t, us) j =>
        let t := t ++ [.point Lⱼ, .point Rⱼ, .challenge]
        (t, us ++ [squeeze t])) (t₀, [])

This module proves that the deployed schedule has the prefix ordering assumed by the prover strategy
and rewinding proofs.

* `roundTranscript` is the prefix used to squeeze one round challenge.
* `roundTranscript_succ` and `roundTranscript_prefix_mono` show how those prefixes grow.
* `roundPoint_mem_roundTranscript` shows that the current point is present before its challenge.

Halo2 does not reabsorb squeezed challenges. The `Prover` type separately ensures that each round
point depends only on earlier challenges.
-/

namespace Zcash.Snark

variable {F G : Type*}

/-- The transcript prefix used to squeeze the round-`j` IPA challenge. -/
def roundTranscript (t₀ : List (TranscriptElt F G)) (rounds : ℕ → G × G) :
    ℕ → List (TranscriptElt F G)
  | 0 => t₀ ++ [.point (rounds 0).1, .point (rounds 0).2, .challenge]
  | j + 1 =>
      roundTranscript t₀ rounds j ++ [.point (rounds (j + 1)).1, .point (rounds (j + 1)).2, .challenge]

/-- Extend a round transcript with the next point and challenge marker. -/
theorem roundTranscript_succ (t₀ : List (TranscriptElt F G)) (rounds : ℕ → G × G) (j : ℕ) :
    roundTranscript t₀ rounds (j + 1)
      = roundTranscript t₀ rounds j
        ++ [.point (rounds (j + 1)).1, .point (rounds (j + 1)).2, .challenge] :=
  rfl

/-- The base and earlier round transcripts are prefixes of every later round transcript. -/
theorem roundTranscript_prefix_mono (t₀ : List (TranscriptElt F G)) (rounds : ℕ → G × G) (j : ℕ) :
    t₀ <+: roundTranscript t₀ rounds j
      ∧ roundTranscript t₀ rounds j <+: roundTranscript t₀ rounds (j + 1) := by
  constructor
  · induction j with
    | zero => exact ⟨_, rfl⟩
    | succ j ih => exact ih.trans ⟨_, (roundTranscript_succ t₀ rounds j).symm⟩
  · exact ⟨_, (roundTranscript_succ t₀ rounds j).symm⟩

/-- The round-`j` point is present in the transcript before `uⱼ` is squeezed. -/
theorem roundPoint_mem_roundTranscript (t₀ : List (TranscriptElt F G)) (rounds : ℕ → G × G) (j : ℕ) :
    TranscriptElt.point (rounds j).1 ∈ roundTranscript t₀ rounds j ∧
      TranscriptElt.point (rounds j).2 ∈ roundTranscript t₀ rounds j := by
  cases j <;> exact ⟨by simp [roundTranscript], by simp [roundTranscript]⟩

/-- Squeeze the round-`j` IPA challenge from its round transcript. -/
def roundChallenge (fs : FiatShamir F G) (t₀ : List (TranscriptElt F G)) (rounds : ℕ → G × G)
    (j : ℕ) : F :=
  fs.squeeze (roundTranscript t₀ rounds j)

/-- The transcript part of the deployed IPA `foldl` is the base followed by each round's absorb block. -/
theorem ipaFold_transcript {ι : Type*} (fs : FiatShamir F G) (rp : ι → G × G)
    (L : List ι) (t₀ : List (TranscriptElt F G)) (us₀ : List F) :
    (L.foldl (fun st i =>
        (st.1 ++ [TranscriptElt.point (rp i).1, TranscriptElt.point (rp i).2, TranscriptElt.challenge],
          st.2 ++ [fs.squeeze (st.1 ++ [TranscriptElt.point (rp i).1, TranscriptElt.point (rp i).2,
            TranscriptElt.challenge])])) (t₀, us₀)).1
      = t₀ ++ (L.map (fun i =>
          [TranscriptElt.point (rp i).1, TranscriptElt.point (rp i).2, TranscriptElt.challenge])).flatten := by
  induction L generalizing t₀ us₀ with
  | nil => simp
  | cons i L ih => simp only [List.foldl_cons, ih, List.map_cons, List.flatten_cons, List.append_assoc]

/-! ## The Prover-tree side: each round point is prefix-determined

In `Prover.node`, the round point is fixed before the challenge selects a continuation. The theorem
below states that two paths with the same prefix therefore have the same next round point.
-/

/-- The prover's round point at depth `j` along challenge path `χ`. -/
def proverRoundPoint : {d : ℕ} → Prover F G d → (Fin d → F) → ℕ → Option (G × G)
  | 0, _, _, _ => none
  | _ + 1, .node L R _, _, 0 => some (L, R)
  | _ + 1, .node _ _ cont, χ, j + 1 => proverRoundPoint (cont (χ 0)) (Fin.tail χ) j

/-- The round point at depth `j` depends only on the first `j` challenges. -/
theorem proverRoundPoint_prefix : {d : ℕ} → (P : Prover F G d) → (χ χ' : Fin d → F) → (j : ℕ) →
    (∀ i : Fin d, (i : ℕ) < j → χ i = χ' i) →
    proverRoundPoint P χ j = proverRoundPoint P χ' j
  | 0, .leaf _ _, _, _, _, _ => rfl
  | _ + 1, .node _ _ _, _, _, 0, _ => rfl
  | _ + 1, .node _ _ cont, χ, χ', j + 1, h => by
      have h0 : χ 0 = χ' 0 := h 0 (Nat.succ_pos j)
      show proverRoundPoint (cont (χ 0)) (Fin.tail χ) j = proverRoundPoint (cont (χ' 0)) (Fin.tail χ') j
      rw [h0]
      exact proverRoundPoint_prefix (cont (χ' 0)) (Fin.tail χ) (Fin.tail χ') j
        (fun i hi => h i.succ (by simp only [Fin.val_succ]; omega))

/-! ## Sealing the module to the deployed derivation

The earlier lemmas use a reconstructed round transcript. `deriveChallenges_ipaRound_eq` proves that
the deployed schedule uses exactly that transcript, so any ordering change breaks the theorem.
-/

/-- The transcript prefix before the deployed IPA round fold begins. -/
def preIpaTranscript {shape : Shape} (init : List (TranscriptElt F G)) (ps : ProofString shape F G) :
    List (TranscriptElt F G) :=
  let t := init ++ absorbPoints2 ps.adviceCommitments ++ [.challenge]
  let t := t ++ absorbLookupPermuted ps.lookupPermutedInput ps.lookupPermutedTable ++ [.challenge]
  let t := t ++ [.challenge]
  let t := t ++ absorbPoints2 ps.permutationProduct ++ absorbPoints2 ps.lookupProduct
    ++ [TranscriptElt.point ps.vanishingRandom] ++ [.challenge]
  let t := t ++ absorbPoints ps.hPieces ++ [.challenge]
  let evalElts := absorbScalars2 ps.instanceEvals ++ absorbScalars2 ps.adviceEvals
    ++ absorbScalars ps.fixedEvals ++ [TranscriptElt.scalar ps.vanishingRandomEval]
    ++ absorbScalars ps.permutationCommonEvals
    ++ (List.ofFn (fun p => (List.ofFn (fun s => absorbPermSet (ps.permutationSetEvals p s))).flatten)).flatten
    ++ (List.ofFn (fun p => (List.ofFn (fun l => absorbLookup (ps.lookupEvals p l))).flatten)).flatten
  let t := t ++ evalElts ++ [.challenge]
  let t := t ++ [.challenge]
  let t := t ++ [TranscriptElt.point ps.multiopenQPrime] ++ [.challenge]
  let t := t ++ absorbScalars ps.multiopenU ++ [.challenge]
  let t := t ++ [TranscriptElt.point ps.ipaS] ++ [.challenge]
  let t := t ++ [.challenge]
  t

/-- The challenges produced by the deployed IPA `foldl`. -/
theorem ipaFold_challenges {ι : Type*} (fs : FiatShamir F G) (rp : ι → G × G)
    (L : List ι) (t₀ : List (TranscriptElt F G)) (us₀ : List F) :
    (L.foldl (fun st i =>
        (st.1 ++ [TranscriptElt.point (rp i).1, TranscriptElt.point (rp i).2, TranscriptElt.challenge],
          st.2 ++ [fs.squeeze (st.1 ++ [TranscriptElt.point (rp i).1, TranscriptElt.point (rp i).2,
            TranscriptElt.challenge])])) (t₀, us₀)).2
      = us₀ ++ (List.range L.length).map (fun m =>
          fs.squeeze (t₀ ++ ((L.take (m + 1)).map (fun i =>
            [TranscriptElt.point (rp i).1, TranscriptElt.point (rp i).2,
              TranscriptElt.challenge])).flatten)) := by
  induction L generalizing t₀ us₀ with
  | nil => simp
  | cons i L ih =>
      rw [List.foldl_cons, ih, List.length_cons, List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, List.take_succ_cons, List.take_zero, List.map_nil,
        List.flatten_cons, List.flatten_nil, Function.comp_def, List.append_assoc,
        List.cons_append, List.nil_append]

/-- Express `roundTranscript` as the base followed by the first `j + 1` absorb blocks. -/
theorem roundTranscript_eq_take (t₀ : List (TranscriptElt F G)) (rounds : ℕ → G × G) (j : ℕ) :
    roundTranscript t₀ rounds j
      = t₀ ++ ((List.range (j + 1)).map (fun i =>
          [TranscriptElt.point (rounds i).1, TranscriptElt.point (rounds i).2,
            TranscriptElt.challenge])).flatten := by
  induction j with
  | zero => simp [roundTranscript]
  | succ j ih =>
      rw [roundTranscript_succ, ih, List.range_succ (n := j + 1), List.map_append,
        List.flatten_append, List.append_assoc]
      simp

/-- The round-`j` transcript for a `Fin`-indexed round vector. -/
def roundTranscriptFin {k : ℕ} (t₀ : List (TranscriptElt F G)) (rounds : Fin k → G × G) (j : Fin k) :
    List (TranscriptElt F G) :=
  t₀ ++ (((List.finRange k).take (j.val + 1)).map (fun i =>
    [TranscriptElt.point (rounds i).1, TranscriptElt.point (rounds i).2,
      TranscriptElt.challenge])).flatten

private theorem length_flatten_map_triple {ι : Type*} (f g h : ι → TranscriptElt F G) :
    ∀ l : List ι, ((l.map (fun i => [f i, g i, h i])).flatten).length = 3 * l.length
  | [] => rfl
  | i :: l => by
      simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons,
        List.length_nil, length_flatten_map_triple f g h l]
      omega

/-- The round-`j` transcript extends the base by `3 · (j + 1)` elements. -/
theorem roundTranscriptFin_length {k : ℕ} (t₀ : List (TranscriptElt F G)) (rounds : Fin k → G × G)
    (j : Fin k) :
    (roundTranscriptFin t₀ rounds j).length = t₀.length + 3 * (j.val + 1) := by
  have hj := j.isLt
  simp only [roundTranscriptFin, List.length_append,
    length_flatten_map_triple (fun i => TranscriptElt.point (rounds i).1)
      (fun i => TranscriptElt.point (rounds i).2) (fun _ => TranscriptElt.challenge),
    List.length_take, List.length_finRange]
  omega

/-- Distinct rounds squeeze from distinct transcript prefixes. -/
theorem roundTranscriptFin_injective {k : ℕ} (t₀ : List (TranscriptElt F G))
    (rounds : Fin k → G × G) :
    Function.Injective (roundTranscriptFin t₀ rounds) := by
  intro a b h
  have hlen := congrArg List.length h
  rw [roundTranscriptFin_length, roundTranscriptFin_length] at hlen
  exact Fin.ext (by omega)

/-- The round-`j` transcript, split at its last absorb block: the base-and-earlier-rounds prefix,
then round `j`'s own `[L, R, marker]` block. The decomposition behind reading a round's committed
points off its own transcript (`roundTranscriptFin_getElem?_fst`/`_snd`) and truncating a
transcript to an earlier round (`roundTranscriptFin_take`). -/
theorem roundTranscriptFin_eq_append {k : ℕ} (t₀ : List (TranscriptElt F G))
    (rounds : Fin k → G × G) (j : Fin k) :
    roundTranscriptFin t₀ rounds j
      = (t₀ ++ (((List.finRange k).take j.val).map (fun i =>
          [TranscriptElt.point (rounds i).1, TranscriptElt.point (rounds i).2,
            TranscriptElt.challenge])).flatten)
        ++ [TranscriptElt.point (rounds j).1, TranscriptElt.point (rounds j).2,
            TranscriptElt.challenge] := by
  rw [roundTranscriptFin, List.take_succ, List.append_assoc]
  congr 1
  rw [List.map_append, List.flatten_append]
  congr 1
  rw [List.getElem?_eq_getElem (by simpa using j.isLt)]
  simp

/-- The pre-block prefix of the round-`j` transcript has length `t₀.length + 3 · j`. -/
theorem roundTranscriptFin_preBlock_length {k : ℕ} (t₀ : List (TranscriptElt F G))
    (rounds : Fin k → G × G) (j : Fin k) :
    (t₀ ++ (((List.finRange k).take j.val).map (fun i =>
        [TranscriptElt.point (rounds i).1, TranscriptElt.point (rounds i).2,
          TranscriptElt.challenge])).flatten).length = t₀.length + 3 * j.val := by
  rw [List.length_append,
    length_flatten_map_triple (fun i => TranscriptElt.point (rounds i).1)
      (fun i => TranscriptElt.point (rounds i).2) (fun _ => TranscriptElt.challenge),
    List.length_take, List.length_finRange]
  have := j.isLt
  omega

/-- The round-`j` transcript carries round `j`'s own `L` point at position `t₀.length + 3j` —
the committed cross-term is readable off the transcript prefix that squeezes its challenge. -/
theorem roundTranscriptFin_getElem?_fst {k : ℕ} (t₀ : List (TranscriptElt F G))
    (rounds : Fin k → G × G) (j : Fin k) :
    (roundTranscriptFin t₀ rounds j)[t₀.length + 3 * j.val]?
      = some (TranscriptElt.point (rounds j).1) := by
  rw [roundTranscriptFin_eq_append,
    List.getElem?_append_right (le_of_eq (roundTranscriptFin_preBlock_length t₀ rounds j)),
    roundTranscriptFin_preBlock_length]
  simp

/-- The round-`j` transcript carries round `j`'s own `R` point at position `t₀.length + 3j + 1`. -/
theorem roundTranscriptFin_getElem?_snd {k : ℕ} (t₀ : List (TranscriptElt F G))
    (rounds : Fin k → G × G) (j : Fin k) :
    (roundTranscriptFin t₀ rounds j)[t₀.length + 3 * j.val + 1]?
      = some (TranscriptElt.point (rounds j).2) := by
  rw [roundTranscriptFin_eq_append,
    List.getElem?_append_right (by rw [roundTranscriptFin_preBlock_length]; omega),
    roundTranscriptFin_preBlock_length,
    show t₀.length + 3 * j.val + 1 - (t₀.length + 3 * j.val) = 1 from by omega]
  simp

/-- Round transcripts grow by prefix: the round-`i` transcript is a prefix of the round-`j` one for
`i ≤ j` — the same rounds' blocks, truncated. -/
theorem roundTranscriptFin_prefix {k : ℕ} (t₀ : List (TranscriptElt F G))
    (rounds : Fin k → G × G) {i j : Fin k} (hij : i.val ≤ j.val) :
    roundTranscriptFin t₀ rounds i <+: roundTranscriptFin t₀ rounds j := by
  rw [roundTranscriptFin, roundTranscriptFin]
  have h1 : (List.finRange k).take (i.val + 1) <+: (List.finRange k).take (j.val + 1) := by
    rw [show (List.finRange k).take (i.val + 1)
        = ((List.finRange k).take (j.val + 1)).take (i.val + 1) from by
      rw [List.take_take, min_eq_left (by omega)]]
    exact List.take_prefix _ _
  obtain ⟨q, hq⟩ := h1.map (fun i =>
    [TranscriptElt.point (rounds i).1, TranscriptElt.point (rounds i).2,
      TranscriptElt.challenge])
  refine ⟨q.flatten, ?_⟩
  rw [List.append_assoc, ← List.flatten_append, hq]

/-- Truncating the round-`j` transcript at the round-`i` length recovers the round-`i` transcript:
the `chainAt` of the deployed prefix decode, computable by `List.take`. -/
theorem roundTranscriptFin_take {k : ℕ} (t₀ : List (TranscriptElt F G))
    (rounds : Fin k → G × G) {i j : Fin k} (hij : i.val ≤ j.val) :
    (roundTranscriptFin t₀ rounds j).take (t₀.length + 3 * (i.val + 1))
      = roundTranscriptFin t₀ rounds i := by
  have h := List.prefix_iff_eq_take.mp (roundTranscriptFin_prefix t₀ rounds hij)
  rw [roundTranscriptFin_length] at h
  exact h.symm

/-- The `Fin`-indexed round transcript equals the recursive `roundTranscript`. -/
theorem roundTranscriptFin_eq_roundTranscript {k : ℕ} (t₀ : List (TranscriptElt F G))
    (rounds : Fin k → G × G) (j : Fin k) :
    roundTranscriptFin t₀ rounds j
      = roundTranscript t₀ (fun i => rounds ⟨i % k, Nat.mod_lt _ j.pos⟩) j.val := by
  rw [roundTranscript_eq_take, roundTranscriptFin]
  congr 2
  apply List.ext_getElem
  · simp only [List.length_map, List.length_take, List.length_finRange, List.length_range]
    have := j.isLt
    omega
  · intro n h1 h2
    simp only [List.length_map, List.length_take, List.length_finRange, List.length_range] at h1 h2
    have hn : n < k := lt_of_lt_of_le (lt_min_iff.mp h1).1 (Nat.succ_le_of_lt j.isLt)
    simp only [List.getElem_map, List.getElem_take, List.getElem_finRange, List.getElem_range]
    refine congrArg (fun x => [TranscriptElt.point (rounds x).1, TranscriptElt.point (rounds x).2,
      TranscriptElt.challenge]) (Fin.ext ?_)
    simp [Nat.mod_eq_of_lt hn]

/-- The deployed round challenge is squeezed from the corresponding `roundTranscriptFin`.

This theorem pins the ordering model to `deriveChallenges`. -/
theorem deriveChallenges_ipaRound_eq {shape : Shape} [Zero F] (fs : FiatShamir F G)
    (init : List (TranscriptElt F G)) (ps : ProofString shape F G) (j : Fin shape.k) :
    (deriveChallenges fs init ps).ipaRound j
      = fs.squeeze (roundTranscriptFin (preIpaTranscript init ps) ps.ipaRounds j) := by
  simp only [deriveChallenges, preIpaTranscript, roundTranscriptFin]
  rw [ipaFold_challenges, List.nil_append, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by simp)]
  rfl

/-- Restate `deriveChallenges_ipaRound_eq` using `roundChallenge`. -/
theorem deriveChallenges_ipaRound_eq_roundChallenge {shape : Shape} [Zero F] (fs : FiatShamir F G)
    (init : List (TranscriptElt F G)) (ps : ProofString shape F G) (j : Fin shape.k) :
    (deriveChallenges fs init ps).ipaRound j
      = roundChallenge fs (preIpaTranscript init ps)
          (fun i => ps.ipaRounds ⟨i % shape.k, Nat.mod_lt _ j.pos⟩) j.val := by
  rw [deriveChallenges_ipaRound_eq, roundChallenge, roundTranscriptFin_eq_roundTranscript]

end Zcash.Snark
