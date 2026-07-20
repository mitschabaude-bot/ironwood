import Zcash.Snark.Soundness.Forking.Adversary

/-!
# Minimal adaptive Fiat--Shamir interface

This module contains only the deployed interfaces needed by the executable recursive extractor:
the round-prefix decoder, the full-record attack event, the adaptive `z = 0` loss, and the bounded
transcript oracle domain. It does not build a separate propositional extraction ladder.
-/

namespace Zcash.Snark

open scoped ENNReal

/-- Decode a transcript point's round and its earlier round-prefix chain. -/
structure PrefixDecode (T : Type*) {P : Type*} (k : ℕ) (prefixes : P → Fin k → T) where
  roundOf : T → ℕ
  chainAt : T → Fin k → T
  roundOf_prefixes : ∀ p (j : Fin k), roundOf (prefixes p j) = (j : ℕ)
  chainAt_prefixes : ∀ p (j i : Fin k), (i : ℕ) ≤ (j : ℕ) →
    chainAt (prefixes p j) i = prefixes p i
  chainAt_ne : ∀ t (i : Fin k), (i : ℕ) < roundOf t → chainAt t i ≠ t

section AdaptiveGame

variable {T F P : Type*} [Fintype T] [DecidableEq T] [Fintype F] [Nonempty F] [Zero F]
  {m k : ℕ}

/-- The adversary's output is checked using every pre-IPA and IPA challenge read from the same
oracle table at that output's own transcript prefixes. -/
def fsWinsFull (A : OracleComp T F P) (accept : P → (Fin m → F) → (Fin k → F) → Prop)
    (prefixesPre : P → Fin m → T) (prefixes : P → Fin k → T) (O : T → F) : Prop :=
  accept (A.run O) (fun i => O (prefixesPre (A.run O) i)) (fun j => O (prefixes (A.run O) j))

open Classical in
/-- The slice on which one adversary-chosen pre-IPA challenge is zero has probability at most
`(Q+1)/|F|`. The extra query reads that challenge from the output's own prefix. -/
theorem fsAdvantageFull_zero_slice_le (A : OracleComp T F P)
    (accept : P → (Fin m → F) → (Fin k → F) → Prop)
    (prefixesPre : P → Fin m → T) (prefixes : P → Fin k → T) (i : Fin m)
    {Q : ℕ} (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure
        {O | fsWinsFull A accept prefixesPre prefixes O ∧
          O (prefixesPre (A.run O) i) = 0}
      ≤ (Q + 1 : ℕ) * (1 / Fintype.card F) := by
  set esc : T → (T → F) → Set F := fun _ _ => {0} with hesc_def
  have hblind : ∀ (t : T) (O : T → F) (v : F), esc t (Function.update O t v) = esc t O :=
    fun _ _ _ => rfl
  have hesc : ∀ t O, (PMF.uniformOfFintype F).toOuterMeasure (esc t O) ≤
      1 / Fintype.card F :=
    fun _ _ => le_of_eq (uniformOfFintype_toOuterMeasure_singleton 0)
  set zc : P → Fin 1 → T := fun p _ => prefixesPre p i with hzc_def
  have hsub : {O : T → F | fsWinsFull A accept prefixesPre prefixes O ∧
      O (prefixesPre (A.run O) i) = 0} ⊆
      {O : T → F | (A.completing zc).escapesDuringC esc O} := by
    intro O hO
    exact OracleComp.escapesDuringC_completing esc zc (j := 0)
      (show O (zc (A.run O) 0) ∈ esc (zc (A.run O) 0) O from
        Set.mem_singleton_iff.mpr hO.2)
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  exact escapesDuringC_measure_le' esc hblind hesc (OracleComp.queryBound_completing zc hQ)

end AdaptiveGame

/-- Extend a round-prefix decoder with the pre-IPA prefix chain available at each round point. -/
structure FullDecode (T : Type*) {P : Type*} (m k : ℕ) (prefixesPre : P → Fin m → T)
    (prefixes : P → Fin k → T) extends PrefixDecode T k prefixes where
  chainPre : T → Fin m → T
  guard : T → Prop
  guard_prefixes : ∀ p (j : Fin k), guard (prefixes p j)
  chainPre_prefixes : ∀ p (j : Fin k) (i : Fin m), chainPre (prefixes p j) i = prefixesPre p i
  chainPre_ne : ∀ t, guard t → ∀ i : Fin m, chainPre t i ≠ t

instance {F G : Type*} [Finite F] [Finite G] : Finite (TranscriptElt F G) :=
  Finite.of_injective (fun e => match e with
    | .point g => Sum.inl g
    | .scalar f => Sum.inr (some f)
    | .challenge => Sum.inr none)
    (by intro a b h; cases a <;> cases b <;> simp_all)

/-- The finite random-oracle domain of transcripts with length at most `L`. -/
def BTranscript (F G : Type*) (L : ℕ) : Type _ := {l : List (TranscriptElt F G) // l.length ≤ L}

namespace BTranscript

instance {F G : Type*} [DecidableEq F] [DecidableEq G] {L : ℕ} :
    DecidableEq (BTranscript F G L) := fun a b =>
  decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm

instance {F G : Type*} [Finite F] [Finite G] {L : ℕ} : Finite (BTranscript F G L) := by
  refine Finite.of_injective (fun t => (fun i : Fin L => t.val[(i : ℕ)]?)) ?_
  intro a b h
  apply Subtype.ext
  apply List.ext_getElem?
  intro n
  by_cases hn : n < L
  · exact congrFun h ⟨n, hn⟩
  · rw [List.getElem?_eq_none (le_trans a.prop (not_lt.mp hn)),
      List.getElem?_eq_none (le_trans b.prop (not_lt.mp hn))]

noncomputable instance {F G : Type*} [Finite F] [Finite G] {L : ℕ} :
    Fintype (BTranscript F G L) := Fintype.ofFinite _

end BTranscript

end Zcash.Snark
