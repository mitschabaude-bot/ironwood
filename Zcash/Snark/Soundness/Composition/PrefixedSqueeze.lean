import Zcash.Snark.Soundness.Composition.DeployedRuntime
import Zcash.Snark.Soundness.FiatShamir.PinnedSqueeze

/-!
# The prefixed `x` squeeze

The concrete constraint bad set reads the pre-`x` transcript and the four earlier Fiat–Shamir
answers.  These facts prove that the earlier points remain pinned when the `x` answer is
resampled, then price the resulting one-level bad-root event directly.  No multiopen rewind or
fourth-root continuation threshold is involved.
-/

namespace Zcash.Snark

open scoped ENNReal
open Classical

variable {shape : Shape}

/-- The eleven pre-IPA prefix lengths strictly increase: each stage absorbs before it squeezes. -/
theorem preIpaLen_strictMono (shape : Shape) (n0 : Nat) : StrictMono (preIpaLen shape n0) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro j
  fin_cases j <;> simp [preIpaLen]
  all_goals omega

/-- A squeeze point strictly before index `n` is a strict prefix of the index-`n` point. -/
theorem preIpaLen_lt_at (shape : Shape) (n0 : Nat) {i n : Fin 11} (hi : (i : Nat) < (n : Nat)) :
    preIpaLen shape n0 i < preIpaLen shape n0 n :=
  preIpaLen_strictMono shape n0 hi

/-- Every pre-`x` squeeze point is a strict prefix of the `x` squeeze point. -/
theorem preIpaLen_lt_x (shape : Shape) (n0 : Nat) {i : Fin 11} (hi : (i : Nat) < 4) :
    preIpaLen shape n0 i < preIpaLen shape n0 4 := by
  have hcase : (i : Nat) = 0 ∨ (i : Nat) = 1 ∨ (i : Nat) = 2 ∨ (i : Nat) = 3 := by omega
  rcases hcase with h | h | h | h
  · obtain rfl : i = ⟨0, by norm_num⟩ := Fin.ext h
    simp [preIpaLen]
    omega
  · obtain rfl : i = ⟨1, by norm_num⟩ := Fin.ext h
    simp [preIpaLen]
    omega
  · obtain rfl : i = ⟨2, by norm_num⟩ := Fin.ext h
    simp [preIpaLen]
    omega
  · obtain rfl : i = ⟨3, by norm_num⟩ := Fin.ext h
    simp [preIpaLen]

/-- Equal `x` squeeze points imply equal earlier squeeze points. -/
theorem algebraicFullPrefixesPre_eq_of_x_eq
    {basis : AugmentedIndex (2 ^ shape.k) -> VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (init : List (TranscriptElt Fp VestaG))
    (p q : AlgebraicWfProof basis vk instanceCommitment)
    (h : algebraicFullPrefixesPre init p 4 = algebraicFullPrefixesPre init q 4)
    {i : Fin 11} (hi : (i : Nat) < 4) :
    algebraicFullPrefixesPre init p i = algebraicFullPrefixesPre init q i := by
  apply Subtype.ext
  have hval : preIpaSqueezePoints init p.proof.1 4 = preIpaSqueezePoints init q.proof.1 4 :=
    congrArg Subtype.val h
  have hpreP := List.prefix_of_prefix_length_le
    (preIpaSqueezePoints_prefix init p.proof.1 i)
    (preIpaSqueezePoints_prefix init p.proof.1 4)
    (by
      rw [preIpaSqueezePoints_length_eq init p.proof.1 p.proof.2,
        preIpaSqueezePoints_length_eq init p.proof.1 p.proof.2]
      exact le_of_lt (preIpaLen_lt_x shape init.length hi))
  have hpreQ := List.prefix_of_prefix_length_le
    (preIpaSqueezePoints_prefix init q.proof.1 i)
    (preIpaSqueezePoints_prefix init q.proof.1 4)
    (by
      rw [preIpaSqueezePoints_length_eq init q.proof.1 q.proof.2,
        preIpaSqueezePoints_length_eq init q.proof.1 q.proof.2]
      exact le_of_lt (preIpaLen_lt_x shape init.length hi))
  show preIpaSqueezePoints init p.proof.1 i = preIpaSqueezePoints init q.proof.1 i
  rw [List.prefix_iff_eq_take.mp hpreP, List.prefix_iff_eq_take.mp hpreQ,
    preIpaSqueezePoints_length_eq init p.proof.1 p.proof.2,
    preIpaSqueezePoints_length_eq init q.proof.1 q.proof.2, hval]

/-- An earlier squeeze point differs from the `x` point because their lengths differ. -/
theorem algebraicFullPrefixesPre_ne_x
    {basis : AugmentedIndex (2 ^ shape.k) -> VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (init : List (TranscriptElt Fp VestaG))
    (p : AlgebraicWfProof basis vk instanceCommitment) {i : Fin 11} (hi : (i : Nat) < 4) :
    algebraicFullPrefixesPre init p i ≠ algebraicFullPrefixesPre init p 4 := by
  intro hEq
  have hlen : (preIpaSqueezePoints init p.proof.1 i).length =
      (preIpaSqueezePoints init p.proof.1 4).length :=
    congrArg (fun t : List (TranscriptElt Fp VestaG) => t.length) (congrArg Subtype.val hEq)
  rw [preIpaSqueezePoints_length_eq init p.proof.1 p.proof.2,
    preIpaSqueezePoints_length_eq init p.proof.1 p.proof.2] at hlen
  exact absurd hlen (Nat.ne_of_lt (preIpaLen_lt_x shape init.length hi))

/-- Equal squeeze points at index `n` imply equal squeeze points at every earlier index. -/
theorem algebraicFullPrefixesPre_eq_of_eq_at
    {basis : AugmentedIndex (2 ^ shape.k) -> VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (init : List (TranscriptElt Fp VestaG))
    (p q : AlgebraicWfProof basis vk instanceCommitment) {n : Fin 11}
    (h : algebraicFullPrefixesPre init p n = algebraicFullPrefixesPre init q n)
    {i : Fin 11} (hi : (i : Nat) < (n : Nat)) :
    algebraicFullPrefixesPre init p i = algebraicFullPrefixesPre init q i := by
  apply Subtype.ext
  have hval : preIpaSqueezePoints init p.proof.1 n = preIpaSqueezePoints init q.proof.1 n :=
    congrArg Subtype.val h
  have hpreP := List.prefix_of_prefix_length_le
    (preIpaSqueezePoints_prefix init p.proof.1 i)
    (preIpaSqueezePoints_prefix init p.proof.1 n)
    (by
      rw [preIpaSqueezePoints_length_eq init p.proof.1 p.proof.2,
        preIpaSqueezePoints_length_eq init p.proof.1 p.proof.2]
      exact le_of_lt (preIpaLen_lt_at shape init.length hi))
  have hpreQ := List.prefix_of_prefix_length_le
    (preIpaSqueezePoints_prefix init q.proof.1 i)
    (preIpaSqueezePoints_prefix init q.proof.1 n)
    (by
      rw [preIpaSqueezePoints_length_eq init q.proof.1 q.proof.2,
        preIpaSqueezePoints_length_eq init q.proof.1 q.proof.2]
      exact le_of_lt (preIpaLen_lt_at shape init.length hi))
  show preIpaSqueezePoints init p.proof.1 i = preIpaSqueezePoints init q.proof.1 i
  rw [List.prefix_iff_eq_take.mp hpreP, List.prefix_iff_eq_take.mp hpreQ,
    preIpaSqueezePoints_length_eq init p.proof.1 p.proof.2,
    preIpaSqueezePoints_length_eq init q.proof.1 q.proof.2, hval]

/-- An earlier squeeze point differs from the index-`n` point: their lengths differ. -/
theorem algebraicFullPrefixesPre_ne_at
    {basis : AugmentedIndex (2 ^ shape.k) -> VestaG}
    {vk : VerifyingKey shape Fp VestaG}
    {instanceCommitment : Fin shape.numProofs -> Nat -> VestaG}
    (init : List (TranscriptElt Fp VestaG))
    (p : AlgebraicWfProof basis vk instanceCommitment) {n i : Fin 11}
    (hi : (i : Nat) < (n : Nat)) :
    algebraicFullPrefixesPre init p i ≠ algebraicFullPrefixesPre init p n := by
  intro hEq
  have hlen : (preIpaSqueezePoints init p.proof.1 i).length =
      (preIpaSqueezePoints init p.proof.1 n).length :=
    congrArg (fun t : List (TranscriptElt Fp VestaG) => t.length) (congrArg Subtype.val hEq)
  rw [preIpaSqueezePoints_length_eq init p.proof.1 p.proof.2,
    preIpaSqueezePoints_length_eq init p.proof.1 p.proof.2] at hlen
  exact absurd hlen (Nat.ne_of_lt (preIpaLen_lt_at shape init.length hi))

open ComputedAlgebraicFSFamily in
/-- The pre-`x` transcript and earlier answers remain pinned while resampling `x`, so a bad-root
event at `x` costs only `(Q + 1) * epsilon`.

The discharge toolkit for `DeployedConstraintXSqueezeSchedule.pinned`: once the `x` prefix is
stable under reprogramming (`hstab`), the earlier answers are too — their squeeze points are
strict sub-prefixes. -/
theorem badX_le_via_squeeze_prefixed {T' : Type*} [DecidableEq T']
    (query : AugmentedIndex (2 ^ shape.k) -> T')
    (family : ComputedAlgebraicFSFamily shape)
    (goodX : (AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.Coins -> Prop)
    (badF : (AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) ->
      (Fin 4 -> Fp) -> Set Fp)
    (hstab : forall basis (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) (v : Fp),
      algebraicFullPrefixesPre family.init ((family.adversary basis).run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) 4) v)) 4 =
        algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 4)
    {epsilon : ENNReal}
    (hbad : forall basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badF basis t nu) <= epsilon)
    (hcontX : forall basis, {coins : family.Coins | ¬ goodX basis coins} <=
      {coins : family.Coins |
        coins (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run coins) 4) ∈
          badF basis (algebraicFullPrefixesPre family.init
              ((family.adversary basis).run coins) 4)
            (fun i : Fin 4 => coins (algebraicFullPrefixesPre family.init
              ((family.adversary basis).run coins) (i.castLE (by omega))))}) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          {q : (AugmentedIndex (2 ^ shape.k) -> VestaG) × family.Coins | ¬ goodX q.1 q.2})
      <= (family.Q + 1 : Nat) * epsilon := by
  have hset : (fun p : (↥(Set.range query) -> VestaG) × family.Coins =>
        (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
        {q : (AugmentedIndex (2 ^ shape.k) -> VestaG) × family.Coins | ¬ goodX q.1 q.2} =
      {x : (↥(Set.range query) -> VestaG) × family.Coins | x.2 ∈
        (fun setup => {coins : family.Coins |
          ¬ goodX (orchardGeneratorROBasis query setup) coins}) x.1} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [hset]
  refine independentProductPMF_fiber_bound (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype family.Coins)
    (fun setup => {coins : family.Coins |
      ¬ goodX (orchardGeneratorROBasis query setup) coins}) ?_
  intro setup
  set basis' := orchardGeneratorROBasis query setup with hbasis'
  refine le_trans (MeasureTheory.measure_mono (hcontX basis')) ?_
  refine xEscTable_measure_le (family.adversary basis')
    (fun p => algebraicFullPrefixesPre family.init p 4)
    (fun p O => badF basis' (algebraicFullPrefixesPre family.init p 4)
      (fun i : Fin 4 => O (algebraicFullPrefixesPre family.init p (i.castLE (by omega)))))
    ?_ (fun p O => hbad basis' _ _) (family.queryBound basis')
  intro O v
  have hx := hstab basis' O v
  show badF basis' (algebraicFullPrefixesPre family.init ((family.adversary basis').run
        (Function.update O (algebraicFullPrefixesPre family.init
          ((family.adversary basis').run O) 4) v)) 4)
      (fun i : Fin 4 => (Function.update O (algebraicFullPrefixesPre family.init
          ((family.adversary basis').run O) 4) v)
        (algebraicFullPrefixesPre family.init ((family.adversary basis').run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis').run O) 4) v)) (i.castLE (by omega)))) =
    badF basis' (algebraicFullPrefixesPre family.init ((family.adversary basis').run O) 4)
      (fun i : Fin 4 => O (algebraicFullPrefixesPre family.init
        ((family.adversary basis').run O) (i.castLE (by omega))))
  rw [hx]
  congr 1
  funext i
  rw [algebraicFullPrefixesPre_eq_of_x_eq family.init _ _ hx
      (show ((i.castLE (by omega) : Fin 11) : Nat) < 4 from i.isLt),
    Function.update_of_ne
      (algebraicFullPrefixesPre_ne_x family.init _
        (show ((i.castLE (by omega) : Fin 11) : Nat) < 4 from i.isLt))]

open ComputedAlgebraicFSFamily in
/-- **A bad-root event at any pre-IPA squeeze costs `(Q + 1) * epsilon`.**  The index-`n`
generalization of `badX_le_via_squeeze_prefixed`: once the index-`n` prefix is stable under
reprogramming (`hstab`), every earlier answer is too, because their squeeze points are strict
sub-prefixes.  Instantiate at `n = 3` for `y`, `n = 2` for `γ`, `n = 1` for `β`, `n = 0` for `θ`;
`n = 4` recovers the `x` statement. -/
theorem badAt_le_via_squeeze_prefixed {T' : Type*} [DecidableEq T'] (n : Fin 11)
    (query : AugmentedIndex (2 ^ shape.k) -> T')
    (family : ComputedAlgebraicFSFamily shape)
    (good : (AugmentedIndex (2 ^ shape.k) -> VestaG) -> family.Coins -> Prop)
    (badF : (AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) ->
      (Fin (n : Nat) -> Fp) -> Set Fp)
    (hstab : forall basis (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) (v : Fp),
      algebraicFullPrefixesPre family.init ((family.adversary basis).run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) n) v)) n =
        algebraicFullPrefixesPre family.init ((family.adversary basis).run O) n)
    {epsilon : ENNReal}
    (hbad : forall basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badF basis t nu) <= epsilon)
    (hcont : forall basis, {coins : family.Coins | ¬ good basis coins} <=
      {coins : family.Coins |
        coins (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run coins) n) ∈
          badF basis (algebraicFullPrefixesPre family.init
              ((family.adversary basis).run coins) n)
            (fun i : Fin (n : Nat) => coins (algebraicFullPrefixesPre family.init
              ((family.adversary basis).run coins)
              (i.castLE (le_of_lt n.isLt))))}) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype family.Coins)).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          {q : (AugmentedIndex (2 ^ shape.k) -> VestaG) × family.Coins | ¬ good q.1 q.2})
      <= (family.Q + 1 : Nat) * epsilon := by
  have hset : (fun p : (↥(Set.range query) -> VestaG) × family.Coins =>
        (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
        {q : (AugmentedIndex (2 ^ shape.k) -> VestaG) × family.Coins | ¬ good q.1 q.2} =
      {x : (↥(Set.range query) -> VestaG) × family.Coins | x.2 ∈
        (fun setup => {coins : family.Coins |
          ¬ good (orchardGeneratorROBasis query setup) coins}) x.1} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [hset]
  refine independentProductPMF_fiber_bound (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype family.Coins)
    (fun setup => {coins : family.Coins |
      ¬ good (orchardGeneratorROBasis query setup) coins}) ?_
  intro setup
  set basis' := orchardGeneratorROBasis query setup with hbasis'
  refine le_trans (MeasureTheory.measure_mono (hcont basis')) ?_
  refine xEscTable_measure_le (family.adversary basis')
    (fun p => algebraicFullPrefixesPre family.init p n)
    (fun p O => badF basis' (algebraicFullPrefixesPre family.init p n)
      (fun i : Fin (n : Nat) => O (algebraicFullPrefixesPre family.init p
        (i.castLE (le_of_lt n.isLt)))))
    ?_ (fun p O => hbad basis' _ _) (family.queryBound basis')
  intro O v
  have hx := hstab basis' O v
  show badF basis' (algebraicFullPrefixesPre family.init ((family.adversary basis').run
        (Function.update O (algebraicFullPrefixesPre family.init
          ((family.adversary basis').run O) n) v)) n)
      (fun i : Fin (n : Nat) => (Function.update O (algebraicFullPrefixesPre family.init
          ((family.adversary basis').run O) n) v)
        (algebraicFullPrefixesPre family.init ((family.adversary basis').run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis').run O) n) v))
          (i.castLE (le_of_lt n.isLt)))) =
    badF basis' (algebraicFullPrefixesPre family.init ((family.adversary basis').run O) n)
      (fun i : Fin (n : Nat) => O (algebraicFullPrefixesPre family.init
        ((family.adversary basis').run O) (i.castLE (le_of_lt n.isLt))))
  rw [hx]
  congr 1
  funext i
  rw [algebraicFullPrefixesPre_eq_of_eq_at family.init _ _ hx
      (show ((i.castLE (le_of_lt n.isLt) : Fin 11) : Nat) < (n : Nat) from i.isLt),
    Function.update_of_ne
      (algebraicFullPrefixesPre_ne_at family.init _
        (show ((i.castLE (le_of_lt n.isLt) : Fin 11) : Nat) < (n : Nat) from i.isLt))]

open ComputedAlgebraicFSFamily in
/-- **The table-level form of the index-`n` squeeze price.**  The semantic endpoint states its
`y`, `β`, `γ` and `θ` premises over oracle tables alone, so this states the
same `(Q + 1) * epsilon` bound at that measure.  It is the shorter statement: the coins-level form
above reduces to it through a tape fiber. -/
theorem badAt_table_le_via_squeeze_prefixed (n : Fin 11)
    (family : ComputedAlgebraicFSFamily shape)
    (basis : AugmentedIndex (2 ^ shape.k) -> VestaG)
    (badF : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) ->
      (Fin (n : Nat) -> Fp) -> Set Fp)
    (hstab : forall (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) (v : Fp),
      algebraicFullPrefixesPre family.init ((family.adversary basis).run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) n) v)) n =
        algebraicFullPrefixesPre family.init ((family.adversary basis).run O) n)
    {epsilon : ENNReal}
    (hbad : forall t nu, (PMF.uniformOfFintype Fp).toOuterMeasure (badF t nu) <= epsilon) :
    (PMF.uniformOfFintype (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)).toOuterMeasure
      {O | O (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) n) ∈
        badF (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) n)
          (fun i : Fin (n : Nat) => O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) (i.castLE (le_of_lt n.isLt))))}
      <= (family.Q + 1 : Nat) * epsilon := by
  refine xEscTable_measure_le (family.adversary basis)
    (fun p => algebraicFullPrefixesPre family.init p n)
    (fun p O => badF (algebraicFullPrefixesPre family.init p n)
      (fun i : Fin (n : Nat) => O (algebraicFullPrefixesPre family.init p
        (i.castLE (le_of_lt n.isLt)))))
    ?_ (fun p O => hbad _ _) (family.queryBound basis)
  intro O v
  have hx := hstab O v
  show badF (algebraicFullPrefixesPre family.init ((family.adversary basis).run
        (Function.update O (algebraicFullPrefixesPre family.init
          ((family.adversary basis).run O) n) v)) n)
      (fun i : Fin (n : Nat) => (Function.update O (algebraicFullPrefixesPre family.init
          ((family.adversary basis).run O) n) v)
        (algebraicFullPrefixesPre family.init ((family.adversary basis).run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) n) v))
          (i.castLE (le_of_lt n.isLt)))) =
    badF (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) n)
      (fun i : Fin (n : Nat) => O (algebraicFullPrefixesPre family.init
        ((family.adversary basis).run O) (i.castLE (le_of_lt n.isLt))))
  rw [hx]
  congr 1
  funext i
  rw [algebraicFullPrefixesPre_eq_of_eq_at family.init _ _ hx
      (show ((i.castLE (le_of_lt n.isLt) : Fin 11) : Nat) < (n : Nat) from i.isLt),
    Function.update_of_ne
      (algebraicFullPrefixesPre_ne_at family.init _
        (show ((i.castLE (le_of_lt n.isLt) : Fin 11) : Nat) < (n : Nat) from i.isLt))]

/-- The basis/table pairs whose index-`n` squeeze answer lands in a per-run bad set.  This is the
shape the semantic endpoint's `badY`, `badBeta`, `badGamma` and `badTheta` take. -/
def squeezeSurfaceEvent (n : Fin 11) (family : ComputedAlgebraicFSFamily shape)
    (badF : (AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) ->
      (Fin (n : Nat) -> Fp) -> Set Fp) :
    Set ((AugmentedIndex (2 ^ shape.k) -> VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp)) :=
  {q | q.2 (algebraicFullPrefixesPre family.init ((family.adversary q.1).run q.2) n) ∈
    badF q.1 (algebraicFullPrefixesPre family.init ((family.adversary q.1).run q.2) n)
      (fun i : Fin (n : Nat) => q.2 (algebraicFullPrefixesPre family.init
        ((family.adversary q.1).run q.2) (i.castLE (le_of_lt n.isLt))))}

open ComputedAlgebraicFSFamily in
/-- **A semantic surface costs `(Q + 1) * epsilon`.**  Each basis pays the index-`n` squeeze price
of `badAt_table_le_via_squeeze_prefixed`, and the generator random oracle's basis draw is averaged
over.  Instantiate at `n = 3` for `y`, `2` for `γ`, `1` for `β`, `0` for `θ` to obtain the four
premises the semantic endpoint takes. -/
theorem squeezeSurfaceEvent_prob_le {T' : Type*} [DecidableEq T'] (n : Fin 11)
    (query : AugmentedIndex (2 ^ shape.k) -> T')
    (family : ComputedAlgebraicFSFamily shape)
    (badF : (AugmentedIndex (2 ^ shape.k) -> VestaG) ->
      BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k) ->
      (Fin (n : Nat) -> Fp) -> Set Fp)
    (hstab : forall basis (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) (v : Fp),
      algebraicFullPrefixesPre family.init ((family.adversary basis).run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) n) v)) n =
        algebraicFullPrefixesPre family.init ((family.adversary basis).run O) n)
    {epsilon : ENNReal}
    (hbad : forall basis t nu,
      (PMF.uniformOfFintype Fp).toOuterMeasure (badF basis t nu) <= epsilon) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹'
          squeezeSurfaceEvent n family badF)
      <= (family.Q + 1 : Nat) * epsilon := by
  have hset : (fun p : (↥(Set.range query) -> VestaG) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) =>
        (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' squeezeSurfaceEvent n family badF =
      {x : (↥(Set.range query) -> VestaG) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp) | x.2 ∈
        (fun setup => {O | O (algebraicFullPrefixesPre family.init
            ((family.adversary (orchardGeneratorROBasis query setup)).run O) n) ∈
          badF (orchardGeneratorROBasis query setup)
            (algebraicFullPrefixesPre family.init
              ((family.adversary (orchardGeneratorROBasis query setup)).run O) n)
            (fun i : Fin (n : Nat) => O (algebraicFullPrefixesPre family.init
              ((family.adversary (orchardGeneratorROBasis query setup)).run O)
              (i.castLE (le_of_lt n.isLt))))}) x.1} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_setOf_eq, squeezeSurfaceEvent]
  rw [hset]
  refine independentProductPMF_fiber_bound (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype (BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) -> Fp))
    (fun setup => {O | O (algebraicFullPrefixesPre family.init
        ((family.adversary (orchardGeneratorROBasis query setup)).run O) n) ∈
      badF (orchardGeneratorROBasis query setup)
        (algebraicFullPrefixesPre family.init
          ((family.adversary (orchardGeneratorROBasis query setup)).run O) n)
        (fun i : Fin (n : Nat) => O (algebraicFullPrefixesPre family.init
          ((family.adversary (orchardGeneratorROBasis query setup)).run O)
          (i.castLE (le_of_lt n.isLt))))}) ?_
  intro setup
  exact badAt_table_le_via_squeeze_prefixed n family (orchardGeneratorROBasis query setup)
    (badF (orchardGeneratorROBasis query setup))
    (hstab (orchardGeneratorROBasis query setup))
    (fun t nu => hbad (orchardGeneratorROBasis query setup) t nu)

/-! ## Discharging the stability input

`badX_le_via_squeeze_prefixed`'s `hstab` is resampling-shaped: updating the oracle at the run's own `x` squeeze
point leaves the point unchanged. For a Fiat–Shamir prover this is a consequence of a more
natural property — the pre-`x` prefix reads only answers at strictly shorter transcripts — and
that property implies `hstab` outright: the update point has exactly the `x` prefix's length, so
no strictly shorter answer moves. -/

/-- **Fiat–Shamir prefix-determinism at index `n`.** The adversary's index-`n` squeeze point reads
only oracle answers at transcripts strictly shorter than that prefix, so two tables agreeing below
that length produce the same point.  Every sequential Fiat–Shamir prover has this shape. -/
def PrefixDeterminedAt (family : ComputedAlgebraicFSFamily shape) (n : Fin 11) : Prop :=
  ∀ basis (O O' : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp),
    (∀ t : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k),
      t.val.length < preIpaLen shape family.init.length n → O t = O' t) →
    algebraicFullPrefixesPre family.init ((family.adversary basis).run O) n
      = algebraicFullPrefixesPre family.init ((family.adversary basis).run O') n

/-- Prefix-determinism at `n` discharges the index-`n` stability input of
`badAt_le_via_squeeze_prefixed`: the update point is that prefix itself, of exactly its own
length, so every strictly shorter answer is untouched. -/
theorem hstab_of_prefixDeterminedAt (family : ComputedAlgebraicFSFamily shape) (n : Fin 11)
    (hdet : PrefixDeterminedAt family n) :
    ∀ basis (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) (v : Fp),
      algebraicFullPrefixesPre family.init ((family.adversary basis).run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) n) v)) n
        = algebraicFullPrefixesPre family.init ((family.adversary basis).run O) n := by
  intro basis O v
  refine hdet basis _ O ?_
  intro t ht
  rw [Function.update_apply, if_neg]
  intro hEq
  have hlen : (algebraicFullPrefixesPre family.init
      ((family.adversary basis).run O) n).val.length
      = preIpaLen shape family.init.length n :=
    preIpaSqueezePoints_length_eq family.init _
      ((family.adversary basis).run O).proof.2 n
  rw [hEq, hlen] at ht
  exact lt_irrefl _ ht

/-- **Fiat–Shamir prefix-determinism.** The adversary's `x` squeeze point reads only oracle
answers at transcripts strictly shorter than the `x` prefix: two tables agreeing below that
length produce the same `x` squeeze point. Every sequential Fiat–Shamir prover has this shape —
its pre-`x` commitments are functions of the earlier challenges alone. -/
def XPrefixDetermined (family : ComputedAlgebraicFSFamily shape) : Prop :=
  ∀ basis (O O' : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp),
    (∀ t : BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k),
      t.val.length < preIpaLen shape family.init.length 4 → O t = O' t) →
    algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 4
      = algebraicFullPrefixesPre family.init ((family.adversary basis).run O') 4

/-- Prefix-determinism discharges the squeeze-point stability input: the update point is the `x`
prefix itself, of exactly the `x` prefix's length, so every strictly shorter answer is untouched
and the determinism hypothesis applies. -/
theorem hstab_of_xPrefixDetermined (family : ComputedAlgebraicFSFamily shape)
    (hdet : XPrefixDetermined family) :
    ∀ basis (O : BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) (v : Fp),
      algebraicFullPrefixesPre family.init ((family.adversary basis).run
          (Function.update O (algebraicFullPrefixesPre family.init
            ((family.adversary basis).run O) 4) v)) 4
        = algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 4 := by
  intro basis O v
  refine hdet basis _ O ?_
  intro t ht
  rw [Function.update_apply, if_neg]
  intro hEq
  have hlen : (algebraicFullPrefixesPre family.init
      ((family.adversary basis).run O) 4).val.length
      = preIpaLen shape family.init.length 4 :=
    preIpaSqueezePoints_length_eq family.init _
      ((family.adversary basis).run O).proof.2 4
  rw [hEq, hlen] at ht
  exact lt_irrefl _ ht

end Zcash.Snark
