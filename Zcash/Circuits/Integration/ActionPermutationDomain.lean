import Zcash.Circuits.Integration.ActionPermutationDomainCompute
import Zcash.Circuits.Integration.ActionPermutationColumns
import Zcash.Circuits.Integration.PermutationCompiler
import Zcash.Snark.Soundness.Canonical.ConstraintModel
import Zcash.Circuits.Integration.TopLevelAssignment
import Zcash.Circuits.Integration.TopLevelConstraintModel

/-!
# Action permutation domain and verifier layout

This module discharges the domain and chunk-layout premises retained by the
generic permutation semantics for the verifying key derived from
`actionCircuit`.

The keygen permutation itself belongs to the separate replay/assembly layer.
`cycleOfKeygenColumns` therefore accepts `fullSigma`, its active restriction,
the restriction equation, and the common-column identification explicitly.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (deltaFp omegaOf omegaOf_isPrimitiveRoot powFast_eq_pow scalarFieldOrder)

open CompPoly.CPolynomial
open Halo2
open Zcash.Arithmetic
  (deltaFp deltaFp_ne_zero deltaFpOrder deltaFp_isPrimitiveRoot
    deltaFp_powers_injective omegaOf omegaOf_isPrimitiveRoot scalarFieldOrder)
open Zcash.Circuits.Action (actionCircuit)

namespace ActionPermutationDomain

variable {G : Type} [AddCommGroup G] [Inhabited G]

abbrev actionShape (pp : Keygen.ProofParams) : Shape :=
  pp.mergeDerived actionCircuit

abbrev actionVk (pp : Keygen.ProofParams) (urs : URS G) :
    VerifyingKey (actionShape pp) Zcash.Circuits.Fp G :=
  Halo2.TopLevelCircuit.toVerifierKey
    actionCircuit pp urs

set_option maxRecDepth 100000 in
/-- The derived Action VK has one verifier permutation set per chunk. -/
theorem chunkCount (pp : Keygen.ProofParams) (urs : URS G) :
    (actionVk pp urs).permutationChunks.length =
      (actionShape pp).numPermutationSets := by
  rw [actionCircuit.toVerifierKey_permutationChunks,
    Keygen.ProofParams.mergeDerived_numPermutationSets]
  exact verifierCS_permutationChunks_length actionCircuit

set_option maxRecDepth 100000 in
/-- Every derived Action permutation chunk has width at most `vk.chunkLen`. -/
theorem chunkLength_le (pp : Keygen.ProofParams) (urs : URS G) :
    ∀ i, i < (actionShape pp).numPermutationSets →
      ((actionVk pp urs).permutationChunks.getD i []).length ≤
        (actionVk pp urs).chunkLen := by
  intro i hi
  change
    (actionCircuit.verifierCS.permutationChunks.getD i []).length ≤
      actionCircuit.chunkLen
  have hiChunks :
      i < actionCircuit.verifierCS.permutationChunks.length := by
    rw [verifierCS_permutationChunks_length]
    simpa only [actionShape,
      Keygen.ProofParams.mergeDerived_numPermutationSets] using hi
  rw [verifierCS_permutationChunks_getD_length actionCircuit i hiChunks]
  exact min_le_left _ _

/-- Resolver pairing preserves each concrete VK chunk's width. -/
theorem resolverPairsLength_le
    (pp : Keygen.ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (p : Fin pp.numProofs) :
    ∀ i, i < actionCircuit.permutationSetCount →
      (ResolverPermutationPairs (actionVk pp urs) poly p i).length ≤
        (actionVk pp urs).chunkLen := by
  intro i hi
  simpa [ResolverPermutationPairs, permutationChunkPairsOfResolver] using
    chunkLength_le pp urs i hi

set_option maxRecDepth 100000 in
/-- A resolver-backed chunk has exactly the compiler-derived suffix width. -/
theorem resolverPairsLength_eq_min
    (pp : Keygen.ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (p : Fin pp.numProofs)
    (chunk : Fin actionCircuit.permutationSetCount) :
    (ResolverPermutationPairs (actionVk pp urs) poly p chunk).length =
      min (actionVk pp urs).chunkLen
        (actionCircuit.permutationColumnCount -
          (chunk : ℕ) * (actionVk pp urs).chunkLen) := by
  simp only [ResolverPermutationPairs,
    permutationChunkPairsOfResolver, List.length_map]
  have hi :
      (chunk : ℕ) < actionCircuit.verifierCS.permutationChunks.length := by
    rw [verifierCS_permutationChunks_length]
    exact chunk.isLt
  change
    (actionCircuit.verifierCS.permutationChunks.getD chunk []).length =
      min actionCircuit.chunkLen
        (actionCircuit.permutationColumnCount -
          (chunk : ℕ) *
            actionCircuit.chunkLen)
  exact verifierCS_permutationChunks_getD_length actionCircuit chunk hi

set_option maxRecDepth 100000 in
/-- Every chunk value reference selects an in-range rotation-zero query-layout
entry, and every common-permutation index is in range. -/
theorem routingCoherent_of_derived
    (pp : Keygen.ProofParams) (urs : URS G) :
    PermutationChunkRoutingCoherent (actionVk pp urs) := by
  have hadviceLayout :
      (actionVk pp urs).adviceQueryLayout =
        actionCircuit.adviceQueryLayout :=
    actionCircuit.toVerifierKey_adviceQueryLayout pp urs
  have hfixedLayout :
      (actionVk pp urs).fixedQueryLayout =
        actionCircuit.fixedQueryLayout :=
    actionCircuit.toVerifierKey_fixedQueryLayout pp urs
  have hinstanceLayout :
      (actionVk pp urs).instanceQueryLayout =
        actionCircuit.instanceQueryLayout :=
    actionCircuit.toVerifierKey_instanceQueryLayout pp urs
  rintro chunk hchunk ⟨ref, common⟩ href
  have hroute := routingCoherent chunk hchunk (ref, common) href
  rcases hroute with ⟨hrefCoherent, hcommon⟩
  constructor
  · cases ref with
    | advice i =>
        rcases hrefCoherent with ⟨hi, hrotation⟩
        change PermutationColumnRef.Coherent
          (actionVk pp urs) (.advice i)
        simp only [PermutationColumnRef.Coherent]
        refine ⟨?_, ?_, ?_⟩
        · simpa only [actionShape,
            Keygen.ProofParams.mergeDerived_numAdviceQueries,
            TopLevelCircuit.adviceQueryCount] using hi
        · simpa only [hadviceLayout] using hi
        · simpa only [hadviceLayout] using hrotation
    | fixed i =>
        rcases hrefCoherent with ⟨hi, hrotation⟩
        change PermutationColumnRef.Coherent
          (actionVk pp urs) (.fixed i)
        simp only [PermutationColumnRef.Coherent]
        refine ⟨?_, ?_, ?_⟩
        · simpa only [actionShape,
            Keygen.ProofParams.mergeDerived_numFixedQueries,
            TopLevelCircuit.fixedQueryCount] using hi
        · simpa only [hfixedLayout] using hi
        · simpa only [hfixedLayout] using hrotation
    | «instance» i =>
        rcases hrefCoherent with ⟨hi, hrotation⟩
        change PermutationColumnRef.Coherent
          (actionVk pp urs) (.instance i)
        simp only [PermutationColumnRef.Coherent]
        refine ⟨?_, ?_, ?_⟩
        · simpa only [actionShape,
            Keygen.ProofParams.mergeDerived_numInstanceQueries,
            TopLevelCircuit.instanceQueryCount] using hi
        · simpa only [hinstanceLayout] using hi
        · simpa only [hinstanceLayout] using hrotation
  · simpa [actionShape, Keygen.ProofParams.mergeDerived] using hcommon

/--
Flattening the derived verifier chunks and decoding their query references
recovers the compiler's original permutation-column order.
-/
theorem permutationColumnAddresses_eq
    (pp : Keygen.ProofParams) (urs : URS G) :
    ((actionVk pp urs).permutationChunks.flatten.map
        (fun reference =>
          permutationColumnAddress (actionVk pp urs) reference.1)) =
      (Keygen.permColsOf
        actionCircuit.constraintSystem).map
          Halo2.Layout.ColRef.toAny := by
  exact topLevelPermutationColumnAddresses_eq
    actionCircuit pp urs
      (routingCoherent_of_derived pp urs)

/-! ## Pasta permutation-name cosets -/

/-- The odd factor of `|Fpˣ|`, after removing Pasta's `2^32` root-of-unity
subgroup. -/
abbrev pastaOddFactor : ℕ := deltaFpOrder

theorem scalarFieldOrder_sub_one_factorization :
    2 ^ 32 * pastaOddFactor = scalarFieldOrder - 1 := by
  norm_num [pastaOddFactor, scalarFieldOrder,
    deltaFpOrder, CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]

/-- `deltaFp = 5^(2^32)` lies in the odd-order factor of `Fpˣ`. -/
theorem deltaFp_pow_pastaOddFactor :
    deltaFp ^ pastaOddFactor = 1 := by
  exact deltaFp_isPrimitiveRoot.pow_eq_one

theorem pastaOddFactor_coprime_domain (k : ℕ) :
    Nat.Coprime (2 ^ k) pastaOddFactor := by
  apply Nat.Coprime.pow_left
  exact Odd.coprime_two_left (by
    norm_num [pastaOddFactor, deltaFpOrder, scalarFieldOrder,
      CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])

/-- Every supported prefix of the permutation-column names `deltaFp^j`
occupies distinct cosets of a supported Pasta evaluation subgroup. -/
theorem deltaFp_domainCosets
    {k n : ℕ} (hk : k ≤ 32) (hn : n ≤ pastaOddFactor)
    (j j' : Fin n) (t : ℕ)
    (h :
      deltaFp ^ (j : ℕ) =
        omegaOf k ^ t * deltaFp ^ (j' : ℕ)) :
    j = j' := by
  have hj :
      (deltaFp ^ (j : ℕ)) ^ pastaOddFactor = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul,
      deltaFp_pow_pastaOddFactor, one_pow]
  have hj' :
      (deltaFp ^ (j' : ℕ)) ^ pastaOddFactor = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul,
      deltaFp_pow_pastaOddFactor, one_pow]
  have hpow := congrArg (fun x : Fp => x ^ pastaOddFactor) h
  change (deltaFp ^ (j : ℕ)) ^ pastaOddFactor =
    (omegaOf k ^ t * deltaFp ^ (j' : ℕ)) ^ pastaOddFactor at hpow
  rw [hj, mul_pow, hj', _root_.mul_one] at hpow
  have htMul : omegaOf k ^ (t * pastaOddFactor) = 1 := by
    rw [pow_mul]
    exact hpow.symm
  have hprimitive : IsPrimitiveRoot (omegaOf k) (2 ^ k) :=
    omegaOf_isPrimitiveRoot k hk
  have hdvdMul : 2 ^ k ∣ t * pastaOddFactor :=
    (hprimitive.pow_eq_one_iff_dvd _).mp htMul
  have hdvd : 2 ^ k ∣ t :=
    (pastaOddFactor_coprime_domain k).dvd_of_dvd_mul_right hdvdMul
  have ht : omegaOf k ^ t = 1 :=
    (hprimitive.pow_eq_one_iff_dvd _).mpr hdvd
  rw [ht, _root_.one_mul] at h
  exact deltaFp_powers_injective n hn h

/-! ## Derived evaluation-domain facts -/

theorem rowsInjective (pp : Keygen.ProofParams) (urs : URS G) :
    Function.Injective fun i : Fin (actionVk pp urs).n =>
      (actionVk pp urs).omega ^ (i : ℕ) := by
  change Function.Injective fun i :
      Fin (2 ^ actionCircuit.domainExponent) =>
    omegaOf actionCircuit.domainExponent ^ (i : ℕ)
  exact TopLevelAssignment.domainRowsInjective domainExponent_lt

theorem root (pp : Keygen.ProofParams) (urs : URS G) :
    (actionVk pp urs).omega ^ (actionVk pp urs).n = 1 := by
  change omegaOf actionCircuit.domainExponent ^
    (2 ^ actionCircuit.domainExponent) = 1
  exact TopLevelAssignment.domainRoot domainExponent_lt

/-- The active permutation prefix ends at the last usable Action row. -/
abbrev activeRows (pp : Keygen.ProofParams) (urs : URS G) : ℕ :=
  (actionVk pp urs).n - (actionVk pp urs).blindingFactors - 1

theorem activeRows_le (pp : Keygen.ProofParams) (urs : URS G) :
    activeRows pp urs ≤ (actionVk pp urs).n := by
  unfold activeRows
  omega

/-- Canonical selectors and the derived usable-row count form the complete
generic permutation-domain record. In particular its `lastRotation` field is
the verifier's `omega^(-(blindingFactors + 1))` rotation. -/
theorem domain
    (pp : Keygen.ProofParams) (urs : URS G)
    (ch : Challenges actionCircuit.domainExponent Fp)
    (poly : CommitmentId → CPoly) :
    let model :=
      actionCircuit.constraintModel pp urs ch poly
    ResolverPermutationDomain (actionVk pp urs)
      model.l0 model.lLast model.lBlind
      (actionVk pp urs).n
      ((actionVk pp urs).n - (actionVk pp urs).blindingFactors - 1) := by
  exact ResolverPermutationDomain.ofCanonicalConstraintModel
    (actionVk pp urs) ch poly
      (actionCircuit.toVerifierKey_blindingFactors_lt_n pp urs)
      (rowsInjective pp urs) (root pp urs)
      (chunkCount pp urs)

/-- The last usable Action row is exactly the verifier's negative rotation. -/
theorem lastRowRotation (pp : Keygen.ProofParams) (urs : URS G) :
    (actionVk pp urs).omega ^
        ((actionVk pp urs).n - (actionVk pp urs).blindingFactors - 1) =
      (actionVk pp urs).omega ^
        (-(((actionVk pp urs).blindingFactors : ℤ) + 1)) := by
  let ch : Challenges actionCircuit.domainExponent Fp :=
    { theta := 0
      beta := 0
      gamma := 0
      y := 0
      x := 0
      x1 := 0
      x2 := 0
      x3 := 0
      x4 := 0
      xi := 0
      z := 0
      ipaRound := fun _ => 0 }
  let poly : CommitmentId → CPoly := fun _ => 0
  exact (domain pp urs ch poly).lastRotation

set_option maxRecDepth 100000 in
/-- Action chunk names are injective on any active prefix of the derived
evaluation domain. This is the `hnames` premise retained by
`ResolverPermutationCycle.ofKeygenColumns`. -/
theorem namesInjective
    (pp : Keygen.ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (p : Fin pp.numProofs)
    {activeRows : ℕ} (hactive : activeRows ≤ (actionVk pp urs).n) :
    Function.Injective fun c :
        ResolverPermutationCell (actionVk pp urs) poly p activeRows =>
      chunkRowName (actionVk pp urs).omega (actionVk pp urs).delta
        (actionVk pp urs).chunkLen c.1 c.2.1 c.2.2 := by
  have hfull :
      Function.Injective fun c :
          ResolverPermutationCell (actionVk pp urs) poly p
            (actionVk pp urs).n =>
        chunkRowName (actionVk pp urs).omega (actionVk pp urs).delta
          (actionVk pp urs).chunkLen c.1 c.2.1 c.2.2 := by
    apply chunkRowName_injective_of_actual_coset
    · intro j
      apply pow_ne_zero
      exact deltaFp_ne_zero
    · exact root pp urs
    · intro i i' hi hi' heq
      have hfin :
          (⟨i, hi⟩ : Fin (actionVk pp urs).n) =
            ⟨i', hi'⟩ :=
        rowsInjective pp urs heq
      exact Fin.ext_iff.mp hfin
    · intro j j' t hcoset
      change
        deltaFp ^
            ((j.1 : ℕ) *
              actionCircuit.chunkLen +
              (j.2 : ℕ)) =
          omegaOf actionCircuit.domainExponent ^ t *
            deltaFp ^
              ((j'.1 : ℕ) *
                actionCircuit.chunkLen +
                (j'.2 : ℕ)) at hcoset
      have hjWidth :
          (j.2 : ℕ) <
            min (actionVk pp urs).chunkLen
              (actionCircuit.permutationColumnCount -
                (j.1 : ℕ) * (actionVk pp urs).chunkLen) := by
        simpa only [resolverPairsLength_eq_min pp urs poly p j.1] using
          j.2.isLt
      have hj'Width :
          (j'.2 : ℕ) <
            min (actionVk pp urs).chunkLen
              (actionCircuit.permutationColumnCount -
                (j'.1 : ℕ) * (actionVk pp urs).chunkLen) := by
        simpa only [resolverPairsLength_eq_min pp urs poly p j'.1] using
          j'.2.isLt
      change
        (j.2 : ℕ) <
          min actionCircuit.chunkLen
            (actionCircuit.permutationColumnCount -
              (j.1 : ℕ) *
                actionCircuit.chunkLen) at hjWidth
      change
        (j'.2 : ℕ) <
          min actionCircuit.chunkLen
            (actionCircuit.permutationColumnCount -
              (j'.1 : ℕ) *
                actionCircuit.chunkLen) at hj'Width
      have hj :
          (j.1 : ℕ) *
                actionCircuit.chunkLen +
              (j.2 : ℕ) <
            actionCircuit.permutationColumnCount := by
        omega
      have hj' :
          (j'.1 : ℕ) *
                actionCircuit.chunkLen +
              (j'.2 : ℕ) <
            actionCircuit.permutationColumnCount := by
        omega
      have hsupported :
          actionCircuit.permutationColumnCount ≤ deltaFpOrder :=
        permutationColumns_le_delta
      have hglobal :
          (⟨(j.1 : ℕ) *
                actionCircuit.chunkLen +
              (j.2 : ℕ), hj⟩ :
              Fin actionCircuit.permutationColumnCount) =
            ⟨(j'.1 : ℕ) *
                actionCircuit.chunkLen +
              (j'.2 : ℕ), hj'⟩ :=
        deltaFp_domainCosets
          (k := actionCircuit.domainExponent)
          (n := actionCircuit.permutationColumnCount)
          (Nat.le_of_lt_succ domainExponent_lt) hsupported
          ⟨_, hj⟩ ⟨_, hj'⟩ t hcoset
      have hindex :
          (j.1 : ℕ) *
                actionCircuit.chunkLen +
              (j.2 : ℕ) =
            (j'.1 : ℕ) *
                actionCircuit.chunkLen +
              (j'.2 : ℕ) :=
        congrArg Fin.val hglobal
      have hchunkLen :
          0 < actionCircuit.chunkLen :=
        constraintSystem_chunkLen_pos
          actionCircuit.constraintSystem
      have hjColumn :
          (j.2 : ℕ) <
            actionCircuit.chunkLen :=
        lt_of_lt_of_le j.2.isLt
          (resolverPairsLength_le pp urs poly p j.1 j.1.isLt)
      have hj'Column :
          (j'.2 : ℕ) <
            actionCircuit.chunkLen :=
        lt_of_lt_of_le j'.2.isLt
          (resolverPairsLength_le pp urs poly p j'.1 j'.1.isLt)
      have hchunk :
          (j.1 : ℕ) = (j'.1 : ℕ) := by
        have hjDiv :
            ((j.1 : ℕ) *
                  actionCircuit.chunkLen +
                (j.2 : ℕ)) /
                actionCircuit.chunkLen =
              (j.1 : ℕ) := by
          calc
            _ =
                (actionCircuit.chunkLen *
                    (j.1 : ℕ) + (j.2 : ℕ)) /
                  actionCircuit.chunkLen := by
                    rw [Nat.mul_comm]
            _ = (j.1 : ℕ) +
                (j.2 : ℕ) /
                  actionCircuit.chunkLen :=
              Nat.mul_add_div hchunkLen _ _
            _ = (j.1 : ℕ) := by
              rw [Nat.div_eq_of_lt hjColumn, Nat.add_zero]
        have hj'Div :
            ((j'.1 : ℕ) *
                  actionCircuit.chunkLen +
                (j'.2 : ℕ)) /
                actionCircuit.chunkLen =
              (j'.1 : ℕ) := by
          calc
            _ =
                (actionCircuit.chunkLen *
                    (j'.1 : ℕ) + (j'.2 : ℕ)) /
                  actionCircuit.chunkLen := by
                    rw [Nat.mul_comm]
            _ = (j'.1 : ℕ) +
                (j'.2 : ℕ) /
                  actionCircuit.chunkLen :=
              Nat.mul_add_div hchunkLen _ _
            _ = (j'.1 : ℕ) := by
              rw [Nat.div_eq_of_lt hj'Column, Nat.add_zero]
        rw [← hjDiv, hindex, hj'Div]
      have hchunkFin : j.1 = j'.1 := Fin.ext hchunk
      have hcolumn : (j.2 : ℕ) = (j'.2 : ℕ) := by
        have hprefix :
            (j.1 : ℕ) *
                actionCircuit.chunkLen =
              (j'.1 : ℕ) *
                actionCircuit.chunkLen :=
          congrArg
            (fun chunk =>
              chunk *
                actionCircuit.chunkLen)
            hchunk
        apply Nat.add_left_cancel
        exact hindex.trans (by rw [hprefix])
      have hwidth :
          (ResolverPermutationPairs
              (actionVk pp urs) poly p j.1).length =
            (ResolverPermutationPairs
              (actionVk pp urs) poly p j'.1).length :=
        congrArg
          (fun chunk : ℕ =>
            (ResolverPermutationPairs
              (actionVk pp urs) poly p chunk).length)
          hchunk
      apply Sigma.ext hchunkFin
      exact (Fin.heq_ext_iff hwidth).mpr hcolumn
  intro c d hname
  have hwiden := widenPermutationChunkCell_injective
    (nc := (actionShape pp).numPermutationSets)
    (width := fun i =>
      (ResolverPermutationPairs (actionVk pp urs) poly p i).length)
    hactive
  have hwname :
      chunkRowName (actionVk pp urs).omega (actionVk pp urs).delta
          (actionVk pp urs).chunkLen
          (widenPermutationChunkCell hactive c).1
          (widenPermutationChunkCell hactive c).2.1
          (widenPermutationChunkCell hactive c).2.2 =
        chunkRowName (actionVk pp urs).omega (actionVk pp urs).delta
          (actionVk pp urs).chunkLen
          (widenPermutationChunkCell hactive d).1
          (widenPermutationChunkCell hactive d).2.1
          (widenPermutationChunkCell hactive d).2.2 := by
    simpa only [widenPermutationChunkCell_fst,
      widenPermutationChunkCell_row,
      widenPermutationChunkCell_column] using hname
  exact hwiden (hfull hwname)

/-- Assemble the semantic cycle at any active-row prefix preserved by the
replayed full permutation. -/
def cycleOfKeygenColumnsAt
    (pp : Keygen.ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (p : Fin pp.numProofs)
    {m : ℕ}
    (hactive : m ≤ (actionVk pp urs).n)
    (fullSigma : Equiv.Perm
      (ResolverPermutationCell (actionVk pp urs) poly p
        (actionVk pp urs).n))
    (sigma : Equiv.Perm
      (ResolverPermutationCell (actionVk pp urs) poly p
        m))
    (hcolumns : ∀
      (chunk : Fin (actionShape pp).numPermutationSets)
      (column : Fin
        (ResolverPermutationPairs (actionVk pp urs) poly p chunk).length),
      (ResolverPermutationPairs
          (actionVk pp urs) poly p chunk)[column].2 =
        keygenSigmaColumn
          (actionVk pp urs).omega (actionVk pp urs).delta
          (actionVk pp urs).chunkLen fullSigma chunk column)
    (hrestrict : ∀ c :
        ResolverPermutationCell (actionVk pp urs) poly p m,
      widenPermutationChunkCell hactive (sigma c) =
        fullSigma
          (widenPermutationChunkCell hactive c)) :
    ResolverPermutationCycle (actionVk pp urs) poly p m :=
  ResolverPermutationCycle.ofKeygenColumns
    (actionVk pp urs) poly p hactive fullSigma sigma
      (rowsInjective pp urs) hcolumns hrestrict
      (namesInjective pp urs poly p hactive)

/-- Assemble the semantic cycle at the verifier-derived active-row boundary. -/
def cycleOfKeygenColumns
    (pp : Keygen.ProofParams) (urs : URS G)
    (poly : CommitmentId → CPoly)
    (p : Fin pp.numProofs)
    (fullSigma : Equiv.Perm
      (ResolverPermutationCell (actionVk pp urs) poly p
        (actionVk pp urs).n))
    (sigma : Equiv.Perm
      (ResolverPermutationCell (actionVk pp urs) poly p
        (activeRows pp urs)))
    (hcolumns : ∀
      (chunk : Fin (actionShape pp).numPermutationSets)
      (column : Fin
        (ResolverPermutationPairs (actionVk pp urs) poly p chunk).length),
      (ResolverPermutationPairs
          (actionVk pp urs) poly p chunk)[column].2 =
        keygenSigmaColumn
          (actionVk pp urs).omega (actionVk pp urs).delta
          (actionVk pp urs).chunkLen fullSigma chunk column)
    (hrestrict : ∀ c :
        ResolverPermutationCell (actionVk pp urs) poly p
          (activeRows pp urs),
      widenPermutationChunkCell (activeRows_le pp urs) (sigma c) =
        fullSigma
          (widenPermutationChunkCell (activeRows_le pp urs) c)) :
    ResolverPermutationCycle (actionVk pp urs) poly p
      (activeRows pp urs) :=
  cycleOfKeygenColumnsAt pp urs poly p (activeRows_le pp urs)
    fullSigma sigma hcolumns hrestrict

assert_no_sorry routingCoherent_of_derived
assert_no_sorry deltaFp_domainCosets
assert_no_sorry domain
assert_no_sorry namesInjective
assert_no_sorry cycleOfKeygenColumnsAt
assert_no_sorry cycleOfKeygenColumns

end ActionPermutationDomain

end Zcash.Snark
