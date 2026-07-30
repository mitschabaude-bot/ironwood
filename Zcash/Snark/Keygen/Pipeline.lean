import CompElliptic.Curves.Pasta
import Zcash.Common.ParMap
import Zcash.Arithmetic.Domain
import Zcash.Arithmetic.Fft
import CompElliptic.Curves.Pasta.Fast.Msm
import Zcash.Circuits.Integration.ExprRich
import Clean.Halo2.Keygen.Layout
import Clean.Halo2.Keygen
import Clean.Halo2.TopLevel
import Zcash.Arithmetic
import Zcash.Snark.Verifier.Assemble
import Zcash.Snark.Verifier.Circuit

/-!
# `TopLevelCircuit.toVerifierKey` — the circuit-side half of halo2 `keygen_vk`, generic

The single generic pipeline from a closed circuit (+ a monomial URS) to the full
`VerifyingKey`: Clean's `Halo2.Keygen` supplies the pinned constraint system, domain
exponent and selector map; this module adds the group side — the Lagrange-basis URS by
inverse FFT, the dense fixed columns from the derived layout, the keygen permutation
polynomials, `commit_lagrange` for both commitment families — and assembles the record.

`ProofParams` carries the only two `Shape` counts that are proof-shape rather than
circuit data (batch size, multiopen point sets); `ProofParams.mergeDerived` computes the
rest from the circuit, so `TopLevelCircuit.toVerifierKey` carries its derived `Shape` in
the return type with no lawfulness side condition. The Action capture certification
lives in `Certificate.lean`.

## Rust reference

* Lagrange URS: `poly/commitment.rs:75-88` (`Params::new`'s `g_lagrange`),
  `arithmetic.rs:192` (`best_fft` — bit-reversal + iterative Cooley–Tukey butterflies).
* `commit_lagrange` blind: `poly/commitment.rs:212-216` (`Blind::default() = Blind(F::ONE)`).
* Fixed commitments: `plonk/keygen.rs:230-240` (`keygen_vk`'s `fixed_commitments`).
* Permutation commitments: `plonk/permutation/keygen.rs:102-152` (`Assembly::build_vk`).
-/

namespace Zcash.Snark.Keygen

open Zcash.Snark
open Zcash.Arithmetic (deltaFp omegaOf)
open Halo2
-- The concrete fast MSM lives in the CompElliptic pin; opening `Curves.Pasta` is what makes its
-- `Fast.Msm.*` spellings resolve here.
open CompElliptic.Curves.Pasta

variable {G : Type} [AddCommGroup G] [Inhabited G]

/-! ## Generalized Lagrange commitment (`poly/commitment.rs:212-216`) -/

/-- Commit to a zero-padded Lagrange-coefficient column against an arbitrary basis with
`Blind::default () = Blind(F::ONE)` (`poly/commitment.rs:212-216`):
`(∑ᵢ coeffsᵢ • basisᵢ) + w` — the same `+ w` blind convention the existing
`commitLagrange` uses, generalized to an arbitrary basis and coefficient list (the
instance-commitment path through `commitLagrange` is deliberately left untouched). -/
def commitLagrangeWith (blind : G) (basis : List G) (coeffs : List Fp) : G :=
  ((List.range coeffs.length).map
    (fun i => (coeffs.getD i 0).val • basis.getD i 0)).sum + blind

/-! ## Commitment helpers over Clean-compiled fixed rows -/

/-- V1 constant allocations in the legacy copy-list tuple order. Values remain
field-valued in Clean; only this permutation-copy adapter reads their canonical `Fp.val`. -/
def constantCopyEntries (cs : ConstraintSystem Fp) (ops : Operations Fp) :
    List (ℕ × ℕ × ℕ) :=
  (FloorPlanner.V1.constantAssignments ops (cs.constants.map (·.index))).map
    fun (value, column, row) => (value.val, column, row)

/-- Commit Clean-compiled fixed rows with one task per column. -/
def fixedCommitmentsWith (commit : List Fp → G)
    (rows : List (List Fp)) : List G :=
  rows.parMap commit

/-- Sequential fixed-row commitment variant used by the concrete certificate. -/
def fixedCommitmentsSeqWith (commit : List Fp → G)
    (rows : List (List Fp)) : List G :=
  rows.map commit

omit [AddCommGroup G] [Inhabited G] in
theorem fixedCommitmentsSeqWith_eq (commit : List Fp → G)
    (rows : List (List Fp)) :
    fixedCommitmentsSeqWith commit rows = fixedCommitmentsWith commit rows := by
  simp only [fixedCommitmentsSeqWith, fixedCommitmentsWith, List.parMap_eq_map]

omit [AddCommGroup G] [Inhabited G] in
theorem fixedCommitmentsSeqWith_congr {f g : List Fp → G}
    (rows : List (List Fp))
    (h : ∀ row ∈ rows, f row = g row) :
    fixedCommitmentsSeqWith f rows = fixedCommitmentsSeqWith g rows := by
  simp only [fixedCommitmentsSeqWith]
  exact List.map_congr_left h

/-- Commit Clean-compiled fixed rows against a Lagrange basis. -/
def fixedCommitmentsOf (blind : G) (lagrange : List G)
    (rows : List (List Fp)) : List G :=
  fixedCommitmentsWith
    (Fast.Msm.commitLagrangeFastWith Fast.Msm.defaultWindow blind lagrange) rows

/-! ## Derived permutation commitments (`plonk/permutation/keygen.rs:102-152`) -/

/-- The permutation columns as `ColRef`s in `enable_equality` order
(`cs.permutationColumns`) — the order the keygen `Assembly` mapping and the `δ^i` scaling
are indexed by, and the column shape `V1.copyList` resolves cells against. -/
def permColsOf (cs : ConstraintSystem Fp) : List Halo2.Layout.ColRef :=
  cs.permutationColumns.map fun c =>
    match c.kind with
    | .advice => .advice c.index
    | .fixed => .fixed c.index
    | .instance => .instance c.index

/-- `[ω^0, ω^1, …, ω^(n−1)]` (`build_vk`'s `omega_powers`, `permutation/keygen.rs:108-116`;
map form rather than iterated multiplication so entries are `getElem`-transparent for the
σ-row identification — `ZMod` powers are binary-fast, so the cost difference is noise). -/
def omegaPowersArr (omega : Fp) (n : ℕ) : Array Fp :=
  (Array.range n).map (omega ^ ·)

/-- `[δ^0, δ^1, …, δ^(m−1)]` (`build_vk`'s `cur *= DELTA`, `permutation/keygen.rs:118-133`;
map form, see `omegaPowersArr`). -/
def deltaPowersArr (delta : Fp) (m : ℕ) : Array Fp :=
  (Array.range m).map (delta ^ ·)

@[simp] theorem omegaPowersArr_getElem! (omega : Fp) {n j : ℕ} (hj : j < n) :
    (omegaPowersArr omega n)[j]! = omega ^ j := by
  simp [omegaPowersArr, hj]

@[simp] theorem deltaPowersArr_getElem! (delta : Fp) {m j : ℕ} (hj : j < m) :
    (deltaPowersArr delta m)[j]! = delta ^ j := by
  simp [deltaPowersArr, hj]

/-- The per-column permutation polynomials in Lagrange form:
`p_i[j] = deltaomega[i'][j'] = δ^{i'} · ω^{j'}` where `(i', j') = mapping[i][j]`
(`build_vk`, `permutation/keygen.rs:135-146`), over the keygen `Assembly` mapping
(`Assembly::copy` replay, `Layout.runAssembly`) of the derived V1 copy list. -/
def permPolysOf (k : ℕ) (cs : ConstraintSystem Fp) (ops : Operations Fp) :
    List (List Fp) :=
  let n := 2 ^ k
  let permCols := permColsOf cs
  let copyList := Layout.V1.copyList permCols (FloorPlanner.V1.starts ops) ops
    (constantCopyEntries cs ops)
  let mapping := Layout.runAssembly n permCols.length copyList
  let omegaPows := omegaPowersArr (omegaOf k) n
  let deltaPows := deltaPowersArr deltaFp permCols.length
  (List.range permCols.length).map fun i =>
    (List.range n).map fun j =>
      let pij := (mapping[i]!)[j]!
      deltaPows[pij.1]! * omegaPows[pij.2]!

/-- The derived permutation common commitments at an explicit per-column committer
(see `fixedCommitmentsWith`). -/
def permutationCommitmentsWith (commit : List Fp → G) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp) : List G :=
  -- `parMap`: one task per column (`parMap_eq_map` — evaluation strategy only)
  (permPolysOf k cs ops).parMap commit

/-- Sequential variant of `permutationCommitmentsWith` (see `fixedCommitmentsSeqWith`). -/
def permutationCommitmentsSeqWith (commit : List Fp → G) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp) : List G :=
  (permPolysOf k cs ops).map commit

omit [AddCommGroup G] [Inhabited G] in
theorem permutationCommitmentsSeqWith_eq (commit : List Fp → G) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp) :
    permutationCommitmentsSeqWith commit k cs ops
      = permutationCommitmentsWith commit k cs ops := by
  simp only [permutationCommitmentsSeqWith, permutationCommitmentsWith,
    List.parMap_eq_map]

/-- Every permutation polynomial is a full-domain row vector. -/
theorem permPolysOf_mem_length (k : ℕ) (cs : ConstraintSystem Fp) (ops : Operations Fp) :
    ∀ l ∈ permPolysOf k cs ops, l.length = 2 ^ k := by
  intro l hl
  simp only [permPolysOf, List.mem_map] at hl
  obtain ⟨i, -, rfl⟩ := hl
  simp

omit [AddCommGroup G] [Inhabited G] in
/-- The permutation twin of `fixedCommitmentsSeqWith_congr`. -/
theorem permutationCommitmentsSeqWith_congr {f g : List Fp → G} (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp)
    (h : ∀ l : List Fp, l.length = 2 ^ k → f l = g l) :
    permutationCommitmentsSeqWith f k cs ops = permutationCommitmentsSeqWith g k cs ops := by
  simp only [permutationCommitmentsSeqWith]
  exact List.map_congr_left fun c hc => h c (permPolysOf_mem_length k cs ops c hc)

/-- The derived permutation common commitments — `commit_lagrange` of each permutation
polynomial with the default blind (`build_vk`, `permutation/keygen.rs:147-151`;
Pippenger per MSM, `commitLagrangeFastWith_eq` — evaluation strategy only). -/
def permutationCommitmentsOf (blind : G) (lagrange : List G) (k : ℕ)
    (cs : ConstraintSystem Fp) (ops : Operations Fp) : List G :=
  permutationCommitmentsWith
    (Fast.Msm.commitLagrangeFastWith Fast.Msm.defaultWindow blind lagrange)
    k cs ops

end Zcash.Snark.Keygen

namespace Zcash.Snark.Keygen

open Zcash.Snark
open Halo2

/-- The two `Shape` counts that are genuinely proof-shape rather than circuit data: the
batch size and the multiopen point-set count. Everything else merges in derived
(`ProofParams.mergeDerived`). -/
structure ProofParams where
  numProofs : ℕ
  numPointSets : ℕ
deriving DecidableEq, Repr

end Zcash.Snark.Keygen

namespace Halo2.TopLevelCircuit

open Zcash.Arithmetic (Fp)

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]

end Halo2.TopLevelCircuit

namespace Zcash.Snark.Keygen

open Zcash.Snark
open Halo2

/-- The `Shape` of a top-level circuit's proofs: the proof-shape counts merged with
everything the circuit derives — the domain exponent (`TopLevelCircuit.domainExponent`),
column/lookup/permutation counts from the configure-recorded constraint system, the
query counts from the derived pinned CS layouts (`TopLevelCircuit.pinnedCS`), the
verifier's permutation chunking `⌈columns / chunkLen⌉` (`permutation/verifier.rs:43-47`),
and the quotient split `cs.degree() − 1` (`vk.domain.get_quotient_poly_degree()`). -/
def ProofParams.mergeDerived (pp : ProofParams)
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) : Shape :=
  { k := top.domainExponent
    numProofs := pp.numProofs
    numAdviceColumns := top.adviceColumnCount
    numLookups := top.lookupCount
    numPermutationSets := top.permutationSetCount
    numPermutationColumns := top.permutationColumnCount
    numQuotientPieces := top.quotientPieceCount
    numInstanceQueries := top.instanceQueryCount
    numAdviceQueries := top.adviceQueryCount
    numFixedQueries := top.fixedQueryCount
    numPointSets := pp.numPointSets }

theorem ProofParams.mergeDerived_k
    (pp : ProofParams)
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) :
    (pp.mergeDerived top).k = top.domainExponent := by
  simp [ProofParams.mergeDerived]

theorem ProofParams.mergeDerived_numProofs
    (pp : ProofParams)
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) :
    (pp.mergeDerived top).numProofs = pp.numProofs := by
  simp [ProofParams.mergeDerived]

theorem ProofParams.mergeDerived_numAdviceColumns
    (pp : ProofParams)
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) :
    (pp.mergeDerived top).numAdviceColumns = top.adviceColumnCount := by
  simp only [ProofParams.mergeDerived,
    TopLevelCircuit.adviceColumnCount]

theorem ProofParams.mergeDerived_numLookups
    (pp : ProofParams)
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) :
    (pp.mergeDerived top).numLookups = top.lookupCount := by
  simp only [ProofParams.mergeDerived,
    TopLevelCircuit.lookupCount]

theorem ProofParams.mergeDerived_numPermutationSets
    (pp : ProofParams)
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) :
    (pp.mergeDerived top).numPermutationSets =
      top.permutationSetCount := by
  simp only [ProofParams.mergeDerived,
    TopLevelCircuit.permutationSetCount,
    TopLevelCircuit.permutationColumnCount,
    TopLevelCircuit.permutationColumns,
    TopLevelCircuit.chunkLen]

theorem ProofParams.mergeDerived_numPermutationColumns
    (pp : ProofParams)
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) :
    (pp.mergeDerived top).numPermutationColumns =
      top.permutationColumnCount := by
  simp only [ProofParams.mergeDerived,
    TopLevelCircuit.permutationColumnCount,
    TopLevelCircuit.permutationColumns]

theorem ProofParams.mergeDerived_numQuotientPieces
    (pp : ProofParams)
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) :
    (pp.mergeDerived top).numQuotientPieces = top.quotientPieceCount := by
  simp only [ProofParams.mergeDerived,
    TopLevelCircuit.quotientPieceCount]

theorem ProofParams.mergeDerived_numInstanceQueries
    (pp : ProofParams)
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) :
    (pp.mergeDerived top).numInstanceQueries = top.instanceQueryCount := by
  simp only [ProofParams.mergeDerived,
    TopLevelCircuit.instanceQueryCount,
    TopLevelCircuit.instanceQueryLayout]

theorem ProofParams.mergeDerived_numAdviceQueries
    (pp : ProofParams)
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) :
    (pp.mergeDerived top).numAdviceQueries = top.adviceQueryCount := by
  simp only [ProofParams.mergeDerived,
    TopLevelCircuit.adviceQueryCount,
    TopLevelCircuit.adviceQueryLayout]

theorem ProofParams.mergeDerived_numFixedQueries
    (pp : ProofParams)
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) :
    (pp.mergeDerived top).numFixedQueries = top.fixedQueryCount := by
  simp only [ProofParams.mergeDerived,
    TopLevelCircuit.fixedQueryCount,
    TopLevelCircuit.fixedQueryLayout]

theorem ProofParams.mergeDerived_numPointSets
    (pp : ProofParams)
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit Fp Config PublicInput) :
    (pp.mergeDerived top).numPointSets = pp.numPointSets := by
  simp [ProofParams.mergeDerived]

end Zcash.Snark.Keygen

namespace Halo2.TopLevelCircuit

open Zcash.Snark
-- This section declares under `Halo2`, not `Zcash`, so the root re-exports of `Fp`/`URS` are not
-- on the enclosing-namespace walk and have to be opened explicitly.
open Zcash.Arithmetic (Fp URS derivedUrsGLagrange)
open Zcash.Snark.Keygen
open Halo2
open CompElliptic.Curves.Pasta

variable {G : Type} [AddCommGroup G] [Inhabited G]
variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]

/-- The derived fixed-column commitments of a closed circuit against a URS. -/
def fixedCommitments
    (top : TopLevelCircuit Fp Config PublicInput) (urs : URS G) : List G :=
  top.fixedRows.parMap
    (Fast.Msm.commitLagrangeFastWith Fast.Msm.defaultWindow urs.w
      (derivedUrsGLagrange urs))

/-- The named top-level fixed-row view is exactly the fixed-commitment computation
used by generic keygen. -/
@[simp] theorem fixedCommitments_eq_fixedCommitmentsOf
    (top : TopLevelCircuit Fp Config PublicInput) (urs : URS G) :
    top.fixedCommitments urs =
      fixedCommitmentsOf urs.w (derivedUrsGLagrange urs)
        top.fixedRows := by
  simp only [fixedCommitments, fixedCommitmentsOf, fixedCommitmentsWith]

/-- The derived permutation common commitments of a closed circuit against a URS. -/
def permutationCommitments
    (top : TopLevelCircuit Fp Config PublicInput) (urs : URS G) : List G :=
  permutationCommitmentsOf urs.w (derivedUrsGLagrange urs) top.domainExponent
    top.constraintSystem (top.operations)

/-- The fitting-domain generator used by the circuit's verifier. -/
def omega (top : TopLevelCircuit Fp Config PublicInput) : Fp :=
  Zcash.Arithmetic.omegaOf top.domainExponent

/-- The fitting-domain generator is nonzero whenever its exponent lies in
Pasta's supported range. -/
theorem omega_ne_zero
    (top : TopLevelCircuit Fp Config PublicInput)
    (hbound : top.domainExponent ≤ 32) :
    top.omega ≠ 0 :=
  (Zcash.Arithmetic.omegaOf_isPrimitiveRoot
    top.domainExponent hbound).isUnit (by positivity) |>.ne_zero

/-- **The verifying key of a closed top-level circuit**: the `TopLevelCircuit` carries
unit configuration and synthesis inputs, so the only remaining inputs are the
proof-shape counts and the URS — `keygen_vk` at the `TopLevelCircuit` level, with the
derived `Shape` in the return type. -/
def toVerifierKey
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    VerifyingKey (pp.mergeDerived top) Fp G :=
  let verifierCS := top.verifierCS
  let fixedCommitments := top.fixedCommitments urs
  let permutationCommitments := top.permutationCommitments urs
  { omega := top.omega
    n := top.n
    blindingFactors := top.blindingFactors
    delta := Zcash.Arithmetic.deltaFp
    chunkLen := top.chunkLen
    gates := verifierCS.gates
    instanceQueryLayout := top.instanceQueryLayout
    adviceQueryLayout := top.adviceQueryLayout
    fixedQueryLayout := top.fixedQueryLayout
    fixedCommitment := fun column => fixedCommitments.getD column 0
    permutationCommonCommitment := fun column =>
      permutationCommitments.getD column.val 0
    permutationChunks := verifierCS.permutationChunks
    lookupInputExprs := verifierCS.lookupInputExprs
    lookupTableExprs := verifierCS.lookupTableExprs }

/-- The derived key uses the circuit's fitting-domain generator. -/
@[simp] theorem toVerifierKey_omega
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).omega =
      top.omega := by
  simp only [toVerifierKey]

/-- The derived key uses the circuit-owned fitting domain size. -/
@[simp]
theorem toVerifierKey_n
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).n = top.n := by
  simp only [toVerifierKey]

/-- The derived key preserves the closed constraint system's blinding count. -/
@[simp]
theorem toVerifierKey_blindingFactors
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).blindingFactors = top.blindingFactors := by
  simp only [toVerifierKey]

/-- The derived key uses the protocol's fixed permutation delta. -/
@[simp] theorem toVerifierKey_delta
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).delta =
      Zcash.Arithmetic.deltaFp := by
  simp only [toVerifierKey]

/-- The derived key uses the circuit-owned permutation chunk width. -/
@[simp] theorem toVerifierKey_chunkLen
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).chunkLen = top.chunkLen := by
  simp only [toVerifierKey]

/--
The fitting domain of a circuit-derived verification key has room for all of
the circuit's blinding rows.
-/
theorem toVerifierKey_blindingFactors_lt_n
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).blindingFactors <
      (top.toVerifierKey pp urs).n := by
  rw [top.toVerifierKey_blindingFactors, top.toVerifierKey_n]
  exact top.blindingFactors_lt_domainSize

/-- The derived key exposes the fixed commitments computed from its own dense rows. -/
theorem toVerifierKey_fixedCommitment
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) (column : ℕ) :
    (top.toVerifierKey pp urs).fixedCommitment column =
      (top.fixedCommitments urs).getD column 0 := by
  simp only [toVerifierKey]

/-- The derived key exposes the common permutation commitments computed from
its own keygen permutation rows. -/
theorem toVerifierKey_permutationCommonCommitment
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (column : Fin top.permutationColumnCount) :
    (top.toVerifierKey pp urs).permutationCommonCommitment column =
      (top.permutationCommitments urs).getD column.val 0 := by
  simp only [toVerifierKey]

/-- The derived key uses the circuit-owned advice-query layout. -/
@[simp] theorem toVerifierKey_adviceQueryLayout
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).adviceQueryLayout =
      top.adviceQueryLayout := by
  simp only [toVerifierKey]

/-- The derived key uses the circuit-owned fixed-query layout. -/
@[simp] theorem toVerifierKey_fixedQueryLayout
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).fixedQueryLayout =
      top.fixedQueryLayout := by
  simp only [toVerifierKey]

/-- The derived key uses the circuit-owned instance-query layout. -/
@[simp] theorem toVerifierKey_instanceQueryLayout
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).instanceQueryLayout =
      top.instanceQueryLayout := by
  simp only [toVerifierKey]

/-- The derived key uses the circuit's Ironwood-native gate expressions. -/
@[simp] theorem toVerifierKey_gates
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).gates = top.verifierCS.gates := by
  simp only [toVerifierKey]

/-- The derived key uses the circuit's Ironwood-native permutation chunks. -/
@[simp] theorem toVerifierKey_permutationChunks
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).permutationChunks =
      top.verifierCS.permutationChunks := by
  simp only [toVerifierKey]

/-- The derived key uses the circuit's Ironwood-native lookup input expressions. -/
@[simp] theorem toVerifierKey_lookupInputExprs
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (lookup : Fin top.lookupCount) :
    (top.toVerifierKey pp urs).lookupInputExprs lookup =
      top.verifierCS.lookupInputExprs lookup := by
  simp only [toVerifierKey]

/-- The derived key uses the circuit's Ironwood-native lookup table expressions. -/
@[simp] theorem toVerifierKey_lookupTableExprs
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G)
    (lookup : Fin top.lookupCount) :
    (top.toVerifierKey pp urs).lookupTableExprs lookup =
      top.verifierCS.lookupTableExprs lookup := by
  simp only [toVerifierKey]

/-- The derived key's advice-query layout has the shape count computed from the same
top-level pinned constraint system. -/
theorem toVerifierKey_adviceQueryCount
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).adviceQueryLayout.length =
      top.adviceQueryCount := by
  simpa only [adviceQueryCount] using
    congrArg List.length (top.toVerifierKey_adviceQueryLayout pp urs)

/-- The derived key's fixed-query layout has the shape count computed from the same
top-level pinned constraint system. -/
theorem toVerifierKey_fixedQueryCount
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).fixedQueryLayout.length =
      top.fixedQueryCount := by
  simpa only [fixedQueryCount] using
    congrArg List.length (top.toVerifierKey_fixedQueryLayout pp urs)

/-- The derived key's instance-query layout has the shape count computed from the same
top-level pinned constraint system. -/
theorem toVerifierKey_instanceQueryCount
    (top : TopLevelCircuit Fp Config PublicInput)
    (pp : ProofParams) (urs : URS G) :
    (top.toVerifierKey pp urs).instanceQueryLayout.length =
      top.instanceQueryCount := by
  simpa only [instanceQueryCount] using
    congrArg List.length (top.toVerifierKey_instanceQueryLayout pp urs)

end Halo2.TopLevelCircuit
