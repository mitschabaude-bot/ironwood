import Mathlib
import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.Multiopen.Decode
import Zcash.Snark.Soundness.Multiopen.Deployed
import Zcash.Snark.Soundness.Multiopen.Compat

/-!
# The opened `x₄` chain: batch decode through the declared `U`/`W` components

The fork bridge opens the *adjusted* commitment: a `ForkedTranscript` declares `U`/`W` components
`pU`/`pW` and its clean IPA transcript accepts `openedCommitment = deployedCommitment − pU•u − pW•w`,
not the raw `deployedCommitment` the plain batch decode (`Soundness.Multiopen.Decode`) consumes. This
module closes that gap: it re-runs the `x₄` batch decode with every witness carried in *augmented*
`(g, u, w)` representation, so the rewound forks' openings — each with its own declared components —
batch, decode, and reconstruct exactly as the plain chain does.

The route, mirroring the plain chain step for step:

1. `OpenedBatchOpenings` — the batch family: per-run witnesses with declared components, the
   commitment equations in augmented power form `commit(aᵣ) + pUᵣ•u + pWᵣ•w = Σⱼ ξᵣʲ • Cⱼ`
   (the plain `BatchOpeningsForWitness` is the `pUᵣ = pWᵣ = 0` slice).
2. `openedColumnDecode` — the canonical Vandermonde decode, run componentwise: the same inverse
   matrix decodes the witness vectors, the `U`-components, and the `W`-components
   (`vandermonde_decode_map`/`vandermonde_reconstruct_map`, the module-valued decode core).
   Each decoded column opens its aggregate in augmented form and every run's triple is
   reconstructed as its `ξᵣ`-power combination.
3. `openedX4Batch_of_witnessFamily` — the deployed instantiation: the power form of the batch
   equations is `deployedCommitment_x4_batch`/`multiopenValue_x4_batch`, so the columns are the
   deployed aggregates (`x4BatchCommitments`/`x4BatchEvals`), as in the plain chain.
4. `openedX4Rewind_of_x4Prob` — the accept-measure floor: the event `OpenedX4Accept` asks each
   rewound `x₄` run for a fork and a clean accepting transcript on *its* opened commitment —
   exactly what `x4_cleanTree_of_deployedAccepts` produces (`openedX4Accept_of_deployedAccepts`)
   — and the single-squeeze counting floor (`exists_injective_accepting_of_measure`) turns the
   measure into the rewound family.
5. `opened_constraint_of_opening_or_relation` — the terminal constraint endpoint over the decoded
   columns, mirroring `decoded_constraint_of_opening_or_relation`.

The augmented representation is not a detour: the deployed aggregates genuinely carry `u`/`w`
contributions (the fingerprint MSM has `uScalar`/`wScalar` slots), and the binding story already
lives in the augmented basis — a collision computes a `NontrivialRelation` among `(g, u, w)`. The
`hquot`/`hgood` hypotheses of the terminal endpoints keep the plain chain's canonical-decode scoping
(`Soundness.Multiopen.Decode`, the scope section).

Not yet built: the `x₁` layer's measure-driven production. Each `x₁`-rewound run's aggregate
witness arrives in this same augmented representation, so feeding
`deployed_witness_member_binding`'s per-run hypotheses from an `x₁` accept measure needs the opened
mirror of that lemma; the per-set gluing is `deployed_witness_two_level`
(`Soundness.Multiopen.Deployed`).
-/

namespace Zcash.Snark

section Opened

variable {G : Type*} [AddCommGroup G] [Module Fp G]

/-! ## The Vandermonde decode core, module-valued

The plain decode inverts the power system for witness vectors (`batch_open_with_coeffs`). The opened
decode inverts the same system three times — witness vectors, `U`-components, `W`-components — so the
core is stated once over an arbitrary `Fp`-module and instantiated per component. -/

/-- Vandermonde decode in any `Fp`-module: a family in flat power form over columns `C` is inverted
columnwise by the inverse-matrix combination. `batch_open_with_coeffs` is the `commitGen` image of
this fact. -/
theorem vandermonde_decode_map {M : Type*} [AddCommMonoid M] [Module Fp M] {n : ℕ}
    {z : Fin n → Fp} {C F : Fin n → M} (μ : Fin n → Fin n → Fp)
    (hμ : ∀ (i j : Fin n), (∑ k : Fin n, μ i k * z k ^ (j : ℕ)) = if i = j then 1 else 0)
    (hF : ∀ r, F r = ∑ j : Fin n, z r ^ (j : ℕ) • C j) (i : Fin n) :
    (∑ r : Fin n, μ i r • F r) = C i := by
  simp only [hF, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hμ, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-- Vandermonde reconstruction in any `Fp`-module: the power combination of the decoded columns
returns each family member. `batch_open_reconstruct_with_coeffs` is the vector instance. -/
theorem vandermonde_reconstruct_map {M : Type*} [AddCommMonoid M] [Module Fp M] {n : ℕ}
    {z : Fin n → Fp} (F : Fin n → M) (μ : Fin n → Fin n → Fp)
    (hμ : ∀ (i j : Fin n), (∑ k : Fin n, z i ^ (k : ℕ) * μ k j) = if i = j then 1 else 0)
    (i : Fin n) :
    (∑ j : Fin n, z i ^ (j : ℕ) • (∑ k : Fin n, μ j k • F k)) = F i := by
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hμ, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-! ## The opened batch family and its canonical decode -/

/-- A family of rewound batched openings carried in augmented `(g, u, w)` representation: run `r`'s
witness `batched r` opens the power batch after removing its declared components, so the commitment
equation reads `commit(batched r) + batchedU r • u + batchedW r • w = Σⱼ ξᵣʲ • Cⱼ`. The current slot
pins the designated run's triple to `(currentWitness, pU, pW)` — for the deployed instantiation, the
honest fork's extracted witness and declared components. `BatchOpeningsForWitness` is the
`batchedU = batchedW = 0` slice. -/
structure OpenedBatchOpenings (urs : URS G) (b : Fin (2 ^ urs.k) → Fp) {numColumns : ℕ}
    (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp)
    (currentWitness : Fin (2 ^ urs.k) → Fp) (pU pW : Fp) where
  batchChallenge : Fin numColumns → Fp
  challengesDistinct : Function.Injective batchChallenge
  batched : Fin numColumns → (Fin (2 ^ urs.k) → Fp)
  batchedU : Fin numColumns → Fp
  batchedW : Fin numColumns → Fp
  current : Fin numColumns
  current_eq : batched current = currentWitness
  currentU_eq : batchedU current = pU
  currentW_eq : batchedW current = pW
  commitment :
    ∀ r, commit urs (batched r) + batchedU r • urs.u + batchedW r • urs.w
      = ∑ j : Fin numColumns, batchChallenge r ^ (j : ℕ) • columnCommitments j
  value :
    ∀ r, commitGen b (batched r)
      = ∑ j : Fin numColumns, batchChallenge r ^ (j : ℕ) • columnEvals j

/-- The decoded columns of an opened batch: per column, a witness vector plus `U`/`W` components
opening the column commitment in augmented form and the claimed evaluation, with every run's triple
reconstructed as its power combination of the decoded triples. -/
structure OpenedColumnDecode {urs : URS G} {b : Fin (2 ^ urs.k) → Fp} {numColumns : ℕ}
    {columnCommitments : Fin numColumns → G} {columnEvals : Fin numColumns → Fp}
    {currentWitness : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (hbatch : OpenedBatchOpenings urs b columnCommitments columnEvals currentWitness pU pW) where
  coeffs : Fin numColumns → (Fin (2 ^ urs.k) → Fp)
  uComp : Fin numColumns → Fp
  wComp : Fin numColumns → Fp
  commitment :
    ∀ i, commit urs (coeffs i) + uComp i • urs.u + wComp i • urs.w = columnCommitments i
  value : ∀ i, commitGen b (coeffs i) = columnEvals i
  reconstruct :
    ∀ r, hbatch.batched r
      = ∑ i : Fin numColumns, hbatch.batchChallenge r ^ (i : ℕ) • coeffs i
  reconstructU :
    ∀ r, hbatch.batchedU r
      = ∑ i : Fin numColumns, hbatch.batchChallenge r ^ (i : ℕ) • uComp i
  reconstructW :
    ∀ r, hbatch.batchedW r
      = ∑ i : Fin numColumns, hbatch.batchChallenge r ^ (i : ℕ) • wComp i

/-- The canonical decode of an opened batch: the Vandermonde-inverse combination, run componentwise
on the witness vectors and the two declared-component families — the same matrix inverts all three
power systems (`vandermonde_decode_map`, one instance per component). -/
noncomputable def openedColumnDecode {urs : URS G} {b : Fin (2 ^ urs.k) → Fp} {numColumns : ℕ}
    {columnCommitments : Fin numColumns → G} {columnEvals : Fin numColumns → Fp}
    {currentWitness : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (hbatch : OpenedBatchOpenings urs b columnCommitments columnEvals currentWitness pU pW) :
    OpenedColumnDecode hbatch := by
  classical
  set μ : Matrix (Fin numColumns) (Fin numColumns) Fp :=
    (Matrix.vandermonde hbatch.batchChallenge)⁻¹ with hμdef
  have hleft :
      ∀ (i j : Fin numColumns), (∑ k : Fin numColumns,
          μ i k * hbatch.batchChallenge k ^ (j : ℕ))
        = if i = j then 1 else 0 := fun i j => by
    simpa [hμdef] using
      vandermonde_inv_left hbatch.batchChallenge hbatch.challengesDistinct i j
  have hright :
      ∀ (i j : Fin numColumns), (∑ k : Fin numColumns,
          hbatch.batchChallenge i ^ (k : ℕ) * μ k j)
        = if i = j then 1 else 0 := fun i j => by
    simpa [hμdef] using
      vandermonde_inv_right hbatch.batchChallenge hbatch.challengesDistinct i j
  refine
    { coeffs := fun i => ∑ r, μ i r • hbatch.batched r
      uComp := fun i => ∑ r, μ i r • hbatch.batchedU r
      wComp := fun i => ∑ r, μ i r • hbatch.batchedW r
      commitment := ?_
      value := ?_
      reconstruct := fun r =>
        (vandermonde_reconstruct_map hbatch.batched μ hright r).symm
      reconstructU := fun r =>
        (vandermonde_reconstruct_map hbatch.batchedU μ hright r).symm
      reconstructW := fun r =>
        (vandermonde_reconstruct_map hbatch.batchedW μ hright r).symm }
  · -- The three linear pieces collapse to one μ-combination of the per-run augmented equations,
    -- which `vandermonde_decode_map` inverts.
    intro i
    have hlin :
        commit urs (∑ r, μ i r • hbatch.batched r)
            + (∑ r, μ i r • hbatch.batchedU r) • urs.u
            + (∑ r, μ i r • hbatch.batchedW r) • urs.w
          = ∑ r, μ i r • (commit urs (hbatch.batched r) + hbatch.batchedU r • urs.u
              + hbatch.batchedW r • urs.w) := by
      rw [commit_eq_commitGen, commitGen_sum, Finset.sum_smul, Finset.sum_smul,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [commitGen_smul_left, smul_eq_mul, smul_eq_mul, mul_smul, mul_smul, smul_add, smul_add,
        commit_eq_commitGen]
    rw [hlin]
    exact vandermonde_decode_map μ hleft hbatch.commitment i
  · intro i
    have hlin : commitGen b (∑ r, μ i r • hbatch.batched r)
        = ∑ r, μ i r • commitGen b (hbatch.batched r) := by
      rw [commitGen_sum]
      exact Finset.sum_congr rfl fun r _ => commitGen_smul_left b _ _
    rw [hlin]
    exact vandermonde_decode_map μ hleft hbatch.value i

/-- The canonical decoded column polynomials of an opened batch. -/
noncomputable def openedDecodedCols {urs : URS G} {b : Fin (2 ^ urs.k) → Fp} {numColumns : ℕ}
    {columnCommitments : Fin numColumns → G} {columnEvals : Fin numColumns → Fp}
    {currentWitness : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (hbatch : OpenedBatchOpenings urs b columnCommitments columnEvals currentWitness pU pW) :
    Fin numColumns → Polynomial Fp :=
  fun i => coeffsToPoly ((openedColumnDecode hbatch).coeffs i)

/-- The current witness is the current-challenge power combination of the decoded column vectors —
the opened counterpart of `DecodedColumnFamilyOfBatch.currentWitness_eq`. -/
theorem OpenedColumnDecode.currentWitness_eq {urs : URS G} {b : Fin (2 ^ urs.k) → Fp}
    {numColumns : ℕ} {columnCommitments : Fin numColumns → G} {columnEvals : Fin numColumns → Fp}
    {currentWitness : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    {hbatch : OpenedBatchOpenings urs b columnCommitments columnEvals currentWitness pU pW}
    (hdecoded : OpenedColumnDecode hbatch) :
    currentWitness
      = ∑ i : Fin numColumns, hbatch.batchChallenge hbatch.current ^ (i : ℕ)
          • hdecoded.coeffs i := by
  calc
    currentWitness = hbatch.batched hbatch.current := hbatch.current_eq.symm
    _ = ∑ i : Fin numColumns, hbatch.batchChallenge hbatch.current ^ (i : ℕ)
          • hdecoded.coeffs i := hdecoded.reconstruct hbatch.current

/-! ## The terminal `∀`-witness form and its transfer -/

/-- Terminal form of the opened rewinding output: a batch family for every opening of the pinned
statement `(P, b, v)`, at the fixed declared components `(pU, pW)`. As in the plain chain
(`MultiopenRewindForRelation`), the `∀`-witness shape costs nothing beyond a transcript-tied one —
the current-slot equations mention only the shared `P`, `v`, `pU`, `pW`, so any opening swaps into
the current slot (`openedRewindForRelation_of_batch`). At the deployed instantiation `P` is the
honest fork's `openedCommitment` and `(pU, pW)` its declared components. -/
abbrev OpenedRewindForRelation (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → Fp) (v : Fp)
    {numColumns : ℕ} (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp)
    (pU pW : Fp) : Type _ :=
  ∀ a, IpaRelation urs P b v a →
    OpenedBatchOpenings urs b columnCommitments columnEvals a pU pW

/-- The `∀`-witness transfer for opened batches: a family for one witness of `(P, b, v)` yields the
terminal form, swapping any other opening into the current slot — the declared-component families are
untouched, and the current-slot equations only read the shared `P`, `v`, `pU`, `pW`. -/
noncomputable def openedRewindForRelation_of_batch {urs : URS G} {P : G}
    {b : Fin (2 ^ urs.k) → Fp} {v : Fp} {numColumns : ℕ}
    {columnCommitments : Fin numColumns → G} {columnEvals : Fin numColumns → Fp}
    {w : Fin (2 ^ urs.k) → Fp} {pU pW : Fp} (hw : IpaRelation urs P b v w)
    (hb : OpenedBatchOpenings urs b columnCommitments columnEvals w pU pW) :
    OpenedRewindForRelation urs P b v columnCommitments columnEvals pU pW := fun a hrel => by
  classical
  obtain ⟨z, hzinj, batched, bU, bW, cur, hcur, hcurU, hcurW, hcomm, hval⟩ := hb
  refine
    { batchChallenge := z
      challengesDistinct := hzinj
      batched := Function.update batched cur a
      batchedU := bU
      batchedW := bW
      current := cur
      current_eq := Function.update_self cur a batched
      currentU_eq := hcurU
      currentW_eq := hcurW
      commitment := ?_
      value := ?_ }
  · intro r
    rcases eq_or_ne r cur with hr | hr
    · rw [hr, Function.update_self, hrel.1, ← hw.1, ← hcur]
      exact hcomm cur
    · rw [Function.update_of_ne hr]
      exact hcomm r
  · intro r
    rcases eq_or_ne r cur with hr | hr
    · have hia : commitGen b a = innerProduct a b := by
        simp [innerProduct, commitGen, smul_eq_mul]
      have hiw : commitGen b w = innerProduct w b := by
        simp [innerProduct, commitGen, smul_eq_mul]
      rw [hr, Function.update_self, hia, hrel.2, ← hw.2, ← hiw, ← hcur]
      exact hval cur
    · rw [Function.update_of_ne hr]
      exact hval r

/-! ## The deployed instantiation -/

/-- Package a family of augmented openings of the rewound deployed statements as an opened batch
over the deployed aggregates: the power form of each run's equations is
`deployedCommitment_x4_batch`/`multiopenValue_x4_batch`, proven, not assumed. -/
noncomputable def openedX4Batch_of_witnessFamily [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) {b : Fin (2 ^ urs.k) → Fp}
    (ξ : Fin (deployedX4PairCount vk ps ch + 1) → Fp) (hξinj : Function.Injective ξ)
    (cur : Fin (deployedX4PairCount vk ps ch + 1))
    (aF : Fin (deployedX4PairCount vk ps ch + 1) → (Fin (2 ^ urs.k) → Fp))
    (pUF pWF : Fin (deployedX4PairCount vk ps ch + 1) → Fp)
    (hC : ∀ r, commit urs (aF r) + pUF r • urs.u + pWF r • urs.w
      = deployedCommitment urs hk vk ps {ch with x4 := ξ r})
    (hv : ∀ r, commitGen b (aF r) = multiopenValue vk ps {ch with x4 := ξ r}) :
    OpenedBatchOpenings urs b (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch)
      (aF cur) (pUF cur) (pWF cur) where
  batchChallenge := ξ
  challengesDistinct := hξinj
  batched := aF
  batchedU := pUF
  batchedW := pWF
  current := cur
  current_eq := rfl
  currentU_eq := rfl
  currentW_eq := rfl
  commitment := fun r => by
    rw [hC r]
    exact deployedCommitment_x4_batch urs hk vk ps ch (ξ r)
  value := fun r => by
    rw [hv r]
    exact multiopenValue_x4_batch vk ps ch (ξ r)

/-- The opened `x₄` accept event at a rewound batching challenge: some fork of the rewound run has a
clean accepting transcript on *its* opened commitment. This is the event
`x4_cleanTree_of_deployedAccepts` feeds (`openedX4Accept_of_deployedAccepts`) and the measure
`openedX4Rewind_of_x4Prob` spends. -/
def OpenedX4Accept [DecidableEq G] [Inhabited G] {shape : Shape} (urs : URS G)
    (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G) (ps : ProofString shape Fp G)
    (ch : Challenges shape.k Fp) (b : Fin (2 ^ urs.k) → Fp) (ξv : Fp) : Prop :=
  ∃ (z blind : Fp) (fs : ForkedTranscript urs hk vk ps {ch with x4 := ξv} b z blind)
    (t : IpaTreeV Fp G urs.k),
    IpaAcceptV urs.g b fs.openedCommitment (multiopenValue vk ps {ch with x4 := ξv}) t

/-- Feed the opened `x₄` accept event from deployed-accept facts: off the relation branch, the
rewound run's Fiat–Shamir bridge peels to a clean accepting transcript on the fork's opened
commitment (`x4_cleanTree_of_deployedAccepts`). -/
theorem openedX4Accept_of_deployedAccepts [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp} (hz : z ≠ 0)
    (hnrel : ¬HasNontrivialRelation (F := Fp) urs.g urs.u urs.w) (ξv : Fp)
    (hFS : FiatShamirTree urs hk vk ps {ch with x4 := ξv} b z blind)
    (hacc : DeployedAccepts urs hk vk ps {ch with x4 := ξv}) :
    OpenedX4Accept urs hk vk ps ch b ξv := by
  obtain ⟨fs, t, ht⟩ := x4_cleanTree_of_deployedAccepts urs hk vk ps ch hz hnrel ξv hFS hacc
  exact ⟨z, blind, fs, t, ht⟩

open scoped ENNReal in
open Classical in
/-- **The `x₄` forking floor through the opened commitment.** If the honest run's opened accept
event holds and the opened accept measure of the `x₄`-rewound runs beats `pairCount / p`, the
terminal opened rewinding output exists for any statement `P` sitting at declared components
`(pU, pW)` of the deployed commitment — over the deployed aggregates. Each rewound run contributes
its own fork's augmented opening; each opening of `P` seeds the current slot itself, so differing
declared components across runs are absorbed by the augmented batch, not assumed away. The measure
hypothesis carries the same random-oracle uniformity axiom as every `hprob`
(`Soundness.Forking.Oracle`); the runs are the `reprogramX4` reprogramming events
(`Soundness.Forking.Rewind`); each run's accepting transcript is that run's own round-forking
output, and `openedX4Accept_of_deployedAccepts` feeds the event from deployed accepts. -/
noncomputable def openedX4Rewind_of_x4Prob [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) {b : Fin (2 ^ urs.k) → Fp}
    (P : G) (pU pW : Fp)
    (hP : P = deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w)
    (hx₀ : OpenedX4Accept urs hk vk ps ch b ch.x4)
    (hprob4 : ((deployedX4PairCount vk ps ch : ℝ≥0∞)) / Fintype.card Fp
      < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
          (OpenedX4Accept urs hk vk ps ch b))) :
    OpenedRewindForRelation urs P b (multiopenValue vk ps ch)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) pU pW := fun a hrel => by
  -- The counting floor yields the injective rewound family with `ch.x4` in slot `0`
  -- (`{ch with x4 := ch.x4}` is `ch` by structure eta). Everything is destructured with
  -- `Classical.choose`/`ipa_extractV` — the target is data, so the bare existentials cannot be
  -- case-split. The supplied opening `a` seeds slot `0`, so no honest-run extraction is needed.
  have hex := exists_injective_accepting_of_measure
    (acc := OpenedX4Accept urs hk vk ps ch b) (x₀ := ch.x4) hx₀ hprob4
  set ξ := Classical.choose hex with hξdef
  have hspec := Classical.choose_spec hex
  have hξinj : Function.Injective ξ := hspec.1
  have hξ0 : ξ 0 = ch.x4 := hspec.2.1
  have hacc : ∀ r : Fin (deployedX4PairCount vk ps ch + 1),
      ∃ (z' blind' : Fp) (fs : ForkedTranscript urs hk vk ps {ch with x4 := ξ r} b z' blind')
        (t : IpaTreeV Fp G urs.k),
        IpaAcceptV urs.g b fs.openedCommitment (multiopenValue vk ps {ch with x4 := ξ r}) t :=
    hspec.2.2
  choose zf blindf fsf tf htf using hacc
  let extF := fun r => ipa_extractV urs.g b ((fsf r).openedCommitment)
    (multiopenValue vk ps {ch with x4 := ξ r}) (tf r) (htf r)
  have hC : ∀ r, commit urs (Fin.cases a (fun i => (extF i.succ).1) r)
      + (Fin.cases (motive := fun _ => Fp) pU (fun i => (fsf i.succ).pU) r) • urs.u
      + (Fin.cases (motive := fun _ => Fp) pW (fun i => (fsf i.succ).pW) r) • urs.w
      = deployedCommitment urs hk vk ps {ch with x4 := ξ r} := by
    intro r
    cases r using Fin.cases with
    | zero =>
        simp only [Fin.cases_zero]
        rw [hξ0, hrel.1, hP]
        show deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w
            + pU • urs.u + pW • urs.w = deployedCommitment urs hk vk ps ch
        abel
    | succ i =>
        simp only [Fin.cases_succ]
        rw [commit_eq_commitGen, (extF i.succ).2.1]
        show deployedCommitment urs hk vk ps {ch with x4 := ξ i.succ}
            - (fsf i.succ).pU • urs.u - (fsf i.succ).pW • urs.w
            + (fsf i.succ).pU • urs.u + (fsf i.succ).pW • urs.w
          = deployedCommitment urs hk vk ps {ch with x4 := ξ i.succ}
        abel
  have hv : ∀ r, commitGen b (Fin.cases a (fun i => (extF i.succ).1) r)
      = multiopenValue vk ps {ch with x4 := ξ r} := by
    intro r
    cases r using Fin.cases with
    | zero =>
        simp only [Fin.cases_zero]
        rw [hξ0]
        have hib : commitGen b a = innerProduct a b := by
          simp [innerProduct, commitGen, smul_eq_mul]
        rw [hib]
        exact hrel.2
    | succ i =>
        simp only [Fin.cases_succ]
        exact (extF i.succ).2.2
  have hbatch := openedX4Batch_of_witnessFamily urs hk vk ps ch ξ hξinj 0
    (Fin.cases (motive := fun _ => Fin (2 ^ urs.k) → Fp) a fun i => (extF i.succ).1)
    (Fin.cases (motive := fun _ => Fp) pU fun i => (fsf i.succ).pU)
    (Fin.cases (motive := fun _ => Fp) pW fun i => (fsf i.succ).pW) hC hv
  simp only [Fin.cases_zero] at hbatch
  exact hbatch

open scoped ENNReal in
open Classical in
/-- `openedX4Rewind_of_x4Prob` at a given honest fork: the statement is the fork's
`openedCommitment` at its declared components, and the fork's clean accepting transcript supplies
the honest-slot event. -/
noncomputable def openedX4Rewind_of_x4Prob_forked [DecidableEq G] [Inhabited G] {shape : Shape}
    (urs : URS G) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp G)
    (ps : ProofString shape Fp G) (ch : Challenges shape.k Fp) {b : Fin (2 ^ urs.k) → Fp}
    {z blind : Fp} (fsCur : ForkedTranscript urs hk vk ps ch b z blind)
    (hcur : ∃ t : IpaTreeV Fp G urs.k,
      IpaAcceptV urs.g b fsCur.openedCommitment (multiopenValue vk ps ch) t)
    (hprob4 : ((deployedX4PairCount vk ps ch : ℝ≥0∞)) / Fintype.card Fp
      < (PMF.uniformOfFintype Fp).toOuterMeasure (Finset.univ.filter
          (OpenedX4Accept urs hk vk ps ch b))) :
    OpenedRewindForRelation urs fsCur.openedCommitment b (multiopenValue vk ps ch)
      (x4BatchCommitments urs hk vk ps ch) (x4BatchEvals vk ps ch) fsCur.pU fsCur.pW :=
  openedX4Rewind_of_x4Prob urs hk vk ps ch fsCur.openedCommitment fsCur.pU fsCur.pW rfl
    (by obtain ⟨t, ht⟩ := hcur; exact ⟨z, blind, fsCur, t, ht⟩) hprob4

/-- At the deployed instantiation with the honest batching challenge in the current slot, the
batch's own current-slot equations already open the fork's statement: the power sums collapse to
`deployedCommitment`/`multiopenValue` at `ch.x4`
(`deployedCommitment_x4_batch`/`multiopenValue_x4_batch`), so the current triple `(a₀, pU, pW)` is
an `IpaRelation` witness for the opened commitment. The pinned capstone derives its opening from
this rather than assuming it. -/
theorem OpenedBatchOpenings.ipaRelation_of_x4Current [DecidableEq G] [Inhabited G] {shape : Shape}
    {urs : URS G} {hk : shape.k = urs.k} {vk : VerifyingKey shape Fp G}
    {ps : ProofString shape Fp G} {ch : Challenges shape.k Fp} {b : Fin (2 ^ urs.k) → Fp}
    {a₀ : Fin (2 ^ urs.k) → Fp} {pU pW : Fp}
    (hb : OpenedBatchOpenings urs b (x4BatchCommitments urs hk vk ps ch)
      (x4BatchEvals vk ps ch) a₀ pU pW)
    (hξcur : hb.batchChallenge hb.current = ch.x4) :
    IpaRelation urs (deployedCommitment urs hk vk ps ch - pU • urs.u - pW • urs.w) b
      (multiopenValue vk ps ch) a₀ := by
  constructor
  · have hc := hb.commitment hb.current
    rw [hb.current_eq, hb.currentU_eq, hb.currentW_eq, hξcur] at hc
    have hd : (∑ j : Fin (deployedX4PairCount vk ps ch + 1),
        ch.x4 ^ (j : ℕ) • x4BatchCommitments urs hk vk ps ch j)
        = deployedCommitment urs hk vk ps ch :=
      (deployedCommitment_x4_batch urs hk vk ps ch ch.x4).symm
    rw [hd] at hc
    rw [← hc]
    abel
  · have hv := hb.value hb.current
    rw [hb.current_eq, hξcur] at hv
    have hd : (∑ j : Fin (deployedX4PairCount vk ps ch + 1),
        ch.x4 ^ (j : ℕ) • x4BatchEvals vk ps ch j) = multiopenValue vk ps ch :=
      (multiopenValue_x4_batch vk ps ch ch.x4).symm
    rw [hd] at hv
    have hib : innerProduct a₀ b = commitGen b a₀ := by
      simp [innerProduct, commitGen, smul_eq_mul]
    rw [hib]
    exact hv

/-! ## The terminal constraint endpoints -/

open Polynomial in
/-- The SNARK relation with the circuit side fed by columns decoded from the opened batch family
containing the extracted witness — the opened counterpart of `SnarkRelationWithDecodedColumns`, the
declared components carried through. -/
structure SnarkRelationWithOpenedColumns (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → Fp) (v : Fp)
    {numColumns numAdvice numInstance : ℕ}
    (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp)
    (adviceIndex : Fin numAdvice → Fin numColumns) (instanceIndex : Fin numInstance → Fin numColumns)
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ)
    (pU pW : Fp)
    (a : Fin (2 ^ urs.k) → Fp) (cols : Fin numColumns → Polynomial Fp) where
  opens : IpaRelation urs P b v a
  batchOpenings : OpenedBatchOpenings urs b columnCommitments columnEvals a pU pW
  decodedColumns : OpenedColumnDecode batchOpenings
  polynomial : ∀ i, cols i = coeffsToPoly (decodedColumns.coeffs i)
  satisfiesCircuit :
    circuitSatViaGates fixedCols (selectedPolysDecode (k := urs.k) cols adviceIndex)
      (selectedPolysDecode (k := urs.k) cols instanceIndex) y gates hpoly deg a

open Polynomial in
/-- Turn a final opened relation plus its batch family into the opened decoded-column SNARK
relation. `hquot`/`hgood` are stated for the canonical decode `openedDecodedCols hbatch` — the
family this proof constructs — with the plain chain's scoping (`Soundness.Multiopen.Decode`, the
scope section). -/
theorem opened_constraint_of_relation_and_batch {urs : URS G} {P : G}
    {b : Fin (2 ^ urs.k) → Fp} {v : Fp}
    {numColumns numAdvice numInstance : ℕ}
    (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp)
    (adviceIndex : Fin numAdvice → Fin numColumns) (instanceIndex : Fin numInstance → Fin numColumns)
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    {pU pW : Fp} {a : Fin (2 ^ urs.k) → Fp}
    (hrel : IpaRelation urs P b v a)
    (hbatch : OpenedBatchOpenings urs b columnCommitments columnEvals a pU pW)
    (hquot : quotientCheck
      (combineGates fixedCols (selectedPolys (openedDecodedCols hbatch) adviceIndex)
        (selectedPolys (openedDecodedCols hbatch) instanceIndex) y gates) hpoly deg x)
    (hgood : combineGates fixedCols (selectedPolys (openedDecodedCols hbatch) adviceIndex)
        (selectedPolys (openedDecodedCols hbatch) instanceIndex) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (selectedPolys (openedDecodedCols hbatch) adviceIndex)
        (selectedPolys (openedDecodedCols hbatch) instanceIndex) y gates
          - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a cols,
      SnarkRelationWithOpenedColumns urs P b v columnCommitments columnEvals adviceIndex
        instanceIndex fixedCols y gates hpoly deg pU pW a cols → S) :
    S := by
  have hsat : circuitSatViaGates fixedCols
      (selectedPolysDecode (k := urs.k) (openedDecodedCols hbatch) adviceIndex)
      (selectedPolysDecode (k := urs.k) (openedDecodedCols hbatch) instanceIndex)
      y gates hpoly deg a :=
    circuitSatViaGates_of_check fixedCols
      (selectedPolysDecode (k := urs.k) (openedDecodedCols hbatch) adviceIndex)
      (selectedPolysDecode (k := urs.k) (openedDecodedCols hbatch) instanceIndex)
      y gates hpoly deg a x hquot hgood
  exact hencodes a (openedDecodedCols hbatch)
    { opens := hrel
      batchOpenings := hbatch
      decodedColumns := openedColumnDecode hbatch
      polynomial := fun i => rfl
      satisfiesCircuit := hsat }

open Polynomial in
/-- Lift an opening-or-relation terminal capstone to the opened decoded-column constraint endpoint,
the batch family supplied by `OpenedRewindForRelation` — the opened counterpart of
`decoded_constraint_of_opening_or_relation`, with the same conditional interface and `hquot`/`hgood`
scoping. Reduction-shaped: quantifying `hquot ∧ hgood` over every opening is jointly unsatisfiable
once the commitment kernel is nontrivial (see the scope section of `Soundness.Multiopen.Decode`);
the live capstones pin the witness instead — the fork's extraction
(`orchard_verifier_vesta_decoded_constraint_of_forked_x4`) or a designated batch with the
mismatch-to-DLR split (`orchard_verifier_vesta_forking_constraint_deployed_x4`). -/
theorem opened_constraint_of_opening_or_relation {urs : URS G} {P : G}
    {b : Fin (2 ^ urs.k) → Fp} {v : Fp}
    {numColumns numAdvice numInstance : ℕ}
    (columnCommitments : Fin numColumns → G) (columnEvals : Fin numColumns → Fp)
    (adviceIndex : Fin numAdvice → Fin numColumns) (instanceIndex : Fin numInstance → Fin numColumns)
    (fixedCols : ℕ → Polynomial Fp)
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    {pU pW : Fp}
    (hopening : (∃ a, IpaRelation urs P b v a) ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w)
    (hbatch : OpenedRewindForRelation urs P b v columnCommitments columnEvals pU pW)
    (hquot : ∀ a (hrel : IpaRelation urs P b v a),
      quotientCheck
        (combineGates fixedCols (selectedPolys (openedDecodedCols (hbatch a hrel)) adviceIndex)
          (selectedPolys (openedDecodedCols (hbatch a hrel)) instanceIndex) y gates) hpoly deg x)
    (hgood : ∀ a (hrel : IpaRelation urs P b v a),
      combineGates fixedCols (selectedPolys (openedDecodedCols (hbatch a hrel)) adviceIndex)
          (selectedPolys (openedDecodedCols (hbatch a hrel)) instanceIndex) y gates
        ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (selectedPolys (openedDecodedCols (hbatch a hrel)) adviceIndex)
          (selectedPolys (openedDecodedCols (hbatch a hrel)) instanceIndex) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a cols,
      SnarkRelationWithOpenedColumns urs P b v columnCommitments columnEvals adviceIndex
        instanceIndex fixedCols y gates hpoly deg pU pW a cols → S) :
    S ∨ HasNontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rcases hopening with ⟨a, hrel⟩ | hrel
  · exact Or.inl (opened_constraint_of_relation_and_batch columnCommitments columnEvals adviceIndex
      instanceIndex fixedCols y gates hpoly deg x hrel (hbatch a hrel) (hquot a hrel) (hgood a hrel)
      hencodes)
  · exact Or.inr hrel

end Opened

end Zcash.Snark
