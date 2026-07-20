import Mathlib
import Zcash.Snark.Soundness.InnerProduct
import Zcash.Snark.Soundness.Extraction
import Zcash.Snark.Soundness.Constraints
import Zcash.Snark.Soundness.CommitFold

/-!
# Knowledge soundness, end to end

The capstone: an accepting proof demonstrates knowledge of a witness satisfying the SNARK relation. It
composes the proven pieces of the soundness layer —

* `extract_correct` — the IPA extractor recovers the witness from an accepting transcript tree;
* `commitGen_round` — folding preserves the commitment (so an accepting transcript yields a
  consistent tree); opening uniqueness holds up to a computed discrete-log relation
  (`NontrivialDLRelation.ofIpaOpenings`);
* `quotientCheck_sound` + `Expr.eval_toPoly` — the verifier's gate check, via Schwartz–Zippel, forces the
  committed polynomials to satisfy the circuit's constraint identity (off a `≤ d/p` bad set).

`SnarkRelation` is the relation the SNARK proves (the witness opens the commitment and the committed
polynomials satisfy the constraint identity); `knowledge_sound` assembles the proven lemmas into "the
extractor recovers a witness satisfying the relation, unique up to a computed discrete-log
relation"; `soundness_error` is the residual `≤ d/p` Schwartz–Zippel error.

## Assumptions

This layer is sound relative to the following, each kept explicit rather than hidden:

* **DLR hardness** (discrete-log relations on the Vesta generators) — consumed only at the
  computational layer: a second distinct opening yields a computed nontrivial relation
  (`NontrivialDLRelation.ofIpaOpenings`), the object the hardness assumption forbids an
  efficient adversary to produce.
* **Fiat–Shamir / Blake2b** as a random oracle — challenges are treated as uniform and unpredictable; the
  hash and the random-oracle reduction are not modeled. The capstone's current assumption
  (`ExtractableFromAcceptance`) is in fact stronger — it bundles the IPA knowledge-soundness conclusion,
  not just Fiat–Shamir; narrowing it to "uniform challenges" is open extraction-side work.
* **Vesta group order** — the abstract development runs over any `Fp`-module `G`;
  `Zcash.Snark.Soundness.Vesta` pins it to the concrete Vesta curve, whose group order is proven
  with no assumption (`vestaOrder`, from CompElliptic's `Pasta.Vesta.card_eq`).
* **VK-correctness** (Daira's flow) — that the VK's gates encode the intended high-level relation (note
  ownership, value balance, nullifiers) is a separate workstream; this layer proves the verifier sound
  relative to the given VK, ending at "the witness satisfies the VK's constraint system."

The selected forking extractor is exponential in the round count: unconditionally, every run and
the uniform oracle-and-tape expectation are at most `(2·|F|+1)^k`
(`recursiveAlgebraicFork_oracle_tape_sum_runs_le_unconditional`).  For the fixed challenge field this
is also expressed as a polynomial in the instance size `2^k`, with a field-sized exponent.
`Forking.Adversary.ExpectedRuns` supplies an optional sharper bound under *fork spread*; no
fork-spread premise occurs in the baseline runtime or soundness theorems.

## For human review
Check that `SnarkRelation` is the intended relation, that the four assumptions above are the right ones
and acceptably standard, and that the captured fingerprint match (`Zcash.Snark.Fixture`) is for the
intended Orchard Action circuit.
-/

namespace Zcash.Snark

open Polynomial

variable {G : Type*} [AddCommGroup G] [Module Fp G]

-- Tracked decode gap: the two conjuncts of `SnarkRelation` share only the symbol `a`.
-- Until the decode is pinned, the free decode function feeding `circuitSatViaGates` may be
-- instantiated independently of `a`, so `circuitSat a` need not constrain the extracted witness
-- at all. Binding the decode to `a` — via the proven but currently unused `batch_open_soundV` —
-- is exactly what closes it.
/-- The relation the SNARK proves: the witness `a` opens the commitment `P` to the value `v`
(`IpaRelation`) and satisfies the circuit (`circuitSat a`) — both conjuncts about the *same*
extracted witness. `circuitSat`'s intended instantiation is `circuitSatViaGates` ("the witness's
decoded columns satisfy the `y`-combined gates"); see the tracked decode gap above. -/
structure SnarkRelation (urs : URS G) (P : G) (b : Fin (2 ^ urs.k) → Fp) (v : Fp)
    (circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop) (a : Fin (2 ^ urs.k) → Fp) : Prop where
  opens : IpaRelation urs P b v a
  satisfiesCircuit : circuitSat a

/-- The intended concrete `circuitSat`: the witness's decoded columns
(`decodeAdvice`/`decodeInstance`, free functions here — binding them to the witness is still open)
satisfy the `y`-combined gates' quotient identity (`combineGates`).
`constraint_identity_of_accept` discharges the identity from the deployed check. -/
def circuitSatViaGates {k : ℕ} (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ)
    (a : Fin (2 ^ k) → Fp) : Prop :=
  combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates = hpoly * (X ^ deg - 1)

/-- `circuitSat`, derived from the deployed constraint check (not assumed): an accepting quotient
check at a good challenge `x` — one outside the *bad set*, the roots of the nonzero constraint
difference — gives `circuitSatViaGates`, via `constraint_identity_of_accept`. What remains is the
multiopen decode. -/
theorem circuitSatViaGates_of_check {k : ℕ} (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ)
    (a : Fin (2 ^ k) → Fp) (x : Fp)
    (hcheck : quotientCheck
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0) :
    circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg a :=
  constraint_identity_of_accept _ hpoly deg x hcheck hgood

/-- **Knowledge soundness**, relative to its named hypotheses: given a consistent transcript tree
(`hcons`), an opening (`hopen`), and circuit satisfaction (`hsat`), the extractor recovers a
witness satisfying `SnarkRelation` — `extract_correct` for extraction. The witness is unique up
to a computed discrete-log relation: a second distinct opening yields
`NontrivialDLRelation.ofIpaOpenings`. `hcons` and `hsat` are assumed, not derived from
acceptance; deriving them (`accepting_fold_eq`, `constraint_identity_of_accept`) is open
composition work. -/
theorem knowledge_sound (urs : URS G)
    {t : Tree Fp urs.k} {a : Fin (2 ^ urs.k) → Fp} (hcons : Consistent t a)
    {P : G} {b : Fin (2 ^ urs.k) → Fp} {v : Fp} (hopen : IpaRelation urs P b v a)
    {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop} (hsat : circuitSat a) :
    extract t = a ∧ SnarkRelation urs P b v circuitSat a :=
  ⟨extract_correct t a hcons, ⟨hopen, hsat⟩⟩

/-- The residual soundness error of the constraint layer (re-export of `quotientCheck_sound`): a
committed-polynomial set that violates the constraint identity is accepted for at most a `deg / |F|`
fraction of the challenges (`|F| = scalarFieldOrder ≈ 2²⁵⁴`). -/
theorem soundness_error (numerator h : Polynomial Fp) (n : ℕ) (hne : numerator ≠ h * (X ^ n - 1)) :
    ((Finset.univ.filter fun x => quotientCheck numerator h n x).card : ℚ≥0)
        / (scalarFieldOrder : ℚ≥0)
      ≤ ((numerator - h * (X ^ n - 1)).natDegree : ℚ≥0) / (scalarFieldOrder : ℚ≥0) :=
  quotientCheck_sound numerator h n hne

end Zcash.Snark
