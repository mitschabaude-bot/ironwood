import Mathlib
import Zcash.Snark.Soundness.Main
import Zcash.Snark.Soundness.Forking.Rewind
import CompElliptic.Curves.Pasta
import CompElliptic.Curves.PastaOrder

/-!
# Vesta instantiation: the verifier group at the deployed curve

The soundness theorems of `Zcash.Snark.Soundness.Main` are proven for an abstract
`Fp`-module `G`. Here `G` is pinned to the actual Vesta curve `SWPoint Vesta.curve` (`y² = x³ + 5`),
whose group law CompElliptic/mathlib have already proven (associativity transported from
`WeierstrassCurve.Affine.Point`). The deployed Orchard verifier runs over Vesta, so these theorems are
the concrete-curve forms of the abstract capstones.

## The setting

The only structure the `Fp`-action needs that the curve does not already carry is the Vesta group
order: every point is `p`-torsion (`p = scalarFieldOrder`). Given that, `AddCommGroup.zmodModule`
turns the curve into an `Fp`-module and the end-to-end theorems apply verbatim.

## Assumptions

* **The Vesta group order — no assumption.** CompElliptic's `Pasta.Vesta.card_eq` proves
  `Nat.card VestaG = scalarFieldOrder` (an elementary point-count bound stands in for Hasse, which
  Mathlib lacks — see CompElliptic's `CurveOrder`), whence every point is annihilated by the group
  order (`vestaOrder`).
-/

namespace Zcash.Snark

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass CompElliptic.CurveOrder

/-- The verifier group `E_q`, concretely: the points of the Vesta curve `y² = x³ + 5`. -/
abbrev VestaG := SWPoint Vesta.curve

/-- The Vesta group order as a proposition: every Vesta point is `p`-torsion, i.e. the group order
divides `p = scalarFieldOrder`. Proven unconditionally (`vestaOrder`); carried as a `Fact` so
`vestaFpModule` can consume it. -/
abbrev VestaOrder : Prop := ∀ P : VestaG, (scalarFieldOrder : ℕ) • P = 0

/-- The Vesta group order, unconditionally: CompElliptic's `Pasta.Vesta.card_eq` gives
`Nat.card VestaG = scalarFieldOrder` with no assumption, and a finite group is annihilated by its
order. -/
theorem vestaOrder : VestaOrder := by
  intro P
  have hcard : Nat.card VestaG = scalarFieldOrder := Vesta.card_eq
  rw [← hcard]
  exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (addOrderOf_dvd_natCard P)

/-- The Vesta order `Fact` — hence the `Fp`-module — is supplied unconditionally, from `vestaOrder`
(CompElliptic pins the order with no assumption). -/
instance : Fact VestaOrder := ⟨vestaOrder⟩

/-- Given the Vesta group order (`Fact VestaOrder`), the curve is an `Fp`-module
(`AddCommGroup.zmodModule` on the `p`-torsion). Conditional — it fires only when the order `Fact`
is in scope (now unconditionally, via `vestaOrder`). Computable (curve addition and the
`ZMod`-action both are), so the break reductions stay plain `def`s at the concrete curve. -/
instance vestaFpModule [h : Fact VestaOrder] : Module Fp VestaG :=
  AddCommGroup.zmodModule h.out

/-- **Conditional soundness at Vesta.** `orchard_verifier_sound_conditional` specialised to
`SWPoint Vesta.curve`; the Vesta group order (hence the `Fp`-module structure) is pinned
unconditionally. Inherits the conditional status — see that docstring.
The deployed Vesta capstones are `orchard_verifier_vesta_opening_of_forked`/`_constraint_of_forked`
below, with `NontrivialRelation.ofUnopenedForkVesta` the computed break. -/
theorem orchard_verifier_sound_vesta_conditional
    (urs : URS VestaG)
    {P : VestaG} {b : Fin (2 ^ urs.k) → Fp} {v : Fp} {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop}
    {accepts : Prop} (haccepts : accepts)
    (hextract : ExtractableFromAcceptance urs P b v circuitSat accepts)
    {S : Prop} (hencodes : ∀ a, SnarkRelation urs P b v circuitSat a → S) :
    S :=
  orchard_verifier_sound_conditional urs haccepts hextract hencodes

/-- **The deployed binding reduction over Vesta, as a computed relation.**
`NontrivialRelation.ofUnopenedFork` specialised to `SWPoint Vesta.curve`: a forked transcript
whose projection is not cleanly accepted computes a nontrivial discrete-log relation among the
Vesta generators `(g, U, W)`, which DLR hardness forbids (the contrapositive reading — see
`The reduction form` in `Soundness.Main`). -/
def NontrivialRelation.ofUnopenedForkVesta [DecidableEq VestaG]
    [Inhabited VestaG]
    {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp} (hz : z ≠ 0)
    (fs : ForkedTranscript urs hk vk ps ch b z blind)
    (hne : ¬ IpaAcceptV urs.g b fs.openedCommitment (multiopenValue vk ps ch)
      (projTree fs.tree)) :
    NontrivialRelation (F := Fp) urs.g urs.u urs.w :=
  NontrivialRelation.ofUnopenedFork urs hk vk ps ch hz fs hne

/-- **Deployed opening over Vesta, given a clean fork.**
`orchard_verifier_deployed_opening_of_forked` specialised to `SWPoint Vesta.curve`: same
hypotheses as the abstract theorem (the Vesta order is unconditional). The clean-accept hypothesis is what
DLR hardness forces (`NontrivialRelation.ofUnopenedForkVesta`); for `hcirc`'s unsatisfiable
shape see the section note in `Soundness.Main`. -/
theorem orchard_verifier_vesta_opening_of_forked [DecidableEq VestaG] [Inhabited VestaG]
    {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp} {circuitSat : (Fin (2 ^ urs.k) → Fp) → Prop}
    (fs : ForkedTranscript urs hk vk ps ch b z blind)
    (hclean : IpaAcceptV urs.g b fs.openedCommitment (multiopenValue vk ps ch)
      (projTree fs.tree))
    (hcirc : ∀ a, IpaRelation urs fs.openedCommitment b (multiopenValue vk ps ch) a →
      circuitSat a)
    {S : Prop} (hencodes : ∀ a, SnarkRelation urs fs.openedCommitment b
      (multiopenValue vk ps ch) circuitSat a → S) :
    S :=
  orchard_verifier_deployed_opening_of_forked urs hk vk ps ch fs hclean hcirc hencodes

open Polynomial in
/-- **Deployed opening and constraint over Vesta, given a clean fork.**
`orchard_verifier_deployed_constraint_of_forked` specialised to `SWPoint Vesta.curve`: the opening
for the declared `fs.openedCommitment` and the pinned `multiopenValue`, and `circuitSat` (concrete
`circuitSatViaGates`) from the verifier's gate point-check `hquot` lifted by Schwartz–Zippel
(`hgood`). Same hypotheses as the abstract theorem (the Vesta order is unconditional); `hquot`/`hgood` share
`hcirc`'s unsatisfiable shape (see the section note in `Soundness.Main`). -/
theorem orchard_verifier_vesta_constraint_of_forked [DecidableEq VestaG] [Inhabited VestaG]
    {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k) (vk : VerifyingKey shape Fp VestaG)
    (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    {b : Fin (2 ^ urs.k) → Fp} {z blind : Fp}
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (fs : ForkedTranscript urs hk vk ps ch b z blind)
    (hclean : IpaAcceptV urs.g b fs.openedCommitment (multiopenValue vk ps ch)
      (projTree fs.tree))
    (hquot : ∀ a, IpaRelation urs fs.openedCommitment b (multiopenValue vk ps ch) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs fs.openedCommitment b (multiopenValue vk ps ch) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs fs.openedCommitment b (multiopenValue vk ps ch)
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S) :
    S :=
  orchard_verifier_deployed_constraint_of_forked urs hk vk ps ch fixedCols decodeAdvice
    decodeInstance y gates hpoly deg x fs hclean hquot hgood hencodes

/-- The powers evaluation vector's leading entry is `1` (`b 0 = x⁰ = 1`), discharging the IPA's `hb0`
structural fact for the concrete deployed `b = evalVector`. -/
theorem evalVector_zero {F : Type*} [Field F] (k : ℕ) (x : F) : evalVector k x 0 = 1 := by
  simp [evalVector]

/-- halo2's adjusted IPA witness: `aMulti` with its `g₀`-coefficient shifted by the claimed value and the
synthetic blinder `ξ·s` folded in, so its commitment is the adjusted commitment `⟨aMulti,G⟩ − [v]g₀ + [ξ]S`.
Making it a *definition* (rather than positing an `aDep` with a relation `hP`) discharges `hP` by the linearity
of `commit`. -/
def adjustedWitness {k : ℕ} (aMulti s : Fin (2 ^ k) → Fp) (v ξ : Fp) : Fin (2 ^ k) → Fp :=
  aMulti - Pi.single 0 v + ξ • s

/-- The adjusted witness commits to halo2's adjusted commitment — `hP` holds by linearity, not by assumption. -/
theorem commit_adjustedWitness {G : Type*} [AddCommGroup G] [Module Fp G] (urs : URS G)
    (aMulti s : Fin (2 ^ urs.k) → Fp) (v ξ : Fp) :
    commit urs (adjustedWitness aMulti s v ξ) = commit urs aMulti - v • urs.g 0 + ξ • commit urs s := by
  have csub : ∀ a a' : Fin (2 ^ urs.k) → Fp, commit urs (a - a') = commit urs a - commit urs a' := by
    intro a a'; simp only [commit, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  rw [adjustedWitness, commit_add, csub, commit_single, commit_smul]

/-- **The deployed commitment lies in the `g`-span (discharging `hcommit`).** At Vesta's prime order a nonzero
generator `urs.g 0` generates the whole group: `c ↦ c • g 0` is injective over the field `Fp` (a nonzero
scalar is invertible) and `Fp` and `VestaG` have equal cardinality (`scalarFieldOrder`), so it is surjective —
every group element, in particular `deployedCommitment`, is the `g`-commitment of some witness. So the
`hcommit` tie is always satisfiable: it is the prime-order/`g`-span fact, the witness being the discrete log of
`P` base `g 0` (existing but not feasibly constructible — the same DLR-side status as the
`⊕' NontrivialRelation` disjunct). -/
theorem commit_surjective [Fact (HasseBound Vesta.curve)] (urs : URS VestaG) (hg0 : urs.g 0 ≠ 0)
    (P : VestaG) : ∃ aMulti : Fin (2 ^ urs.k) → Fp, commit urs aMulti = P := by
  have hinj : Function.Injective (fun c : Fp => c • urs.g 0) := by
    intro c c' h
    have h' : c • urs.g 0 = c' • urs.g 0 := h
    rcases eq_or_ne c c' with hcc | hcc
    · exact hcc
    · refine absurd ?_ hg0
      have hd : c - c' ≠ 0 := sub_ne_zero.mpr hcc
      have h0 : (c - c') • urs.g 0 = 0 := by rw [sub_smul, h', sub_self]
      rw [← one_smul Fp (urs.g 0), ← inv_mul_cancel₀ hd, mul_smul, h0, smul_zero]
  haveI : Fintype VestaG := Fintype.ofFinite VestaG
  have hcardeq : Fintype.card Fp = Fintype.card VestaG := by
    rw [card_Fp, ← Nat.card_eq_fintype_card, Vesta.card_eq Fact.out]
  obtain ⟨c, hc⟩ := ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcardeq⟩).surjective P
  exact ⟨Pi.single 0 c, by rw [commit_single]; exact hc⟩

open scoped ENNReal in
/-- **The ξ-randomization budget behind the constraint capstone's value recovery.** A malicious blinder with
`⟨s,b⟩ = δ ≠ 0` satisfies the value-recovery premise `ξ·⟨s,b⟩ = 0` — which pins the opened value back to the
claimed `multiopenValue` — only at `ξ = 0`, a set of uniform random-oracle measure `≤ 1/p`. So the `hξ`
hypothesis of `orchard_verifier_vesta_forking_constraint` is, for a nonzero blinder, satisfiable only on a
`1/p`-measure set of post-`S` challenges: the Schwartz–Zippel `ξ`-exclusion (`blinder_shift_badSet_measure`)
made explicit for the constraint side. -/
theorem blinder_value_recovery_badSet {k : ℕ} (s : Fin (2 ^ k) → Fp) (xEval : Fp)
    (hδ : innerProduct s (evalVector k xEval) ≠ 0) :
    uniformChallenge.toOuterMeasure
        (Finset.univ.filter (fun ξ : Fp => ξ * innerProduct s (evalVector k xEval) = 0))
      ≤ 1 / (Fintype.card Fp : ℝ≥0∞) :=
  blinder_shift_badSet_measure (innerProduct s (evalVector k xEval)) 0 hδ

open scoped ENNReal in
open Classical in
/-- **The deployed Orchard opening over Vesta, via the forking refinements (no `FiatShamirTree`), with the
structural facts discharged.** Routes the forking development to the concrete deployed instance. The multiopen
evaluation vector is the concrete powers vector `b = evalVector urs.k xEval` (so `b 0 = 1` is *proved* by
`evalVector_zero`, not assumed); the multiopen witness `aMulti` is *recovered* from the `g`-span
(`commit_surjective`, from the nonzero generator `hg0`), so the `g`-span tie `hcommit` is **discharged** rather
than assumed; and the adjusted witness is *constructed*, so halo2's adjusted-commitment relation `hP` holds by
linearity (`commit_adjustedWitness`). The synthetic blinder is stripped *unconditionally*: the conclusion is
the **true** opened value `multiopenValue − ξ·⟨s,b⟩`, with no `⟨s,b⟩ = 0` assumed — covering a malicious blinder
(the honest case `⟨s,b⟩ = 0` recovers the claimed value). What remains is the explicit prover-as-oracle bridge
`hbridge` (the irreducible random-oracle floor), plus the antecedents `z ≠ 0`, the nonzero generator `hg0`, and
the accept probability `hprob` beating the knowledge error `kerr/Nᵏ`. The `⊕' NontrivialRelation` caveat is
unchanged — vacuous at Vesta's prime order, the force in the out-of-Lean DLR/AGM layer. -/
noncomputable def orchard_verifier_vesta_forking_opening [Fact (HasseBound Vesta.curve)] [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    (xEval ξ z blind : Fp) (s : Fin (2 ^ urs.k) → Fp)
    (Q : Prover Fp VestaG urs.k) (accepts : (Fin urs.k → Fp) → Prop)
    (hz : z ≠ 0) (hg0 : urs.g 0 ≠ 0)
    (hbridge : ∀ χ, accepts χ ↔ flatAccept Q urs.g (evalVector urs.k xEval) urs.u urs.w z
        (deployedCommitment urs hk vk ps ch - multiopenValue vk ps ch • urs.g 0 + ξ • commit urs s
          + (z * 0) • urs.u + blind • urs.w) χ)
    (hprob : (kerr (Fintype.card Fp) urs.k : ℝ≥0∞) / Fintype.card (Fin urs.k → Fp)
        < (PMF.uniformOfFintype (Fin urs.k → Fp)).toOuterMeasure (Finset.univ.filter accepts)) :
    (∃ a, IpaRelation urs (deployedCommitment urs hk vk ps ch) (evalVector urs.k xEval)
        (multiopenValue vk ps ch - ξ * innerProduct s (evalVector urs.k xEval)) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  -- `aMulti` is the (prime-order) `g`-preimage of the deployed commitment, named as data by
  -- `Classical.choose` — the source of this `def`'s `noncomputable`.
  have hcs := commit_surjective urs hg0 (deployedCommitment urs hk vk ps ch)
  set aMulti := hcs.choose with haMulti
  have hcommit : commit urs aMulti = deployedCommitment urs hk vk ps ch := hcs.choose_spec
  have hbr : ∀ χ, accepts χ ↔ flatAccept Q urs.g (evalVector urs.k xEval) urs.u urs.w z
      (commit urs (adjustedWitness aMulti s (multiopenValue vk ps ch) ξ)
        + (z * 0) • urs.u + blind • urs.w) χ := by
    intro χ
    rw [commit_adjustedWitness, hcommit]
    exact hbridge χ
  have h := deployed_forking_soundness_of_bridge urs (evalVector urs.k xEval) (multiopenValue vk ps ch) ξ z
    blind aMulti (adjustedWitness aMulti s (multiopenValue vk ps ch) ξ) s Q accepts hz
    (evalVector_zero urs.k xEval) (commit_adjustedWitness urs aMulti s (multiopenValue vk ps ch) ξ)
    hbr hprob
  rwa [hcommit] at h

open Polynomial in
open scoped ENNReal in
open Classical in
/-- **The deployed Orchard opening *and constraint* over Vesta, via the forking refinements (no
`FiatShamirTree`), with the structural facts discharged.** The constraint-side companion of
`orchard_verifier_vesta_forking_opening`: same concrete instance (`b = evalVector urs.k xEval`, so `b 0 = 1` is
*proved*; `aMulti` recovered from the `g`-span so `hcommit` is discharged; the adjusted witness *constructed*
so `hP` holds by linearity) and the same gate seam as `orchard_verifier_vesta_constraint_of_forked`
(`hquot`/`hgood` → `circuitSatViaGates`, `hencodes`). Unlike the opening, the circuit is checked at the
*claimed* value `multiopenValue`, so the minimal value-recovery hypothesis `hξ : ξ·⟨s,b⟩ = 0` is retained — it
pins the opened value `multiopenValue − ξ·⟨s,b⟩` (unique under binding) from the forking opening back to
`multiopenValue`. `hξ`
generalises honest blinding (`⟨s,b⟩ = 0`); for a *malicious* blinder (`⟨s,b⟩ ≠ 0`) it holds only on a
`1/p`-measure set of post-`S` challenges `ξ` (`blinder_value_recovery_badSet`, the `ξ`-randomization budget).
The deployed-curve residual is the explicit prover-as-oracle bridge `hbridge` (and the nonzero generator
`hg0`); both the opening and the constraint side now route through it with `b 0 = 1`, `hcommit`, and `hP`
discharged. The original `FiatShamirTree` reductions
(`orchard_verifier_vesta_opening_of_forked`/`_constraint`) remain as the coarser legacy endpoints. The
`⊕' NontrivialRelation` caveat is unchanged — vacuous at Vesta's prime order, the force in the out-of-Lean
DLR/AGM layer. `hquot`/`hgood` retain the ∀-openings shape — unsatisfiable at Vesta for any decode that
genuinely reads the witness (see `orchard_verifier_deployed_constraint_of_forked`'s caveat). -/
noncomputable def orchard_verifier_vesta_forking_constraint [Fact (HasseBound Vesta.curve)] [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    (xEval ξ z blind : Fp) (s : Fin (2 ^ urs.k) → Fp)
    (Q : Prover Fp VestaG urs.k) (accepts : (Fin urs.k → Fp) → Prop)
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hz : z ≠ 0) (hg0 : urs.g 0 ≠ 0)
    (hξ : ξ * innerProduct s (evalVector urs.k xEval) = 0)
    (hbridge : ∀ χ, accepts χ ↔ flatAccept Q urs.g (evalVector urs.k xEval) urs.u urs.w z
        (deployedCommitment urs hk vk ps ch - multiopenValue vk ps ch • urs.g 0 + ξ • commit urs s
          + (z * 0) • urs.u + blind • urs.w) χ)
    (hquot : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps ch) (evalVector urs.k xEval)
        (multiopenValue vk ps ch) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps ch) (evalVector urs.k xEval)
        (multiopenValue vk ps ch) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs (deployedCommitment urs hk vk ps ch) (evalVector urs.k xEval)
        (multiopenValue vk ps ch)
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S)
    (hprob : (kerr (Fintype.card Fp) urs.k : ℝ≥0∞) / Fintype.card (Fin urs.k → Fp)
        < (PMF.uniformOfFintype (Fin urs.k → Fp)).toOuterMeasure (Finset.univ.filter accepts)) :
    S ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rcases orchard_verifier_vesta_forking_opening urs hk vk ps ch xEval ξ z blind s Q accepts
      hz hg0 hbridge hprob with hopen | hrel
  · refine PSum.inl ?_
    obtain ⟨a, hrel'⟩ := hopen
    rw [hξ, sub_zero] at hrel'
    have hsat : circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg a :=
      circuitSatViaGates_of_check fixedCols decodeAdvice decodeInstance y gates hpoly deg a x
        (hquot a hrel') (hgood a hrel')
    exact hencodes a ⟨hrel', hsat⟩
  · exact PSum.inr hrel

/-- The deployed adjusted-commitment's value term `Σᵢ [-v].getD i • gᵢ` is `-v` on the single generator `g 0`
(the value list `[-v]` has one entry, placed at index `0`). Lets the deployed verifier's adjusted commitment
`multiopen + Σ[-v].getD·g` meet the capstone's `-v • g 0` form. Pure module algebra, stated over any
`Fp`-module (the Vesta instances supply `Module Fp VestaG` at the call sites). -/
theorem sum_getD_single {k : ℕ} {G : Type*} [AddCommGroup G] [Module Fp G] (gg : Fin (2 ^ k) → G)
    (v : Fp) :
    (∑ i, ([-v].getD i.val 0 : Fp) • gg i) = -v • gg 0 := by
  rw [Finset.sum_eq_single (0 : Fin (2 ^ k))]
  · simp
  · intro i _ hi
    have hival : i.val ≠ 0 := Fin.val_ne_zero_iff.mpr hi
    rw [List.getD_eq_default, zero_smul]
    simp only [List.length_cons, List.length_nil, Nat.zero_add]
    omega
  · intro h; exact absurd (Finset.mem_univ _) h

open scoped ENNReal in
open Classical in
/-- **The deployed Orchard opening over Vesta, with `hbridge` discharged.** This is
`orchard_verifier_vesta_forking_opening` with the abstract prover-as-oracle bridge *removed*: `accepts` is
halo2's **actual** verifier equation `DeployedIpaVerifierEq` at the rewound IPA challenges, and the bridge to
`flatAccept` of the concrete proof tree `proverOfRounds ps.ipaRounds ps.ipaC ps.ipaF` is **proven** internally
by `deployedVerifierEq_iff_flatAccept` — not assumed. The `shape.k`↔`urs.k` transport is discharged by
`subst`, and the commitment slot is reconciled (`sum_getD_single`, `deployedCommitment = multiopenCommitment`,
the `S`-opening `hs : commit urs s = ps.ipaS`, `module`). The remaining hypotheses are `z ≠ 0`, the nonzero
generator `hg0` (prime-order `g`-span), and the `S`-opening witness `hs` (such an opening always *exists* at
prime order but is not feasibly constructible for a malicious prover — the same exists-but-not-findable tier
as `commit_surjective` and the `⊕' NontrivialRelation` disjunct), plus the accept *probability* `hprob`
over the uniform IPA-challenge measure.

**Quantifier-shape caveat (`hprob`).** Discharging the bridge with the *constant* strategy `proverOfRounds`
changes what `hprob` measures: it is the accept set of this **fixed** proof string over *all* round-challenge
vectors — not the Fiat–Shamir attack event. A real prover (honest ones included) produces a proof whose
accept set is a low-degree variety of measure ≤ `3k/p` — clearing the verifier equation by `∏ χⱼ` leaves
total degree ≤ `2k`, so Schwartz–Zippel gives ≤ `2k/p`, plus ≤ `k/p` for the zero-challenge hyperplanes
where the total inverse departs from the cleared polynomial — generically ≈ `1/p`, and never *strictly
above* the `3k/p` threshold: `hprob` here is satisfiable only by a proof that accepts *identically*, while
a forger only needs its single RO-derived vector to land on that variety. So this theorem is the *static
dichotomy* "a proof accepting on more than `3k/p` of challenge space yields an opening". For adaptive
adversaries, use `orchard_verifier_vesta_forking_opening_adaptive` for the bridge-discharge over a
prefix-respecting strategy and `orchard_verifier_vesta_forking_opening_adaptive_rewind` when the accept event
should be stated over reprogrammed-oracle runs. The remaining floor there is not the deterministic bridge but
the execution-semantics identification — a rewound random-oracle adversary induces such a strategy, with its
RO-query loss. The `⊕' NontrivialRelation` caveat is unchanged — vacuous at Vesta's prime order. -/
noncomputable def orchard_verifier_vesta_forking_opening_deployed [Fact (HasseBound Vesta.curve)] [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    (s : Fin (2 ^ urs.k) → Fp) (hz : ch.z ≠ 0) (hg0 : urs.g 0 ≠ 0) (hs : commit urs s = ps.ipaS)
    (hprob : (kerr (Fintype.card Fp) shape.k : ℝ≥0∞) / Fintype.card (Fin shape.k → Fp)
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk ps
              {ch with ipaRound := χ}))) :
    (∃ a, IpaRelation urs (deployedCommitment urs hk vk ps ch) (evalVector urs.k ch.x3)
        (multiopenValue vk ps ch - ch.xi * innerProduct s (evalVector urs.k ch.x3)) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  obtain ⟨k, gg, ww, uu⟩ := urs
  change shape.k = k at hk
  subst hk
  refine orchard_verifier_vesta_forking_opening ⟨shape.k, gg, ww, uu⟩ rfl vk ps ch ch.x3 ch.xi ch.z 0 s
    (proverOfRounds ps.ipaRounds ps.ipaC ps.ipaF)
    (fun χ => DeployedIpaVerifierEq gg ww uu vk ps {ch with ipaRound := χ}) hz hg0 ?_ hprob
  intro χ
  dsimp only
  rw [deployedVerifierEq_iff_flatAccept]
  have hPwhole :
      (multiopenCommitment gg ww uu vk ps {ch with ipaRound := χ}
          + (∑ i, ([-(multiopenValue vk ps {ch with ipaRound := χ})].getD i.val 0) • gg i)
          + ({ch with ipaRound := χ} : Challenges shape.k Fp).xi • ps.ipaS)
        = (deployedCommitment ⟨shape.k, gg, ww, uu⟩ rfl vk ps ch
            - multiopenValue vk ps ch • gg 0 + ch.xi • commit ⟨shape.k, gg, ww, uu⟩ s
            + (ch.z * 0) • uu + 0 • ww) := by
    have e1 : multiopenValue vk ps {ch with ipaRound := χ} = multiopenValue vk ps ch := rfl
    have e2 : multiopenCommitment gg ww uu vk ps {ch with ipaRound := χ}
        = multiopenCommitment gg ww uu vk ps ch := rfl
    have e3 : ({ch with ipaRound := χ} : Challenges shape.k Fp).xi = ch.xi := rfl
    rw [e1, e2, e3, sum_getD_single gg (multiopenValue vk ps ch), ← hs]
    simp only [deployedCommitment]
    module
  rw [hPwhole]
  exact Iff.rfl

open Polynomial in
open scoped ENNReal in
open Classical in
/-- **The deployed Orchard opening *and constraint* over Vesta, with `hbridge` discharged.** The constraint
companion of `orchard_verifier_vesta_forking_opening_deployed`: same discharged bridge (halo2's actual verifier
accept, no abstract `hbridge`), routed through the opening to the gate-satisfaction seam
(`hquot`/`hgood` → `circuitSatViaGates`, `hencodes`) at the *claimed* value `multiopenValue` — pinned from the
forking opening's `multiopenValue − ξ·⟨s,b⟩` by the minimal value-recovery hypothesis
`hξ : ch.xi·⟨s,b⟩ = 0` (honest blinding, or a `1/p`-measure set of post-`S` challenges for a malicious blinder,
`blinder_value_recovery_badSet`). Residual assumptions: `z ≠ 0`, the nonzero generator `hg0`, the `S`-opening
witness `hs`, and `hξ` — plus the accept probability `hprob`, which carries the same quantifier-shape caveat
as `orchard_verifier_vesta_forking_opening_deployed`: with the constant `proverOfRounds` strategy it measures
the *fixed* proof's accept set over all round-challenge vectors, not the Fiat–Shamir attack event. For the
adaptive form, use `orchard_verifier_vesta_forking_constraint_adaptive`; for the same statement over
reprogrammed-oracle runs, use `orchard_verifier_vesta_forking_constraint_adaptive_rewind`. `hquot`/`hgood`
retain the ∀-openings shape — unsatisfiable at Vesta for any decode that genuinely
reads the witness (see `orchard_verifier_deployed_constraint_of_forked`'s caveat). -/
noncomputable def orchard_verifier_vesta_forking_constraint_deployed [Fact (HasseBound Vesta.curve)] [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    (s : Fin (2 ^ urs.k) → Fp)
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hz : ch.z ≠ 0) (hg0 : urs.g 0 ≠ 0) (hs : commit urs s = ps.ipaS)
    (hξ : ch.xi * innerProduct s (evalVector urs.k ch.x3) = 0)
    (hquot : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps ch) (evalVector urs.k ch.x3)
        (multiopenValue vk ps ch) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps ch) (evalVector urs.k ch.x3)
        (multiopenValue vk ps ch) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs (deployedCommitment urs hk vk ps ch) (evalVector urs.k ch.x3)
        (multiopenValue vk ps ch)
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S)
    (hprob : (kerr (Fintype.card Fp) shape.k : ℝ≥0∞) / Fintype.card (Fin shape.k → Fp)
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk ps
              {ch with ipaRound := χ}))) :
    S ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rcases orchard_verifier_vesta_forking_opening_deployed urs hk vk ps ch s hz hg0 hs hprob with hopen | hrel
  · refine PSum.inl ?_
    obtain ⟨a, hrel'⟩ := hopen
    rw [hξ, sub_zero] at hrel'
    have hsat : circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg a :=
      circuitSatViaGates_of_check fixedCols decodeAdvice decodeInstance y gates hpoly deg a x
        (hquot a hrel') (hgood a hrel')
    exact hencodes a ⟨hrel', hsat⟩
  · exact PSum.inr hrel

open scoped ENNReal in
open Classical in
/-- **The deployed Orchard opening over Vesta for the staged (round-adaptive) adversary, bridge
discharged.** `orchard_verifier_vesta_forking_opening_deployed` upgraded from the constant strategy to an
arbitrary prefix-respecting strategy `P : Prover`: the accept event is halo2's **actual** verifier equation
on the strategy's spliced proof (`spliceIpa` at `pathData P χ` — pre-IPA fields the fixed `ps`'s, since
rewinding shares the pre-IPA prefix; IPA fields the strategy's own outputs along `χ`), and the bridge to
`flatAccept P` is **proven** internally (`deployedVerifierEq_iff_flatAccept_adaptive`). So `hprob` is the
accept probability of an adaptive round-strategy — the object rewinding produces — not one fixed proof's
accept measure: the static-dichotomy caveat of the `_deployed` capstone does not apply at this rung. What
remains is the execution-semantics identification (that a rewound random-oracle adversary *induces* such a
staged strategy, with its RO-query loss), the random-oracle uniformity axiom in `hprob`, and the structural
witnesses (`z ≠ 0`, `hg0`, the `S`-opening `hs` — with `ps.ipaS` splice-invariant, so one `s` serves every
path). The transcript-ordering and reprogramming content is already on this path through the
`_adaptive_rewind` capstone. The `⊕' NontrivialRelation` caveat is unchanged — vacuous at Vesta's prime
order. -/
noncomputable def orchard_verifier_vesta_forking_opening_adaptive [Fact (HasseBound Vesta.curve)] [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    (s : Fin (2 ^ urs.k) → Fp) (P : Prover Fp VestaG shape.k)
    (hz : ch.z ≠ 0) (hg0 : urs.g 0 ≠ 0) (hs : commit urs s = ps.ipaS)
    (hprob : (kerr (Fintype.card Fp) shape.k : ℝ≥0∞) / Fintype.card (Fin shape.k → Fp)
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk
              (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2)
              {ch with ipaRound := χ}))) :
    (∃ a, IpaRelation urs (deployedCommitment urs hk vk ps ch) (evalVector urs.k ch.x3)
        (multiopenValue vk ps ch - ch.xi * innerProduct s (evalVector urs.k ch.x3)) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  obtain ⟨k, gg, ww, uu⟩ := urs
  change shape.k = k at hk
  subst hk
  refine orchard_verifier_vesta_forking_opening ⟨shape.k, gg, ww, uu⟩ rfl vk ps ch ch.x3 ch.xi ch.z 0 s
    P (fun χ => DeployedIpaVerifierEq gg ww uu vk
      (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2) {ch with ipaRound := χ})
    hz hg0 ?_ hprob
  intro χ
  dsimp only
  rw [deployedVerifierEq_iff_flatAccept_adaptive]
  have hPwhole : (multiopenCommitment gg ww uu vk ps ch
        + (∑ i, ([-(multiopenValue vk ps ch)].getD i.val 0) • gg i) + ch.xi • ps.ipaS)
      = (deployedCommitment ⟨shape.k, gg, ww, uu⟩ rfl vk ps ch
          - multiopenValue vk ps ch • gg 0 + ch.xi • commit ⟨shape.k, gg, ww, uu⟩ s
          + (ch.z * 0) • uu + 0 • ww) := by
    rw [sum_getD_single gg (multiopenValue vk ps ch), ← hs]
    simp only [deployedCommitment]
    module
  rw [hPwhole]
  exact Iff.rfl

open Polynomial in
open scoped ENNReal in
open Classical in
/-- **The deployed Orchard opening *and constraint* over Vesta for the staged (round-adaptive) adversary,
bridge discharged.** The constraint companion of `orchard_verifier_vesta_forking_opening_adaptive`: same
adaptive accept event and internally-proven bridge, routed to the gate-satisfaction seam
(`hquot`/`hgood` → `circuitSatViaGates`, `hencodes`) at the *claimed* value `multiopenValue`, pinned by the
value-recovery hypothesis `hξ` (honest blinding, or a `1/p`-measure set of post-`S` challenges for a
malicious blinder, `blinder_value_recovery_badSet`). Residual: the execution-semantics identification, the
random-oracle uniformity axiom in `hprob`, and the structural witnesses; the static-dichotomy caveat does not
apply at this rung. The transcript-ordering and reprogramming content is discharged by the staged
rewinding capstones below. `hquot`/`hgood` retain the ∀-openings shape — unsatisfiable at Vesta for any decode
that genuinely reads the witness. -/
noncomputable def orchard_verifier_vesta_forking_constraint_adaptive [Fact (HasseBound Vesta.curve)]
    [DecidableEq VestaG] [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG) (ch : Challenges shape.k Fp)
    (s : Fin (2 ^ urs.k) → Fp) (P : Prover Fp VestaG shape.k)
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hz : ch.z ≠ 0) (hg0 : urs.g 0 ≠ 0) (hs : commit urs s = ps.ipaS)
    (hξ : ch.xi * innerProduct s (evalVector urs.k ch.x3) = 0)
    (hquot : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps ch) (evalVector urs.k ch.x3)
        (multiopenValue vk ps ch) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps ch) (evalVector urs.k ch.x3)
        (multiopenValue vk ps ch) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs (deployedCommitment urs hk vk ps ch) (evalVector urs.k ch.x3)
        (multiopenValue vk ps ch)
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S)
    (hprob : (kerr (Fintype.card Fp) shape.k : ℝ≥0∞) / Fintype.card (Fin shape.k → Fp)
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk
              (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2)
              {ch with ipaRound := χ}))) :
    S ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rcases orchard_verifier_vesta_forking_opening_adaptive urs hk vk ps ch s P hz hg0 hs hprob
    with hopen | hrel
  · refine PSum.inl ?_
    obtain ⟨a, hrel'⟩ := hopen
    rw [hξ, sub_zero] at hrel'
    have hsat : circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg a :=
      circuitSatViaGates_of_check fixedCols decodeAdvice decodeInstance y gates hpoly deg a x
        (hquot a hrel') (hgood a hrel')
    exact hencodes a ⟨hrel', hsat⟩
  · exact PSum.inr hrel

/-! ## The forking capstones: staged and rewound endpoints

The terminal readings, ordered by how much of the prover-as-oracle and rewinding content is internalized:

* **Constant** — `orchard_verifier_vesta_forking_opening_deployed`/`_constraint_deployed`: halo2's actual
  accept on the *fixed* proof string, bridge proven for the constant strategy `proverOfRounds`. Their
  `hprob` is one proof's accept measure over the whole challenge space (the static dichotomy), not the
  Fiat–Shamir attack event: see the quantifier-shape caveat on each.
* **Staged (round-adaptive)** — `orchard_verifier_vesta_forking_opening_adaptive`/`_constraint_adaptive`:
  halo2's actual accept on the spliced proofs of an arbitrary prefix-respecting strategy `P : Prover`,
  bridge proven for every such strategy (`deployedVerifierEq_iff_flatAccept_adaptive`). Their `hprob` is an
  adaptive strategy's accept probability — the object rewinding produces — so the static-dichotomy caveat
  falls away; what remains is the execution-semantics identification that a rewound random-oracle adversary
  *induces* such a strategy, with its RO-query loss, plus the random-oracle uniformity axiom.
* **Constant, rewound** — the `_rewind` forms below state the constant rung's accept events over
  **reprogrammed-oracle runs** (`reprogramRounds`), deriving the `{ch with ipaRound := χ}` round-vector
  surgery from the rewinding primitive via `roChallenges_reprogramRounds` — the transcript-ordering module
  (`Soundness.Forking.Ordering`) on the Fiat–Shamir path.
* **Staged, rewound** — the `_adaptive_rewind` forms below state the staged rung over reprogrammed-oracle
  runs on each strategy-spliced proof. `roChallenges_spliceIpa_pre` proves those splices share the fixed
  pre-IPA challenge prefix with `ps`; `roChallenges_reprogramRounds` then supplies the per-path round vector.
* **Abstract** — `orchard_verifier_vesta_forking_opening`/`_constraint`, whose modular `hbridge` names the
  full prover-as-oracle identification; the staged rungs prove its deterministic content, while the
  execution-semantics content stays the floor.

The legacy `orchard_verifier_vesta_opening_of_forked`/`_constraint` remain compiled and checked but are no
longer the top statement a reader takes. -/

open scoped ENNReal in
open Classical in
/-- **The deployed Orchard opening over Vesta, from oracle rewinding.**
`orchard_verifier_vesta_forking_opening_deployed` at the honest run's challenges `roChallenges O init ps`,
with the accept probability stated over **reprogrammed-oracle runs**: the event is halo2's verifier equation
at `roChallenges (reprogramRounds O init ps χ) init ps` — the deployed schedule re-run under the oracle
reprogrammed at the `k` round prefixes — rather than an unexplained `{ch with ipaRound := χ}` surgery.
`roChallenges_reprogramRounds` proves the two events equal, so the round-vector semantics of the forking
measure is *derived* from the rewinding primitive, consuming the transcript ordering. Residuals
are unchanged: `z ≠ 0`, the nonzero generator `hg0`, the `S`-opening `hs`, and the random-oracle uniformity
axiom in `hprob` — including the constant rung's static-dichotomy scope: `hprob` is still the *fixed*
proof's accept measure over the whole challenge space (see
`orchard_verifier_vesta_forking_opening_deployed`); the `_adaptive`/`_adaptive_rewind` rungs are the
attack-event forms. -/
noncomputable def orchard_verifier_vesta_forking_opening_rewind [Fact (HasseBound Vesta.curve)] [DecidableEq VestaG]
    [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG)
    (O : List (TranscriptElt Fp VestaG) → Fp) (init : List (TranscriptElt Fp VestaG))
    (s : Fin (2 ^ urs.k) → Fp) (hz : (roChallenges O init ps).z ≠ 0) (hg0 : urs.g 0 ≠ 0)
    (hs : commit urs s = ps.ipaS)
    (hprob : (kerr (Fintype.card Fp) shape.k : ℝ≥0∞) / Fintype.card (Fin shape.k → Fp)
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk ps
              (roChallenges (reprogramRounds O init ps χ) init ps)))) :
    (∃ a, IpaRelation urs (deployedCommitment urs hk vk ps (roChallenges O init ps))
        (evalVector urs.k (roChallenges O init ps).x3)
        (multiopenValue vk ps (roChallenges O init ps)
          - (roChallenges O init ps).xi * innerProduct s (evalVector urs.k (roChallenges O init ps).x3)) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  refine orchard_verifier_vesta_forking_opening_deployed urs hk vk ps (roChallenges O init ps)
    s hz hg0 hs ?_
  simpa only [roChallenges_reprogramRounds] using hprob

open Polynomial in
open scoped ENNReal in
open Classical in
/-- The constraint companion of `orchard_verifier_vesta_forking_opening_rewind`:
`orchard_verifier_vesta_forking_constraint_deployed` with the accept probability over reprogrammed-oracle
runs, the round-vector semantics derived via `roChallenges_reprogramRounds`. The `hquot`/`hgood`
caveat is unchanged — see `orchard_verifier_deployed_constraint_of_forked`'s caveat — and so
is the constant rung's static-dichotomy scope (see `orchard_verifier_vesta_forking_opening_deployed`); the
`_adaptive_rewind` pair is the attack-event form. -/
noncomputable def orchard_verifier_vesta_forking_constraint_rewind [Fact (HasseBound Vesta.curve)]
    [DecidableEq VestaG] [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG)
    (O : List (TranscriptElt Fp VestaG) → Fp) (init : List (TranscriptElt Fp VestaG))
    (s : Fin (2 ^ urs.k) → Fp)
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hz : (roChallenges O init ps).z ≠ 0) (hg0 : urs.g 0 ≠ 0) (hs : commit urs s = ps.ipaS)
    (hξ : (roChallenges O init ps).xi
        * innerProduct s (evalVector urs.k (roChallenges O init ps).x3) = 0)
    (hquot : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps (roChallenges O init ps))
        (evalVector urs.k (roChallenges O init ps).x3)
        (multiopenValue vk ps (roChallenges O init ps)) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps (roChallenges O init ps))
        (evalVector urs.k (roChallenges O init ps).x3)
        (multiopenValue vk ps (roChallenges O init ps)) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs (deployedCommitment urs hk vk ps (roChallenges O init ps))
        (evalVector urs.k (roChallenges O init ps).x3) (multiopenValue vk ps (roChallenges O init ps))
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S)
    (hprob : (kerr (Fintype.card Fp) shape.k : ℝ≥0∞) / Fintype.card (Fin shape.k → Fp)
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk ps
              (roChallenges (reprogramRounds O init ps χ) init ps)))) :
    S ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  refine orchard_verifier_vesta_forking_constraint_deployed urs hk vk ps (roChallenges O init ps)
    s fixedCols decodeAdvice decodeInstance y gates hpoly deg x hz hg0 hs hξ hquot hgood hencodes ?_
  simpa only [roChallenges_reprogramRounds] using hprob

open scoped ENNReal in
open Classical in
/-- **The staged Orchard opening over Vesta, from oracle rewinding.**
This is `orchard_verifier_vesta_forking_opening_adaptive` with the adaptive accept probability stated over
reprogrammed-oracle runs on each strategy-spliced proof. For each challenge path `χ`, the proof string is
`spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2`; the oracle is reprogrammed at that
spliced proof's IPA round prefixes and the deployed schedule is re-run. `roChallenges_reprogramRounds` turns
that run into round-vector replacement, and `roChallenges_spliceIpa_pre` removes the irrelevant spliced
pre-IPA fields. The residual is unchanged from the staged rung: the execution-semantics identification that a
rewound random-oracle adversary induces such a strategy, with its RO-query loss, plus the uniformity axiom in
`hprob`. -/
noncomputable def orchard_verifier_vesta_forking_opening_adaptive_rewind [Fact (HasseBound Vesta.curve)]
    [DecidableEq VestaG] [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG)
    (O : List (TranscriptElt Fp VestaG) → Fp) (init : List (TranscriptElt Fp VestaG))
    (s : Fin (2 ^ urs.k) → Fp) (P : Prover Fp VestaG shape.k)
    (hz : (roChallenges O init ps).z ≠ 0) (hg0 : urs.g 0 ≠ 0) (hs : commit urs s = ps.ipaS)
    (hprob : (kerr (Fintype.card Fp) shape.k : ℝ≥0∞) / Fintype.card (Fin shape.k → Fp)
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk
              (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2)
              (roChallenges
                (reprogramRounds O init
                  (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2) χ)
                init
                (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2))))) :
    (∃ a, IpaRelation urs (deployedCommitment urs hk vk ps (roChallenges O init ps))
        (evalVector urs.k (roChallenges O init ps).x3)
        (multiopenValue vk ps (roChallenges O init ps)
          - (roChallenges O init ps).xi * innerProduct s (evalVector urs.k (roChallenges O init ps).x3)) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  refine orchard_verifier_vesta_forking_opening_adaptive urs hk vk ps (roChallenges O init ps)
    s P hz hg0 hs ?_
  simpa only [roChallenges_reprogramRounds, roChallenges_spliceIpa_pre] using hprob

open Polynomial in
open scoped ENNReal in
open Classical in
/-- The constraint companion of `orchard_verifier_vesta_forking_opening_adaptive_rewind`: the staged
round-adaptive capstone with its accept event grounded in reprogrammed-oracle runs on each spliced proof. The
`hquot`/`hgood` caveat is unchanged — see `orchard_verifier_deployed_constraint_of_forked`'s caveat. -/
noncomputable def orchard_verifier_vesta_forking_constraint_adaptive_rewind [Fact (HasseBound Vesta.curve)]
    [DecidableEq VestaG] [Inhabited VestaG] {shape : Shape} (urs : URS VestaG) (hk : shape.k = urs.k)
    (vk : VerifyingKey shape Fp VestaG) (ps : ProofString shape Fp VestaG)
    (O : List (TranscriptElt Fp VestaG) → Fp) (init : List (TranscriptElt Fp VestaG))
    (s : Fin (2 ^ urs.k) → Fp) (P : Prover Fp VestaG shape.k)
    (fixedCols : ℕ → Polynomial Fp)
    (decodeAdvice decodeInstance : (Fin (2 ^ urs.k) → Fp) → (ℕ → Polynomial Fp))
    (y : Fp) {ng : ℕ} (gates : Fin ng → Expr Fp) (hpoly : Polynomial Fp) (deg : ℕ) (x : Fp)
    (hz : (roChallenges O init ps).z ≠ 0) (hg0 : urs.g 0 ≠ 0) (hs : commit urs s = ps.ipaS)
    (hξ : (roChallenges O init ps).xi
        * innerProduct s (evalVector urs.k (roChallenges O init ps).x3) = 0)
    (hquot : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps (roChallenges O init ps))
        (evalVector urs.k (roChallenges O init ps).x3)
        (multiopenValue vk ps (roChallenges O init ps)) a →
      quotientCheck (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates) hpoly deg x)
    (hgood : ∀ a, IpaRelation urs (deployedCommitment urs hk vk ps (roChallenges O init ps))
        (evalVector urs.k (roChallenges O init ps).x3)
        (multiopenValue vk ps (roChallenges O init ps)) a →
      combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates ≠ hpoly * (X ^ deg - 1) →
      (combineGates fixedCols (decodeAdvice a) (decodeInstance a) y gates
        - hpoly * (X ^ deg - 1)).eval x ≠ 0)
    {S : Prop}
    (hencodes : ∀ a, SnarkRelation urs (deployedCommitment urs hk vk ps (roChallenges O init ps))
        (evalVector urs.k (roChallenges O init ps).x3) (multiopenValue vk ps (roChallenges O init ps))
      (circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg) a → S)
    (hprob : (kerr (Fintype.card Fp) shape.k : ℝ≥0∞) / Fintype.card (Fin shape.k → Fp)
        < (PMF.uniformOfFintype (Fin shape.k → Fp)).toOuterMeasure
            (Finset.univ.filter (fun χ => DeployedIpaVerifierEq (hk ▸ urs.g) urs.w urs.u vk
              (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2)
              (roChallenges
                (reprogramRounds O init
                  (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2) χ)
                init
                (spliceIpa ps (pathData P χ).1 (pathData P χ).2.1 (pathData P χ).2.2))))) :
    S ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rcases orchard_verifier_vesta_forking_opening_adaptive_rewind urs hk vk ps O init s P hz hg0 hs hprob
    with hopen | hrel
  · refine PSum.inl ?_
    obtain ⟨a, hrel'⟩ := hopen
    rw [hξ, sub_zero] at hrel'
    have hsat : circuitSatViaGates fixedCols decodeAdvice decodeInstance y gates hpoly deg a :=
      circuitSatViaGates_of_check fixedCols decodeAdvice decodeInstance y gates hpoly deg a x
        (hquot a hrel') (hgood a hrel')
    exact hencodes a ⟨hrel', hsat⟩
  · exact PSum.inr hrel

end Zcash.Snark
