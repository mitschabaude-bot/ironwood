import Zcash.Snark.Verifier.AssembleSpec
import Zcash.Snark.Soundness.Deployed.Fold

/-!
# Deployed acceptance implies the explicit IPA verifier equation

This module combines `eval_assembleFinalMsm` and `deployed_gterm_foldAll` into halo2's IPA equation
and ties that equation to the deployed accept condition:

* `multiopenCommitment` / `multiopenValue` — the `P` and `v` halo2's IPA verifier opens, read off the
  multiopen assembly on `(vk, ps, ch)`.
* `deployed_verification_eq` — `(assembleFinalMsm …).eval` is the explicit equation
  `P + [-v]g₀ + [ξ]S + Σ(rounds) + [-c·b·z]U + [-f]W + [-c]G'₀`.
* `DeployedIpaVerifierEq` — that equation set to the identity.
Deployed acceptance uses the rejecting `assemble?`; `Verifier/AssembleSpec.lean` says what its
`some` is, which is how the equation transfers.

`Soundness.Main` transfers deployed acceptance to this equation;
`FiatShamir.Adversary.Algebraic` supplies the represented execution consumed by the current
straight-line and adaptive AGM reductions.
-/

namespace Zcash.Snark

open Zcash.Arithmetic (Msm Msm.zero)

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The deployed multiopen commitment `P` the IPA verifier opens: the `x₁`-compressed, `x₄`-collapsed
multiopen assembly on `(vk, ps, ch)`, evaluated against the URS. -/
def multiopenCommitment {shape : Shape} [DecidableEq F] [DecidableEq G] [Inhabited G]
    (g : Fin (2 ^ shape.k) → G) (w u : G)
    (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F) : G :=
  (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
    (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)) (Msm.zero shape.k F G)).1.eval ⟨shape.k, g, w, u⟩

/-- The deployed multiopen value `v` the IPA verifier opens `P` to (halo2 `multiopen/verifier.rs`). -/
def multiopenValue {shape : Shape} [DecidableEq F] [DecidableEq G] [Inhabited G]
    (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G)
    (ch : Challenges shape.k F) : F :=
  (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
    (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)) (Msm.zero shape.k F G)).2

/-- The deployed fingerprint MSM evaluates to halo2's explicit IPA verifier equation: the
multiopen commitment, the `[-v]g₀` value term, the `[ξ]S` blinding poly, the round total
`Σ([uⱼ⁻¹]Lⱼ+[uⱼ]Rⱼ)`, the value-binding `[-c·b·z]U`, the blinding `[-f]W`, and the folded
generator `[-c]G'₀` (`G'₀ = foldAll`). `eval_assembleFinalMsm` plus `deployed_gterm_foldAll`
(the `g`-term is `[-c]·G'₀`). -/
theorem deployed_verification_eq {shape : Shape} (g : Fin (2 ^ shape.k) → G) (w u : G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F)
    (grouped : MultiopenGrouped shape.k F G) :
    (assembleFinalMsm ps ch grouped).eval ⟨shape.k, g, w, u⟩
      = (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU) grouped
            (Msm.zero shape.k F G)).1.eval ⟨shape.k, g, w, u⟩
        + (∑ i, ([-(assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
            grouped (Msm.zero shape.k F G)).2].getD i.val 0) • g i)
        + ch.xi • ps.ipaS
        + (((List.ofFn ps.ipaRounds).zip (List.ofFn ch.ipaRound)).map
            (fun p => p.2⁻¹ • p.1.1 + p.2 • p.1.2)).sum
        + (-ps.ipaC * computeB ch.x3 (List.ofFn ch.ipaRound) * ch.z) • u
        + (-ps.ipaF) • w
        + (-ps.ipaC) • foldAll (List.ofFn ch.ipaRound)
            (fun j => g (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j)) 0 := by
  rw [eval_assembleFinalMsm, deployed_gterm_foldAll]

/-- halo2's explicit IPA verifier equation for the deployed proof, set to the group identity. By
`deployed_verification_eq` this is exactly `(assembleFinalMsm …).eval = 0`. Stating it explicitly
lets the represented-execution reduction consume halo2's actual IPA equation, with `P`/`v` the
pinned `multiopenCommitment`/`multiopenValue`.

Totality note: the closed form uses Lean's total inverse (`0⁻¹ = 0`), and the deployed code
computes the same thing — halo2 batch-inverts the round challenges with ff's `batch_invert`,
which leaves a zero challenge at zero — so at `uⱼ = 0` the equation and the Rust agree
term for term. The corner is faithful in both directions: nothing about acceptance can be
shown from this form that the deployed verifier would not exhibit. The current reduction treats
inadmissible challenge values as explicit bad-root events rather than restricting this equation's
domain. -/
def DeployedIpaVerifierEq {shape : Shape} [DecidableEq F] [DecidableEq G] [Inhabited G]
    (g : Fin (2 ^ shape.k) → G) (w u : G)
    (vk : VerifyingKey shape F G) (instanceCommitment : Fin shape.numProofs → ℕ → G)
    (ps : ProofString shape F G) (ch : Challenges shape.k F) : Prop :=
  (assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
        (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)) (Msm.zero shape.k F G)).1.eval ⟨shape.k, g, w, u⟩
      + (∑ i, ([-(assembleOpening ch.x1 ch.x2 ch.x3 ch.x4 ps.multiopenQPrime (List.ofFn ps.multiopenU)
          (constructIntermediateSets (assembleQueries vk instanceCommitment ps ch)) (Msm.zero shape.k F G)).2].getD i.val 0) • g i)
      + ch.xi • ps.ipaS
      + (((List.ofFn ps.ipaRounds).zip (List.ofFn ch.ipaRound)).map
          (fun p => p.2⁻¹ • p.1.1 + p.2 • p.1.2)).sum
      + (-ps.ipaC * computeB ch.x3 (List.ofFn ch.ipaRound) * ch.z) • u
      + (-ps.ipaF) • w
      + (-ps.ipaC) • foldAll (List.ofFn ch.ipaRound)
          (fun j => g (Fin.cast (congrArg (2 ^ ·) List.length_ofFn) j)) 0 = 0

end Zcash.Snark
