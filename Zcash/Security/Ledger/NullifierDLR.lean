import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Zcash.Security.Ledger.Spendability
import Zcash.Security.Ledger.NoteCommitDLR

/-!
# The Orchard-protocol nullifier collision computes a discrete-log relation

The pre-quantum discharge of the nullifier arm at the deployed primitives: a
`NullifierCollision` at the Orchard-protocol primitives — two openings with distinct
`(rcm, note)` pairs whose nullifiers agree under the given nullifier keys — computes a
nontrivial relation among the Sinsemilla table, the `NoteCommit` domain point, its
randomness base, and the nullifier base 𝒦^Orchard, in the combined deployed basis.

The deployed nullifier is the extracted coordinate of `cm + s • 𝒦` with `s` the Poseidon
hash of `(nk, ρ)` plus `ψ` (`deriveNullifier_eq_extract`), so equal nullifiers are a point
equation up to sign between the two shifted commitments. The reduction unpacks the openings
into their defined Sinsemilla chains and applies the chain-collision reducer
`relationOfChainVecPmEq` at two blinding points, the randomness base with the commitment
randomness and the nullifier base with `s`. Adding the commitment inside the derivation is
what keeps the nullifier keys out of the argument: no assumption on the Poseidon hash
enters, and the scalars appear only as coefficients on the nullifier base (the
[Orchard nullifier design](https://zcash.github.io/orchard/design/nullifiers.html)).

The reduction is hypothesis-free. The word-coefficient injectivity is `preCoeffs_inj`, and
`note_eq_of_noteScalars_words_eq` recovers the notes from their words. The value bounds the
collision carries are the 64-bit type of a note's value, which the model's `Note`, holding
the value as an unbounded `ℕ`, does not enforce.
-/

namespace Zcash.Security.Ledger.Bridge

open Zcash.Circuits
open Zcash.Circuits.Specs (K)
open Zcash.Circuits.Specs.Sinsemilla
open Zcash.Security.Concrete
open Zcash.Security.Ledger.Model (NullifierCollision)
open Zcash.Security.Ledger.Pool

/-- The deployed nullifier is the extracted coordinate of the commitment shifted by the
nullifier-scalar multiple of the nullifier base. -/
theorem deriveNullifier_eq_extract (nk ρ ψ : Fp) (cm : PallasGroup) :
    deriveNullifier nk ρ ψ cm = extract (cm + nullifierScalar nk ρ ψ • nullifierKpt) := by
  unfold deriveNullifier extract
  rw [PallasGroup.toPoint_add, PallasGroup.toPoint_smul, nullifierKpt,
    PallasGroup.toPoint_ofPoint]

/-- **The Orchard-protocol nullifier collision computes a discrete-log relation.** Two
openings with distinct `(rcm, note)` pairs whose deployed nullifiers agree: the reduction
turns the equal extracted coordinates into a point equation up to sign between the shifted
commitments, unpacks the openings into their defined Sinsemilla chains, and applies the
chain-collision reducer at the `NoteCommit` domain point with the note-commitment
randomness base and the nullifier base as blinding points. -/
def relationOfNullifierCollision {MSG SIG : Type*}
    (spendAuthVerify bindingVerify : PallasGroup → MSG → SIG → Prop)
    (c : NullifierCollision (primitives (MSG := MSG) (SIG := SIG) spendAuthVerify bindingVerify)) :
    NontrivialRelation (F := Fq) pallasS orchardPoints :=
  toOrchardPoints (V := ![noteQpt, noteCommitRpt, nullifierKpt])
    (g := ![.idxNoteQ, .idxNoteCommitR, .idxNullifierK])
    (gr := fun s => match s with
      | .idxNoteQ => some 0
      | .idxNoteCommitR => some 1
      | .idxNullifierK => some 2
      | _ => none)
    (hg := by intro x y; fin_cases x <;> cases y <;> decide)
    (hpt := fun i => by fin_cases i <;> rfl) <|
  relationOfChainVecPmEq (Q := noteQ) (Or.inl noteQ_onCurve)
    (V := ![noteCommitRpt, nullifierKpt])
    (fun _ hm => chunksOf_mem_lt hm) (fun _ hm => chunksOf_mem_lt hm)
    (by simp [Pool.noteScalars])
    (Option.some_get (noteCommit_hash_isSome c.open₁)).symm
    (noteCommit_get_valid c.open₁)
    (Option.some_get (noteCommit_hash_isSome c.open₂)).symm
    (noteCommit_get_valid c.open₂)
    (c₁ := ![c.rcm₁, nullifierScalar c.nk₁ c.note₁.ρ c.note₁.ψ])
    (c₂ := ![c.rcm₂, nullifierScalar c.nk₂ c.note₂.ρ c.note₂.ψ])
    (X₁ := c.cm₁ + nullifierScalar c.nk₁ c.note₁.ρ c.note₁.ψ • nullifierKpt)
    (X₂ := c.cm₂ + nullifierScalar c.nk₂ c.note₂.ρ c.note₂.ψ • nullifierKpt)
    (by
      conv_lhs => rw [noteCommit_get_eq c.open₁]
      simp only [sinsemillaCommitBlind, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, add_assoc])
    (by
      conv_lhs => rw [noteCommit_get_eq c.open₂]
      simp only [sinsemillaCommitBlind, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, add_assoc])
    (by
      have hx : extract (c.cm₁ + nullifierScalar c.nk₁ c.note₁.ρ c.note₁.ψ • nullifierKpt)
          = extract (c.cm₂ + nullifierScalar c.nk₂ c.note₂.ρ c.note₂.ψ • nullifierKpt) := by
        rw [← deriveNullifier_eq_extract, ← deriveNullifier_eq_extract]
        exact c.eq
      exact (PallasGroup.toPoint_x_eq_iff _ _).mp hx)
    (by simp [Pool.noteScalars])
    (by
      rintro ⟨hl, hc⟩
      exact c.ne (by
        rw [note_eq_of_noteScalars_words_eq c.v₁_lt c.v₂_lt hl,
          show c.rcm₁ = c.rcm₂ by simpa only [Matrix.cons_val_zero] using congrFun hc 0]))

end Zcash.Security.Ledger.Bridge
