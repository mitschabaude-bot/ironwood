import Zcash.Arithmetic.InvDft

/-!
# The executable scalar inverse DFT

`scalarInvDft` is the statement-surface transform, and its `·.val • ·` steps go through
`ZMod`'s default `nsmul` — a linear recursion that cannot execute on 255-bit scalars.
This module gives the executable spelling: the same `fftGen` loop nest at `Fp` with
**multiplication** butterflies (`ZMod` multiplication is GMP-backed), proven equal
pointwise via `n • x = ↑n * x`.
-/

namespace Zcash.Arithmetic

open CompElliptic.Curves.Pasta.Fast
open CompElliptic.Curves.Pasta.Fast.Msm (Fp)


/-- `bestFftG`'s internal twiddle table, extracted verbatim (so that factoring it out of
the loop nest is definitional). -/
private def twArr (omega : Fp) (m : ℕ) : Array Fp := Id.run do
  let mut tw : Array Fp := Array.mkEmpty m
  let mut w : Fp := 1
  for _ in [0:m] do
    tw := tw.push w
    w := w * omega
  return tw

/-- `bestFftG` at `G := Fp` is the generic loop nest at the field's own operations, with
the twiddle table factored out. -/
private theorem bestFftG_eq_gen (a0 : Array Fp) (omega : Fp) (logN : ℕ) :
    bestFftG a0 omega logN
      = fftGen (· + ·) (· - ·) (fun (t : Fp) p => t.val • p) a0
          (twArr omega (a0.size / 2)) logN := rfl

/-- The scalar action along the butterflies is plain field multiplication. -/
private theorem val_smul_eq_mul (t p : Fp) : t.val • p = t * p := by
  rw [nsmul_eq_mul, ZMod.natCast_rightInverse t]

/-- The executable FFT at `Fp`: the same loop nest, multiplication butterflies. -/
def fftFpMul (a0 : Array Fp) (omega : Fp) (logN : ℕ) : Array Fp :=
  fftGen (· + ·) (· - ·) (fun (t : Fp) p => t * p) a0 (twArr omega (a0.size / 2)) logN

private theorem fftFpMul_eq_bestFftG (a0 : Array Fp) (omega : Fp) (logN : ℕ) :
    fftFpMul a0 omega logN = bestFftG a0 omega logN := by
  rw [bestFftG_eq_gen, fftFpMul]
  congr 1
  funext t p
  rw [val_smul_eq_mul]

/-- **The executable scaled inverse DFT**, read out as the canonical `ℕ` scalars an MSM
consumes: multiplication throughout, one `ZMod.val` per cell at the end. -/
def invDftScalars (k : ℕ) (coeffs : List Fp) : List ℕ :=
  ((fftFpMul coeffs.toArray (omegaInvOf k) k).toList.map
    fun c => ((((2 : Fp) ^ k)⁻¹) * c).val)

/-- **The executable inverse DFT is `scalarInvDft`**, in canonical `ℕ` form. -/
theorem invDftScalars_eq (k : ℕ) (coeffs : List Fp) :
    invDftScalars k coeffs = (scalarInvDft k coeffs).map ZMod.val := by
  rw [invDftScalars, scalarInvDft, fftFpMul_eq_bestFftG, List.map_map]
  refine List.map_congr_left fun c _ => ?_
  rw [Function.comp_apply, val_smul_eq_mul]

end Zcash.Arithmetic
