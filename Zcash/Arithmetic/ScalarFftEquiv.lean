/-
Copyright (c) 2026 Ironwood Contributors.
Released under the Apache License, Version 2.0.
-/
import Zcash.Vendor.CompPoly.ScalarFftDefs
import Zcash.Vendor.CompPoly.Montgomery.Pasta
import Zcash.Vendor.CompElliptic.NatKernelEquiv

/-!
# The scalar Montgomery FFT is the proven group FFT at `G := Fp`

`Zcash.Vendor.CompPoly.ScalarFftDefs` is a zero-import transplant of the radix-2 DIT FFT onto the
eight-limb Montgomery representation of the Vesta **scalar** field, so that it can sit in the
`FastFieldNative` `precompileModules` leaf.  This module — mathlib-side, and therefore *not*
in that lane — proves that the transplant computes `Keygen.bestFftG` instantiated at the
`Fp`-module `Fp`.

The bridge is the value map `montValS : Limbs8 → Fp`, `x ↦ x.toNat / 2 ^ 256`, which is
`Montgomery.Native64x8.FastField.toField` read off raw limbs; it is correct on **well-formed**
residues (`WFs x := x.Bounded ∧ x.toNat < p`), the carrier property of the proven
`FastField PALLAS_BASE_CARD`.  Every scalar operation of the kernel is the corresponding
`FastField` operation on the nose, so the per-operation cast lemmas are the vendored field's
`toField_*` homomorphism lemmas.

`ScalarFftDefs.fft` and `bestFftG` are recognized as the same generic loop nest
`NatKernel.fftGen` (`rfl` on both sides), which `NatKernel.fftGen_eq_folds` turns into pure
`List.foldl`s; the simulation invariant `SimS` is then pushed through the permutation and each
butterfly, exactly as `NatKernelEquiv` does for the group lane.  The twiddle table of
`bestFftG` is the only piece that differs: the kernel receives it in Montgomery form from the
caller, so the butterflies compare `mul` against `t.val • ·` at corresponding entries.
-/

namespace Zcash.Vendor.ScalarMont

open Montgomery.Native64x8
open Montgomery.Native64x8 (Limbs8)
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)

/-- The Vesta scalar field — `PALLAS_BASE_CARD` in the Pasta naming. -/
local notation "Fp" => Zcash.Snark.Fp

/-! ## The field level -/

/-- A well-formed Montgomery residue of the scalar field: bounded limbs holding a value below
`p`.  This is exactly the carrier property of `FastField PALLAS_BASE_CARD`. -/
def WFs (x : Limbs8) : Prop := x.Bounded ∧ x.toNat < PALLAS_BASE_CARD

/-- The field value of a Montgomery residue: the residue divided by the radix `R = 2 ^ 256`. -/
def montValS (x : Limbs8) : Fp := (x.toNat : Fp) * ((2 ^ 256 : ℕ) : Fp)⁻¹

private def toFFs (x : Limbs8) (h : WFs x) : FastField PALLAS_BASE_CARD := ⟨x, h⟩

theorem montValS_eq_toField {x : Limbs8} (h : WFs x) :
    montValS x = FastField.toField (toFFs x h) := by
  rw [montValS]
  exact (FastField.toField_eq (toFFs x h)).symm

theorem wfs_add {a b : Limbs8} (ha : WFs a) (hb : WFs b) : WFs (PallasFq.add a b) :=
  (FastField.add (toFFs a ha) (toFFs b hb)).property

theorem montValS_add {a b : Limbs8} (ha : WFs a) (hb : WFs b) :
    montValS (PallasFq.add a b) = montValS a + montValS b := by
  rw [montValS_eq_toField (wfs_add ha hb), montValS_eq_toField ha, montValS_eq_toField hb]
  exact FastField.toField_add (toFFs a ha) (toFFs b hb)

theorem wfs_sub {a b : Limbs8} (ha : WFs a) (hb : WFs b) : WFs (PallasFq.sub a b) :=
  (FastField.sub (toFFs a ha) (toFFs b hb)).property

theorem montValS_sub {a b : Limbs8} (ha : WFs a) (hb : WFs b) :
    montValS (PallasFq.sub a b) = montValS a - montValS b := by
  rw [montValS_eq_toField (wfs_sub ha hb), montValS_eq_toField ha, montValS_eq_toField hb]
  exact FastField.toField_sub (toFFs a ha) (toFFs b hb)

theorem wfs_mul {a b : Limbs8} (ha : WFs a) (hb : WFs b) : WFs (PallasFq.mul a b) :=
  (FastField.mul (toFFs a ha) (toFFs b hb)).property

theorem montValS_mul {a b : Limbs8} (ha : WFs a) (hb : WFs b) :
    montValS (PallasFq.mul a b) = montValS a * montValS b := by
  rw [montValS_eq_toField (wfs_mul ha hb), montValS_eq_toField ha, montValS_eq_toField hb]
  exact FastField.toField_mul (toFFs a ha) (toFFs b hb)

theorem wfs_zero : WFs PallasFq.zero := (FastField.zero PALLAS_BASE_CARD).property

theorem montValS_zero : montValS PallasFq.zero = 0 := by
  rw [montValS_eq_toField wfs_zero]
  exact FastField.toField_zero

/-- **Entering Montgomery form is the canonical cast**, for canonical naturals. -/
theorem wfs_ofNat {k : ℕ} (h : k < PALLAS_BASE_CARD) : WFs (PallasFq.ofNat k) :=
  (FastField.ofCanonicalNat k h).property

theorem montValS_ofNat {k : ℕ} (h : k < PALLAS_BASE_CARD) :
    montValS (PallasFq.ofNat k) = (k : Fp) := by
  rw [montValS_eq_toField (wfs_ofNat h)]
  exact FastField.toField_ofCanonicalNat h

/-- Leaving Montgomery form yields the canonical representative of the field value. -/
theorem toNat_toLimbs8 {x : Limbs8} (h : WFs x) :
    (PallasFq.toLimbs8 x).toNat = (montValS x).val := by
  have hlt : FastField.toNat (toFFs x h) < PALLAS_BASE_CARD := FastField.toNat_lt _
  rw [montValS_eq_toField h, FastField.toField]
  rw [ZMod.val_natCast_of_lt hlt]
  rfl

/-- `Array.get!` out of range hands back `default`, which is Montgomery zero. -/
theorem default_eq_zero : (default : Limbs8) = PallasFq.zero := rfl

theorem wfs_default : WFs (default : Limbs8) := wfs_zero

theorem montValS_default : montValS (default : Limbs8) = (default : Fp) := by
  rw [default_eq_zero, montValS_zero]
  rfl

/-! ## The twiddle table

`bestFftG`'s twiddle table is built internally from `omega`; the kernel receives it from the
caller in Montgomery form.  `twArrS` is that internal table extracted verbatim (so that
`bestFftG_eq_genS` is `rfl`), and `twArrS_get` reads off its entries. -/

private def twArrS (omega : Fp) (m : ℕ) : Array Fp := Id.run do
  let mut tw : Array Fp := Array.mkEmpty m
  let mut w : Fp := 1
  for _ in [0:m] do
    tw := tw.push w
    w := w * omega
  return tw

private theorem twArrS_eq_foldl (omega : Fp) (m : ℕ) :
    twArrS omega m = ((List.range m).foldl
      (fun (p : MProd (Array Fp) Fp) _ => ⟨p.1.push p.2, p.2 * omega⟩)
      ⟨Array.mkEmpty m, 1⟩).1 := by
  show (forIn (m := Id) [0:m] (⟨Array.mkEmpty m, 1⟩ : MProd (Array Fp) Fp) (fun _ p =>
      pure (ForInStep.yield ⟨p.1.push p.2, p.2 * omega⟩)) >>= fun r =>
        match r with | ⟨tw, _⟩ => (pure tw : Id (Array Fp))) = _
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', List.forIn_pure_yield_eq_foldl]
  rfl

private theorem twFoldS_eq (omega : Fp) (m l : ℕ) :
    (List.range l).foldl (fun (p : MProd (Array Fp) Fp) _ => ⟨p.1.push p.2, p.2 * omega⟩)
        ⟨Array.mkEmpty m, 1⟩ =
      ⟨((List.range l).map (omega ^ ·)).toArray, omega ^ l⟩ := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    refine congrArg₂ MProd.mk ?_ (by rw [pow_succ])
    rw [List.map_append, List.map_cons, List.map_nil, ← List.push_toArray]

private theorem twArrS_get (omega : Fp) (m i : ℕ) :
    (twArrS omega m)[i]! = if i < m then omega ^ i else 0 := by
  rw [twArrS_eq_foldl, twFoldS_eq]
  by_cases hi : i < m
  · rw [if_pos hi, getElem!_pos _ i (by simpa using hi)]
    simp
  · rw [if_neg hi, getElem!_neg _ i (by simp; omega)]
    rfl

/-! ## The loop nest -/

/-- The kernel FFT is the generic loop nest at the scalar field operations. -/
private theorem fftS_eq_gen (a0 : Array Limbs8) (tw : Array Limbs8) (logN : ℕ) :
    fft a0 tw logN
      = NatKernel.fftGen PallasFq.add PallasFq.sub PallasFq.mul a0 tw logN := rfl

/-- `bestFftG` at `G := Fp` is the generic loop nest at the field's own operations, with the
twiddle table factored out. -/
private theorem bestFftG_eq_genS (a0 : Array Fp) (omega : Fp) (logN : ℕ) :
    Zcash.Snark.Keygen.bestFftG a0 omega logN
      = NatKernel.fftGen (· + ·) (· - ·) (fun (t : Fp) p => t.val • p) a0
          (twArrS omega (a0.size / 2)) logN := rfl

/-! ## The simulation invariant -/

/-- The kernel array simulates the field array: every cell is a well-formed residue, and the
cellwise Montgomery readings are the field array. -/
private def SimS (a : Array Limbs8) (b : Array Fp) : Prop :=
  (∀ x ∈ a, WFs x) ∧ a.map montValS = b

private theorem SimS.wf_get {a : Array Limbs8} {b : Array Fp} (h : SimS a b) (i : ℕ) :
    WFs a[i]! := by
  by_cases hi : i < a.size
  · rw [getElem!_pos a i hi]
    exact h.1 _ (Array.getElem_mem hi)
  · rw [getElem!_neg a i hi]
    exact wfs_default

private theorem SimS.get {a : Array Limbs8} {b : Array Fp} (h : SimS a b) (i : ℕ) :
    montValS a[i]! = b[i]! := by
  rw [← h.2]
  by_cases hi : i < a.size
  · rw [getElem!_pos a i hi, getElem!_pos (a.map montValS) i (by simpa using hi),
      Array.getElem_map]
  · rw [getElem!_neg a i hi, getElem!_neg (a.map montValS) i (by simpa using hi),
      montValS_default]

private theorem SimS.set {a : Array Limbs8} {b : Array Fp} (h : SimS a b) (i : ℕ) {p : Limbs8}
    (hp : WFs p) : SimS (a.set! i p) (b.set! i (montValS p)) := by
  refine ⟨?_, ?_⟩
  · intro q hq
    rw [Array.set!_eq_setIfInBounds] at hq
    rcases Array.mem_or_eq_of_mem_setIfInBounds hq with hq | rfl
    · exact h.1 q hq
    · exact hp
  · rw [Array.set!_eq_setIfInBounds, Array.set!_eq_setIfInBounds, Array.map_setIfInBounds, h.2]

private theorem foldl_relS {σ σ' β : Type} (R : σ → σ' → Prop) (l : List β)
    (f : σ → β → σ) (g : σ' → β → σ')
    (hstep : ∀ s s' x, R s s' → R (f s x) (g s' x)) :
    ∀ s s', R s s' → R (l.foldl f s) (l.foldl g s') := by
  induction l with
  | nil => exact fun s s' h => h
  | cons x l ih => exact fun s s' h => ih _ _ (hstep s s' x h)

private theorem simS_permStep (logN : ℕ) {a : Array Limbs8} {b : Array Fp} (h : SimS a b)
    (k : ℕ) : SimS (NatKernel.permStep logN a k) (NatKernel.permStep logN b k) := by
  unfold NatKernel.permStep
  split
  · have h1 : SimS (a.set! k a[Zcash.Snark.Keygen.bitreverse k logN]!)
        (b.set! k (montValS a[Zcash.Snark.Keygen.bitreverse k logN]!)) :=
      h.set k (h.wf_get _)
    rw [h.get (Zcash.Snark.Keygen.bitreverse k logN)] at h1
    have h2 := h1.set (Zcash.Snark.Keygen.bitreverse k logN) (h.wf_get k)
    rw [h.get k] at h2
    exact h2
  · exact h

/-- **A single butterfly preserves the simulation**: `add`/`sub` are the field's own, and the
Montgomery twiddle multiply is the `ZMod.val`-smul of the corresponding field twiddle. -/
private theorem simS_bfly {a : Array Limbs8} {b : Array Fp} (h : SimS a b) (iA iB : ℕ)
    (d : Limbs8) (e : Fp) (hd : WFs d) (he : montValS d = e) :
    SimS ((a.set! iA (PallasFq.add a[iA]! (PallasFq.mul d a[iB]!))).set! iB
            (PallasFq.sub a[iA]! (PallasFq.mul d a[iB]!)))
        ((b.set! iA (b[iA]! + e.val • b[iB]!)).set! iB (b[iA]! - e.val • b[iB]!)) := by
  have hwA : WFs a[iA]! := h.wf_get iA
  have hwB : WFs a[iB]! := h.wf_get iB
  have hwt : WFs (PallasFq.mul d a[iB]!) := wfs_mul hd hwB
  have hst : montValS (PallasFq.mul d a[iB]!) = e.val • b[iB]! := by
    rw [montValS_mul hd hwB, he, h.get iB,
      ← Nat.cast_smul_eq_nsmul Fp e.val b[iB]!, ZMod.natCast_rightInverse e, smul_eq_mul]
  have hplus : montValS (PallasFq.add a[iA]! (PallasFq.mul d a[iB]!))
      = b[iA]! + e.val • b[iB]! := by
    rw [montValS_add hwA hwt, h.get iA, hst]
  have hminus : montValS (PallasFq.sub a[iA]! (PallasFq.mul d a[iB]!))
      = b[iA]! - e.val • b[iB]! := by
    rw [montValS_sub hwA hwt, h.get iA, hst]
  have s1 := h.set iA (wfs_add hwA hwt)
  rw [hplus] at s1
  have s2 := s1.set iB (wfs_sub hwA hwt)
  rw [hminus] at s2
  exact s2

private theorem simS_butterfly (n half : ℕ) (tw : Array Limbs8) (twFp : Array Fp)
    (hwtw : ∀ i : ℕ, WFs tw[i]!) (htw : ∀ i : ℕ, montValS tw[i]! = twFp[i]!) (c j : ℕ)
    {a : Array Limbs8} {b : Array Fp} (h : SimS a b) :
    SimS (NatKernel.butterflyGen PallasFq.add PallasFq.sub PallasFq.mul n half tw c j a)
        (NatKernel.butterflyGen (· + ·) (· - ·) (fun (t : Fp) p => t.val • p) n half twFp c j b) :=
  simS_bfly h _ _ _ _ (hwtw (j * (n / (2 * half)))) (htw (j * (n / (2 * half))))

private theorem simS_roundFold (n half : ℕ) (tw : Array Limbs8) (twFp : Array Fp)
    (hwtw : ∀ i : ℕ, WFs tw[i]!) (htw : ∀ i : ℕ, montValS tw[i]! = twFp[i]!)
    {a : Array Limbs8} {b : Array Fp} (h : SimS a b) :
    SimS (NatKernel.roundFoldGen PallasFq.add PallasFq.sub PallasFq.mul n half tw a)
        (NatKernel.roundFoldGen (· + ·) (· - ·) (fun (t : Fp) p => t.val • p) n half twFp b) :=
  foldl_relS SimS _ _ _
    (fun s s' c hs => foldl_relS SimS _ _ _
      (fun _ _ j hr => simS_butterfly n half tw twFp hwtw htw c j hr) s s' hs) a b h

/-! ## The simulation theorem -/

/-- **The scalar kernel FFT is `bestFftG` at `G := Fp`.**  With Montgomery twiddles reading back
as `ω^i`, the kernel's limb array stays well formed and maps cellwise, under `montValS`, onto
`bestFftG` of the mapped input: the bit-reversal permutation moves cells, and every butterfly is
the field's own add/sub/mul.  Statement shape mirrors `NatKernel.fft_spec`. -/
theorem fftS_spec (a0 : Array Limbs8) (tw : Array Limbs8) (omega : Fp) (logN : ℕ)
    (hwf : ∀ x ∈ a0, WFs x) (hwtw : ∀ i : ℕ, WFs tw[i]!)
    (htwsize : tw.size = a0.size / 2)
    (htw : ∀ i, i < a0.size / 2 → montValS tw[i]! = omega ^ i) :
    (∀ x ∈ fft a0 tw logN, WFs x)
      ∧ (fft a0 tw logN).map montValS
          = Zcash.Snark.Keygen.bestFftG (a0.map montValS) omega logN := by
  have hsize : (a0.map montValS).size = a0.size := Array.size_map ..
  have htw' : ∀ i : ℕ, montValS tw[i]! = (twArrS omega (a0.size / 2))[i]! := by
    intro i
    rw [twArrS_get]
    by_cases hi : i < a0.size / 2
    · rw [if_pos hi, htw i hi]
    · rw [if_neg hi, getElem!_neg tw i (by omega), montValS_default]
      rfl
  have hsim0 : SimS a0 (a0.map montValS) := ⟨hwf, rfl⟩
  have hperm : SimS ((List.range a0.size).foldl (NatKernel.permStep logN) a0)
      ((List.range a0.size).foldl (NatKernel.permStep logN) (a0.map montValS)) :=
    foldl_relS SimS _ _ _ (fun s s' k hs => simS_permStep logN hs k) _ _ hsim0
  have hrounds : SimS
      ((List.range logN).foldl (fun a r =>
        NatKernel.roundFoldGen PallasFq.add PallasFq.sub PallasFq.mul a0.size (2 ^ r) tw a)
        ((List.range a0.size).foldl (NatKernel.permStep logN) a0))
      ((List.range logN).foldl (fun a r =>
        NatKernel.roundFoldGen (· + ·) (· - ·) (fun (t : Fp) p => t.val • p) a0.size (2 ^ r)
          (twArrS omega (a0.size / 2)) a)
        ((List.range a0.size).foldl (NatKernel.permStep logN) (a0.map montValS))) :=
    foldl_relS SimS _ _ _
      (fun s s' r hs => simS_roundFold a0.size (2 ^ r) tw _ hwtw htw' hs) _ _ hperm
  rw [fftS_eq_gen, NatKernel.fftGen_eq_folds, bestFftG_eq_genS, NatKernel.fftGen_eq_folds,
    hsize]
  exact hrounds

end Zcash.Vendor.ScalarMont
