import Zcash.Circuits.ConfigureAppendOnly
import Zcash.Circuits.Ecc.WitnessPoint
import Zcash.Circuits.Ecc.AddIncomplete
import Zcash.Circuits.Ecc.Add
import Zcash.Circuits.Ecc.Mul
import Zcash.Circuits.Ecc.MulFixed
import Zcash.Circuits.Ecc.MulFixed.FullWidth
import Zcash.Circuits.Ecc.MulFixed.Short
import Zcash.Circuits.Ecc.MulFixed.BaseFieldElem

/-!
# ECC chip configure (Ironwood)

The aggregate ECC configuration, in VK-exact registration order: witness point, incomplete
addition, complete addition, variable-base mul, the shared `mul_fixed` core, then the
full-width / short / base-field-element wrappers.

Reference: `halo2_gadgets/src/ecc/chip.rs`.
-/

namespace Zcash.Circuits.Ecc

open Halo2

structure EccConfig where
  -- Witness point.
  witnessPoint : WitnessPoint.Config
  -- Incomplete addition.
  addIncomplete : AddIncomplete.Config
  -- Complete addition.
  add : Add.Config
  -- Variable-base scalar multiplication.
  mul : Mul.Config
  -- Fixed-base full-width scalar multiplication.
  mulFixedFull : MulFixed.FullWidth.Config
  -- Fixed-base signed short scalar multiplication.
  mulFixedShort : MulFixed.Short.Config
  -- Fixed-base mul using a base field element as a scalar.
  mulFixedBaseField : MulFixed.BaseFieldElem.Config

/-- The aggregate ECC configuration, in VK-exact registration order. All `advices` columns are
equality-enabled. -/
def configure (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) : Configure Fp EccConfig := do
  -- witness point gate
  let witnessPoint ← WitnessPoint.configure (advices 0) (advices 1)
  -- incomplete point addition gate
  let addIncomplete ← AddIncomplete.add.configure
    (advices 0, advices 1, advices 2, advices 3)
  -- complete point addition gate
  let add ← Add.add.configure
    (advices 0, advices 1, advices 2, advices 3, advices 4, advices 5,
     advices 6, advices 7, advices 8)
  -- variable-base scalar mul gates
  let mul ← Mul.configure add rangeCheck advices
  -- the shared fixed-base mul core (short, base-field, and full-width)
  let mulFixed ← MulFixed.configure lagrangeCoeffs (advices 4) (advices 5)
    add addIncomplete
  -- full-width fixed-base mul gate
  let mulFixedFull ← MulFixed.FullWidth.configure mulFixed
  -- short fixed-base mul gate
  let mulFixedShort ← MulFixed.Short.configure mulFixed
  -- base-field-element fixed-base mul gate
  let mulFixedBaseField ← MulFixed.BaseFieldElem.configure
    ![advices 6, advices 7, advices 8] rangeCheck mulFixed
  return { witnessPoint, addIncomplete, add, mul, mulFixedFull, mulFixedShort,
           mulFixedBaseField }

/-- The whole ECC `configure` only appends to the constraint system's registration lists.

Five children take a config bound earlier in the `do` block, so their facts are named
quantified over that config and applied by hand at the end; the body says where. -/
theorem configure_appendOnly (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) :
    Configure.AppendOnly (configure advices lagrangeCoeffs rangeCheck) := by
  have hwitnessPoint := WitnessPoint.configure_appendOnly (advices 0) (advices 1)
  have haddIncomplete := AddIncomplete.add_configure_appendOnly
    (advices 0) (advices 1) (advices 2) (advices 3)
  have hadd := Add.add_configure_appendOnly
    (advices 0) (advices 1) (advices 2) (advices 3) (advices 4) (advices 5)
    (advices 6) (advices 7) (advices 8)
  have hmul : ∀ addConfig, Configure.AppendOnly (Mul.configure addConfig rangeCheck advices) :=
    fun addConfig => Mul.configure_appendOnly addConfig rangeCheck advices
  have hmulFixed : ∀ addConfig addIncompleteConfig,
      Configure.AppendOnly (MulFixed.configure lagrangeCoeffs (advices 4) (advices 5)
        addConfig addIncompleteConfig) :=
    fun addConfig addIncompleteConfig => MulFixed.configure_appendOnly lagrangeCoeffs
      (advices 4) (advices 5) addConfig addIncompleteConfig
  have hmulFixedFull : ∀ cfg, Configure.AppendOnly (MulFixed.FullWidth.configure cfg) :=
    MulFixed.FullWidth.configure_appendOnly
  have hmulFixedShort : ∀ cfg, Configure.AppendOnly (MulFixed.Short.configure cfg) :=
    MulFixed.Short.configure_appendOnly
  have hmulFixedBaseField : ∀ cfg, Configure.AppendOnly
      (MulFixed.BaseFieldElem.configure ![advices 6, advices 7, advices 8] rangeCheck cfg) :=
    fun cfg => MulFixed.BaseFieldElem.configure_appendOnly
      ![advices 6, advices 7, advices 8] rangeCheck cfg
  unfold configure
  append_only
  -- `append_only`'s `assumption` step matches only the fully-applied facts, so the five
  -- children taking a config bound earlier in the `do` block are instantiated by hand.
  · exact hmul _ _
  · exact hmulFixed _ _ _
  · exact hmulFixedFull _ _
  · exact hmulFixedShort _ _
  · exact hmulFixedBaseField _ _

end Zcash.Circuits.Ecc
