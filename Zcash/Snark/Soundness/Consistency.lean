import Zcash.Snark.Soundness.Halves
import Zcash.Snark.Soundness.CommitFold

/-!
# Folded IPA generators

`foldGens` is one IPA round's generator fold in the extractor's convention (`gLo + u⁻¹ • gHi`), used by
the IPA soundness layer (`Zcash.Snark.Soundness.IpaSoundness`).
-/

namespace Zcash.Snark

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

/-- The folded generators for one IPA round: `gLo + u⁻¹ • gHi`. The extractor's convention — the
witness folds by `u` (`foldVec`), so the generators fold by `u⁻¹`, the pairing under which an
accepting response is the true fold (`accepting_fold_eq_foldVec`). -/
def foldGens {k : ℕ} (g : Fin (2 ^ (k + 1)) → G) (u : F) : Fin (2 ^ k) → G :=
  loHalf g + u⁻¹ • hiHalf g

end Zcash.Snark
