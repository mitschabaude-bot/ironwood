import Zcash.Snark.Soundness.Forking.Oracle
import Zcash.Snark.Soundness.Forking.Tree
import Zcash.Snark.Soundness.Forking.Probability
import Zcash.Snark.Soundness.Forking.Extractor
import Zcash.Snark.Soundness.Forking.Assembly
import Zcash.Snark.Soundness.Forking.Ordering
import Zcash.Snark.Soundness.Forking.Rewind
import Zcash.Snark.Soundness.Forking.Adversary

/-!
# Fiat–Shamir forking soundness

Reusable random-oracle lemmas, fork certificates, transcript assembly, and the querying-adversary
reduction.
-/
