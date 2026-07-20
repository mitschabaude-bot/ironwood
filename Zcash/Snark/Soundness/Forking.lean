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

`Soundness/Forking/` is the reusable forking kernel: random-oracle primitives, fork trees and
certificates, probability lemmas, transcript ordering and assembly, and the
certificate-to-opening-or-relation reduction.

`Soundness/Forking/Adversary/` is the concrete producer layered on that kernel. It models the
querying Fiat–Shamir adversary, computes the fork certificate, and packages the AGM inputs.
-/
