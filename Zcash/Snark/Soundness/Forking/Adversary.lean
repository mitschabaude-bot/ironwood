import Zcash.Snark.Soundness.Forking.Adversary.OracleComp
import Zcash.Snark.Soundness.Forking.Adversary.Adaptive
import Zcash.Snark.Soundness.Forking.Adversary.PreIpa
import Zcash.Snark.Soundness.Forking.Adversary.DomainReduction
import Zcash.Snark.Soundness.Forking.Adversary.Recursive
import Zcash.Snark.Soundness.Forking.Adversary.ExpectedRuns
import Zcash.Snark.Soundness.Forking.Adversary.Algebraic
import Zcash.Snark.Soundness.Forking.Adversary.Provenance

/-!
# Fiat–Shamir adversary and extraction

`Soundness/Forking/Adversary/` constructs the fork data consumed by the reusable kernel:

* `OracleComp` and `Adaptive` define the querying adversary and deployed attack game.
* `PreIpa` and `DomainReduction` connect that game to the deployed transcript and oracle domain.
* `Recursive` and `ExpectedRuns` compute the fork certificate and analyze its run count.
* `Algebraic` and `Provenance` package the certificate and standard AGM data for the DL reduction.
-/
