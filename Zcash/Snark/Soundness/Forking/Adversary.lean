import Zcash.Snark.Soundness.Forking.Adversary.OracleComp
import Zcash.Snark.Soundness.Forking.Adversary.Adaptive
import Zcash.Snark.Soundness.Forking.Adversary.PreIpa
import Zcash.Snark.Soundness.Forking.Adversary.DomainReduction
import Zcash.Snark.Soundness.Forking.Adversary.Recursive
import Zcash.Snark.Soundness.Forking.Adversary.ExpectedRuns
import Zcash.Snark.Soundness.Forking.Adversary.ExpectedRunsPoly
import Zcash.Snark.Soundness.Forking.Adversary.Algebraic
import Zcash.Snark.Soundness.Forking.Adversary.Provenance

/-!
# Fiat–Shamir adversary and extraction

Model a querying adversary, compute its fork certificate, and package the AGM reduction input.
-/
