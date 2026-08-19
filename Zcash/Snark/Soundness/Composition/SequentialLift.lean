import Zcash.Snark.Soundness.Composition.StraightLineDeployed
import Zcash.Snark.Soundness.Composition.PrefixedSqueeze

/-!
# Sequential online-AGM provers lift to the staged family

The adversary-coverage theorem of issue #127: any Fiat–Shamir prover presented in its own
execution order — a pre-`x` phase, one query at its `x` squeeze point, a continuation — admits
the staged constraint-`x` chronology, so it lifts to the full staged family with its run
function, and hence its outputs, acceptance probability, and query bound, unchanged.

The model (`SequentialPreXProver`) is purely structural.  Its fields name the prover's internal
state, its pre-`x` computation, its own `x` squeeze point, and the pre-`x` *view* — the messages
it has emitted before the `x` query.  No field mentions a bad event, a decode, or a polynomial;
the lifting proves the total constraint difference is computable from the view because the
difference reads nothing the prover has not yet emitted.

The root and IPA traces are intrinsic to the family the lift extends; the lift adds the one
chronology layer issue #127 changed.
-/

namespace Zcash.Snark

open Classical CompPoly.CPolynomial

variable {shape : Shape}

local instance vestaInhabitedSequentialLift : Inhabited VestaG := ⟨0⟩

/-! ## The pre-`x` view and its total difference -/

/-- Everything the total constraint difference reads, as a prover has emitted it before its `x`
query: the pre-`x₁` representation points, the quotient-piece representations, the proof-string
fields the feeds consume, and the four folding challenges. -/
structure PreXView (shape : Shape) (basis : AugmentedIndex (2 ^ shape.k) → VestaG) where
  ps : ProofString shape Fp VestaG
  points : List (AlgebraicPoint (F := Fp) basis)
  pieces : Fin shape.numQuotientPieces → AlgebraicPoint (F := Fp) basis
  theta : Fp
  beta : Fp
  gamma : Fp
  y : Fp

namespace PreXView

variable {basis : AugmentedIndex (2 ^ shape.k) → VestaG}

/-- The view's four folding challenges in their squeeze slots, zero elsewhere. -/
def nu (v : PreXView shape basis) : Fin 11 → Fp :=
  fun j => if j = 0 then v.theta else if j = 1 then v.beta else if j = 2 then v.gamma
    else if j = 3 then v.y else 0

/-- The total pre-`x` constraint difference computed from a view alone. -/
def difference (v : PreXView shape basis)
    (vk : VerifyingKey shape Fp VestaG)
    (ic : Fin shape.numProofs → ℕ → VestaG)
    (fixed : List (AlgebraicPoint (F := Fp) basis)) : CPoly :=
  committedPreXConstraintDifference
    (onlinePointPolynomial (v.points ++ fixed))
    (fun i => coeffsToPoly (onlinePointCoordinates (v.points ++ fixed) (v.pieces i).point).1)
    vk ic v.ps (chRecord v.nu (fun _ => 0))

end PreXView

/-! ## Congruences: what the difference reads -/

/-- The advice feed reads only the advice commitments. -/
private theorem committedAdviceFeed_congr (poly : VestaG → CPoly)
    (vk : VerifyingKey shape Fp VestaG) {ps₁ ps₂ : ProofString shape Fp VestaG}
    (hadv : ∀ q, ps₁.adviceCommitments q = ps₂.adviceCommitments q) :
    committedAdviceFeed poly vk ps₁ = committedAdviceFeed poly vk ps₂ := by
  funext q
  unfold committedAdviceFeed
  exact congrArg (rotatedFeed vk.omega vk.adviceQueryLayout)
    (funext fun j => by rw [hadv q])

/-- The permutation-set carriers read the products and the `lastEval` schedule only; on the
schedule both sides' `lastEval` values are never consulted. -/
private theorem committedPermSets_congr (poly : VestaG → CPoly)
    (vk : VerifyingKey shape Fp VestaG) {ps₁ ps₂ : ProofString shape Fp VestaG}
    (hprod : ∀ q s, ps₁.permutationProduct q s = ps₂.permutationProduct q s)
    (hwf₁ : PsWellFormed ps₁) (hwf₂ : PsWellFormed ps₂) :
    committedPermSets poly vk ps₁ = committedPermSets poly vk ps₂ := by
  funext q
  unfold committedPermSets
  refine congrArg List.ofFn (funext fun s => ?_)
  rw [hprod q s]
  refine congrArg (PermSetEval.mk _ _) ?_
  by_cases hs : (s : ℕ) + 1 < shape.numPermutationSets
  · obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp ((hwf₁ q s).symm ▸ hs)
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp ((hwf₂ q s).symm ▸ hs)
    rw [ha, hb]
    simp [hs]
  · have ha : (ps₁.permutationSetEvals q s).lastEval = none :=
      Option.not_isSome_iff_eq_none.mp ((hwf₁ q s).symm ▸ hs)
    have hb : (ps₂.permutationSetEvals q s).lastEval = none :=
      Option.not_isSome_iff_eq_none.mp ((hwf₂ q s).symm ▸ hs)
    rw [ha, hb]

/-- The lookup carriers read the three lookup commitments. -/
private theorem committedLookups_congr (poly : VestaG → CPoly)
    (vk : VerifyingKey shape Fp VestaG) {ps₁ ps₂ : ProofString shape Fp VestaG}
    (hprod : ∀ q l, ps₁.lookupProduct q l = ps₂.lookupProduct q l)
    (hin : ∀ q l, ps₁.lookupPermutedInput q l = ps₂.lookupPermutedInput q l)
    (htab : ∀ q l, ps₁.lookupPermutedTable q l = ps₂.lookupPermutedTable q l) :
    committedLookups poly vk ps₁ = committedLookups poly vk ps₂ := by
  funext q
  unfold committedLookups
  exact congrArg List.ofFn (funext fun l => by rw [hprod q l, hin q l, htab q l])

/-- **What the total difference reads from the proof string**: advice commitments, permutation
products with the `lastEval` schedule, and the lookup commitments.  Everything else — including
every claimed evaluation — is invisible to it. -/
theorem committedPreXConstraintDifference_ps_congr (poly : VestaG → CPoly)
    (piecePoly : Fin shape.numQuotientPieces → CPoly)
    (vk : VerifyingKey shape Fp VestaG) (ic : Fin shape.numProofs → ℕ → VestaG)
    {ps₁ ps₂ : ProofString shape Fp VestaG} (ch : Challenges shape.k Fp)
    (hadv : ∀ q, ps₁.adviceCommitments q = ps₂.adviceCommitments q)
    (hpermProd : ∀ q s, ps₁.permutationProduct q s = ps₂.permutationProduct q s)
    (hwf₁ : PsWellFormed ps₁) (hwf₂ : PsWellFormed ps₂)
    (hlkProd : ∀ q l, ps₁.lookupProduct q l = ps₂.lookupProduct q l)
    (hlkIn : ∀ q l, ps₁.lookupPermutedInput q l = ps₂.lookupPermutedInput q l)
    (hlkTab : ∀ q l, ps₁.lookupPermutedTable q l = ps₂.lookupPermutedTable q l) :
    committedPreXConstraintDifference poly piecePoly vk ic ps₁ ch =
      committedPreXConstraintDifference poly piecePoly vk ic ps₂ ch := by
  unfold committedPreXConstraintDifference committedPermChunks
  rw [committedAdviceFeed_congr poly vk hadv,
    committedPermSets_congr poly vk hpermProd hwf₁ hwf₂,
    committedLookups_congr poly vk hlkProd hlkIn hlkTab]

/-- The total difference reads the challenge record only through `θ`, `β`, `γ`, `y`. -/
theorem committedPreXConstraintDifference_challenge_congr (poly : VestaG → CPoly)
    (piecePoly : Fin shape.numQuotientPieces → CPoly)
    (vk : VerifyingKey shape Fp VestaG) (ic : Fin shape.numProofs → ℕ → VestaG)
    (ps : ProofString shape Fp VestaG) {ch₁ ch₂ : Challenges shape.k Fp}
    (htheta : ch₁.theta = ch₂.theta) (hbeta : ch₁.beta = ch₂.beta)
    (hgamma : ch₁.gamma = ch₂.gamma) (hy : ch₁.y = ch₂.y) :
    committedPreXConstraintDifference poly piecePoly vk ic ps ch₁ =
      committedPreXConstraintDifference poly piecePoly vk ic ps ch₂ := by
  unfold committedPreXConstraintDifference
  rw [htheta, hbeta, hgamma, hy]

/-! ## The sequential prover model -/

/-- **A sequential online-AGM Fiat–Shamir prover, cut at its `x` squeeze.**  The fields are the
prover's own execution order: an internal state type, the computation up to the `x` query, the
`x` squeeze point read off that state, and the pre-`x` view — the messages emitted so far.  The
equations tie the state to the final run and record that the pre-`x` phase does not query the
`x` point.  Nothing here mentions a bad event, a decode, or a witness. -/
structure SequentialPreXProver (family : ComputedDeployedRootFSFamily shape) where
  /-- The prover's internal state at its `x` query. -/
  State : Type
  /-- The computation up to (excluding) the `x` query. -/
  pre : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) →
    OracleComp
      (BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k))
      Fp State
  /-- The prover's own `x` squeeze point, read off its state. -/
  xPoint : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → State →
    BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k)
  /-- The messages emitted before the `x` query, decoded from the state. -/
  view : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → State → PreXView shape basis
  /-- The state's `x` point is the run's `x` prefix. -/
  xPoint_run : ∀ basis O, xPoint basis ((pre basis).run O) =
    algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 4
  /-- The pre-`x` phase never queries the `x` point. -/
  pre_fresh : ∀ basis O, xPoint basis ((pre basis).run O) ∉ (pre basis).queries O
  /-- The view's representation points are the run's pre-`x₁` points. -/
  view_points : ∀ basis O, (view basis ((pre basis).run O)).points =
    ((family.adversary basis).run O).algebraicProof.preX1Points
  /-- The view's quotient-piece representations are the run's. -/
  view_pieces : ∀ basis O i, (view basis ((pre basis).run O)).pieces i =
    ((family.adversary basis).run O).algebraicProof.hPieces i
  /-- The view's advice commitments are the run's. -/
  view_advice : ∀ basis O q, (view basis ((pre basis).run O)).ps.adviceCommitments q =
    ((family.adversary basis).run O).proof.1.adviceCommitments q
  /-- The view's permutation products are the run's. -/
  view_permProduct : ∀ basis O q s,
    (view basis ((pre basis).run O)).ps.permutationProduct q s =
      ((family.adversary basis).run O).proof.1.permutationProduct q s
  /-- The view's proof-string skeleton follows the reader schedule. -/
  view_wf : ∀ basis O, PsWellFormed (view basis ((pre basis).run O)).ps
  /-- The view's lookup products are the run's. -/
  view_lookupProduct : ∀ basis O q l,
    (view basis ((pre basis).run O)).ps.lookupProduct q l =
      ((family.adversary basis).run O).proof.1.lookupProduct q l
  /-- The view's permuted lookup inputs are the run's. -/
  view_lookupInput : ∀ basis O q l,
    (view basis ((pre basis).run O)).ps.lookupPermutedInput q l =
      ((family.adversary basis).run O).proof.1.lookupPermutedInput q l
  /-- The view's permuted lookup tables are the run's. -/
  view_lookupTable : ∀ basis O q l,
    (view basis ((pre basis).run O)).ps.lookupPermutedTable q l =
      ((family.adversary basis).run O).proof.1.lookupPermutedTable q l
  /-- The view's `θ` is the oracle's answer at the run's `θ` prefix. -/
  view_theta : ∀ basis O, (view basis ((pre basis).run O)).theta =
    O (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 0)
  /-- The view's `β` is the oracle's answer at the run's `β` prefix. -/
  view_beta : ∀ basis O, (view basis ((pre basis).run O)).beta =
    O (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 1)
  /-- The view's `γ` is the oracle's answer at the run's `γ` prefix. -/
  view_gamma : ∀ basis O, (view basis ((pre basis).run O)).gamma =
    O (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 2)
  /-- The view's `y` is the oracle's answer at the run's `y` prefix. -/
  view_y : ∀ basis O, (view basis ((pre basis).run O)).y =
    O (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 3)

namespace SequentialPreXProver

variable {family : ComputedDeployedRootFSFamily shape}

/-- The lifted constraint-`x` stage: run the prover's own pre-`x` phase and price the view's
difference. -/
def constraintXStage (sp : SequentialPreXProver family)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) :
    OracleComp
      (BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k))
      Fp (Set Fp) :=
  (sp.pre basis).bind fun st => .pure
    ↑(szBadSet ((sp.view basis st).difference (family.vk basis)
      (family.instanceCommitment basis) (family.fixedRepresentations basis)))

/-- **The view's difference is the run's total difference.**  Each argument of the difference is
matched: the representation source by `view_points`, the pieces by `view_pieces`, the proof
string by the `ps`-congruence at the fields the difference reads, and the record by the
challenge congruence at the four folding reads. -/
theorem view_difference_eq (sp : SequentialPreXProver family)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    (sp.view basis ((sp.pre basis).run O)).difference (family.vk basis)
        (family.instanceCommitment basis) (family.fixedRepresentations basis) =
      deployedConstraintDifferencePreX family basis O := by
  have hrun : (deployedRootRunOutput family basis O).1 =
      (family.adversary basis).run O :=
    wrappedAdversary_run_fst family.toFamily basis O
  have hreads : ∀ i, wrappedPreIpaReads (deployedRootRunOutput family basis O) i =
      O (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) i) := by
    intro i
    have h := congrFun (wrappedPreIpaReads_run family.toFamily basis O) i
    simpa [runReads, runProof] using h
  simp only [PreXView.difference, deployedConstraintDifferencePreX,
    deployedConstraintSource, deployedConstraintPieceCoordinates,
    AlgebraicProofString.preX1AssemblySource]
  rw [show ((sp.view basis ((sp.pre basis).run O)).points :
        List (AlgebraicPoint (F := Fp) basis)) =
      (deployedRootRunOutput family basis O).1.algebraicProof.preX1Points by
    rw [hrun]; exact sp.view_points basis O]
  rw [show (sp.view basis ((sp.pre basis).run O)).pieces =
      (deployedRootRunOutput family basis O).1.algebraicProof.hPieces by
    funext i; rw [hrun]; exact sp.view_pieces basis O i]
  rw [committedPreXConstraintDifference_ps_congr
    (ps₂ := (deployedRootRunOutput family basis O).1.proof.1) _ _ _ _ _
    (fun q => by rw [hrun]; exact sp.view_advice basis O q)
    (fun q s => by rw [hrun]; exact sp.view_permProduct basis O q s)
    (sp.view_wf basis O)
    (by rw [hrun]; exact ((family.adversary basis).run O).proof.2)
    (fun q l => by rw [hrun]; exact sp.view_lookupProduct basis O q l)
    (fun q l => by rw [hrun]; exact sp.view_lookupInput basis O q l)
    (fun q l => by rw [hrun]; exact sp.view_lookupTable basis O q l)]
  exact committedPreXConstraintDifference_challenge_congr _ _ _ _ _
    (by show (sp.view basis ((sp.pre basis).run O)).nu 0 = _
        simp only [PreXView.nu]
        rw [sp.view_theta basis O, ← hreads 0]
        rfl)
    (by show (sp.view basis ((sp.pre basis).run O)).nu 1 = _
        simp only [PreXView.nu]
        norm_num
        rw [sp.view_beta basis O, ← hreads 1]
        rfl)
    (by show (sp.view basis ((sp.pre basis).run O)).nu 2 = _
        simp only [PreXView.nu]
        norm_num
        rw [sp.view_gamma basis O, ← hreads 2]
        rfl)
    (by show (sp.view basis ((sp.pre basis).run O)).nu 3 = _
        simp only [PreXView.nu]
        norm_num
        rw [sp.view_y basis O, ← hreads 3]
        rfl)

/-- The lifted stage computes the run's total bad set. -/
theorem constraintXStage_agrees (sp : SequentialPreXProver family)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    (sp.constraintXStage basis).run O = deployedConstraintXBadSet family basis O := by
  rw [constraintXStage, OracleComp.run_bind, OracleComp.run_pure]
  ext x
  simp only [Finset.mem_coe, deployedConstraintXBadSet]
  rw [sp.view_difference_eq basis O]

/-- The lifted stage's queries are the prover's own pre-`x` queries, so the `x` prefix is
untouched. -/
theorem constraintXStage_fresh (sp : SequentialPreXProver family)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) :
    algebraicFullPrefixesPre family.init ((family.adversary basis).run O) 4 ∉
      (sp.constraintXStage basis).queries O := by
  rw [← sp.xPoint_run basis O]
  intro hmem
  apply sp.pre_fresh basis O
  simpa [constraintXStage, OracleComp.queries_bind, OracleComp.queries] using hmem

/-- **The lifted constraint-`x` chronology.** -/
def toConstraintXTrace (sp : SequentialPreXProver family) :
    DeployedConstraintXOnlineTrace family where
  stage := fun basis => sp.constraintXStage basis
  agrees := fun basis O => sp.constraintXStage_agrees basis O
  fresh := fun basis O => sp.constraintXStage_fresh basis O

/-- **Adversary coverage** (issue #127 C8).  A sequential online-AGM prover over a deployed root
family lifts to the full staged family: the root and IPA chronologies are intrinsic to the
inputs, and the constraint-`x` chronology is derived from the prover's own execution order.
The family's adversary, query budget, and hence outputs and acceptance probability are the
inputs' own — see the `rfl` lemmas below. -/
def lift (sp : SequentialPreXProver family)
    (ipaTrace : StraightLineIpaOnlineTrace family.toFamily) :
    ComputedStraightLineDeployedFSFamily shape where
  toComputedDeployedRootFSFamily := family
  ipaTrace := ipaTrace
  constraintXTrace := sp.toConstraintXTrace

/-- The lift preserves the adversary: outputs and acceptance probability are unchanged. -/
theorem lift_adversary (sp : SequentialPreXProver family)
    (ipaTrace : StraightLineIpaOnlineTrace family.toFamily) :
    (sp.lift ipaTrace).adversary = family.adversary := rfl

/-- The lift preserves the query budget. -/
theorem lift_Q (sp : SequentialPreXProver family)
    (ipaTrace : StraightLineIpaOnlineTrace family.toFamily) :
    (sp.lift ipaTrace).Q = family.Q := rfl

/-- The lift preserves the verifying key and the instance commitment. -/
theorem lift_vk (sp : SequentialPreXProver family)
    (ipaTrace : StraightLineIpaOnlineTrace family.toFamily) :
    (sp.lift ipaTrace).vk = family.vk ∧
      (sp.lift ipaTrace).instanceCommitment = family.instanceCommitment :=
  ⟨rfl, rfl⟩

end SequentialPreXProver

/-! ## A complete sequential online-AGM prover

The public sequential model carries stopped root and IPA computations and derives all traces
internally before applying the pre-`x` lift.
-/

/-- Executable stages of an online member prover stopped before each of the six deployed-root
squeezes.  The agreement and freshness fields state that these are phases of the prover's own
execution, not independently selected bad sets. -/
structure SequentialRootProver (online : ComputedOnlineMemberFSFamily shape) where
  stage :
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → Fin 6 →
      OracleComp
        (BTranscript Fp VestaG
          (preIpaLen shape online.init.length 10 + 3 * shape.k)) Fp (Set Fp)
  agrees : ∀ (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (i : Fin 6)
      (O : BTranscript Fp VestaG
        (preIpaLen shape online.init.length 10 + 3 * shape.k) → Fp),
    (stage basis i).run O =
      deployedRootBad online.toFamily (deployedRootOutcomeOfCovered online) basis
        ((wrappedAdversary online.toFamily basis).run O) O i
  fresh : ∀ (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (i : Fin 6)
      (O : BTranscript Fp VestaG
        (preIpaLen shape online.init.length 10 + 3 * shape.k) → Fp),
    deployedRootPoint online.toFamily ((wrappedAdversary online.toFamily basis).run O) i ∉
      (stage basis i).queries O

namespace SequentialRootProver

variable {online : ComputedOnlineMemberFSFamily shape}

/-- The deployed-root trace generated by the prover's stopped computations. -/
def toTrace (sp : SequentialRootProver online) :
    DeployedRootOnlineTrace online.toFamily (deployedRootOutcomeOfCovered online) where
  stage := sp.stage
  agrees := sp.agrees
  fresh := sp.fresh

/-- The deployed-root family generated from the online prover and its execution stages. -/
def toFamily (sp : SequentialRootProver online) : ComputedDeployedRootFSFamily shape :=
  ComputedDeployedRootFSFamily.ofCovered online sp.toTrace

end SequentialRootProver

/-- The remaining executable stages of a sequential prover: every IPA-round computation and the
pre-`x` computation.  Together with `root`, these data generate the complete straight-line
family while preserving the underlying adversary and query bound definitionally. -/
structure SequentialStraightLineProver {online : ComputedOnlineMemberFSFamily shape}
    (root : SequentialRootProver online) where
  ipaStage :
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → Fin shape.k →
      OracleComp
        (BTranscript Fp VestaG
          (preIpaLen shape online.init.length 10 + 3 * shape.k)) Fp (CPoly)
  ipaAgrees : ∀ (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k)
      (O : BTranscript Fp VestaG
        (preIpaLen shape online.init.length 10 + 3 * shape.k) → Fp),
    (ipaStage basis j).run O =
      ((online.adversary basis).run O).straightLineIpaRootPolynomial
        (fun i => O (algebraicFullPrefixesPre online.init
          ((online.adversary basis).run O) i))
        (fun r => O (algebraicFullPrefixes online.init
          ((online.adversary basis).run O) r)) j
  ipaFresh : ∀ (basis : AugmentedIndex (2 ^ shape.k) → VestaG) (j : Fin shape.k)
      (O : BTranscript Fp VestaG
        (preIpaLen shape online.init.length 10 + 3 * shape.k) → Fp),
    straightLineIpaRootPoint online.toFamily ((online.adversary basis).run O) j ∉
      (ipaStage basis j).queries O
  preX : SequentialPreXProver root.toFamily

namespace SequentialStraightLineProver

variable {online : ComputedOnlineMemberFSFamily shape}
  {root : SequentialRootProver online}

/-- The IPA trace generated by the prover's stopped round computations. -/
def toIpaTrace (sp : SequentialStraightLineProver root) :
    StraightLineIpaOnlineTrace online.toFamily where
  stage := sp.ipaStage
  agrees := sp.ipaAgrees
  fresh := sp.ipaFresh

/-- The complete staged family generated by one sequential prover.  No root, IPA, or constraint
trace is accepted as an input to this constructor. -/
def toFamily (sp : SequentialStraightLineProver root) :
    ComputedStraightLineDeployedFSFamily shape :=
  sp.preX.lift sp.toIpaTrace

end SequentialStraightLineProver

/-- The advertised bounded sequential online-AGM adversary model.  It begins with the ordinary
online member producer and packages its executable stopped computations; all chronology
interfaces consumed by the soundness proof are generated projections. -/
structure SequentialOnlineAGMProver (shape : Shape) where
  online : ComputedOnlineMemberFSFamily shape
  root : SequentialRootProver online
  straight : SequentialStraightLineProver root

namespace SequentialOnlineAGMProver

/-- Generate the complete straight-line family from the phased prover. -/
def toFamily (sp : SequentialOnlineAGMProver shape) :
    ComputedStraightLineDeployedFSFamily shape :=
  sp.straight.toFamily

/-- The lift preserves the original adversary. -/
theorem toFamily_adversary (sp : SequentialOnlineAGMProver shape) :
    sp.toFamily.adversary = sp.online.adversary := rfl

/-- The lift preserves the original random-oracle query budget. -/
theorem toFamily_Q (sp : SequentialOnlineAGMProver shape) : sp.toFamily.Q = sp.online.Q := rfl

end SequentialOnlineAGMProver

/-! ## Cuts at arbitrary squeeze indices

The constraint-`x` lifting above is the cut at index `4`.  The semantic challenge budgets need
the same discipline at the four folding squeezes, so the cut is packaged uniformly: a prover's
computation up to its `n`-th squeeze query, with every pre-cut query strictly shorter than the
prefix it is about to squeeze.  Prefix-determinism at `n` — the pricing input the squeeze
machinery consumes — is derived, never assumed.
-/

/-- Two tables agreeing on every point a computation queries produce the same run and the same
query log. -/
theorem OracleComp.run_congr_of_agree {T F α : Type*} (A : OracleComp T F α)
    (O O' : T → F) (h : ∀ t ∈ A.queries O, O t = O' t) :
    A.run O = A.run O' ∧ A.queries O = A.queries O' := by
  induction A with
  | pure a => exact ⟨rfl, rfl⟩
  | query t k ih =>
      have ht : O t = O' t := h t (by simp [OracleComp.queries])
      obtain ⟨hr, hq⟩ := ih (O t) (fun u hu => h u (by simp [OracleComp.queries, hu]))
      constructor
      · rw [OracleComp.run_query, OracleComp.run_query, ← ht, hr]
      · rw [OracleComp.queries, OracleComp.queries, ← ht, hq]

/-- **A sequential cut at pre-IPA squeeze index `n`**: the prover's computation up to its `n`-th
squeeze query.  Purely structural — an internal state, the pre-cut computation, and the squeeze
point read off the state — plus the execution-order discipline: every pre-cut query is strictly
shorter than the prefix about to be squeezed. -/
structure SequentialCut (family : ComputedAlgebraicFSFamily shape) (n : Fin 11) where
  /-- The prover's internal state at its `n`-th squeeze query. -/
  State : Type
  /-- The computation up to (excluding) the `n`-th squeeze query. -/
  pre : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) →
    OracleComp
      (BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k))
      Fp State
  /-- The prover's own `n`-th squeeze point, read off its state. -/
  point : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → State →
    BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k)
  /-- The state's point is the run's `n`-th squeeze prefix. -/
  point_run : ∀ basis O, point basis ((pre basis).run O) =
    algebraicFullPrefixesPre family.init ((family.adversary basis).run O) n
  /-- Every pre-cut query is strictly shorter than the `n`-th squeeze prefix. -/
  pre_short : ∀ basis O t, t ∈ (pre basis).queries O →
    t.val.length < preIpaLen shape family.init.length n

/-- A sequential phase whose computation returns the data emitted before squeeze `n`.  Unlike a
bare `SequentialCut`, the state exposed to later semantic arguments is exactly the phase output;
there is no separately postulated state-to-view function. -/
structure SequentialPhase (family : ComputedAlgebraicFSFamily shape) (n : Fin 11)
    (View : Type) where
  pre : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) →
    OracleComp
      (BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k))
      Fp View
  point : (basis : AugmentedIndex (2 ^ shape.k) → VestaG) → View →
    BTranscript Fp VestaG (preIpaLen shape family.init.length 10 + 3 * shape.k)
  point_run : ∀ basis O, point basis ((pre basis).run O) =
    algebraicFullPrefixesPre family.init ((family.adversary basis).run O) n
  pre_short : ∀ basis O t, t ∈ (pre basis).queries O →
    t.val.length < preIpaLen shape family.init.length n

/-- Forget a phase's typed output while retaining its derived sequential cut. -/
def SequentialPhase.toCut {family : ComputedAlgebraicFSFamily shape} {n : Fin 11}
    {View : Type} (phase : SequentialPhase family n View) : SequentialCut family n where
  State := View
  pre := phase.pre
  point := phase.point
  point_run := phase.point_run
  pre_short := phase.pre_short

/-- **Prefix-determinism from execution order.**  A cut at `n` yields the index-`n`
prefix-determinism the squeeze pricing consumes: tables agreeing below the prefix length agree
on every pre-cut query, so the state — and with it the squeeze point — is unchanged. -/
theorem SequentialCut.toPrefixDeterminedAt {family : ComputedAlgebraicFSFamily shape}
    {n : Fin 11} (c : SequentialCut family n) :
    PrefixDeterminedAt family n := by
  intro basis O O' hagree
  have hpre : (c.pre basis).run O = (c.pre basis).run O' :=
    (OracleComp.run_congr_of_agree _ O O' (fun t ht =>
      hagree t (c.pre_short basis O t ht))).1
  calc algebraicFullPrefixesPre family.init ((family.adversary basis).run O) n
      = c.point basis ((c.pre basis).run O) := (c.point_run basis O).symm
    _ = c.point basis ((c.pre basis).run O') := by rw [hpre]
    _ = algebraicFullPrefixesPre family.init ((family.adversary basis).run O') n :=
      c.point_run basis O'

/-- The cut state is unchanged when the oracle is re-answered at the cut's own squeeze point:
that point has exactly the prefix length, and every pre-cut query is strictly shorter. -/
theorem SequentialCut.state_stable {family : ComputedAlgebraicFSFamily shape}
    {n : Fin 11} (c : SequentialCut family n)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) (v : Fp) :
    (c.pre basis).run (Function.update O (algebraicFullPrefixesPre family.init
        ((family.adversary basis).run O) n) v) = (c.pre basis).run O := by
  refine ((OracleComp.run_congr_of_agree _ O _ (fun t ht => ?_)).1).symm
  rw [Function.update_apply, if_neg]
  intro hEq
  have hshort := c.pre_short basis O t ht
  have hlen : (algebraicFullPrefixesPre family.init
      ((family.adversary basis).run O) n).val.length
      = preIpaLen shape family.init.length n :=
    preIpaSqueezePoints_length_eq family.init _
      ((family.adversary basis).run O).proof.2 n
  rw [hEq, hlen] at hshort
  exact lt_irrefl _ hshort

/-- The basis/table pairs whose index-`n` squeeze answer lands in a bad set computed from the
cut state.  This is the shape a semantic exclusion event takes once its set is rewritten to the
cut's own view: the set may read anything the prover has computed before the squeeze, and
nothing after it. -/
def SequentialCut.surfaceEvent {family : ComputedAlgebraicFSFamily shape}
    {n : Fin 11} (c : SequentialCut family n)
    (bad : (AugmentedIndex (2 ^ shape.k) → VestaG) → c.State → Set Fp) :
    Set ((AugmentedIndex (2 ^ shape.k) → VestaG) ×
      (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)) :=
  {q | q.2 (algebraicFullPrefixesPre family.init ((family.adversary q.1).run q.2) n) ∈
    bad q.1 ((c.pre q.1).run q.2)}

/-- One basis's index-`n` state surface costs `(Q + 1) * epsilon`: the squeeze answer is fresh
for the state that chose the bad set, so each of the at most `Q + 1` candidate points pays the
per-state measure. -/
theorem SequentialCut.surfaceEvent_basis_le {family : ComputedAlgebraicFSFamily shape}
    {n : Fin 11} (c : SequentialCut family n)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (bad : (AugmentedIndex (2 ^ shape.k) → VestaG) → c.State → Set Fp)
    {epsilon : ENNReal}
    (hbad : ∀ basis s, (PMF.uniformOfFintype Fp).toOuterMeasure (bad basis s) ≤ epsilon) :
    (PMF.uniformOfFintype (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp)).toOuterMeasure
      {O | O (algebraicFullPrefixesPre family.init ((family.adversary basis).run O) n) ∈
        bad basis ((c.pre basis).run O)}
      ≤ (family.Q + 1 : ℕ) * epsilon := by
  refine xEscTable_measure_le (family.adversary basis)
    (fun p => algebraicFullPrefixesPre family.init p n)
    (fun _p O => bad basis ((c.pre basis).run O))
    (fun O v => ?_) (fun _p O => hbad basis _) (family.queryBound basis)
  show bad basis ((c.pre basis).run (Function.update O (algebraicFullPrefixesPre family.init
      ((family.adversary basis).run O) n) v)) = bad basis ((c.pre basis).run O)
  rw [c.state_stable basis O v]

/-- **A state surface costs `(Q + 1) * epsilon`.**  The generator random oracle's basis draw is
averaged over the per-basis squeeze price.  Instantiate at `n = 3` for `y`, `2` for `γ`, `1`
for `β`, `0` for `θ`, with `bad` the semantic exclusion set read off the cut state. -/
theorem SequentialCut.surfaceEvent_prob_le {T' : Type*} [DecidableEq T']
    {family : ComputedAlgebraicFSFamily shape}
    {n : Fin 11} (c : SequentialCut family n)
    (query : AugmentedIndex (2 ^ shape.k) → T')
    (bad : (AugmentedIndex (2 ^ shape.k) → VestaG) → c.State → Set Fp)
    {epsilon : ENNReal}
    (hbad : ∀ basis s, (PMF.uniformOfFintype Fp).toOuterMeasure (bad basis s) ≤ epsilon) :
    (independentProductPMF (orchardGeneratorROSetup query)
      (PMF.uniformOfFintype (BTranscript Fp VestaG
        (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp))).toOuterMeasure
        ((fun p => (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' c.surfaceEvent bad)
      ≤ (family.Q + 1 : ℕ) * epsilon := by
  have hset : (fun p : (↥(Set.range query) → VestaG) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) =>
        (orchardGeneratorROBasis query p.1, p.2)) ⁻¹' c.surfaceEvent bad =
      {x : (↥(Set.range query) → VestaG) ×
        (BTranscript Fp VestaG
          (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp) | x.2 ∈
        (fun setup => {O | O (algebraicFullPrefixesPre family.init
            ((family.adversary (orchardGeneratorROBasis query setup)).run O) n) ∈
          bad (orchardGeneratorROBasis query setup)
            ((c.pre (orchardGeneratorROBasis query setup)).run O)}) x.1} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_setOf_eq, SequentialCut.surfaceEvent]
  rw [hset]
  refine independentProductPMF_fiber_bound (orchardGeneratorROSetup query)
    (PMF.uniformOfFintype (BTranscript Fp VestaG
      (preIpaLen shape family.init.length 10 + 3 * shape.k) → Fp))
    (fun setup => {O | O (algebraicFullPrefixesPre family.init
        ((family.adversary (orchardGeneratorROBasis query setup)).run O) n) ∈
      bad (orchardGeneratorROBasis query setup)
        ((c.pre (orchardGeneratorROBasis query setup)).run O)}) ?_
  intro setup
  exact c.surfaceEvent_basis_le (orchardGeneratorROBasis query setup) bad hbad

end Zcash.Snark
