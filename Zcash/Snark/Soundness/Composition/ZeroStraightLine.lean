import Zcash.Snark.Soundness.AGM.ZeroFamilyRoots
import Zcash.Snark.Soundness.Composition.StraightLineWitness

/-!
# The straight-line deployed interface, inhabited with live IPA rounds

`zeroStraightLineDeployedFamily` inhabits the straight-line deployed interface over the
shape-generic zero prover, with the IPA-round obligations live: at `k = 11` the staged trace
carries eleven rounds, each discharged by `straightLineIpaRootPolynomial_of_zero_coordinates`
rather than by an empty index type.  `Composition.StraightLineWitness` inhabits the same
interface at the witness shape, where `k = 0` empties those obligations.

Two hypotheses carry it.  The key's two group-valued commitment families are zero, which is what
the zero prover's assembly needs.  And the shape is instance-free, which is what discharges the
constraint layer: with no sub-proofs the folded constraint list is empty and the decoded quotient
pieces have zero coordinates, so the pre-`x` constraint difference is the zero polynomial and the
constraint-`x` root set is empty on every table.

The instance-free hypothesis is a simplification, not a boundary.  With issue #127's total
constraint-`x` event, `zeroConstStraightLineDeployedFamily` below discharges every obligation at
any shape: the constant-walk IPA trace leaves the multiopen value free, and the constraint-`x`
stage prices the explicit zero-data difference from the four folding squeezes alone.
`Fixtures.MultiAction.CapturedZeroFamily` instantiates it with both sub-proofs live.
-/

namespace Zcash.Snark

open CompPoly.CPolynomial
open scoped ENNReal

local instance vestaInhabitedZeroStraightLine : Inhabited VestaG := ⟨0⟩

variable {shape : Shape}

section ConstraintX

variable (vkS : VerifyingKey shape Fp VestaG)
  (hfixed : ∀ i, vkS.fixedCommitment i = 0)
  (hperm : ∀ i, vkS.permutationCommonCommitment i = 0)

/-- With no sub-proofs the folded constraint list is empty. -/
theorem constraintPolys_nil_of_no_proofs (hproofs : shape.numProofs = 0)
    (fixedCols : ℕ → CPoly)
    (adviceCols instanceCols : Fin shape.numProofs → ℕ → CPoly)
    (gates : List (Expr Fp))
    (sets : Fin shape.numProofs → List (PermSetEval (CPoly)))
    (chunks : Fin shape.numProofs →
      List (PermSetEval (CPoly) × List (CPoly × CPoly)))
    (lookups : Fin shape.numProofs →
      List (LookupEval (CPoly) × List (Expr Fp) × List (Expr Fp)))
    (beta gamma delta theta : Fp) (chunkLen : ℕ) (l0 lLast lBlind : CPoly) :
    constraintPolys fixedCols adviceCols instanceCols gates sets chunks lookups
      beta gamma delta theta chunkLen l0 lLast lBlind = [] := by
  unfold constraintPolys allConstraints
  have hnil : (List.ofFn (fun p : Fin shape.numProofs =>
      subProofConstraints fixedCols (adviceCols p) (instanceCols p) (gates.map (Expr.map C))
        (sets p) (chunks p)
        (((fun p => (lookups p).map (fun lk =>
          (lk.1, lk.2.1.map (Expr.map C), lk.2.2.map (Expr.map C)))) p))
        (C beta) (C gamma) X (C delta) (C theta) chunkLen l0 lLast lBlind)) = [] :=
    List.eq_nil_of_length_eq_zero (by rw [List.length_ofFn, hproofs])
  rw [hnil]
  rfl

/-- At an instance-free shape the zero family's pre-`x` constraint difference is the zero
polynomial: no sub-proof contributes a constraint, and the decoded quotient pieces read the
all-zero assembly source. -/
theorem zeroConstraintDifference_eq_zero (hproofs : shape.numProofs = 0)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (coins : (zeroDeployedRootFamily vkS hfixed hperm).toFamily.Coins) :
    deployedConstraintDifferencePreX (zeroDeployedRootFamily vkS hfixed hperm) basis coins
      = 0 := by
  have hsource : ∀ ap ∈ deployedConstraintSource (zeroDeployedRootFamily vkS hfixed hperm) basis
      (deployedRootRunOutput (zeroDeployedRootFamily vkS hfixed hperm) basis coins),
      ap = zeroAlgebraicPoint basis := by
    intro ap hap
    refine zeroAlgebraicProofString_source_eq basis ?_
    have hrun : (deployedRootRunOutput (zeroDeployedRootFamily vkS hfixed hperm) basis
        coins).1 = zeroWfProof basis vkS hfixed hperm :=
      zeroFamily_wrapped_run basis vkS hfixed hperm coins
    unfold deployedConstraintSource at hap
    rw [hrun] at hap
    exact hap
  have hpieces : ∀ i, coeffsToPoly (deployedConstraintPieceCoordinates
      (zeroDeployedRootFamily vkS hfixed hperm) basis
      (deployedRootRunOutput (zeroDeployedRootFamily vkS hfixed hperm) basis coins) i).1 = 0 := by
    intro i
    unfold deployedConstraintPieceCoordinates
    rw [onlinePointCoordinates_zeroSource basis hsource]
    show coeffsToPoly (fun _ => (0 : Fp)) = 0
    rw [coeffsToPoly]
    simp
  unfold deployedConstraintDifferencePreX
  rw [committedPreXConstraintDifference_eq, committedPreXQuotient_eq]
  simp only [combineConstraints, constraintPolys_nil_of_no_proofs hproofs, List.foldl_nil,
    preXQuotient]
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => by rw [hpieces i, MulZeroClass.mul_zero])]
  simp

/-- Hence the zero family's constraint-`x` root set is empty on every oracle table. -/
theorem zeroConstraintXBadSet_empty (hproofs : shape.numProofs = 0)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape (zeroDeployedRootFamily vkS hfixed hperm).init.length 10 +
        3 * shape.k) → Fp) :
    deployedConstraintXBadSet (zeroDeployedRootFamily vkS hfixed hperm) basis O = ∅ := by
  ext x
  simp only [deployedConstraintXBadSet, Set.mem_empty_iff_false, iff_false]
  intro hx
  rw [zeroConstraintDifference_eq_zero vkS hfixed hperm hproofs basis O] at hx
  exact (mem_szBadSet.mp hx).1 rfl

/-- **The zero family's executable constraint-`x` stage.**  The root set is empty, so the stage
returns it without reading the oracle and freshness of the `x` squeeze is immediate. -/
def zeroConstraintXTrace (hproofs : shape.numProofs = 0) :
    DeployedConstraintXOnlineTrace (zeroDeployedRootFamily vkS hfixed hperm) where
  stage := fun _basis => .pure (∅ : Set Fp)
  agrees := fun basis O => by
    rw [OracleComp.run_pure, zeroConstraintXBadSet_empty vkS hfixed hperm hproofs basis O]
  fresh := fun _basis _O => List.not_mem_nil

/-! ### The constraint-`x` stage without the instance-free hypothesis

With sub-proofs the zero prover's difference does not vanish, but the total event needs no
witness: the stage computes the explicit zero-data difference from the `θ`, `β`, `γ`, `y`
squeezes alone — indices `0`–`3`, all before the `x` prefix.
-/

/-- The zero prover's constraint difference, as an explicit function of the four folding
challenges: every feed reads the all-zero source, so only the key's own polynomials and the
challenge scalars remain. -/
def zeroExplicitConstraintDifference (ν : Fin 11 → Fp) : CPoly :=
  committedPreXConstraintDifference (fun _ => 0) (fun _ => 0)
    vkS (fun _ _ => 0) (zeroProofString shape Fp VestaG) (chRecord ν (fun _ => 0))

/-- The total difference of the zero family is the explicit zero-data difference at the run's
pre-IPA reads.  No instance-free hypothesis. -/
theorem zeroConstraintDifference_explicit
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (coins : (zeroDeployedRootFamily vkS hfixed hperm).toFamily.Coins) :
    deployedConstraintDifferencePreX (zeroDeployedRootFamily vkS hfixed hperm) basis coins =
      zeroExplicitConstraintDifference vkS
        (wrappedPreIpaReads
          (deployedRootRunOutput (zeroDeployedRootFamily vkS hfixed hperm) basis coins)) := by
  have hsource : ∀ ap ∈ deployedConstraintSource (zeroDeployedRootFamily vkS hfixed hperm) basis
      (deployedRootRunOutput (zeroDeployedRootFamily vkS hfixed hperm) basis coins),
      ap = zeroAlgebraicPoint basis := by
    intro ap hap
    refine zeroAlgebraicProofString_source_eq basis ?_
    have hrun : (deployedRootRunOutput (zeroDeployedRootFamily vkS hfixed hperm) basis
        coins).1 = zeroWfProof basis vkS hfixed hperm :=
      zeroFamily_wrapped_run basis vkS hfixed hperm coins
    unfold deployedConstraintSource at hap
    rw [hrun] at hap
    exact hap
  have hpoint : deployedConstraintPointPolynomial (zeroDeployedRootFamily vkS hfixed hperm)
      basis (deployedRootRunOutput (zeroDeployedRootFamily vkS hfixed hperm) basis coins) =
      fun _ => 0 := by
    funext P
    unfold deployedConstraintPointPolynomial onlinePointPolynomial
    rw [onlinePointCoordinates_zeroSource basis hsource]
    show coeffsToPoly (fun _ => (0 : Fp)) = 0
    rw [coeffsToPoly]
    simp
  have hpieces : (fun i => coeffsToPoly (deployedConstraintPieceCoordinates
      (zeroDeployedRootFamily vkS hfixed hperm) basis
      (deployedRootRunOutput (zeroDeployedRootFamily vkS hfixed hperm) basis coins) i).1) =
      fun _ => (0 : CPoly) := by
    funext i
    unfold deployedConstraintPieceCoordinates
    rw [onlinePointCoordinates_zeroSource basis hsource]
    show coeffsToPoly (fun _ => (0 : Fp)) = 0
    rw [coeffsToPoly]
    simp
  have hps : (deployedRootRunOutput (zeroDeployedRootFamily vkS hfixed hperm) basis
      coins).1.proof.1 = zeroProofString shape Fp VestaG := by
    show ((wrappedAdversary (zeroOnlineMemberFamily vkS hfixed hperm).toFamily basis).run
      coins).1.proof.1 = _
    rw [zeroFamily_wrapped_run basis vkS hfixed hperm coins]
    rfl
  simp only [deployedConstraintDifferencePreX, zeroExplicitConstraintDifference]
  rw [hpoint, hpieces, hps]
  rfl

/-- The explicit difference reads only the four folding challenges. -/
theorem zeroExplicitConstraintDifference_reads (ν ν' : Fin 11 → Fp)
    (h0 : ν 0 = ν' 0) (h1 : ν 1 = ν' 1) (h2 : ν 2 = ν' 2) (h3 : ν 3 = ν' 3) :
    zeroExplicitConstraintDifference vkS ν = zeroExplicitConstraintDifference vkS ν' := by
  unfold zeroExplicitConstraintDifference committedPreXConstraintDifference
  simp only [chRecord]
  rw [h0, h1, h2, h3]

/-- The constraint-`x` stage at any shape: read the four folding squeezes and return the explicit
difference's root set.  The `x` prefix — index `4` — is never queried. -/
def zeroConstConstraintXStage (basis : AugmentedIndex (2 ^ shape.k) → VestaG) :
    OracleComp
      (BTranscript Fp VestaG
        (preIpaLen shape (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init.length 10 +
          3 * shape.k)) Fp (Set Fp) :=
  (OracleComp.readFin (F := Fp)
    (fun i : Fin 4 =>
      algebraicFullPrefixesPre (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init
        (zeroWfProof basis vkS hfixed hperm) (i.castLE (by omega)))).bind
    fun ν₄ => .pure ↑(szBadSet (zeroExplicitConstraintDifference vkS
      (fun i => if h : (i : ℕ) < 4 then ν₄ ⟨i, h⟩ else 0)))

/-- The staged set is the run's actual total bad set. -/
theorem zeroConstConstraintXStage_agrees (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init.length 10 +
        3 * shape.k) → Fp) :
    (zeroConstConstraintXStage vkS hfixed hperm basis).run O =
      deployedConstraintXBadSet (zeroDeployedRootFamily vkS hfixed hperm) basis O := by
  rw [zeroConstConstraintXStage, OracleComp.run_bind, OracleComp.run_readFin,
    OracleComp.run_pure]
  ext x
  simp only [deployedConstraintXBadSet]
  constructor
  · intro hx
    rw [zeroConstraintDifference_explicit vkS hfixed hperm basis]
    rw [zeroExplicitConstraintDifference_reads vkS
      (fun i => wrappedPreIpaReads (deployedRootRunOutput
        (zeroDeployedRootFamily vkS hfixed hperm) basis O) i)
      (fun i => if h : (i : ℕ) < 4 then O (algebraicFullPrefixesPre
        (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init
        (zeroWfProof basis vkS hfixed hperm) ((⟨i, h⟩ : Fin 4).castLE (by omega))) else 0)]
    · exact hx
    all_goals
      exact congrFun (zeroFamily_reads_eq basis vkS hfixed hperm O) _
  · intro hx
    rw [zeroConstraintDifference_explicit vkS hfixed hperm basis] at hx
    rw [zeroExplicitConstraintDifference_reads vkS
      (fun i => if h : (i : ℕ) < 4 then O (algebraicFullPrefixesPre
        (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init
        (zeroWfProof basis vkS hfixed hperm) ((⟨i, h⟩ : Fin 4).castLE (by omega))) else 0)
      (fun i => wrappedPreIpaReads (deployedRootRunOutput
        (zeroDeployedRootFamily vkS hfixed hperm) basis O) i)]
    · exact hx
    all_goals
      exact (congrFun (zeroFamily_reads_eq basis vkS hfixed hperm O) _).symm

/-- The stage queries only the four folding prefixes, never the `x` prefix. -/
theorem zeroConstConstraintXStage_fresh (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (O : BTranscript Fp VestaG
      (preIpaLen shape (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init.length 10 +
        3 * shape.k) → Fp) :
    algebraicFullPrefixesPre (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init
        (((zeroDeployedRootFamily vkS hfixed hperm).toFamily.adversary basis).run O) 4 ∉
      (zeroConstConstraintXStage vkS hfixed hperm basis).queries O := by
  have hpoint : algebraicFullPrefixesPre (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init
      (((zeroDeployedRootFamily vkS hfixed hperm).toFamily.adversary basis).run O) 4 =
      algebraicFullPrefixesPre (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init
        (zeroWfProof basis vkS hfixed hperm) 4 := rfl
  rw [hpoint]
  simp only [zeroConstConstraintXStage, OracleComp.queries_bind, OracleComp.queries_readFin,
    OracleComp.queries, List.append_nil]
  intro hmem
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
  exact zeroFamily_prefixesPre_injective basis vkS hfixed hperm
    (by exact Fin.ne_of_val_ne (by have := i.isLt; simp; omega)) hi

/-- **The zero family's constraint-`x` trace at any shape** (issue #127 C10): the total event
needs no decode, so the stage prices the explicit zero-data difference with sub-proofs live. -/
def zeroConstConstraintXTrace :
    DeployedConstraintXOnlineTrace (zeroDeployedRootFamily vkS hfixed hperm) where
  stage := fun basis => zeroConstConstraintXStage vkS hfixed hperm basis
  agrees := fun basis O => zeroConstConstraintXStage_agrees vkS hfixed hperm basis O
  fresh := fun basis O => zeroConstConstraintXStage_fresh vkS hfixed hperm basis O

end ConstraintX

section IpaTrace

variable (vkS : VerifyingKey shape Fp VestaG)
  (hfixed : ∀ i, vkS.fixedCommitment i = 0)
  (hperm : ∀ i, vkS.permutationCommonCommitment i = 0)

/-- Every straight-line IPA round polynomial of the zero prover is the zero polynomial, at every
round of every `k`.  The walk starts at zero because an instance-free zero proof claims only zero
evaluations, so its multiopen value vanishes. -/
theorem zeroWfProof_straightLineIpaRootPolynomial (hproofs : shape.numProofs = 0)
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (ν : Fin 11 → Fp) (χ : Fin shape.k → Fp) (j : Fin shape.k) :
    (zeroWfProof basis vkS hfixed hperm).straightLineIpaRootPolynomial ν χ j = 0 := by
  refine straightLineIpaRootPolynomial_of_zero_coordinates _ ν χ
    (zeroWfProof_aMulti basis vkS hfixed hperm ν)
    (zeroWfProof_multiU basis vkS hfixed hperm ν)
    (zeroWfProof_s basis vkS hfixed hperm)
    (zeroWfProof_sU basis vkS hfixed hperm) ?_ ?_ j
  · show multiopenValue vkS (fun _ _ => 0) (zeroProofString shape Fp VestaG)
      (chRecord ν (fun _ => 0)) = 0
    exact multiopenValue_zeroProofString hproofs vkS (fun _ _ => 0) _
  · intro r
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- **The zero family's staged IPA trace.**  The staged polynomial is zero at every one of the
shape's `k` rounds, so `agrees` is a theorem about the discrepancy walk rather than an empty
quantification. -/
def zeroStraightLineIpaTrace (hproofs : shape.numProofs = 0) :
    StraightLineIpaOnlineTrace (zeroDeployedRootFamily vkS hfixed hperm).toFamily where
  stage := fun _basis _j => .pure 0
  agrees := fun basis j O => by
    rw [OracleComp.run_pure]
    show (0 : CPoly) = _
    rw [show ((zeroDeployedRootFamily vkS hfixed hperm).toFamily.adversary basis).run O =
      zeroWfProof basis vkS hfixed hperm from rfl]
    exact (zeroWfProof_straightLineIpaRootPolynomial vkS hfixed hperm hproofs basis _ _ j).symm
  fresh := fun _basis _j _O => List.not_mem_nil

/-- **An inhabitant of the straight-line deployed family interface with live IPA rounds**: the
zero prover's root family, its empty constraint-`x` stage, and the staged IPA trace over all `k`
rounds. -/
def zeroStraightLineDeployedFamily (hproofs : shape.numProofs = 0) :
    ComputedStraightLineDeployedFSFamily shape where
  toComputedDeployedRootFSFamily := zeroDeployedRootFamily vkS hfixed hperm
  ipaTrace := zeroStraightLineIpaTrace vkS hfixed hperm hproofs
  constraintXTrace := zeroConstraintXTrace vkS hfixed hperm hproofs

/-! ### The constant walk, without the instance-free hypothesis

With sub-proofs the zero prover's multiopen value `v` survives, and its walk is the constant
`c = -(ν₁₀ · v)`: every staged IPA polynomial is `C c * X`.  The trace below carries that walk at
any shape — the remaining instance-bearing obligation is the constraint-`x` stage, not the IPA
rounds.
-/

/-- Every straight-line IPA root polynomial of the zero prover is `C (-(ν₁₀ · v)) * X`, `v` the
zero proof's multiopen value.  No instance-free hypothesis: at `numProofs = 0` the constant
vanishes and this reduces to the zero walk. -/
theorem zeroWfProof_straightLineIpaRootPolynomial_const
    (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (ν : Fin 11 → Fp) (χ : Fin shape.k → Fp) (j : Fin shape.k) :
    (zeroWfProof basis vkS hfixed hperm).straightLineIpaRootPolynomial ν χ j =
      C (-(ν 10 * multiopenValue vkS (fun _ _ => 0)
        (zeroProofString shape Fp VestaG) (chRecord ν (fun _ => 0)))) * X := by
  rw [straightLineIpaRootPolynomial_of_zero_group_coordinates _ ν χ
    (fun _ => ⟨rfl, rfl, rfl, rfl⟩) j]
  rw [straightLineInitialDiscrepancy_of_zero_coordinates _ ν
    (zeroWfProof_aMulti basis vkS hfixed hperm ν)
    (zeroWfProof_multiU basis vkS hfixed hperm ν)
    (zeroWfProof_s basis vkS hfixed hperm)
    (zeroWfProof_sU basis vkS hfixed hperm)]
  have hps : (zeroWfProof basis vkS hfixed hperm).proof.1 =
      zeroProofString shape Fp VestaG := rfl
  rw [hps]

/-- The constant-walk staged polynomial: read the eleven pre-IPA squeezes, then return
`C (-(ν₁₀ · v)) * X`.  No IPA-round point is read. -/
def zeroConstIpaStage (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (_j : Fin shape.k) :
    OracleComp
      (BTranscript Fp VestaG
        (preIpaLen shape (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init.length 10 +
          3 * shape.k)) Fp (CPoly) :=
  (OracleComp.readFin (F := Fp)
    (fun i : Fin 11 =>
      algebraicFullPrefixesPre (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init
        (zeroWfProof basis vkS hfixed hperm) i)).bind
    fun ν => .pure (C (-(ν 10 * multiopenValue vkS (fun _ _ => 0)
      (zeroProofString shape Fp VestaG) (chRecord ν (fun _ => 0)))) * X)

/-- The staged polynomial is the run's actual root polynomial: both are the constant walk at the
oracle's answers on the fixed squeeze points. -/
theorem zeroConstIpaStage_agrees (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (j : Fin shape.k)
    (O : BTranscript Fp VestaG
      (preIpaLen shape (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init.length 10 +
        3 * shape.k) → Fp) :
    (zeroConstIpaStage vkS hfixed hperm basis j).run O =
      AlgebraicWfProof.straightLineIpaRootPolynomial
        (((zeroDeployedRootFamily vkS hfixed hperm).toFamily.adversary basis).run O)
        (fun i => O (algebraicFullPrefixesPre
          (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init
          (((zeroDeployedRootFamily vkS hfixed hperm).toFamily.adversary basis).run O) i))
        (fun r => O (algebraicFullPrefixes
          (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init
          (((zeroDeployedRootFamily vkS hfixed hperm).toFamily.adversary basis).run O) r))
        j := by
  rw [zeroConstIpaStage, OracleComp.run_bind, OracleComp.run_readFin, OracleComp.run_pure]
  rw [show (((zeroDeployedRootFamily vkS hfixed hperm).toFamily.adversary basis).run O) =
    zeroWfProof basis vkS hfixed hperm from rfl]
  show _ = AlgebraicWfProof.straightLineIpaRootPolynomial
    (vk := vkS) (instanceCommitment := fun _ _ => 0)
    (zeroWfProof basis vkS hfixed hperm) _ _ j
  exact (zeroWfProof_straightLineIpaRootPolynomial_const vkS hfixed hperm basis
    (fun i => O (algebraicFullPrefixesPre
      (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init
      (zeroWfProof basis vkS hfixed hperm) i))
    (fun r => O (algebraicFullPrefixes
      (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init
      (zeroWfProof basis vkS hfixed hperm) r)) j).symm

/-- The stage reads only pre-IPA squeeze points, which are strictly shorter than any IPA round
prefix. -/
theorem zeroConstIpaStage_fresh (basis : AugmentedIndex (2 ^ shape.k) → VestaG)
    (j : Fin shape.k)
    (O : BTranscript Fp VestaG
      (preIpaLen shape (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init.length 10 +
        3 * shape.k) → Fp) :
    straightLineIpaRootPoint (zeroDeployedRootFamily vkS hfixed hperm).toFamily
        (((zeroDeployedRootFamily vkS hfixed hperm).toFamily.adversary basis).run O) j ∉
      (zeroConstIpaStage vkS hfixed hperm basis j).queries O := by
  have hpoint : straightLineIpaRootPoint (zeroDeployedRootFamily vkS hfixed hperm).toFamily
      (((zeroDeployedRootFamily vkS hfixed hperm).toFamily.adversary basis).run O) j =
      algebraicFullPrefixes (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init
        (zeroWfProof basis vkS hfixed hperm) j := rfl
  rw [hpoint]
  simp only [zeroConstIpaStage, OracleComp.queries_bind, OracleComp.queries_readFin,
    OracleComp.queries, List.append_nil]
  intro hmem
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hmem
  have hlen := congrArg (fun t : BTranscript Fp VestaG _ => t.val.length) hi
  simp only [algebraicFullPrefixesPre, algebraicFullPrefixes,
    fullPrefixesPre, fullPrefixes, roundTranscriptFin_length] at hlen
  have hle := preIpaSqueezePoints_length_le
    (zeroDeployedRootFamily vkS hfixed hperm).toFamily.init
    (zeroWfProof basis vkS hfixed hperm).proof.1 i
  omega

/-- **The constant-walk staged IPA trace, at any shape.**  The instance-free zero trace above is
its special case; this one leaves the multiopen value free. -/
def zeroConstStraightLineIpaTrace :
    StraightLineIpaOnlineTrace (zeroDeployedRootFamily vkS hfixed hperm).toFamily where
  stage := fun basis j => zeroConstIpaStage vkS hfixed hperm basis j
  agrees := fun basis j O => zeroConstIpaStage_agrees vkS hfixed hperm basis j O
  fresh := fun basis j O => zeroConstIpaStage_fresh vkS hfixed hperm basis j O

/-- The zero family also inhabits the intermediate deployed constraint interface. -/
def zeroDeployedConstraintFamily (hproofs : shape.numProofs = 0) :
    ComputedDeployedConstraintFSFamily shape :=
  .ofRoot (zeroDeployedRootFamily vkS hfixed hperm) (zeroConstraintXTrace vkS hfixed hperm hproofs)

/-- **The zero prover inhabits the full straight-line interface at any shape** (issue #127 C10):
the six root events, the constant-walk IPA trace, and the total constraint-`x` stage, with no
instance-free hypothesis.  This is the interface smoke test — it is not the deployed Action
adversary. -/
def zeroConstStraightLineDeployedFamily :
    ComputedStraightLineDeployedFSFamily shape where
  toComputedDeployedRootFSFamily := zeroDeployedRootFamily vkS hfixed hperm
  ipaTrace := zeroConstStraightLineIpaTrace vkS hfixed hperm
  constraintXTrace := zeroConstConstraintXTrace vkS hfixed hperm

end IpaTrace

end Zcash.Snark
