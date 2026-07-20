import Zcash.Snark.Soundness.Forking.Adaptive

/-!
# The unbounded oracle domain reduces to finite subdomains

The deployed capstones price adversaries over a finite, length-bounded transcript domain. A real
adversary may hash transcripts of *arbitrary* length — an infinite query domain over which no
uniform table measure exists. This module closes that model boundary by reduction:

* a `Q`-bounded machine can only ever reach finitely many query points, over all tables
  (`OracleComp.reachSet`), and its run depends on the table only there
  (`OracleComp.run_congr_reachSet`);
* the game points of its attainable outputs likewise form a finite set (`gamePoints`), because
  attainable outputs are runs over the finitely many reach-set assignments;
* therefore every bounded-query adversary over an arbitrary — possibly infinite — domain factors,
  table by table, through a `Q`-bounded adversary over a finite subdomain with the same wins
  (`finite_domain_restriction`);
* and the finite game is *canonical*: embedding it into any larger finite domain leaves the
  uniform win probability exactly unchanged (`fsWinsFull_mapDomain_measure_eq`), because the win
  event is a cylinder over the small domain's coordinates.

Composed with `fsWinsFull_restrictSum_le` (junk domains add no power at the same query budget),
this grounds the deployed bounded-domain capstones against adversaries hashing arbitrary
transcripts: restrict along `finite_domain_restriction`, split the finite domain into the deployed
transcript points and the junk remainder, and price the junk by restriction. The only semantics
this fixes for the infinite domain is the lazy one — answers at the finitely many points the
machine can actually reach — which is exactly the random-oracle reading.
-/

namespace Zcash.Snark

namespace OracleComp

variable {T T' F α : Type*}

/-- Reindex a machine's query points. -/
def mapDomain (f : T → T') : OracleComp T F α → OracleComp T' F α
  | .pure a => .pure a
  | .query t k => .query (f t) fun u => (k u).mapDomain f

@[simp] theorem run_mapDomain (f : T → T') :
    (A : OracleComp T F α) → (O : T' → F) → (A.mapDomain f).run O = A.run (O ∘ f)
  | .pure _, _ => rfl
  | .query t k, O => run_mapDomain f (k (O (f t))) O

theorem queryBound_mapDomain (f : T → T') {A : OracleComp T F α} {Q : ℕ}
    (h : A.QueryBound Q) : (A.mapDomain f).QueryBound Q := by
  induction h with
  | pure a Q => exact .pure a Q
  | query hk ih => exact .query fun u => ih u

variable [DecidableEq T] [Fintype F]

/-- The finite set of points a machine can ever query, over all tables. -/
def reachSet : OracleComp T F α → Finset T
  | .pure _ => ∅
  | .query t k => insert t (Finset.univ.biUnion fun u : F => (k u).reachSet)

theorem mem_reachSet_query_self (t : T) (k : F → OracleComp T F α) :
    t ∈ (query t k).reachSet :=
  Finset.mem_insert_self t _

theorem reachSet_query_subset (t : T) (k : F → OracleComp T F α) (u : F) :
    (k u).reachSet ⊆ (query t k).reachSet := fun x hx =>
  Finset.subset_insert t _
    (Finset.subset_biUnion_of_mem (fun v : F => (k v).reachSet) (Finset.mem_univ u) hx)

/-- **Run locality.** The run depends on the table only at the reachable points. -/
theorem run_congr_reachSet : (A : OracleComp T F α) → {O O' : T → F} →
    (∀ t ∈ A.reachSet, O t = O' t) → A.run O = A.run O'
  | .pure _, _, _, _ => rfl
  | .query t k, O, O', h => by
      have ht : O t = O' t := h t (mem_reachSet_query_self t k)
      simp only [run_query, ht]
      exact run_congr_reachSet (k (O' t))
        (fun x hx => h x (reachSet_query_subset t k (O' t) hx))

/-- Restrict a machine to a finite subdomain containing its reachable points. -/
def restrictTo (S : Finset T) : (A : OracleComp T F α) → A.reachSet ⊆ S →
    OracleComp {t // t ∈ S} F α
  | .pure a, _ => .pure a
  | .query t k, h =>
      .query ⟨t, h (mem_reachSet_query_self t k)⟩ fun u =>
        (k u).restrictTo S (fun x hx => h (reachSet_query_subset t k u hx))

/-- The restriction reproduces the run against any table agreeing on the subdomain. -/
theorem run_restrictTo (S : Finset T) :
    (A : OracleComp T F α) → (h : A.reachSet ⊆ S) → (O : {t // t ∈ S} → F) → (Ō : T → F) →
    (∀ (t : T) (ht : t ∈ S), Ō t = O ⟨t, ht⟩) →
    (A.restrictTo S h).run O = A.run Ō
  | .pure _, _, _, _, _ => rfl
  | .query t k, h, O, Ō, hagree => by
      simp only [restrictTo, run_query]
      rw [show O ⟨t, h (mem_reachSet_query_self t k)⟩ = Ō t from
        (hagree t (h (mem_reachSet_query_self t k))).symm]
      exact run_restrictTo S (k (Ō t)) _ O Ō hagree

/-- Restriction never adds queries. -/
theorem queryBound_restrictTo (S : Finset T) {A : OracleComp T F α} {Q : ℕ}
    (hQ : A.QueryBound Q) : ∀ h : A.reachSet ⊆ S, (A.restrictTo S h).QueryBound Q := by
  induction hQ with
  | pure a Q => intro h; exact .pure a Q
  | query hk ih => intro h; exact .query fun u => ih u _

end OracleComp

section GamePoints

variable {T F α : Type*} [DecidableEq T] [Fintype F]

/-- Extend a subdomain assignment to a full table with a fixed junk value. -/
def extendOn (S : Finset T) (assign : {t // t ∈ S} → F) (f₀ : F) : T → F :=
  fun t => if h : t ∈ S then assign ⟨t, h⟩ else f₀

open Classical in
/-- The finite set of game points of a machine's attainable outputs: attainable outputs are runs
over the finitely many reach-set assignments. -/
noncomputable def gamePoints {n : ℕ} (A : OracleComp T F α) (pts : α → Fin n → T)
    (f₀ : F) : Finset T :=
  Finset.univ.biUnion fun assign : {t // t ∈ A.reachSet} → F =>
    Finset.univ.image fun j : Fin n => pts (A.run (extendOn A.reachSet assign f₀)) j

open Classical in
/-- Every run's game points land in the finite game-point set: the run agrees with the run over
its own reach-set assignment. -/
theorem pts_run_mem_gamePoints {n : ℕ} (A : OracleComp T F α) (pts : α → Fin n → T)
    (f₀ : F) (O : T → F) (j : Fin n) :
    pts (A.run O) j ∈ gamePoints A pts f₀ := by
  have hagree : ∀ t ∈ A.reachSet, O t = extendOn A.reachSet (fun t' => O t'.1) f₀ t := by
    intro t ht
    rw [extendOn, dif_pos ht]
  rw [show A.run O = A.run (extendOn A.reachSet (fun t' => O t'.1) f₀) from
    OracleComp.run_congr_reachSet A hagree]
  exact Finset.mem_biUnion.mpr ⟨fun t' => O t'.1, Finset.mem_univ _,
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩

end GamePoints

section Reduction

variable {T F P : Type*} [DecidableEq T] [Fintype F] [Nonempty F]

open Classical in
/-- **The finite-domain reduction.** A bounded-query adversary over an arbitrary — possibly
infinite — oracle domain factors through a finite subdomain: there is an equally-bounded machine
over a finite point set, with game points inside it, whose full-record win agrees with the
original's on every table. The infinite-domain game therefore has lazy semantics by construction:
only the finitely many reachable answers and attainable game points ever matter. -/
theorem finite_domain_restriction {m k : ℕ} (hm : 0 < m)
    (A : OracleComp T F P) {Q : ℕ} (hQ : A.QueryBound Q)
    (accept : P → (Fin m → F) → (Fin k → F) → Prop)
    (prefixesPre : P → Fin m → T) (prefixes : P → Fin k → T) :
    ∃ (S : Finset T) (A₀ : OracleComp {t // t ∈ S} F P)
      (preS : P → Fin m → {t // t ∈ S}) (ptsS : P → Fin k → {t // t ∈ S}),
      A₀.QueryBound Q ∧
      ∀ O : T → F,
        fsWinsFull A accept prefixesPre prefixes O
          ↔ fsWinsFull A₀ accept preS ptsS (fun t => O t.1) := by
  classical
  obtain ⟨f₀⟩ := ‹Nonempty F›
  set S : Finset T := A.reachSet ∪ gamePoints A prefixesPre f₀ ∪ gamePoints A prefixes f₀
    with hSdef
  have hreach : A.reachSet ⊆ S := fun x hx =>
    Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hpreS : ∀ (O : T → F) (i : Fin m), prefixesPre (A.run O) i ∈ S := fun O i =>
    Finset.mem_union_left _ (Finset.mem_union_right _
      (pts_run_mem_gamePoints A prefixesPre f₀ O i))
  have hptsS : ∀ (O : T → F) (j : Fin k), prefixes (A.run O) j ∈ S := fun O j =>
    Finset.mem_union_right _ (pts_run_mem_gamePoints A prefixes f₀ O j)
  have hd : prefixesPre (A.run (fun _ => f₀)) ⟨0, hm⟩ ∈ S := hpreS (fun _ => f₀) ⟨0, hm⟩
  set d : {t // t ∈ S} := ⟨prefixesPre (A.run (fun _ => f₀)) ⟨0, hm⟩, hd⟩ with hddef
  refine ⟨S, A.restrictTo S hreach,
    (fun p i => if h : prefixesPre p i ∈ S then ⟨prefixesPre p i, h⟩ else d),
    (fun p j => if h : prefixes p j ∈ S then ⟨prefixes p j, h⟩ else d),
    OracleComp.queryBound_restrictTo S hQ hreach, ?_⟩
  intro O
  have hrun : (A.restrictTo S hreach).run (fun t => O t.1) = A.run O :=
    OracleComp.run_restrictTo S A hreach (fun t => O t.1) O (fun t ht => rfl)
  rw [fsWinsFull, fsWinsFull, hrun]
  have h1 : (fun i => (fun t : {t // t ∈ S} => O t.1)
        ((fun p i => if h : prefixesPre p i ∈ S then
          (⟨prefixesPre p i, h⟩ : {t // t ∈ S}) else d) (A.run O) i))
      = fun i => O (prefixesPre (A.run O) i) := by
    funext i
    beta_reduce
    rw [dif_pos (hpreS O i)]
  have h2 : (fun j => (fun t : {t // t ∈ S} => O t.1)
        ((fun p j => if h : prefixes p j ∈ S then
          (⟨prefixes p j, h⟩ : {t // t ∈ S}) else d) (A.run O) j))
      = fun j => O (prefixes (A.run O) j) := by
    funext j
    beta_reduce
    rw [dif_pos (hptsS O j)]
  rw [h1, h2]

open Classical in
/-- **Finite games are canonical under domain enlargement.** Embedding a finite-domain adversary
and its game points into any larger split domain leaves the uniform win probability exactly
unchanged: the win event is a cylinder over the small domain's coordinates, and the junk
coordinates integrate out. Together with `finite_domain_restriction` this identifies the
infinite-domain game with the deployed bounded-domain game, independent of the chosen finite
subdomain. -/
theorem fsWinsFull_mapDomain_measure_eq {T₀ J : Type*} [Fintype T₀] [DecidableEq T₀]
    [Fintype J] [DecidableEq J] {m k : ℕ}
    (A : OracleComp T₀ F P) (accept : P → (Fin m → F) → (Fin k → F) → Prop)
    (prefixesPre : P → Fin m → T₀) (prefixes : P → Fin k → T₀) :
    (PMF.uniformOfFintype ((T₀ ⊕ J) → F)).toOuterMeasure
        {O' : (T₀ ⊕ J) → F | fsWinsFull (A.mapDomain Sum.inl) accept
          (fun p i => Sum.inl (prefixesPre p i)) (fun p j => Sum.inl (prefixes p j)) O'}
      = (PMF.uniformOfFintype (T₀ → F)).toOuterMeasure
          {O : T₀ → F | fsWinsFull A accept prefixesPre prefixes O} := by
  have hset : {O' : (T₀ ⊕ J) → F | fsWinsFull (A.mapDomain Sum.inl) accept
        (fun p i => Sum.inl (prefixesPre p i)) (fun p j => Sum.inl (prefixes p j)) O'}
      = (fun O' : (T₀ ⊕ J) → F => O' ∘ Sum.inl) ⁻¹'
          {O : T₀ → F | fsWinsFull A accept prefixesPre prefixes O} := by
    ext O'
    simp only [Set.mem_preimage, Set.mem_setOf_eq, fsWinsFull, OracleComp.run_mapDomain]
    exact Iff.rfl
  rw [hset, ← PMF.toOuterMeasure_map_apply,
    uniformOfFintype_map_precomp_injective Sum.inl Sum.inl_injective]

end Reduction

end Zcash.Snark
