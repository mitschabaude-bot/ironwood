import Zcash.Snark.Soundness.Forking.Rewind

/-!
# The oracle-querying Fiat–Shamir adversary

This module models a `Q`-query adversary as an adaptive query tree, following VCVio's eager
`OracleComp` semantics (https://eprint.iacr.org/2024/1819). `fsAdvantage` measures acceptance when
the adversary and verifier read the same uniformly sampled oracle table.

## Proof route

1. Query histories support replay, deduplication, and one-point reprogramming.
2. `escapesDuringC_measure_le'` bounds adaptive queries into blind escape sets.
3. `AdSched.map_read_uniform` and `schedule_fork_bound` prove the staged and single-fork cases.
4. `Forking.Adversary.Recursive` constructs the deployed fork certificate;
   `Forking.Adversary.Algebraic` packages it for the AGM reduction.

## Why the loss uses escape sets

A grinding adversary may choose its proof after seeing oracle answers, so its advantage is not
bounded by `(Q + 1)` times the worst fixed-output acceptance probability. The proof instead charges
each query for entering a blind escape set. A prefix does not determine the later proof points, so
`StagedDecode` applies only to staged strategies. The recursive extractor instead preserves the
operational state of arbitrary querying adversaries, matching the state-restoration boundary of
Attema–Fehr–Klooß (https://eprint.iacr.org/2021/1377).

The `legacy_*` definitions below retain the propositional staged path. The deployed path computes
certificate data in `Forking.Adversary.Recursive`.
-/

namespace Zcash.Snark

open scoped ENNReal

/-- An adaptive computation with one oracle `T → F`: either a result or a query whose continuation
receives the answer. -/
inductive OracleComp (T F α : Type*) where
  | pure (a : α)
  | query (t : T) (k : F → OracleComp T F α)

namespace OracleComp

variable {T F α : Type*}

/-- Run the machine against an oracle table `O`, answering each query by lookup (the eager/whole-table
semantics: drawing `O` uniformly makes every fresh answer uniform). -/
def run : OracleComp T F α → (T → F) → α
  | .pure a, _ => a
  | .query t k, O => (k (O t)).run O

@[simp] theorem run_pure (a : α) (O : T → F) : (pure a : OracleComp T F α).run O = a := rfl

@[simp] theorem run_query (t : T) (k : F → OracleComp T F α) (O : T → F) :
    (query t k).run O = (k (O t)).run O := rfl

/-- The query log of a run: the points the machine asks, in order, on the path the table induces. -/
def queries : OracleComp T F α → (T → F) → List T
  | .pure _, _ => []
  | .query t k, O => t :: (k (O t)).queries O

/-- The machine makes at most `Q` queries on every path (VCVio's structural `IsQueryBound`). The
forking reduction charges its query loss against this `Q`. -/
inductive QueryBound : OracleComp T F α → ℕ → Prop
  | pure (a : α) (Q : ℕ) : QueryBound (.pure a) Q
  | query {t : T} {k : F → OracleComp T F α} {Q : ℕ}
      (h : ∀ u, QueryBound (k u) Q) : QueryBound (.query t k) (Q + 1)

/-- A query bound is monotone: a machine within budget `Q` is within any larger budget. -/
theorem QueryBound.mono {A : OracleComp T F α} {Q Q' : ℕ} (h : QueryBound A Q) (hle : Q ≤ Q') :
    QueryBound A Q' := by
  induction h generalizing Q' with
  | pure a _ => exact .pure a Q'
  | query _ ih =>
      obtain ⟨Q'', rfl⟩ : ∃ Q'', Q' = Q'' + 1 := ⟨Q' - 1, by omega⟩
      exact .query fun u => ih u (by omega)

/-- A `Q`-bounded machine's query log has length at most `Q`, on every table. -/
theorem queries_length_le {A : OracleComp T F α} {Q : ℕ} (h : QueryBound A Q) (O : T → F) :
    (A.queries O).length ≤ Q := by
  induction h with
  | pure => exact Nat.zero_le _
  | query h ih => simpa [queries] using Nat.succ_le_succ (ih _)

/-- The query–answer history of a run: the points asked with the answers received, in order. The
rewinding layer's central object — a fork is two tables sharing a history prefix and diverging at
its end. -/
def history : OracleComp T F α → (T → F) → List (T × F)
  | .pure _, _ => []
  | .query t k, O => (t, O t) :: (k (O t)).history O

@[simp] theorem history_pure (a : α) (O : T → F) :
    (pure a : OracleComp T F α).history O = [] := rfl

@[simp] theorem history_query (t : T) (k : F → OracleComp T F α) (O : T → F) :
    (query t k).history O = (t, O t) :: (k (O t)).history O := rfl

/-- The query log is the history's points. -/
theorem queries_eq_map_fst_history (A : OracleComp T F α) (O : T → F) :
    A.queries O = (A.history O).map Prod.fst := by
  induction A with
  | pure a => rfl
  | query t k ih => simp [queries, ih (O t)]

/-- Every recorded answer is the table's. -/
theorem history_mem_answer (A : OracleComp T F α) (O : T → F) :
    ∀ p ∈ A.history O, O p.1 = p.2 := by
  induction A with
  | pure a => intro p hp; simp at hp
  | query t k ih =>
      intro p hp
      rcases List.mem_cons.mp hp with hp | hp
      · subst hp; rfl
      · exact ih (O t) p hp

/-- **The replay lemma.** A table agreeing with the recorded answers of a run's first `i` steps
reproduces those steps: the machine is deterministic given its answers, so the fork of two tables
happens exactly where their answers first differ. -/
theorem history_take_replay (A : OracleComp T F α) (O O' : T → F) (i : ℕ)
    (h : ∀ p ∈ (A.history O).take i, O' p.1 = p.2) :
    (A.history O').take i = (A.history O).take i := by
  induction A generalizing i with
  | pure a => rfl
  | query t k ih =>
      cases i with
      | zero => rfl
      | succ j =>
          have ht : O' t = O t := h (t, O t) (by simp)
          simp only [history_query, List.take_succ_cons, ht]
          congr 1
          exact ih (O t) j fun p hp => h p (by simp [hp])

/-- **The history cylinder.** Realizing a run's first `i` steps is exactly agreeing with their
recorded answers — the event the conditioning layer prices, in the same override shape as
`applyUpdates`. -/
theorem history_take_eq_iff (A : OracleComp T F α) (O O' : T → F) (i : ℕ) :
    (A.history O').take i = (A.history O).take i
      ↔ ∀ p ∈ (A.history O).take i, O' p.1 = p.2 := by
  constructor
  · intro heq p hp
    rw [← heq] at hp
    exact history_mem_answer A O' p (List.mem_of_mem_take hp)
  · exact history_take_replay A O O' i

/-- Shared history determines the next query point: two runs agreeing on their first `i` steps ask
the same `i`-th question (the answers may then diverge — the fork). -/
theorem history_getElem_fst_congr (A : OracleComp T F α) (O O' : T → F) (i : ℕ)
    (h : (A.history O').take i = (A.history O).take i) :
    ((A.history O')[i]?).map Prod.fst = ((A.history O)[i]?).map Prod.fst := by
  induction A generalizing i with
  | pure a => rfl
  | query t k ih =>
      cases i with
      | zero => rfl
      | succ j =>
          simp only [history_query, List.take_succ_cons, List.cons.injEq] at h
          have ht : O' t = O t := congrArg Prod.snd h.1
          simp only [history_query, List.getElem?_cons_succ, ht]
          exact ih (O t) j (ht ▸ h.2)

/-- The run of the machine on table `O` makes an *escaping* query: some query's answer lands in
that point's escape set. The event the escape bound (`escapesDuring_measure_le`) prices at `ε`
per query. -/
def escapesDuring (esc : T → Set F) : OracleComp T F α → (T → F) → Prop
  | .pure _, _ => False
  | .query t k, O => O t ∈ esc t ∨ (k (O t)).escapesDuring esc O

/-- Conditional escape: some query's answer lands in that point's escape set, the set now chosen
by the whole table — the state-function shape, where a round's bad challenges depend on the
earlier ones (the oracle's answers at the sub-prefixes). Priced by
`escapesDuringC_measure_le'`. -/
def escapesDuringC (esc : T → (T → F) → Set F) : OracleComp T F α → (T → F) → Prop
  | .pure _, _ => False
  | .query t k, O => O t ∈ esc t O ∨ (k (O t)).escapesDuringC esc O

/-- The machine's queries avoid the cache and stay pairwise fresh below it: no point is queried
twice on any path. The shape `dedup` produces; the conditional escape bound inducts on it. -/
inductive AvoidsCache [DecidableEq T] : List (T × F) → OracleComp T F α → Prop
  | pure (c : List (T × F)) (a : α) : AvoidsCache c (.pure a)
  | query {c : List (T × F)} {t : T} {k : F → OracleComp T F α}
      (ht : t ∉ c.map Prod.fst) (h : ∀ u, AvoidsCache ((t, u) :: c) (k u)) :
      AvoidsCache c (.query t k)

/-- Deduplicate a machine's queries against a cache: cached points are answered from the cache,
fresh points are queried once and recorded. Never more queries, never a repeated one — the wlog
behind lifting the conditional escape bound to arbitrary machines. -/
def dedup [DecidableEq T] (c : List (T × F)) : OracleComp T F α → OracleComp T F α
  | .pure a => .pure a
  | .query t k =>
      match (c.find? (fun p => p.1 = t)) with
      | some p => dedup c (k p.2)
      | none => .query t (fun u => dedup ((t, u) :: c) (k u))

theorem dedup_avoidsCache [DecidableEq T] (c : List (T × F)) (A : OracleComp T F α) :
    AvoidsCache c (dedup c A) := by
  induction A generalizing c with
  | pure a => exact .pure c a
  | query t k ih =>
      rw [dedup]
      cases hfind : c.find? (fun p => p.1 = t) with
      | some p => exact ih p.2 c
      | none =>
          refine .query ?_ (fun u => ih u ((t, u) :: c))
          intro hmem
          obtain ⟨p, hp, hpt⟩ := List.mem_map.mp hmem
          have := List.find?_eq_none.mp hfind p hp
          simp [hpt] at this

theorem dedup_queryBound [DecidableEq T] {A : OracleComp T F α} {Q : ℕ}
    (h : A.QueryBound Q) (c : List (T × F)) : (dedup c A).QueryBound Q := by
  induction h generalizing c with
  | pure a Q => exact .pure a Q
  | @query t k Q hk ih =>
      rw [dedup]
      cases hfind : c.find? (fun p => p.1 = t) with
      | some p => exact (ih p.2 c).mono (Nat.le_succ Q)
      | none => exact .query (fun u => ih u ((t, u) :: c))

/-- An escape of the original machine is an escape of the deduplicated machine, provided the
cache is table-consistent and its recorded answers do not escape: the first query of the escaping
point survives deduplication with the same answer and the same (table-determined) escape set. -/
theorem escapesDuringC_dedup [DecidableEq T] (esc : T → (T → F) → Set F) {A : OracleComp T F α}
    {O : T → F} {c : List (T × F)}
    (hcon : ∀ p ∈ c, O p.1 = p.2) (hesc : ∀ p ∈ c, O p.1 ∉ esc p.1 O)
    (h : A.escapesDuringC esc O) : (dedup c A).escapesDuringC esc O := by
  induction A generalizing c with
  | pure a => exact h
  | query t k ih =>
      rw [dedup]
      cases hfind : c.find? (fun p => p.1 = t) with
      | some p =>
          have hp := List.find?_some hfind
          have hpmem := List.mem_of_find?_eq_some hfind
          have hpt : p.1 = t := by simpa using hp
          subst hpt
          have hval : O p.1 = p.2 := hcon p hpmem
          rcases h with h | h
          · exact absurd h (hesc p hpmem)
          · show (dedup c (k p.2)).escapesDuringC esc O
            rw [← hval]
            exact ih (O p.1) hcon hesc h
      | none =>
          by_cases hOt : O t ∈ esc t O
          · exact Or.inl hOt
          · rcases h with h | h
            · exact absurd h hOt
            · refine Or.inr (ih (O t) ?_ ?_ h)
              · intro p hp
                rcases List.mem_cons.mp hp with hp | hp
                · subst hp; rfl
                · exact hcon p hp
              · intro p hp
                rcases List.mem_cons.mp hp with hp | hp
                · subst hp; exact hOt
                · exact hesc p hp


variable {β : Type*}

/-- Sequence two machines: run the first, feed its result to the second. -/
def bind : OracleComp T F α → (α → OracleComp T F β) → OracleComp T F β
  | .pure a, f => f a
  | .query t k, f => .query t (fun u => (k u).bind f)

@[simp] theorem run_bind (A : OracleComp T F α) (f : α → OracleComp T F β) (O : T → F) :
    (A.bind f).run O = ((f (A.run O)).run O) := by
  induction A with
  | pure a => rfl
  | query t k ih => exact ih (O t)

/-- Query a list of points in order, ignoring the answers, and return `p`. -/
def queryList (p : α) : List T → OracleComp T F α
  | [] => .pure p
  | t :: ts => .query t (fun _ => queryList p ts)

@[simp] theorem run_queryList (p : α) (ts : List T) (O : T → F) :
    (queryList p ts).run O = p := by
  induction ts with
  | nil => rfl
  | cons t ts ih => exact ih

theorem queryBound_bind {A : OracleComp T F α} {f : α → OracleComp T F β} {Q Q' : ℕ}
    (hA : A.QueryBound Q) (hf : ∀ a, (f a).QueryBound Q') : (A.bind f).QueryBound (Q + Q') := by
  induction hA with
  | pure a Q => exact (hf a).mono (Nat.le_add_left _ _)
  | @query t k Q h ih =>
      have : (OracleComp.query t k).bind f = .query t (fun u => (k u).bind f) := rfl
      rw [this, Nat.succ_add]
      exact .query fun u => ih u

theorem queryBound_queryList (p : α) (ts : List T) :
    (queryList (F := F) p ts).QueryBound ts.length := by
  induction ts with
  | nil => exact .pure p 0
  | cons t ts ih => exact .query fun _ => ih

/-- An escape inside the second machine is an escape of the sequence. -/
theorem escapesDuringC_bind_right (esc : T → (T → F) → Set F) {A : OracleComp T F α}
    {f : α → OracleComp T F β} {O : T → F}
    (h : (f (A.run O)).escapesDuringC esc O) : (A.bind f).escapesDuringC esc O := by
  induction A with
  | pure a => exact h
  | query t k ih => exact Or.inr (ih (O t) h)

/-- An escaping answer at some listed point is an escape of the listing run. -/
theorem escapesDuringC_queryList (esc : T → (T → F) → Set F) (p : α) {ts : List T} {O : T → F}
    {t : T} (ht : t ∈ ts) (h : O t ∈ esc t O) : (queryList p ts).escapesDuringC esc O := by
  induction ts with
  | nil => exact absurd ht (List.not_mem_nil)
  | cons t' ts ih =>
      rcases List.mem_cons.mp ht with rfl | hmem
      · exact Or.inl h
      · exact Or.inr (ih hmem)

/-- Complete a machine against its own output: after computing it, query its `k` round prefixes
(ignoring the answers) and return it unchanged. The wlog step that makes every winning chain point
a queried point, so a ladder escape is an escaping query. -/
def completing {P : Type*} {k : ℕ} (prefixes : P → Fin k → T) (A : OracleComp T F P) :
    OracleComp T F P :=
  A.bind fun p => queryList p (List.ofFn (prefixes p))

@[simp] theorem run_completing {P : Type*} {k : ℕ} (prefixes : P → Fin k → T)
    (A : OracleComp T F P) (O : T → F) : (A.completing prefixes).run O = A.run O := by
  rw [completing, run_bind, run_queryList]

theorem queryBound_completing {P : Type*} {k : ℕ} (prefixes : P → Fin k → T)
    {A : OracleComp T F P} {Q : ℕ} (hA : A.QueryBound Q) :
    (A.completing prefixes).QueryBound (Q + k) := by
  refine queryBound_bind hA fun p => ?_
  have h := queryBound_queryList (F := F) p (List.ofFn (prefixes p))
  rwa [List.length_ofFn] at h

/-- An escaping answer at one of the output's own prefixes is an escape of the completed run. -/
theorem escapesDuringC_completing (esc : T → (T → F) → Set F) {P : Type*} {k : ℕ}
    (prefixes : P → Fin k → T) {A : OracleComp T F P} {O : T → F} {j : Fin k}
    (h : O (prefixes (A.run O) j) ∈ esc (prefixes (A.run O) j) O) :
    (A.completing prefixes).escapesDuringC esc O :=
  escapesDuringC_bind_right esc
    (escapesDuringC_queryList esc _ (by exact List.mem_ofFn.mpr ⟨j, rfl⟩) h)


/-- Fix the junk half of a split-domain oracle and retain only queries to the game domain. The query
budget is unchanged, and `fsWinsFull_restrictSum_le` recovers the original advantage by averaging
over independent uniform junk tables. -/
def restrictSum {J : Type*} (j : J → F) : OracleComp (T ⊕ J) F α → OracleComp T F α
  | .pure a => .pure a
  | .query (Sum.inl t) k => .query t (fun u => restrictSum j (k u))
  | .query (Sum.inr x) k => restrictSum j (k (j x))

/-- The restriction's run against `O` is the original run against `O` with the junk table glued
on. -/
theorem run_restrictSum {J : Type*} (j : J → F) :
    (A : OracleComp (T ⊕ J) F α) → (O : T → F) →
    (restrictSum j A).run O = A.run (Sum.elim O j)
  | .pure _, _ => rfl
  | .query (Sum.inl t) k, O => run_restrictSum j (k (O t)) O
  | .query (Sum.inr x) k, O => run_restrictSum j (k (j x)) O

/-- Restriction never adds queries: the junk answers are read from the fixed table for free. -/
theorem queryBound_restrictSum {J : Type*} {A : OracleComp (T ⊕ J) F α} {Q : ℕ}
    (h : A.QueryBound Q) (j : J → F) : (restrictSum j A).QueryBound Q := by
  induction h with
  | pure a Q => exact .pure a Q
  | @query t k Q hk ih =>
      cases t with
      | inl t => exact .query fun u => ih u
      | inr x => exact (ih (j x)).mono (Nat.le_succ Q)

/-- A cache-avoiding machine queries pairwise-distinct points along every run, and none of them is a
cached point: the structural distinctness (`Nodup`) that lets a reprogram at one query be replayed
without disturbing the others — the foundation of the rewinding fork. -/
theorem AvoidsCache.run_queries_nodup [DecidableEq T] :
    {c : List (T × F)} → {A : OracleComp T F α} → AvoidsCache c A → (O : T → F) →
    (A.queries O).Nodup ∧ ∀ p ∈ c, p.1 ∉ A.queries O
  | _, _, .pure c a, O => ⟨by simp [queries], by intro p _; simp [queries]⟩
  | c, _, .query (t := t) (k := k) ht h, O => by
      obtain ⟨hnd, hdis⟩ := (h (O t)).run_queries_nodup O
      have htnotin : t ∉ (k (O t)).queries O := hdis ⟨t, O t⟩ (List.mem_cons_self ..)
      refine ⟨?_, ?_⟩
      · rw [queries]
        exact List.nodup_cons.mpr ⟨htnotin, hnd⟩
      · intro p hp
        rw [queries, List.mem_cons]
        push_neg
        refine ⟨fun hpt => ?_, ?_⟩
        · exact absurd (hpt ▸ List.mem_map_of_mem (f := Prod.fst) hp) ht
        · exact hdis p (List.mem_cons_of_mem _ hp)

/-- **The reprogram-and-replay fork.** For a cache-avoiding machine, reprogramming the oracle at the
`i`-th query point of a run (via `Function.update`) replays the run identically through the first `i`
queries — their points are distinct from the forked one (`run_queries_nodup`), so `history_take_replay`
applies — and delivers the fresh answer `u` at query `i`. The rewinding primitive the forking lemma
iterates: fork a run at a chosen query, keeping the prefix fixed and resampling that one challenge. -/
theorem reprogram_replay_fork [DecidableEq T] {A : OracleComp T F α}
    (hac : A.AvoidsCache []) (O : T → F) {i : ℕ} (hi : i < (A.history O).length) (u : F) :
    ((A.history (Function.update O ((A.history O)[i].1) u)).take i = (A.history O).take i)
      ∧ (A.history (Function.update O ((A.history O)[i].1) u))[i]?
          = some ((A.history O)[i].1, u) := by
  set t := (A.history O)[i].1 with ht
  set O' := Function.update O t u with hO'
  have hnd : ((A.history O).map Prod.fst).Nodup := by
    have h := (hac.run_queries_nodup O).1
    rwa [queries_eq_map_fst_history] at h
  have hagree : ∀ p ∈ (A.history O).take i, O' p.1 = p.2 := by
    intro p hp
    obtain ⟨j, hj, hpj⟩ := List.getElem_of_mem hp
    rw [List.length_take] at hj
    have hji : j < i := lt_of_lt_of_le hj (min_le_left _ _)
    have hjlen : j < (A.history O).length := lt_of_lt_of_le hji hi.le
    have hpoint : p.1 = (A.history O)[j].1 := by
      rw [← hpj, List.getElem_take]
    have hne : p.1 ≠ t := by
      rw [hpoint, ht]
      intro heq
      have hmap : ((A.history O).map Prod.fst)[j]'(by rw [List.length_map]; exact hjlen)
          = ((A.history O).map Prod.fst)[i]'(by rw [List.length_map]; exact hi) := by
        rw [List.getElem_map, List.getElem_map]; exact heq
      exact absurd (hnd.getElem_inj_iff.mp hmap) (by omega)
    have hval : p.2 = O p.1 := (A.history_mem_answer O p (List.mem_of_mem_take hp)).symm
    rw [hO', Function.update_apply, if_neg hne, hval]
  have htake : (A.history O').take i = (A.history O).take i := A.history_take_replay O O' i hagree
  refine ⟨htake, ?_⟩
  have hpt : ((A.history O')[i]?).map Prod.fst = ((A.history O)[i]?).map Prod.fst :=
    A.history_getElem_fst_congr O O' i htake
  have hrhs : ((A.history O)[i]?).map Prod.fst = some t := by
    rw [List.getElem?_eq_getElem hi]; rfl
  rw [hrhs] at hpt
  obtain ⟨q, hq⟩ : ∃ q, (A.history O')[i]? = some q := by
    cases hc : (A.history O')[i]? with
    | none => rw [hc] at hpt; simp at hpt
    | some q => exact ⟨q, rfl⟩
  rw [hq] at hpt ⊢
  rw [Option.map_some] at hpt
  have hq1 : q.1 = t := Option.some.inj hpt
  have hqmem : q ∈ A.history O' := List.mem_of_getElem? hq
  have hans : O' q.1 = q.2 := A.history_mem_answer O' q hqmem
  rw [hq1, hO', Function.update_self] at hans
  rw [Option.some.injEq, Prod.ext_iff]
  exact ⟨hq1, hans.symm⟩


/-- The fork index of a run: the position in the query log where the output's fork point `fp` (its
round prefix) is first read. On a winning run the adversary must have queried that point to obtain
the challenge, so the index is `< Q` (`forkIdx_lt`). The index the local forking bound sums over. -/
def forkIdx [DecidableEq T] (A : OracleComp T F α) (fp : α → T) (O : T → F) : ℕ :=
  (A.queries O).idxOf (fp (A.run O))

theorem forkIdx_lt [DecidableEq T] {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q)
    (fp : α → T) {O : T → F} (hmem : fp (A.run O) ∈ A.queries O) :
    forkIdx A fp O < Q :=
  lt_of_lt_of_le (List.idxOf_lt_length_iff.mpr hmem) (A.queries_length_le hQ O)

/-- **Fork-index decomposition of the win set.** The winning tables partition by fork index into the
`Q` slices `{win ∧ forkIdx = i}` — every winning run queries its fork point, so its index is `< Q`.
The first step of the local forking bound: bound each slice, then sum. -/
theorem card_win_eq_sum_forkIdx [Fintype T] [DecidableEq T] [Fintype F] [DecidableEq F]
    {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q) (fp : α → T)
    (win : (T → F) → Prop) [DecidablePred win]
    (hquery : ∀ O, win O → fp (A.run O) ∈ A.queries O) :
    (Finset.univ.filter win).card
      = ∑ i ∈ Finset.range Q,
          (Finset.univ.filter (fun O => win O ∧ forkIdx A fp O = i)).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := fun O => forkIdx A fp O) (t := Finset.range Q) ?_]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.filter_filter]
  · intro O hO
    exact Finset.mem_range.mpr (forkIdx_lt hQ fp (hquery O (Finset.mem_filter.mp hO).2))

end OracleComp

/-! ## Overridden tables: the escape bound's conditioning record

The escape bound's induction conditions on each fresh answer in turn. The record of conditioned
answers is a list of point-value overrides applied over the free table — so the measure always
ranges over full uniform tables, and the induction hypothesis carries the overrides instead of a
shrinking table type. -/

variable {T F : Type*} [DecidableEq T]

/-- Apply a list of point-value overrides to a table, later entries winning. -/
def applyUpdates (σ : List (T × F)) (O : T → F) : T → F :=
  σ.foldl (fun g p => Function.update g p.1 p.2) O

@[simp] theorem applyUpdates_nil (O : T → F) : applyUpdates ([] : List (T × F)) O = O := rfl

theorem applyUpdates_cons (p : T × F) (σ : List (T × F)) (O : T → F) :
    applyUpdates (p :: σ) O = applyUpdates σ (Function.update O p.1 p.2) := rfl

theorem applyUpdates_append_single (σ : List (T × F)) (t : T) (u : F) (O : T → F) :
    applyUpdates (σ ++ [(t, u)]) O = Function.update (applyUpdates σ O) t u := by
  simp [applyUpdates, List.foldl_append]

/-- Off the override domain, the table shows through. -/
theorem applyUpdates_apply_not_mem {σ : List (T × F)} {t : T}
    (h : t ∉ σ.map Prod.fst) (O : T → F) : applyUpdates σ O t = O t := by
  induction σ generalizing O with
  | nil => rfl
  | cons p σ ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at h
      rw [applyUpdates_cons, ih h.2, Function.update_apply, if_neg h.1]

/-- On the override domain, the value is one of the recorded overrides at that point. -/
theorem applyUpdates_pair_mem {σ : List (T × F)} {t : T}
    (h : t ∈ σ.map Prod.fst) (O : T → F) : (t, applyUpdates σ O t) ∈ σ := by
  induction σ generalizing O with
  | nil => simp at h
  | cons p σ ih =>
      by_cases hmem : t ∈ σ.map Prod.fst
      · exact List.mem_cons_of_mem _ (ih hmem _)
      · simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · subst h
          rw [applyUpdates_cons, applyUpdates_apply_not_mem hmem, Function.update_self]
          exact List.mem_cons_self ..
        · exact absurd h hmem

/-- On the override domain, the value does not depend on the underlying table. -/
theorem applyUpdates_apply_of_mem {σ : List (T × F)} {t : T}
    (h : t ∈ σ.map Prod.fst) (O O' : T → F) : applyUpdates σ O t = applyUpdates σ O' t := by
  induction σ generalizing O O' with
  | nil => simp at h
  | cons p σ ih =>
      by_cases hmem : t ∈ σ.map Prod.fst
      · exact ih hmem _ _
      · simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · subst h
          rw [applyUpdates_cons, applyUpdates_cons, applyUpdates_apply_not_mem hmem,
            applyUpdates_apply_not_mem hmem, Function.update_self, Function.update_self]
        · exact absurd h hmem

/-- Off the override domain, overriding the underlying table commutes with the record. -/
theorem applyUpdates_update_not_mem {σ : List (T × F)} {t : T}
    (h : t ∉ σ.map Prod.fst) (O : T → F) (v : F) :
    applyUpdates σ (Function.update O t v) = Function.update (applyUpdates σ O) t v := by
  funext j
  by_cases hj : j = t
  · subst hj
    rw [applyUpdates_apply_not_mem h, Function.update_self, Function.update_self]
  · by_cases hdom : j ∈ σ.map Prod.fst
    · rw [Function.update_apply, if_neg hj, applyUpdates_apply_of_mem hdom]
    · simp [applyUpdates_apply_not_mem hdom, hj]

/-- Overriding the table at an already-overridden point changes nothing. -/
theorem applyUpdates_update_of_mem {σ : List (T × F)} {t : T}
    (h : t ∈ σ.map Prod.fst) (O : T → F) (v : F) :
    applyUpdates σ (Function.update O t v) = applyUpdates σ O := by
  induction σ generalizing O with
  | nil => simp at h
  | cons p σ ih =>
      rw [applyUpdates_cons, applyUpdates_cons]
      by_cases hp : t = p.1
      · subst hp
        rw [Function.update_idem]
      · simp only [List.map_cons, List.mem_cons] at h
        rcases h with h | h
        · exact absurd h hp
        · rw [Function.update_comm hp]
          exact ih h _

open Classical in
/-- **Adaptive escape bound.** A `Q`-query machine enters pointwise escape sets of measure at most
`ε` with probability at most `Q · ε`. Fresh queries pay `ε`; cached queries pay nothing. The
override record `σ` carries the conditioning history. -/
theorem escapesDuring_measure_le {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [Nonempty F] {α : Type*} (esc : T → Set F) {ε : ℝ≥0∞}
    (hesc : ∀ t, (PMF.uniformOfFintype F).toOuterMeasure (esc t) ≤ ε)
    {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q)
    (σ : List (T × F)) (hσ : ∀ p ∈ σ, p.2 ∉ esc p.1) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure
      {O : T → F | A.escapesDuring esc (applyUpdates σ O)} ≤ Q * ε := by
  induction hQ generalizing σ with
  | pure a Q' =>
      have : {O : T → F | (OracleComp.pure a : OracleComp T F α).escapesDuring esc
          (applyUpdates σ O)} = ∅ := by
        ext O; simp [OracleComp.escapesDuring]
      rw [this]
      simp
  | @query t k Q h ih =>
      by_cases hmem : t ∈ σ.map Prod.fst
      · -- re-queried point: the recorded answer does not escape; recurse at the same budget
        obtain ⟨f₀⟩ := (inferInstance : Nonempty F)
        set v := applyUpdates σ (fun _ => f₀) t with hv
        have hvin : (t, v) ∈ σ := applyUpdates_pair_mem hmem _
        have hvesc : v ∉ esc t := hσ _ hvin
        have hset : {O : T → F | (OracleComp.query t k).escapesDuring esc (applyUpdates σ O)}
            = {O : T → F | (k v).escapesDuring esc (applyUpdates σ O)} := by
          ext O
          have hOv : applyUpdates σ O t = v := applyUpdates_apply_of_mem hmem _ _
          simp only [OracleComp.escapesDuring, Set.mem_setOf_eq, hOv]
          exact or_iff_right hvesc
        rw [hset]
        refine (ih v σ hσ).trans ?_
        gcongr
        exact_mod_cast Nat.le_succ Q
      · -- fresh point: pay ε at the point, recurse conditioned on the new answer
        have happ : ∀ O : T → F, applyUpdates σ O t = O t :=
          fun O => applyUpdates_apply_not_mem hmem O
        have hsub : {O : T → F | (OracleComp.query t k).escapesDuring esc (applyUpdates σ O)}
            ⊆ {O : T → F | O t ∈ esc t} ∪ ⋃ u : F, {O : T → F | O t = u ∧
                O ∈ {O' : T → F | u ∉ esc t ∧
                  (k u).escapesDuring esc (applyUpdates (σ ++ [(t, u)]) O')}} := by
          intro O hO
          simp only [OracleComp.escapesDuring, Set.mem_setOf_eq, happ O] at hO
          by_cases hesc' : O t ∈ esc t
          · exact Or.inl hesc'
          · rcases hO with h1 | h2
            · exact Or.inl h1
            · refine Or.inr (Set.mem_iUnion.mpr ⟨O t, rfl, hesc', ?_⟩)
              rw [applyUpdates_append_single]
              have hupd : Function.update (applyUpdates σ O) t (O t) = applyUpdates σ O := by
                rw [← happ O, Function.update_eq_self]
              rw [hupd]
              exact h2
        refine le_trans (MeasureTheory.measure_mono hsub) ?_
        refine le_trans (MeasureTheory.measure_union_le _ _) ?_
        have hfirst : (PMF.uniformOfFintype (T → F)).toOuterMeasure {O : T → F | O t ∈ esc t}
            ≤ ε := by
          rw [uniformOfFintype_point_measure]
          exact hesc t
        have hsecond : (PMF.uniformOfFintype (T → F)).toOuterMeasure
            (⋃ u : F, {O : T → F | O t = u ∧ O ∈ {O' : T → F | u ∉ esc t ∧
              (k u).escapesDuring esc (applyUpdates (σ ++ [(t, u)]) O')}}) ≤ Q * ε := by
          refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
          rw [tsum_fintype]
          have hper : ∀ u : F, (PMF.uniformOfFintype (T → F)).toOuterMeasure
              {O : T → F | O t = u ∧ O ∈ {O' : T → F | u ∉ esc t ∧
                (k u).escapesDuring esc (applyUpdates (σ ++ [(t, u)]) O')}}
              ≤ (Q * ε) / Fintype.card F := by
            intro u
            by_cases huesc : u ∈ esc t
            · have hempty : {O : T → F | O t = u ∧ O ∈ {O' : T → F | u ∉ esc t ∧
                  (k u).escapesDuring esc (applyUpdates (σ ++ [(t, u)]) O')}} = ∅ := by
                ext O; simp [huesc]
              rw [hempty]
              simp
            · have hblind : ∀ (O : T → F) (v : F),
                  Function.update O t v ∈ {O' : T → F | u ∉ esc t ∧
                    (k u).escapesDuring esc (applyUpdates (σ ++ [(t, u)]) O')}
                  ↔ O ∈ {O' : T → F | u ∉ esc t ∧
                    (k u).escapesDuring esc (applyUpdates (σ ++ [(t, u)]) O')} := by
                intro O v
                have hdom : t ∈ (σ ++ [(t, u)]).map Prod.fst := by simp
                simp only [Set.mem_setOf_eq, applyUpdates_update_of_mem hdom]
              rw [uniformOfFintype_cond_point t u _ hblind]
              have hEle : (PMF.uniformOfFintype (T → F)).toOuterMeasure
                  {O' : T → F | u ∉ esc t ∧
                    (k u).escapesDuring esc (applyUpdates (σ ++ [(t, u)]) O')} ≤ Q * ε := by
                have hsub2 : {O' : T → F | u ∉ esc t ∧
                    (k u).escapesDuring esc (applyUpdates (σ ++ [(t, u)]) O')}
                    ⊆ {O' : T → F | (k u).escapesDuring esc (applyUpdates (σ ++ [(t, u)]) O')} :=
                  fun O' hO' => hO'.2
                refine le_trans (MeasureTheory.measure_mono hsub2) ?_
                refine ih u (σ ++ [(t, u)]) ?_
                intro p hp
                rcases List.mem_append.mp hp with hp | hp
                · exact hσ p hp
                · simp only [List.mem_singleton] at hp
                  subst hp
                  exact huesc
              exact ENNReal.div_le_div_right hEle _
          refine le_trans (Finset.sum_le_sum fun u _ => hper u) ?_
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm,
            ENNReal.div_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
              (ENNReal.natCast_ne_top _)]
        calc (PMF.uniformOfFintype (T → F)).toOuterMeasure {O : T → F | O t ∈ esc t}
              + (PMF.uniformOfFintype (T → F)).toOuterMeasure (⋃ u : F, _)
            ≤ ε + Q * ε := add_le_add hfirst hsecond
          _ = (Q + 1) * ε := by ring
          _ = ((Q + 1 : ℕ) : ℝ≥0∞) * ε := by push_cast; ring

open Classical in
/-- **The conditional escape bound.** As `escapesDuring_measure_le`, with each point's escape set
chosen by the rest of the table (`hblind`: never by its own answer) — the state-function shape,
where a round's bad challenges depend on the earlier ones. Stated for machines that never repeat
a query (`OracleComp.AvoidsCache`); `escapesDuringC_measure_le'` lifts to arbitrary machines by
deduplication. Every query here is fresh, so each pays `ε` by the blind-set point bound
(`uniformOfFintype_point_mem_blind_le`) and recurses conditionally; no invariant on the record is
needed. -/
theorem escapesDuringC_measure_le {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [Nonempty F] {α : Type*} (esc : T → (T → F) → Set F)
    (hblind : ∀ (t : T) (O : T → F) (v : F), esc t (Function.update O t v) = esc t O)
    {ε : ℝ≥0∞} (hesc : ∀ t O, (PMF.uniformOfFintype F).toOuterMeasure (esc t O) ≤ ε)
    {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q)
    {σ : List (T × F)} (hσ : OracleComp.AvoidsCache σ A) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure
      {O : T → F | A.escapesDuringC esc (applyUpdates σ O)} ≤ Q * ε := by
  induction hQ generalizing σ with
  | pure a Q' =>
      have hempty : {O : T → F | (OracleComp.pure a : OracleComp T F α).escapesDuringC esc
          (applyUpdates σ O)} = ∅ := by
        ext O; simp [OracleComp.escapesDuringC]
      rw [hempty]
      simp
  | @query t k Q h ih =>
      cases hσ with
      | query ht hk =>
      have happ : ∀ O : T → F, applyUpdates σ O t = O t :=
        fun O => applyUpdates_apply_not_mem ht O
      have hsub : {O : T → F | (OracleComp.query t k).escapesDuringC esc (applyUpdates σ O)}
          ⊆ {O : T → F | O t ∈ esc t (applyUpdates σ O)} ∪ ⋃ u : F, {O : T → F | O t = u ∧
              O ∈ {O' : T → F | (k u).escapesDuringC esc (applyUpdates ((t, u) :: σ) O')}} := by
        intro O hO
        simp only [OracleComp.escapesDuringC, Set.mem_setOf_eq, happ O] at hO
        rcases hO with h1 | h2
        · exact Or.inl h1
        · refine Or.inr (Set.mem_iUnion.mpr ⟨O t, rfl, ?_⟩)
          have hcons : applyUpdates ((t, O t) :: σ) O = applyUpdates σ O := by
            rw [applyUpdates_cons, Function.update_eq_self]
          simp only [Set.mem_setOf_eq, hcons]
          exact h2
      refine le_trans (MeasureTheory.measure_mono hsub) ?_
      refine le_trans (MeasureTheory.measure_union_le _ _) ?_
      have hfirst : (PMF.uniformOfFintype (T → F)).toOuterMeasure
          {O : T → F | O t ∈ esc t (applyUpdates σ O)} ≤ ε := by
        refine uniformOfFintype_point_mem_blind_le t (fun O => esc t (applyUpdates σ O))
          (fun O v => ?_) (fun O => hesc t _)
        beta_reduce
        rw [applyUpdates_update_not_mem ht, hblind]
      have hsecond : (PMF.uniformOfFintype (T → F)).toOuterMeasure
          (⋃ u : F, {O : T → F | O t = u ∧
            O ∈ {O' : T → F | (k u).escapesDuringC esc (applyUpdates ((t, u) :: σ) O')}})
          ≤ Q * ε := by
        refine le_trans (MeasureTheory.measure_iUnion_le _) ?_
        rw [tsum_fintype]
        have hper : ∀ u : F, (PMF.uniformOfFintype (T → F)).toOuterMeasure
            {O : T → F | O t = u ∧
              O ∈ {O' : T → F | (k u).escapesDuringC esc (applyUpdates ((t, u) :: σ) O')}}
            ≤ (Q * ε) / Fintype.card F := by
          intro u
          have hblindE : ∀ (O : T → F) (v : F),
              Function.update O t v ∈ {O' : T → F |
                (k u).escapesDuringC esc (applyUpdates ((t, u) :: σ) O')}
              ↔ O ∈ {O' : T → F |
                (k u).escapesDuringC esc (applyUpdates ((t, u) :: σ) O')} := by
            intro O v
            have hcons : applyUpdates ((t, u) :: σ) (Function.update O t v)
                = applyUpdates ((t, u) :: σ) O := by
              rw [applyUpdates_cons, applyUpdates_cons, Function.update_idem]
            simp only [Set.mem_setOf_eq, hcons]
          rw [uniformOfFintype_cond_point t u _ hblindE]
          exact ENNReal.div_le_div_right (ih u (hk u)) _
        refine le_trans (Finset.sum_le_sum fun u _ => hper u) ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm,
          ENNReal.div_mul_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
            (ENNReal.natCast_ne_top _)]
      calc (PMF.uniformOfFintype (T → F)).toOuterMeasure
            {O : T → F | O t ∈ esc t (applyUpdates σ O)}
            + (PMF.uniformOfFintype (T → F)).toOuterMeasure (⋃ u : F, _)
          ≤ ε + Q * ε := add_le_add hfirst hsecond
        _ = (Q + 1) * ε := by ring
        _ = ((Q + 1 : ℕ) : ℝ≥0∞) * ε := by push_cast; ring

open Classical in
/-- The conditional escape bound for an arbitrary machine: deduplicate
(`OracleComp.escapesDuringC_dedup`), then apply the fresh-query bound. -/
theorem escapesDuringC_measure_le' {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F]
    [Nonempty F] {α : Type*} (esc : T → (T → F) → Set F)
    (hblind : ∀ (t : T) (O : T → F) (v : F), esc t (Function.update O t v) = esc t O)
    {ε : ℝ≥0∞} (hesc : ∀ t O, (PMF.uniformOfFintype F).toOuterMeasure (esc t O) ≤ ε)
    {A : OracleComp T F α} {Q : ℕ} (hQ : A.QueryBound Q) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure
      {O : T → F | A.escapesDuringC esc O} ≤ Q * ε := by
  have hsub : {O : T → F | A.escapesDuringC esc O}
      ⊆ {O : T → F | (OracleComp.dedup [] A).escapesDuringC esc
          (applyUpdates ([] : List (T × F)) O)} := by
    intro O hO
    simp only [Set.mem_setOf_eq, applyUpdates_nil]
    exact OracleComp.escapesDuringC_dedup esc (by simp) (by simp) hO
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  exact escapesDuringC_measure_le esc hblind hesc (OracleComp.dedup_queryBound hQ [])
    (OracleComp.dedup_avoidsCache [] A)


/-! ## The Fiat–Shamir attack game

The abstract game: the adversary outputs a proof `p : P`; `prefixes p` are the `k` round transcript
prefixes that proof induces (deployed: `roundTranscriptFin`, pairwise distinct by
`roundTranscriptFin_injective`); `accept p χ` is the verifier's accept at round challenges `χ`
(deployed: `DeployedIpaVerifierEq` with the round vector replaced). The attack event reads the round
challenges off the *same* table the adversary queried — the defining self-referentiality of
Fiat–Shamir. The full deployed event (every challenge, pre-IPA included, derived from the table via
`roChallenges`) instantiates this once the table domain is restricted to a finite transcript space;
that instantiation belongs with the query-loss reduction. -/

/-! ## Adaptive reads of a uniform random function

The round-adaptive rung's uniformity: a Fiat–Shamir prover's oracle queries form an *adaptive*
schedule — round `j`'s point is fixed by the answers to rounds `< j` — so the challenge vector's
prefixes are path-dependent and the fixed-`φ` uniformity (`roChallenges_ipaRound_uniform`) does not
apply directly. `AdSched.map_read_uniform` supplies the adaptive form. -/

universe u v

/-- A depth-`k` adaptive query schedule: the first query point, then the remaining schedule as a
function of that query's answer. -/
def AdSched (T : Type u) (F : Type v) : ℕ → Type (max u v)
  | 0 => PUnit
  | k + 1 => T × (F → AdSched T F k)

namespace AdSched

variable {T F : Type*}

/-- The points the schedule visits when its reads are `χ`. -/
def points : {k : ℕ} → AdSched T F k → (Fin k → F) → (Fin k → T)
  | 0, _, _ => Fin.elim0
  | k + 1, s, χ => Fin.cons s.1 (points (s.2 (χ 0)) (Fin.tail χ))

/-- The schedule's reads against a table `O`. -/
def read : {k : ℕ} → AdSched T F k → (T → F) → (Fin k → F)
  | 0, _, _ => Fin.elim0
  | k + 1, s, O => Fin.cons (O s.1) (read (s.2 (O s.1)) O)

/-- **Reads meet the target iff the table agrees at the target's own points.** -/
theorem read_eq_iff : {k : ℕ} → (s : AdSched T F k) → (O : T → F) → (χ : Fin k → F) →
    (s.read O = χ ↔ ∀ j, O (s.points χ j) = χ j)
  | 0, _, _, χ => ⟨fun _ j => j.elim0, fun _ => funext fun j => j.elim0⟩
  | k + 1, s, O, χ => by
      constructor
      · intro h
        have h0 : O s.1 = χ 0 := by have := congrFun h 0; rwa [read, Fin.cons_zero] at this
        have htail : (s.2 (χ 0)).read O = Fin.tail χ := by
          have := congrArg Fin.tail h
          rwa [read, Fin.tail_cons, h0] at this
        intro j
        refine Fin.cases ?_ ?_ j
        · rw [points, Fin.cons_zero]; exact h0
        · intro i
          rw [points, Fin.cons_succ]
          exact (read_eq_iff (s.2 (χ 0)) O (Fin.tail χ)).mp htail i
      · intro h
        have h0 : O s.1 = χ 0 := by have := h 0; rwa [points, Fin.cons_zero] at this
        have htail : (s.2 (χ 0)).read O = Fin.tail χ :=
          (read_eq_iff (s.2 (χ 0)) O (Fin.tail χ)).mpr fun i => by
            have := h i.succ; rwa [points, Fin.cons_succ] at this
        rw [read, h0, htail, Fin.cons_self_tail]

/-- Freshness along `χ`: the χ-determined points are pairwise distinct. -/
def Fresh {k : ℕ} (s : AdSched T F k) : Prop := ∀ χ : Fin k → F, Function.Injective (s.points χ)

open Classical in
/-- **Adaptive reads of a uniform random function are uniform.** A fresh depth-`k` adaptive schedule
reads a uniform table to a uniform answer vector: for each target `χ`, the read-equals-`χ` event is
the fixed cylinder over `χ`'s distinct points (`read_eq_iff`), of uniform measure `1/|F|ᵏ`
(`uniformOfFintype_map_precomp_injective`) — the same for every `χ`. The adaptivity is absorbed by
computing the pushforward pointwise; no probability monad. -/
theorem map_read_uniform [Fintype T] [DecidableEq T] [Fintype F] [Nonempty F] {k : ℕ}
    (s : AdSched T F k) (hs : s.Fresh) :
    (PMF.uniformOfFintype (T → F)).map s.read = PMF.uniformOfFintype (Fin k → F) := by
  refine PMF.ext fun χ => ?_
  have hset : {O : T → F | s.read O = χ} = (fun O => O ∘ s.points χ) ⁻¹' {χ} := by
    ext O
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    rw [read_eq_iff s O χ]
    exact ⟨fun h => funext fun j => h j, fun h j => congrFun h j⟩
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    show s.read ⁻¹' {χ} = {O : T → F | s.read O = χ} from rfl, hset,
    ← PMF.toOuterMeasure_map_apply, uniformOfFintype_map_precomp_injective _ (hs χ),
    PMF.toOuterMeasure_apply_singleton]

/-- Append a final adaptive read to a schedule: after the schedule's `k` reads, query the point
`pt` chosen from all `k` answers. This is how the rewinding forking bound turns "the fork state's
`i` reads, then the challenge read at the fork point" into one depth-`(i+1)` schedule, so the joint
distribution of `(fork state, fork challenge)` is `map_read_uniform` at `i+1` — the joint uniformity
the per-fork-index bound needs. -/
def snoc : {k : ℕ} → AdSched T F k → ((Fin k → F) → T) → AdSched T F (k + 1)
  | 0, _, pt => (pt Fin.elim0, fun _ => PUnit.unit)
  | _ + 1, s, pt => (s.1, fun u => (s.2 u).snoc (fun χ => pt (Fin.cons u χ)))

/-- The reads of `s.snoc pt`: the schedule's `k` reads, then the answer at `pt` applied to them. -/
theorem read_snoc : {k : ℕ} → (s : AdSched T F k) → (pt : (Fin k → F) → T) → (O : T → F) →
    (s.snoc pt).read O = Fin.snoc (s.read O) (O (pt (s.read O)))
  | 0, _, pt, O => by
      funext j
      fin_cases j
      simp [snoc, read, Fin.snoc]
  | k + 1, s, pt, O => by
      rw [snoc, read, read_snoc (s.2 (O s.1)) _ O, read]
      exact Fin.cons_snoc_eq_snoc_cons _ _ _

/-- The points of `s.snoc pt` along `χ`: the schedule's points, then `pt` at the read prefix. -/
theorem points_snoc : {k : ℕ} → (s : AdSched T F k) → (pt : (Fin k → F) → T) → (χ : Fin (k+1) → F) →
    (s.snoc pt).points χ = Fin.snoc (s.points (Fin.init χ)) (pt (Fin.init χ))
  | 0, _, pt, χ => by
      have he : (Fin.init χ : Fin 0 → F) = Fin.elim0 := funext fun x => x.elim0
      funext j
      rw [Fin.fin_one_eq_zero j, he]
      simp [snoc, points, Fin.snoc]
  | k + 1, s, pt, χ => by
      have hit : Fin.init (Fin.tail χ) = Fin.tail (Fin.init χ) := by
        funext i; simp [Fin.init, Fin.tail]
      have h0 : (Fin.init χ) 0 = χ 0 := by simp [Fin.init, Fin.castSucc_zero]
      rw [snoc, points, points_snoc (s.2 (χ 0)) _ (Fin.tail χ), points, hit,
          show pt (Fin.cons (χ 0) (Fin.tail (Fin.init χ))) = pt (Fin.init χ) from by
            rw [← h0, Fin.cons_self_tail], h0]
      exact Fin.cons_snoc_eq_snoc_cons _ _ _

/-- Appending a point that is fresh along every path preserves schedule freshness: the extended
`(fork state, fork challenge)` schedule is fresh, so `map_read_uniform` applies at depth `k+1`. -/
theorem Fresh.snoc {k : ℕ} {s : AdSched T F k} (hs : s.Fresh) {pt : (Fin k → F) → T}
    (hpt : ∀ ψ : Fin k → F, pt ψ ∉ Set.range (s.points ψ)) : (s.snoc pt).Fresh := by
  intro χ
  rw [points_snoc]
  exact Fin.snoc_injective_iff.mpr ⟨hs (Fin.init χ), hpt (Fin.init χ)⟩

/-- A snoc-extended schedule's base is fresh: freshness of `s.snoc pt` restricts to `s`. -/
theorem Fresh.of_snoc [Nonempty F] {k : ℕ} {s : AdSched T F k} {pt : (Fin k → F) → T}
    (h : (s.snoc pt).Fresh) : s.Fresh := by
  intro ψ
  have hinj := h (Fin.snoc ψ (Classical.arbitrary F))
  rw [points_snoc, Fin.init_snoc] at hinj
  exact (Fin.snoc_injective_iff.mp hinj).1

end AdSched

/-- **Adaptive-fork blind-set bound.** Under a fresh schedule, the challenge read at the fork point
remains uniform after conditioning on the preceding fork state. Its chance of landing in the
state-dependent set `S` is therefore at most the worst measure of `S`. -/
theorem adaptive_fork_mem_le {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F] [Nonempty F]
    {k : ℕ} (s : AdSched T F k) (pt : (Fin k → F) → T) (hf : (s.snoc pt).Fresh)
    (S : (Fin k → F) → Set F) {ε : ℝ≥0∞}
    (hS : ∀ ψ, (PMF.uniformOfFintype F).toOuterMeasure (S ψ) ≤ ε) :
    (PMF.uniformOfFintype (T → F)).toOuterMeasure
        {O : T → F | O (pt (s.read O)) ∈ S (s.read O)} ≤ ε := by
  set e : (Fin (k + 1) → F) ≃ F × (Fin k → F) := (Fin.snocEquiv (fun _ : Fin (k + 1) => F)).symm
    with he
  have hB : {O : T → F | O (pt (s.read O)) ∈ S (s.read O)}
      = (s.snoc pt).read ⁻¹' {χ : Fin (k + 1) → F | χ (Fin.last k) ∈ S (Fin.init χ)} := by
    ext O
    simp only [Set.mem_setOf_eq, Set.mem_preimage, AdSched.read_snoc, Fin.snoc_last, Fin.init_snoc]
  rw [hB, ← PMF.toOuterMeasure_map_apply, AdSched.map_read_uniform (s.snoc pt) hf]
  have hB2 : {χ : Fin (k + 1) → F | χ (Fin.last k) ∈ S (Fin.init χ)}
      = e ⁻¹' {x : F × (Fin k → F) | x.1 ∈ S x.2} := by
    ext χ
    simp only [he, Set.mem_setOf_eq, Set.mem_preimage, Fin.snocEquiv_symm_apply]
  rw [hB2, ← PMF.toOuterMeasure_map_apply, map_uniformOfFintype_equiv e]
  exact uniformOfFintype_prod_fiber_bound S hS

/-- Reorder `F × (F × X)` (last, mid, initial) as `(X, F, F)` (initial, mid, last). -/
def reorder3 (F X : Type*) : F × F × X ≃ X × F × F where
  toFun x := (x.2.2, x.2.1, x.1)
  invFun y := (y.2.2, y.2.1, y.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Reindex a length-`(k+2)` vector as `(initial k-tuple, k-th, (k+1)-th)`, via two `Fin.snocEquiv`
peels and a reordering. -/
def reindex2 (F : Type*) (k : ℕ) : (Fin (k + 2) → F) ≃ (Fin k → F) × F × F :=
  ((Fin.snocEquiv (fun _ : Fin (k + 2) => F)).symm.trans
    ((Equiv.refl F).prodCongr (Fin.snocEquiv (fun _ : Fin (k + 1) => F)).symm)).trans
    (reorder3 F (Fin k → F))

@[simp] theorem reindex2_apply (F : Type*) (k : ℕ) (v : Fin (k + 2) → F) :
    reindex2 F k v = (Fin.init (Fin.init v), (Fin.init v) (Fin.last k), v (Fin.last (k + 1))) := by
  simp only [reindex2, Equiv.trans_apply, Equiv.prodCongr_apply,
    Fin.snocEquiv_symm_apply, Equiv.coe_refl, Prod.map_apply, id_eq, reorder3, Equiv.coe_fn_mk]

/-- Reindex a length-`(k+1)` vector as `(initial k-tuple, last)`. -/
def reindex1 (F : Type*) (k : ℕ) : (Fin (k + 1) → F) ≃ (Fin k → F) × F :=
  (Fin.snocEquiv (fun _ : Fin (k + 1) => F)).symm.trans (Equiv.prodComm F (Fin k → F))

@[simp] theorem reindex1_apply (F : Type*) (k : ℕ) (v : Fin (k + 1) → F) :
    reindex1 F k v = (Fin.init v, v (Fin.last k)) := by
  simp only [reindex1, Equiv.trans_apply, Fin.snocEquiv_symm_apply, Equiv.prodComm_apply,
    Prod.swap_prod_mk]

/-- **Single-round forking bound.** Two fresh fork points both accept with distinct challenges with
probability at least `ε² − ε/N`. `AdSched.map_read_uniform` reduces the oracle experiment to the
uniform Bellare–Neven fork counted by `forking_measure_bound`. -/
theorem schedule_fork_bound {T F : Type*} [Fintype T] [DecidableEq T] [Fintype F] [Nonempty F]
    [DecidableEq F] {k : ℕ} (s : AdSched T F k) (pt₁ pt₂ : (Fin k → F) → T)
    (hd : ((s.snoc pt₁).snoc (fun χ : Fin (k + 1) → F => pt₂ (Fin.init χ))).Fresh)
    (acc : (Fin k → F) → F → Prop) [∀ ψ, DecidablePred (acc ψ)] :
    ((PMF.uniformOfFintype (T → F)).toOuterMeasure
        {O | acc (s.read O) (O (pt₁ (s.read O)))}) ^ 2
      ≤ (PMF.uniformOfFintype (T → F)).toOuterMeasure
          {O | acc (s.read O) (O (pt₁ (s.read O))) ∧ acc (s.read O) (O (pt₂ (s.read O)))
                ∧ O (pt₁ (s.read O)) ≠ O (pt₂ (s.read O))}
        + (PMF.uniformOfFintype (T → F)).toOuterMeasure
            {O | acc (s.read O) (O (pt₁ (s.read O)))} / Fintype.card F := by
  classical
  set sd := (s.snoc pt₁).snoc (fun χ : Fin (k + 1) → F => pt₂ (Fin.init χ)) with hsd
  have hs1 : (s.snoc pt₁).Fresh := AdSched.Fresh.of_snoc hd
  have hread1 : ∀ O, (s.snoc pt₁).read O = Fin.snoc (s.read O) (O (pt₁ (s.read O))) :=
    fun O => AdSched.read_snoc s pt₁ O
  have hreadd : ∀ O, sd.read O
      = Fin.snoc (Fin.snoc (s.read O) (O (pt₁ (s.read O)))) (O (pt₂ (s.read O))) := by
    intro O
    rw [hsd, AdSched.read_snoc (s.snoc pt₁) _ O, hread1]
    simp only [Fin.init_snoc]
  have hLHS : (PMF.uniformOfFintype (T → F)).toOuterMeasure {O | acc (s.read O) (O (pt₁ (s.read O)))}
      = (PMF.uniformOfFintype ((Fin k → F) × F)).toOuterMeasure {x | acc x.1 x.2} := by
    have hset : {O : T → F | acc (s.read O) (O (pt₁ (s.read O)))}
        = (s.snoc pt₁).read ⁻¹' (reindex1 F k ⁻¹' {x : (Fin k → F) × F | acc x.1 x.2}) := by
      ext O
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hread1, reindex1_apply, Fin.init_snoc,
        Fin.snoc_last]
    rw [hset, ← PMF.toOuterMeasure_map_apply, AdSched.map_read_uniform (s.snoc pt₁) hs1,
      ← PMF.toOuterMeasure_map_apply, map_uniformOfFintype_equiv (reindex1 F k)]
  have hTRIPLE : (PMF.uniformOfFintype (T → F)).toOuterMeasure
        {O | acc (s.read O) (O (pt₁ (s.read O))) ∧ acc (s.read O) (O (pt₂ (s.read O)))
              ∧ O (pt₁ (s.read O)) ≠ O (pt₂ (s.read O))}
      = (PMF.uniformOfFintype ((Fin k → F) × F × F)).toOuterMeasure
          {x | acc x.1 x.2.1 ∧ acc x.1 x.2.2 ∧ x.2.1 ≠ x.2.2} := by
    have hset : {O : T → F | acc (s.read O) (O (pt₁ (s.read O)))
              ∧ acc (s.read O) (O (pt₂ (s.read O))) ∧ O (pt₁ (s.read O)) ≠ O (pt₂ (s.read O))}
        = sd.read ⁻¹'
            (reindex2 F k ⁻¹'
              {x : (Fin k → F) × F × F | acc x.1 x.2.1 ∧ acc x.1 x.2.2 ∧ x.2.1 ≠ x.2.2}) := by
      ext O
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hreadd, reindex2_apply, Fin.init_snoc,
        Fin.snoc_last]
    rw [hset, ← PMF.toOuterMeasure_map_apply, AdSched.map_read_uniform sd hd,
      ← PMF.toOuterMeasure_map_apply, map_uniformOfFintype_equiv (reindex2 F k)]
  rw [hLHS, hTRIPLE]
  exact forking_measure_bound acc


section Game

variable {T P F : Type*} [Fintype T] [DecidableEq T] [Fintype F] [Nonempty F] {k : ℕ}

/-- The Fiat–Shamir attack event on table `O`: the adversary's output, taken with the round-challenge
vector the same oracle induces at the output's own round prefixes, is accepted. -/
def fsWins (A : OracleComp T F P) (accept : P → (Fin k → F) → Prop)
    (prefixes : P → Fin k → T) (O : T → F) : Prop :=
  accept (A.run O) (fun j => O (prefixes (A.run O) j))

/-- The adversary's advantage `ε`: the probability, over a uniformly drawn oracle table, of the
Fiat–Shamir attack event. -/
noncomputable def fsAdvantage (A : OracleComp T F P) (accept : P → (Fin k → F) → Prop)
    (prefixes : P → Fin k → T) : ℝ≥0∞ :=
  (PMF.uniformOfFintype (T → F)).toOuterMeasure {O | fsWins A accept prefixes O}

/-- **The zero-query anchor.** A query-free adversary's advantage is exactly its fixed output's accept
measure over the uniform challenge vector — the measure `hprob` is stated over
(`uniformOfFintype_map_precomp_injective` at the output's distinct round prefixes). The general
query-loss reduction is this identity's `Q`-query generalization (module docstring). -/
theorem fsAdvantage_pure (p : P) (accept : P → (Fin k → F) → Prop)
    (prefixes : P → Fin k → T) (hinj : Function.Injective (prefixes p)) :
    fsAdvantage (.pure p) accept prefixes
      = (PMF.uniformOfFintype (Fin k → F)).toOuterMeasure {χ | accept p χ} := by
  rw [fsAdvantage, ← uniformOfFintype_map_precomp_injective (prefixes p) hinj,
    PMF.toOuterMeasure_map_apply]
  rfl

/-- **Query-loss composition.** If every winning run either makes an escaping query or reaches a
residual event `R`, its advantage is at most `Q · ε + δ`: `ε` for each query and `δ` for the
residual event. -/
theorem fsAdvantage_le_of_forcing (A : OracleComp T F P) (accept : P → (Fin k → F) → Prop)
    (prefixes : P → Fin k → T) (esc : T → Set F) {ε : ℝ≥0∞}
    (hesc : ∀ t, (PMF.uniformOfFintype F).toOuterMeasure (esc t) ≤ ε)
    {Q : ℕ} (hQ : A.QueryBound Q) (R : Set (T → F)) {δ : ℝ≥0∞}
    (hR : (PMF.uniformOfFintype (T → F)).toOuterMeasure R ≤ δ)
    (hwin : ∀ O, fsWins A accept prefixes O → A.escapesDuring esc O ∨ O ∈ R) :
    fsAdvantage A accept prefixes ≤ Q * ε + δ := by
  have hsub : {O : T → F | fsWins A accept prefixes O}
      ⊆ {O : T → F | A.escapesDuring esc O} ∪ R := by
    intro O hO
    rcases hwin O hO with h | h
    · exact Or.inl h
    · exact Or.inr h
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  refine le_trans (MeasureTheory.measure_union_le _ _) ?_
  have hesc' : (PMF.uniformOfFintype (T → F)).toOuterMeasure
      {O : T → F | A.escapesDuring esc O} ≤ Q * ε := by
    have h0 : {O : T → F | A.escapesDuring esc O}
        = {O : T → F | A.escapesDuring esc (applyUpdates ([] : List (T × F)) O)} := by
      simp
    rw [h0]
    exact escapesDuring_measure_le esc hesc hQ [] (by simp)
  exact add_le_add hesc' hR

end Game

open scoped ENNReal in
open Classical in
/-- **Legacy fixed-strategy soundness.** If a fixed strategy's oracle-table advantage exceeds
`kerr/Nᵏ`, compute an IPA opening or relation. `fsAdvantage_pure` supplies the uniform challenge
vector; the deployed arbitrary-query path is in `Forking.Adversary.Recursive`. -/
noncomputable def legacy_deployed_forking_soundness_of_fixed_adversary
    {G : Type*} [AddCommGroup G]
    [Module Fp G] [DecidableEq G] [Inhabited G]
    (urs : URS G) (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp)
    (aMulti aDep s : Fin (2 ^ urs.k) → Fp) (P : Prover Fp G urs.k)
    {T : Type*} [Fintype T] [DecidableEq T] (prefixes : Fin urs.k → T)
    (hinj : Function.Injective prefixes)
    (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (hadv : (kerr (Fintype.card Fp) urs.k : ℝ≥0∞) / Fintype.card (Fin urs.k → Fp)
        < fsAdvantage (.pure P)
            (fun P' => proverAccept P' urs.g b urs.u urs.w z
              (commit urs aDep + (z * 0) • urs.u + blind • urs.w))
            (fun _ => prefixes)) :
    (∃ a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  rw [fsAdvantage_pure P _ (fun _ => prefixes) hinj] at hadv
  refine legacy_deployed_forking_soundness urs b v ξ z blind aMulti aDep s P hz hb0 hP ?_
  convert hadv using 2
  ext χ
  simp

section StagedAdversary

variable {G : Type*}

/-- The adaptive query schedule of a staged strategy: append `(L,R)` and the challenge marker,
squeeze, then continue under the answer. -/
def schedOfProver : {d : ℕ} → Prover Fp G d → List (TranscriptElt Fp G) →
    AdSched (List (TranscriptElt Fp G)) Fp d
  | 0, _, _ => PUnit.unit
  | _ + 1, .node L R cont, t =>
      (t ++ [.point L, .point R, .challenge],
       fun u => schedOfProver (cont u) (t ++ [.point L, .point R, .challenge]))

/-- Each round's point extends the base by `3·(j+1)` — every squeeze absorbs a fresh point pair and
marker — so the schedule's points have strictly increasing length. -/
theorem schedOfProver_points_length : {d : ℕ} → (P : Prover Fp G d) →
    (t : List (TranscriptElt Fp G)) → (χ : Fin d → Fp) → (j : Fin d) →
    ((schedOfProver P t).points χ j).length = t.length + 3 * (j.val + 1)
  | _ + 1, .node L R cont, t, χ, j => by
      refine Fin.cases ?_ ?_ j
      · show ((schedOfProver (.node L R cont) t).points χ 0).length = _
        rw [schedOfProver, AdSched.points, Fin.cons_zero]
        simp
      · intro i
        show ((schedOfProver (.node L R cont) t).points χ i.succ).length = _
        rw [schedOfProver, AdSched.points, Fin.cons_succ,
          schedOfProver_points_length (cont (χ 0)) _ (Fin.tail χ) i]
        simp only [List.length_append, List.length_cons, List.length_nil, Fin.val_succ]
        omega

/-- **Staged schedule freshness.** Distinct rounds have distinct transcript lengths, so their
squeeze points are pairwise distinct along every path. -/
theorem schedOfProver_fresh {d : ℕ} (P : Prover Fp G d) (t : List (TranscriptElt Fp G)) :
    (schedOfProver P t).Fresh := by
  intro χ a c hac
  have hlen : ((schedOfProver P t).points χ a).length
      = ((schedOfProver P t).points χ c).length := congrArg List.length hac
  rw [schedOfProver_points_length P t χ a, schedOfProver_points_length P t χ c] at hlen
  exact Fin.ext (by omega)

open Classical in
/-- **Legacy staged-strategy soundness.** If a fresh staged schedule's oracle-table advantage
exceeds `kerr/Nᵏ`, compute an IPA opening or relation. `AdSched.map_read_uniform` supplies the
path-dependent uniform challenge vector. -/
noncomputable def legacy_deployed_forking_soundness_of_staged_adversary
    [AddCommGroup G] [Module Fp G]
    [DecidableEq G] [Inhabited G]
    (urs : URS G) (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp)
    (aMulti aDep s : Fin (2 ^ urs.k) → Fp) (Q : Prover Fp G urs.k)
    {T : Type*} [Fintype T] [DecidableEq T] (sched : AdSched T Fp urs.k) (hfresh : sched.Fresh)
    (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    (hadv : (kerr (Fintype.card Fp) urs.k : ℝ≥0∞) / Fintype.card (Fin urs.k → Fp)
        < (PMF.uniformOfFintype (T → Fp)).toOuterMeasure
            {O | flatAccept Q urs.g b urs.u urs.w z
                  (commit urs aDep + (z * 0) • urs.u + blind • urs.w) (sched.read O)}) :
    (∃ a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  refine legacy_deployed_forking_soundness_flat urs b v ξ z blind aMulti aDep s Q hz hb0 hP ?_
  rw [show {O : T → Fp | flatAccept Q urs.g b urs.u urs.w z
        (commit urs aDep + (z * 0) • urs.u + blind • urs.w) (sched.read O)}
      = sched.read ⁻¹' {χ | flatAccept Q urs.g b urs.u urs.w z
          (commit urs aDep + (z * 0) • urs.u + blind • urs.w) χ} from rfl,
    ← PMF.toOuterMeasure_map_apply, AdSched.map_read_uniform sched hfresh] at hadv
  convert hadv using 2
  ext χ
  simp

end StagedAdversary

/-- A staged decode assigns each transcript point its round, earlier prefix chain, and continuation
accept predicate. The consistency fields make its escape sets depend only on earlier answers. -/
structure StagedDecode (T F P : Type*) (k : ℕ) (accept : P → (Fin k → F) → Prop)
    (prefixes : P → Fin k → T) : Type _ where
  /-- The full-vector accept predicate of the transcript's staged continuation. -/
  stateAt : T → ((Fin k → F) → Prop)
  /-- The round the transcript point sits at. -/
  roundOf : T → ℕ
  /-- The round-prefix chain through the transcript point. -/
  chainAt : T → Fin k → T
  /-- On an output's own prefixes, the decoded state is the output's accept predicate. -/
  stateAt_prefixes : ∀ p (j : Fin k), stateAt (prefixes p j) = accept p
  /-- On an output's own prefixes, the decoded round is the prefix's round. -/
  roundOf_prefixes : ∀ p (j : Fin k), roundOf (prefixes p j) = (j : ℕ)
  /-- On an output's own prefixes, the decoded chain is the output's chain. -/
  chainAt_prefixes : ∀ p (j : Fin k), chainAt (prefixes p j) = prefixes p
  /-- Chain points before a transcript point's round are distinct from it (deployed: strictly
  shorter prefixes). -/
  chainAt_ne : ∀ t (i : Fin k), (i : ℕ) < roundOf t → chainAt t i ≠ t

namespace StagedDecode

variable {T F P : Type*} [Zero F] {k : ℕ} {accept : P → (Fin k → F) → Prop}
  {prefixes : P → Fin k → T}

/-- The decode's escape sets: at each transcript point, the ladder's escape set for the decoded
state at the decoded round, over the chain's answers. -/
def esc [DecidableEq T] (D : StagedDecode T F P k accept prefixes) : T → (T → F) → Set F :=
  fun t O => ladderEscapeSet (D.stateAt t) (fun i => O (D.chainAt t i)) (D.roundOf t)

/-- The decode's escape sets are blind at their own point: the ladder reads only the rounds before
`roundOf t`, whose chain points differ from `t`. -/
theorem esc_blind [DecidableEq T] (D : StagedDecode T F P k accept prefixes)
    (t : T) (O : T → F) (v : F) : D.esc t (Function.update O t v) = D.esc t O := by
  refine ladderEscapeSet_congr _ _ _ _ (fun i hi => ?_)
  rw [Function.update_apply, if_neg (D.chainAt_ne t i hi)]

/-- The decode's escape sets sit inside three challenges. -/
theorem esc_measure_le [DecidableEq T] [Fintype F] [Nonempty F]
    (D : StagedDecode T F P k accept prefixes) (t : T) (O : T → F) :
    (PMF.uniformOfFintype F).toOuterMeasure (D.esc t O) ≤ 3 / Fintype.card F := by
  obtain ⟨a, b, hab⟩ := ladderEscapeSet_subset_triple (D.stateAt t)
    (fun i => O (D.chainAt t i)) (D.roundOf t)
  exact uniformOfFintype_toOuterMeasure_triple_le hab

/-- **Winning forces an escape or an extractable output.** The attack's accepted vector walks the
ladder (`extractable_or_ladderEscape`): extraction at the root, or an escaping round whose prefix
the completed machine queried. -/
theorem win_forces [DecidableEq T] (D : StagedDecode T F P k accept prefixes)
    {A : OracleComp T F P} {O : T → F} (hwin : fsWins A accept prefixes O) :
    (A.completing prefixes).escapesDuringC D.esc O ∨ Extractable (accept (A.run O)) := by
  rcases extractable_or_ladderEscape (accept (A.run O))
      (fun j => O (prefixes (A.run O) j)) hwin with hext | hlad
  · exact Or.inr hext
  · obtain ⟨j, hj⟩ := exists_mem_ladderEscapeSet _ _ hlad
    refine Or.inl (OracleComp.escapesDuringC_completing D.esc prefixes (j := j) ?_)
    show O (prefixes (A.run O) j) ∈ ladderEscapeSet (D.stateAt (prefixes (A.run O) j))
      (fun i => O (D.chainAt (prefixes (A.run O) j) i)) (D.roundOf (prefixes (A.run O) j))
    rw [D.stateAt_prefixes, D.roundOf_prefixes, D.chainAt_prefixes]
    exact hj

open Classical in
/-- **The staged query loss.** Under a staged decode, an adversary with no extractable output has
advantage at most `(Q + k) · 3/|F|`: winning forces an escaping query of the completed machine
(`win_forces`), and the conditional escape bound prices its `Q + k` queries at `3/|F|` each. -/
theorem fsAdvantage_le [Fintype T] [DecidableEq T] [Fintype F] [Nonempty F]
    (D : StagedDecode T F P k accept prefixes) {A : OracleComp T F P} {Q : ℕ}
    (hQ : A.QueryBound Q)
    (hnoext : ∀ O : T → F, ¬ Extractable (accept (A.run O))) :
    fsAdvantage A accept prefixes ≤ (Q + k) * (3 / Fintype.card F) := by
  have hsub : {O : T → F | fsWins A accept prefixes O}
      ⊆ {O : T → F | (A.completing prefixes).escapesDuringC D.esc O} := by
    intro O hO
    rcases D.win_forces hO with h | h
    · exact h
    · exact absurd h (hnoext O)
  refine le_trans (MeasureTheory.measure_mono hsub) ?_
  have h := escapesDuringC_measure_le' D.esc D.esc_blind D.esc_measure_le
    (OracleComp.queryBound_completing prefixes hQ)
  exact_mod_cast h

open Classical in
/-- **Staged extraction dichotomy.** Advantage above `(Q + k) · 3/|F|` yields a table whose output
is `Extractable`, hence carries the full ternary fork tree. -/
theorem extractable_of_lt_fsAdvantage [Fintype T] [DecidableEq T] [Fintype F] [Nonempty F]
    (D : StagedDecode T F P k accept prefixes) {A : OracleComp T F P} {Q : ℕ}
    (hQ : A.QueryBound Q)
    (h : (Q + k) * (3 / Fintype.card F) < fsAdvantage A accept prefixes) :
    ∃ O : T → F, Extractable (accept (A.run O)) := by
  by_contra hno
  push_neg at hno
  exact absurd (D.fsAdvantage_le hQ hno) (not_le.mpr h)

end StagedDecode


open Classical in
/-- **Legacy querying-adversary soundness.** A staged `Q`-query adversary above the
`(Q + k) · 3/p` loss yields an IPA opening or relation. This existence-form wrapper is
supplementary; `Forking.Adversary.Recursive` computes the deployed certificate. -/
noncomputable def legacy_deployed_forking_soundness_of_adversary
    {G : Type*} [AddCommGroup G]
    [Module Fp G] [DecidableEq G] [Inhabited G]
    (urs : URS G) (b : Fin (2 ^ urs.k) → Fp) (v ξ z blind : Fp)
    (aMulti aDep s : Fin (2 ^ urs.k) → Fp)
    {T : Type*} [Fintype T] [DecidableEq T]
    (A : OracleComp T Fp (Prover Fp G urs.k)) (prefixes : Prover Fp G urs.k → Fin urs.k → T)
    (D : StagedDecode T Fp (Prover Fp G urs.k) urs.k
      (fun P χ => proverAccept P urs.g b urs.u urs.w z
        (commit urs aDep + (z * 0) • urs.u + blind • urs.w) χ) prefixes)
    (hz : z ≠ 0) (hb0 : b 0 = 1)
    (hP : commit urs aDep = commit urs aMulti - v • urs.g 0 + ξ • commit urs s)
    {Q : ℕ} (hQ : A.QueryBound Q)
    (hadv : (Q + urs.k) * (3 / Fintype.card Fp)
        < fsAdvantage A (fun P χ => proverAccept P urs.g b urs.u urs.w z
            (commit urs aDep + (z * 0) • urs.u + blind • urs.w) χ) prefixes) :
    (∃ a, IpaRelation urs (commit urs aMulti) b (v - ξ * innerProduct s b) a)
      ⊕' NontrivialRelation (F := Fp) urs.g urs.u urs.w := by
  have hext := D.extractable_of_lt_fsAdvantage hQ hadv
  have hpf := proverAccept_forkValid (A.run hext.choose) urs.g b
    (commit urs aDep + (z * 0) • urs.u + blind • urs.w) hext.choose_spec
  rcases deployed_forking_relation urs b v ξ z blind aMulti aDep s hpf.choose hz hb0 hP
    hpf.choose_spec with ⟨a, ha⟩ | r
  · exact PSum.inl ⟨a, ha⟩
  · exact PSum.inr r

end Zcash.Snark
