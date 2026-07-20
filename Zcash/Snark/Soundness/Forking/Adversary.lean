import Zcash.Snark.Soundness.Forking.Rewind

/-!
# The oracle-querying Fiat–Shamir adversary

The forking capstones (`Soundness.Vesta`) are conditional on `hprob` — an accept probability over the
uniform challenge vector. What produces that probability in the random-oracle model is an *adversary*:
a machine that queries the oracle up to `Q` times and outputs a proof, winning when the deployed
verifier accepts its output under the challenges the same oracle derives. This module supplies that
querying machine and its attack advantage; deriving `hprob` from the advantage — the forking reduction
with its query-loss — is the target theorem this vocabulary is for (see the query-loss section note).

The machine mirrors VCVio's `OracleComp` (Verified-zkEVM/VCV-io, https://eprint.iacr.org/2024/1819),
minimized to the single Fiat–Shamir oracle: a free monad with `pure` and `query`, run against a whole
oracle *table* `O : T → F` (VCVio's eager semantics). For query-bounded adversaries the whole-table and
lazily-sampled semantics agree, so the finite counting style of `Forking.Probability` applies: the
advantage is a measure over uniformly drawn tables, no probability monad required.

* `OracleComp` — the querying machine: an adaptive query tree, each continuation seeing the answer.
* `OracleComp.run` / `OracleComp.queries` — the output and the query log against a table.
* `OracleComp.QueryBound` — at most `Q` queries on every path (the `Q` of the query-loss).
* `fsWins` / `fsAdvantage` — the Fiat–Shamir attack event and its advantage `ε` over uniform tables.
* `fsAdvantage_pure` — the zero-query anchor: a query-free adversary's advantage *is* its fixed
  output's accept measure over the uniform challenge vector — `hprob`'s measure, recovered exactly.

## Legacy propositional staged interfaces and the executable path

For an adversary that **is** a staged `Prover` strategy, the closure needs **no `StagedDecode` and
no query loss**: reading its challenges off a uniform oracle table is a uniform challenge vector
(`AdSched.map_read_uniform` for the path-dependent prefixes), which the existing forking
(`extractable_of_prob`) turns into the tree — `legacy_deployed_forking_soundness_of_fixed_adversary`
(constant) and `legacy_deployed_forking_soundness_of_staged_adversary` (round-adaptive). Their `hprob` *is*
that adversary's advantage over uniformly drawn oracle tables (the random-oracle table experiment).

**These assume staging, which a malicious prover need not respect.** Transcript ordering
(`Soundness.Forking.Ordering`) shows a *completed* proof hashes each round point before its
challenge; it does **not** stop a **grinding** forger from querying many candidate prefixes and
choosing its proof afterward. The deployed arbitrary-query path is now
`Soundness.Forking.Recursive`: it runs and rewinds `OracleComp` directly, constructs the algebraic
fork certificate from explicit coins, and prices failure through the conditional escape bound
below. `Soundness.Forking.Algebraic` packages that result for the AGM reduction. The `legacy_*`
staged definitions later in this file remain supplementary. What the loss is paid against:

* **Not the plain accept measure.** Beyond `Q = 0` (`fsAdvantage_pure`), `(Q + 1) · β` with `β`
  the worst per-output accept measure is **false**, even for committed queries: seeing one round
  challenge, the adversary may choose its remaining proof around it — with per-`p` accept sets
  `Z_p × full` (each of measure `β`, the `Z_p` covering the challenge space), one query wins with
  probability far above `2β`. Grinding round by round scales the same gap to every round (the
  state-restoration gap).
* **Round-by-round structure.** The loss prices correctly against per-point *escape* budgets:
  when every point's escaping answers have measure at most `ε`, an adaptive `Q`-query machine
  makes an escaping query with probability at most `Q · ε` — the **escape bound**,
  `escapesDuring_measure_le`, proven below by conditioning one query at a time
  (`uniformOfFintype_cond_point`), with `escapesDuringC_measure_le'` the state-dependent form.
  The state function itself exists: `Extractable` doubles as doom on challenge prefixes, an
  accepted vector certifies extraction or escapes doom at some round (`extractable_or_ladderEscape`,
  `Soundness.Forking.Tree`), doomed escape sets have at most three challenges
  (`escapeSet_subset_triple` — the `kerr` count, per round), and `OracleComp.completing` makes the
  winning chain queried.

## Where the gluing must pass: the state lives on the win set, not the adversary

Evaluating the ladder's escape sets at the machine's queries has one exact obstruction, recorded
here so it is not re-derived. The round-`j` ladder state is the accept predicate continued past
round `j`, which depends on the proof's *later* round points: a round-`j` transcript prefix does
not determine it, and defining the escape set through the machine's final output breaks the
blindness `escapesDuringC_measure_le'` needs precisely when the machine queries its own chain —
which every real forger does. This is not a formalization artifact: it is the
state-restoration/AFK wall itself (`(Q + 1) · κ`, Attema–Fehr–Klooß,
https://eprint.iacr.org/2021/1377). A `StagedDecode.stateAt` — the prefix's continuation as a
fixed function of the transcript — resolves it *only* for adversaries that respect staging; for a
grinder no such `stateAt` exists (two outputs sharing a round-`j` prefix may differ later, so one
prefix would need two values).

**The resolution** is operational. `Forking.Recursive` defines a blind escape set from the current
finite tape and recursive continuations. An accepting run either falls into that priced escape set
or the same algorithm returns three successful continuations and recurses. This yields certificate
data directly instead of selecting a tree from a proposition.

The Bellare–Neven *local-forking* core is verified here as supplementary material —
`reprogram_replay_fork` (deterministic replay of a reprogrammed query), `forkIdx` /
`card_win_eq_sum_forkIdx` (the fork-index decomposition of the win set), `AdSched.snoc` /
`adaptive_fork_mem_le` (the fork challenge stays uniform against the prefix), and
`schedule_fork_bound` (the single BN fork `ε² − ε/N` in the oracle experiment, from
`forking_card_bound` / `forking_measure_bound`, `Soundness.Forking.Probability`) — an independent,
fully-proven route to single-round forking. The deployed capstone routes through the win-set
ladder above, which reaches all `k` rounds at once.
-/

namespace Zcash.Snark

open scoped ENNReal

/-- A computation with oracle access to a single oracle `T → F`, as a free monad: either a result, or
a query at `t` whose continuation sees the answer. This is the adaptive querying machine — each query
may depend on all previous answers. Mirrors VCVio's `OracleComp` at a single oracle. -/
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

/-- The machine makes at most `Q` queries on every path (VCVio's `IsQueryBound`, structural form).
This is the `Q` the forking reduction's query-loss counts. -/
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


/-- Answer a split-domain machine's junk queries from a fixed table: `inl`-queries go to the real
oracle, `inr`-queries are answered from `j`. This is the restriction of an adversary that may
query points outside the game's transcript domain — hashing longer strings and using their answers
as grinding randomness. For each fixed junk table the restriction queries only `T` within the same
budget (`queryBound_restrictSum`), and over a uniform split-domain table the junk answers are an
independent uniform table, so the original advantage is an average of the restrictions' advantages
(`fsWinsFull_restrictSum_le`, `Soundness.Forking.Adaptive`): larger oracle domains add no power. -/
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
/-- **The adaptive escape bound.** A machine making at most `Q` queries — however adaptively —
makes an escaping query with probability at most `Q · ε` over uniform tables, when every point's
escape set has measure at most `ε`. This is the multi-round Fiat–Shamir query loss in its correct
currency (module docstring): each fresh query pays `ε` by the one-point marginal, a re-queried
point pays nothing (its recorded answer already failed to escape), and the recursion conditions on
the fresh answer via `uniformOfFintype_cond_point`, carried by the override record `σ` — every
recorded answer non-escaping — so the measure always ranges over full uniform tables. Instantiate
at `σ = []` for the bare statement. -/
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

/-- **The adaptive-fork blind-set bound.** For a schedule `s` whose one-read extension `s.snoc pt` is
fresh, the reprogrammed fork challenge `O (pt (s.read O))` lands in a set `S` chosen by the fork
state `s.read O` with probability at most the worst set's measure. The joint distribution of
`(fork state, fork challenge)` is uniform on `Fin (k+1) → F` (`AdSched.map_read_uniform` at the
snoc), so the event is a Fubini fiber over the last coordinate (`uniformOfFintype_prod_fiber_bound`).
This is the per-fork-index uniformity the rewinding forking bound consumes: what the machine reads at
the fork point stays uniform against everything it computed from the prefix. -/
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

/-- **The single-round forking bound, in the oracle experiment.** For a schedule `s` with two fresh
fork points `pt₁, pt₂` (their double extension is fresh), the probability over uniform oracle tables
that both fresh fork challenges accept *and differ* is at least `ε² − ε/N`, where `ε` is the accept
probability of a single fork. `AdSched.map_read_uniform` (at the double `snoc`) transports the oracle
experiment to uniform `(state, c₁, c₂)`, and `forking_measure_bound` supplies the arithmetic. This is
the Bellare–Neven single fork in the random-oracle model — the base case the rewinding tree iterates. -/
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

/-- **The query-loss composition.** If winning forces the machine's run to make an escaping query
or the table to land in a residual event `R` (the state-function hypothesis: the win walks out of
doom at some queried point, or at an unqueried one — the residual), the advantage decomposes as
the escape bound plus the residual: `ε` per query, `δ` once. This is the socket the deployed
state function plugs into (module docstring): supplying `hwin` for the IPA verifier equation is
the protocol side of the query loss. -/
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
/-- **Legacy propositional capstone for a fixed-strategy adversary.** An
adversary committing to a fixed strategy `P` (a `.pure P` machine that reads its round-prefix
challenges) whose Fiat–Shamir advantage *over uniformly drawn oracle tables* beats the knowledge
error `kerr/Nᵏ` yields the deployed opening or a computed relation. `fsAdvantage_pure` rewrites the
table advantage to the challenge-vector accept measure — that rewrite *is* challenge-vector
uniformity (#24, `uniformOfFintype_map_precomp_injective`) — which
`legacy_deployed_forking_soundness`
consumes. This closes the random-oracle **table experiment** → `hprob` step for the constant rung.
The genuinely round-adaptive rung is the staged strategy of
`legacy_deployed_forking_soundness_of_adversary`; the computed deployed path is in
`Forking.Recursive` and
`Forking.Algebraic`. -/
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

/-- The adaptive query schedule the staged strategy `P` induces over a running transcript `t`: at
each node commit `(L,R)` (appending the round block and the challenge marker), squeeze from the
extended transcript, and continue under the answer. The `AdSched` companion of the deployed
round-by-round derivation. -/
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

/-- **The staged schedule is fresh.** Distinct rounds squeeze from distinct-length transcripts, so
the schedule's points are pairwise distinct along every path — the freshness `map_read_uniform`
needs, from length alone (independent of the committed points). -/
theorem schedOfProver_fresh {d : ℕ} (P : Prover Fp G d) (t : List (TranscriptElt Fp G)) :
    (schedOfProver P t).Fresh := by
  intro χ a c hac
  have hlen : ((schedOfProver P t).points χ a).length
      = ((schedOfProver P t).points χ c).length := congrArg List.length hac
  rw [schedOfProver_points_length P t χ a, schedOfProver_points_length P t χ c] at hlen
  exact Fin.ext (by omega)

open Classical in
/-- **Legacy propositional capstone for a staged adversary.** A strategy `Q` (a `Prover` tree — the
object a rewound Fiat–Shamir prover realizes) whose
accept event over uniformly drawn oracle tables, reading its challenges through the adaptive
schedule `sched`, beats the knowledge error `kerr/Nᵏ`, yields the deployed opening or a computed
relation. `AdSched.map_read_uniform` (needing only `sched.Fresh`, supplied for the deployed schedule
by `schedOfProver_fresh`) rewrites the table advantage to the challenge-vector accept measure —
challenge-vector uniformity for *path-dependent* prefixes — which
`legacy_deployed_forking_soundness_flat`
consumes. This closes the random-oracle **table experiment** → `hprob` step for the round-adaptive
rung with no `StagedDecode` and no query loss. The computed arbitrary-query path is in
`Forking.Recursive` and `Forking.Algebraic`. -/
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

/-- **The staged decode: the execution-semantics bridge as data.** At each transcript point the
protocol determines a round index, the chain of that round's transcript prefixes, and the
full-vector accept predicate of the transcript's staged continuation — fixed functions of the
transcript, so the escape sets read only earlier answers and stay blind at their own point. The
consistency fields tie the decode to the attack game's outputs; producing such a decode for the
deployed verifier's rewound adversary is the execution-semantics floor the Vesta capstones
carry. -/
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
/-- **The staged dichotomy.** Advantage beyond `(Q + k) · 3/|F|` produces a table whose output's
accept predicate carries the full `(3,…,3)` tree — the object `proverAccept_forkValid` and
`deployed_forking_relation` consume. The query loss, paid in the `kerr` currency. -/
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
/-- **Legacy propositional capstone for an oracle-querying adversary.** A `Q`-query machine
outputting staged strategies, equipped with a staged decode, whose Fiat–Shamir advantage beats the
query loss `(Q + k) · 3/p`, yields the deployed opening or a computed relation:
`StagedDecode.extractable_of_lt_fsAdvantage` produces a table whose output strategy carries the
full `(3,…,3)` tree, `proverAccept_forkValid` reads off the forking certificate, and the
computable `deployed_forking_relation` extracts. This staged, existence-form definition is retained
as supplementary material; the deployed arbitrary-query producer is the computable path in
`Forking.Recursive` and `Forking.Algebraic`. -/
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
