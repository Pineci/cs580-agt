import DatingAlgo.TwoCap

/-!
# Which results depend on the clock

Vault note "Ranked-Feed Model of the Dating Market", section "The clock".

A dating market runs as a sequence of events: someone is shown a profile and swipes, the
platform re-ranks, a round or a session ends. A *clock* is the order of these events.
Rios and Torrico's model has synchronized rounds; a scrolling feed has none.

**Part 1: the incentive theorems hold for every clock.** A `FeedProtocol` is what one user
faces once the platform's coins and the other users' strategies are fixed: a machine that
takes internal steps (anything that does not ask this user to swipe), asks the user to
swipe on a profile, or halts with the user's matches. The number and kind of internal
steps between two swipes is arbitrary and may depend on the user's swipes.
* `FeedProtocol.toTree`, `outcome_iff_reach`: the user's possible outcomes are exactly the
  leaves of a swipe tree. Internal steps disappear.
* `protocol_liveSet_iff` (Theorem A), `protocol_regret_le` (Theorem B),
  `protocol_keepBest` (Theorem E): the three theorems for every protocol.
* `FeedMarket.toProtocol`, `market_liveSet_iff`: a market with an arbitrary scheduler
  (who is shown whom next, as a function of the whole history) and arbitrary strategies
  of the other users is a protocol for each user, so Theorem A holds in it.
* `FeedMarket.final`, `realized`, `welfare`: the run of the whole market under a strategy
  profile. `realized_outcome`, `realized_run` tie it to the one-user protocol, and
  `market_sincere_dominant` states truthfulness for actual strategy profiles: no
  deviation by one user raises that user's realized utility.

**Part 2: the queue results do not.**
* `queue_guarantee_needs_order`: the `c_K` guarantee of the responder queue fails if a
  responder acts before the initiators have swiped; `queueConvAt_le` says waiting never
  hurts.
* `lp1_bound_needs_order`: the bound `LP_1` fails if responders swipe first. A mechanism
  that shows the initiator one responder who already accepted beats it.
* `refill_not_truthful`: refilling an unmatched initiator's feed in a second round breaks
  truthfulness, although each round shows at most `k` profiles.
-/

namespace DatingAlgo

open Finset

/-! ### Part 1: protocols -/

/-- One step of a feed protocol, seen by one user: an internal step to a new state, a
profile shown to the user with the two states that follow a like and a pass, or the end
with the user's matches. -/
inductive FeedMove (σ β : Type*) where
  | internal (s : σ) : FeedMove σ β
  | ask (x : β) (onLike onPass : σ) : FeedMove σ β
  | halt (M : Finset β) : FeedMove σ β

/-- What one user faces under any clock, once the platform's coins and the other users'
strategies are fixed. `rank` bounds the number of remaining steps. -/
structure FeedProtocol (σ β : Type*) where
  step : σ → FeedMove σ β
  rank : σ → ℕ
  rank_internal : ∀ s s', step s = FeedMove.internal s' → rank s' < rank s
  rank_like : ∀ s x l p, step s = FeedMove.ask x l p → rank l < rank s
  rank_pass : ∀ s x l p, step s = FeedMove.ask x l p → rank p < rank s

namespace FeedProtocol

variable {σ β : Type*} (P : FeedProtocol σ β)

set_option linter.unusedVariables false in
/-- The swipe tree of a protocol: skip the internal steps. -/
def toTree (s : σ) : SwipeTree β :=
  match h : P.step s with
  | FeedMove.internal s' => toTree s'
  | FeedMove.ask x l p => SwipeTree.ask x (toTree l) (toTree p)
  | FeedMove.halt M => SwipeTree.stop M
termination_by P.rank s
decreasing_by
  all_goals first
    | exact P.rank_internal _ _ h
    | exact P.rank_like _ _ _ _ h
    | exact P.rank_pass _ _ _ _ h

theorem toTree_internal {s s' : σ} (h : P.step s = FeedMove.internal s') :
    P.toTree s = P.toTree s' := by
  rw [toTree]
  split
  · rename_i t ht; rw [h] at ht; cases ht; rfl
  · rename_i x l p ht; rw [h] at ht; cases ht
  · rename_i M ht; rw [h] at ht; cases ht

theorem toTree_ask {s l p : σ} {x : β} (h : P.step s = FeedMove.ask x l p) :
    P.toTree s = SwipeTree.ask x (P.toTree l) (P.toTree p) := by
  rw [toTree]
  split
  · rename_i t ht; rw [h] at ht; cases ht
  · rename_i x' l' p' ht; rw [h] at ht; cases ht; rfl
  · rename_i M ht; rw [h] at ht; cases ht

theorem toTree_halt {s : σ} {M : Finset β} (h : P.step s = FeedMove.halt M) :
    P.toTree s = SwipeTree.stop M := by
  rw [toTree]
  split
  · rename_i t ht; rw [h] at ht; cases ht
  · rename_i x' l' p' ht; rw [h] at ht; cases ht
  · rename_i M' ht; rw [h] at ht; cases ht; rfl

/-- Induction on the number of remaining steps. -/
theorem rank_induction {C : σ → Prop} (s : σ)
    (h : ∀ s, (∀ s', P.rank s' < P.rank s → C s') → C s) : C s :=
  (measure P.rank).wf.induction s h

/-- `P.Outcome s M`: from state `s`, some way of swiping ends with the matches `M`. -/
inductive Outcome : σ → Finset β → Prop
  | halt {s : σ} {M : Finset β} : P.step s = FeedMove.halt M → Outcome s M
  | internal {s s' : σ} {M : Finset β} :
      P.step s = FeedMove.internal s' → Outcome s' M → Outcome s M
  | like {s l p : σ} {x : β} {M : Finset β} :
      P.step s = FeedMove.ask x l p → Outcome l M → Outcome s M
  | pass {s l p : σ} {x : β} {M : Finset β} :
      P.step s = FeedMove.ask x l p → Outcome p M → Outcome s M

/-- **One user's view is a swipe tree, for every clock.** The outcomes the user can reach
in the protocol are exactly the leaves of its swipe tree. -/
theorem outcome_iff_reach [DecidableEq β] (s : σ) (M : Finset β) :
    P.Outcome s M ↔ (P.toTree s).Reach M := by
  constructor
  · intro h
    induction h with
    | halt hs => rw [P.toTree_halt hs]; exact SwipeTree.Reach.stop _
    | internal hs _ ih => rw [P.toTree_internal hs]; exact ih
    | like hs _ ih => rw [P.toTree_ask hs]; exact SwipeTree.Reach.like ih
    | pass hs _ ih => rw [P.toTree_ask hs]; exact SwipeTree.Reach.pass ih
  · refine P.rank_induction (C := fun s => (P.toTree s).Reach M → P.Outcome s M) s ?_
    intro s ih hr
    cases hs : P.step s with
    | internal s' =>
      rw [P.toTree_internal hs] at hr
      exact Outcome.internal hs (ih s' (P.rank_internal s s' hs) hr)
    | ask x l p =>
      rw [P.toTree_ask hs] at hr
      cases hr with
      | like h' => exact Outcome.like hs (ih l (P.rank_like s x l p hs) h')
      | pass h' => exact Outcome.pass hs (ih p (P.rank_pass s x l p hs) h')
    | halt M' =>
      rw [P.toTree_halt hs] at hr
      cases hr
      exact Outcome.halt hs

/-- Bookkeeping that makes the protocol a valid feed: `shown s` and `liked s` are the
profiles the user has been shown and has liked on the way to `s`. Internal steps change
neither, no profile is shown twice, and the final matches are liked profiles. -/
structure Sound [DecidableEq β] (shown liked : σ → Finset β) : Prop where
  internal : ∀ s s', P.step s = FeedMove.internal s' → shown s' = shown s ∧ liked s' = liked s
  fresh : ∀ s x l p, P.step s = FeedMove.ask x l p → x ∉ shown s
  like : ∀ s x l p, P.step s = FeedMove.ask x l p →
    shown l = insert x (shown s) ∧ liked l = insert x (liked s)
  pass : ∀ s x l p, P.step s = FeedMove.ask x l p →
    shown p = insert x (shown s) ∧ liked p = liked s
  halt : ∀ s M, P.step s = FeedMove.halt M → M ⊆ liked s

theorem validFrom_toTree [DecidableEq β] {shown liked : σ → Finset β}
    (hS : P.Sound shown liked) (s : σ) : (P.toTree s).ValidFrom (shown s) (liked s) := by
  refine P.rank_induction (C := fun s => (P.toTree s).ValidFrom (shown s) (liked s)) s ?_
  intro s ih
  cases hs : P.step s with
  | internal s' =>
    have h := ih s' (P.rank_internal s s' hs)
    obtain ⟨h1, h2⟩ := hS.internal s s' hs
    rw [P.toTree_internal hs]
    rwa [h1, h2] at h
  | ask x l p =>
    have hl := ih l (P.rank_like s x l p hs)
    have hp := ih p (P.rank_pass s x l p hs)
    obtain ⟨l1, l2⟩ := hS.like s x l p hs
    obtain ⟨p1, p2⟩ := hS.pass s x l p hs
    rw [l1, l2] at hl
    rw [p1, p2] at hp
    rw [P.toTree_ask hs]
    simp only [SwipeTree.ValidFrom]
    exact ⟨hS.fresh s x l p hs, hl, hp⟩
  | halt M =>
    rw [P.toTree_halt hs]
    simp only [SwipeTree.ValidFrom]
    exact hS.halt s M hs

/-- A sound protocol started with nothing shown gives a valid swipe tree. -/
theorem valid_toTree [DecidableEq β] {shown liked : σ → Finset β} (hS : P.Sound shown liked)
    {s₀ : σ} (h0 : shown s₀ = ∅) (h1 : liked s₀ = ∅) : (P.toTree s₀).Valid := by
  have h := P.validFrom_toTree hS s₀
  rwa [h0, h1] at h

end FeedProtocol

section ProtocolTheorems

variable {σ β : Type*} [Fintype β] [DecidableEq β] (P : FeedProtocol σ β)

/-- **Theorem A for every clock.** In a sound protocol, whatever happens between the
user's swipes: no way of swiping beats sincere swiping, for every type within `δ` of the
cost, iff the user who likes exactly `X` is matched with `X ∩ S` for a fixed set `S` of at
most `k` profiles. -/
theorem protocol_liveSet_iff {shown liked : σ → Finset β} (hS : P.Sound shown liked) {s₀ : σ}
    (h0 : shown s₀ = ∅) (h1 : liked s₀ = ∅) {k : ℕ} {c d δ : ℝ} (hc : 0 < c) (hd : 0 < d)
    (hδ : 0 < δ) (hδc : δ ≤ c) :
    (∀ q : β → ℝ, (∀ x, |q x - c| < δ) → ∀ M', P.Outcome s₀ M' →
      twoCostUtil (topK q k) c d M' ≤
        twoCostUtil (topK q k) c d ((P.toTree s₀).run (sincereSet q c univ)))
      ↔ ∃ S : Finset β, S.card ≤ k ∧ ∀ X, (P.toTree s₀).run X = X ∩ S := by
  rw [← swipeTree_liveSet_iff hc hd hδ hδc (P.valid_toTree hS h0 h1)]
  constructor
  · exact fun h q hq M' hM' => h q hq M' ((P.outcome_iff_reach s₀ M').mpr hM')
  · exact fun h q hq M' hM' => h q hq M' ((P.outcome_iff_reach s₀ M').mp hM')

/-- **Theorem B for every clock.** If the user who likes exactly `X` is matched with
`X ∩ R` for a fixed set `R` of any size, then no way of swiping beats sincere swiping by
more than `d (|M| - k)^+`, where `M` is the sincere match set. -/
theorem protocol_regret_le {shown liked : σ → Finset β} (hS : P.Sound shown liked) {s₀ : σ}
    (h0 : shown s₀ = ∅) (h1 : liked s₀ = ∅) {q : β → ℝ} (hq : ∀ x, 0 ≤ q x) (k : ℕ)
    {c d : ℝ} (hd : 0 ≤ d) (hdc : d ≤ c) {R : Finset β}
    (hform : ∀ X, (P.toTree s₀).run X = X ∩ R) {M' : Finset β} (hM' : P.Outcome s₀ M') :
    twoCostUtil (topK q k) c d M' ≤
      twoCostUtil (topK q k) c d (sincereSet q c univ ∩ R) +
        d * ((sincereSet q c univ ∩ R).card - k : ℕ) := by
  obtain ⟨L, rfl⟩ := SwipeTree.exists_run_of_reach (P.valid_toTree hS h0 h1)
    ((P.outcome_iff_reach s₀ M').mp hM')
  rw [hform]
  exact twoCost_topK_regret_le hq k hd hdc univ R (subset_univ L)

omit [Fintype β] in
/-- **Theorem E for every clock.** Suppose every outcome the user can reach lies inside a
set `R`, and sincere swiping ends with a best set `W'` of at most `k` acceptable members
of `R` (the keep-best rule). Then no way of swiping beats sincere swiping. -/
theorem protocol_keepBest {s₀ : σ} {q : β → ℝ} (hq : ∀ x, 0 ≤ q x) {k : ℕ} {c d : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (N R : Finset β) (hsub : ∀ M', P.Outcome s₀ M' → M' ⊆ N ∩ R)
    {W' : Finset β} (hW' : W' ⊆ sincereSet q c N ∩ R) (hW'k : W'.card ≤ k)
    (hbest : topK (fun x => q x - c) k (sincereSet q c N ∩ R) = ∑ x ∈ W', (q x - c))
    {M' : Finset β} (hM' : P.Outcome s₀ M') :
    twoCostUtil (topK q k) c d M' ≤ twoCostUtil (topK q k) c d W' :=
  keepBest_optimal hq hc hd N R hW' hW'k hbest (hsub M' hM')

end ProtocolTheorems

/-! ### Markets with an arbitrary scheduler -/

/-- A market under any clock. In state `s` the platform either closes (`sched s = none`)
or shows user `u` the profile `x` (`sched s = some (u, x)`); `update` gives the state after
`u`'s swipe. The scheduler reads the whole state, so who acts next may depend on every
earlier swipe: rounds, sessions and continuous feeds are all schedulers. -/
structure FeedMarket (U σ : Type*) where
  sched : σ → Option (U × U)
  update : σ → U → U → Bool → σ
  matchesOf : σ → U → Finset U
  rank : σ → ℕ
  rank_lt : ∀ s u x b, sched s = some (u, x) → rank (update s u x b) < rank s

/-- The protocol user `ℓ` faces when every other user `u` swipes by `strat u`, a function
of the whole state. Swipes by other users are internal steps. -/
def FeedMarket.toProtocol {U σ : Type*} [DecidableEq U] (G : FeedMarket U σ) (ℓ : U)
    (strat : U → σ → U → Bool) : FeedProtocol σ U where
  step s :=
    match G.sched s with
    | none => FeedMove.halt (G.matchesOf s ℓ)
    | some (u, x) =>
        if u = ℓ then FeedMove.ask x (G.update s ℓ x true) (G.update s ℓ x false)
        else FeedMove.internal (G.update s u x (strat u s x))
  rank := G.rank
  rank_internal := by
    intro s s' h
    cases hs : G.sched s with
    | none => simp [hs] at h
    | some ux =>
      obtain ⟨u, x⟩ := ux
      simp only [hs] at h
      split_ifs at h with hu
      cases h
      exact G.rank_lt s u x _ hs
  rank_like := by
    intro s x l p h
    cases hs : G.sched s with
    | none => simp [hs] at h
    | some ux =>
      obtain ⟨u, x'⟩ := ux
      simp only [hs] at h
      split_ifs at h with hu
      subst hu
      cases h
      exact G.rank_lt s u x true hs
  rank_pass := by
    intro s x l p h
    cases hs : G.sched s with
    | none => simp [hs] at h
    | some ux =>
      obtain ⟨u, x'⟩ := ux
      simp only [hs] at h
      split_ifs at h with hu
      subst hu
      cases h
      exact G.rank_lt s u x false hs

/-- **Theorem A in a market with any scheduler.** Fix a market, a user `ℓ` and the other
users' strategies. If `ℓ` is never shown a profile twice and is matched only with profiles
it liked, then sincere swiping is dominant for `ℓ` iff `ℓ`'s matches are the liked
profiles inside a fixed set of at most `k`. -/
theorem market_liveSet_iff {U σ : Type*} [Fintype U] [DecidableEq U] (G : FeedMarket U σ)
    (ℓ : U) (strat : U → σ → U → Bool) {shown liked : σ → Finset U}
    (hS : (G.toProtocol ℓ strat).Sound shown liked) {s₀ : σ} (h0 : shown s₀ = ∅)
    (h1 : liked s₀ = ∅) {k : ℕ} {c d δ : ℝ} (hc : 0 < c) (hd : 0 < d) (hδ : 0 < δ)
    (hδc : δ ≤ c) :
    (∀ q : U → ℝ, (∀ x, |q x - c| < δ) → ∀ M', (G.toProtocol ℓ strat).Outcome s₀ M' →
      twoCostUtil (topK q k) c d M' ≤
        twoCostUtil (topK q k) c d
          (((G.toProtocol ℓ strat).toTree s₀).run (sincereSet q c univ)))
      ↔ ∃ S : Finset U, S.card ≤ k ∧
          ∀ X, ((G.toProtocol ℓ strat).toTree s₀).run X = X ∩ S :=
  protocol_liveSet_iff (G.toProtocol ℓ strat) hS h0 h1 hc hd hδ hδc

/-! ### The whole market: realized outcomes for a strategy profile -/

namespace FeedMarket

variable {U σ : Type*} [DecidableEq U] (G : FeedMarket U σ)

set_option linter.unusedVariables false in
/-- The state in which the market closes when every user `u` swipes by `strat u`. -/
def final (strat : U → σ → U → Bool) (s : σ) : σ :=
  match h : G.sched s with
  | none => s
  | some (u, x) => final strat (G.update s u x (strat u s x))
termination_by G.rank s
decreasing_by exact G.rank_lt _ _ _ _ h

/-- User `ℓ`'s matches under the strategy profile `strat`. -/
def realized (strat : U → σ → U → Bool) (s : σ) (ℓ : U) : Finset U :=
  G.matchesOf (G.final strat s) ℓ

/-- Welfare of a strategy profile, for any utility of a user's match set. -/
def welfare [Fintype U] (util : U → Finset U → ℝ) (strat : U → σ → U → Bool) (s : σ) : ℝ :=
  ∑ ℓ, util ℓ (G.realized strat s ℓ)

omit [DecidableEq U] in
theorem final_none {strat : U → σ → U → Bool} {s : σ} (h : G.sched s = none) :
    G.final strat s = s := by
  rw [final]
  split
  · rfl
  · rename_i u x hs; rw [h] at hs; cases hs

omit [DecidableEq U] in
theorem final_some {strat : U → σ → U → Bool} {s : σ} {u x : U}
    (h : G.sched s = some (u, x)) :
    G.final strat s = G.final strat (G.update s u x (strat u s x)) := by
  rw [final]
  split
  · rename_i hs; rw [h] at hs; cases hs
  · rename_i u' x' hs; rw [h] at hs; cases hs; rfl

theorem toProtocol_step_none {ℓ : U} {strat : U → σ → U → Bool} {s : σ}
    (h : G.sched s = none) :
    (G.toProtocol ℓ strat).step s = FeedMove.halt (G.matchesOf s ℓ) := by
  simp [toProtocol, h]

theorem toProtocol_step_self {ℓ : U} {strat : U → σ → U → Bool} {s : σ} {x : U}
    (h : G.sched s = some (ℓ, x)) :
    (G.toProtocol ℓ strat).step s =
      FeedMove.ask x (G.update s ℓ x true) (G.update s ℓ x false) := by
  simp [toProtocol, h]

theorem toProtocol_step_other {ℓ : U} {strat : U → σ → U → Bool} {s : σ} {u x : U}
    (h : G.sched s = some (u, x)) (hu : u ≠ ℓ) :
    (G.toProtocol ℓ strat).step s = FeedMove.internal (G.update s u x (strat u s x)) := by
  simp [toProtocol, h, hu]

omit [DecidableEq U] in
theorem rank_induction {C : σ → Prop} (s : σ)
    (h : ∀ s, (∀ s', G.rank s' < G.rank s → C s') → C s) : C s :=
  (measure G.rank).wf.induction s h

/-- **Realized outcomes are protocol outcomes.** Whatever `ℓ` does, as long as the others
play `strat`, `ℓ`'s realized matches are an outcome of the protocol `ℓ` faces. -/
theorem realized_outcome (ℓ : U) (strat strat' : U → σ → U → Bool)
    (hagree : ∀ u, u ≠ ℓ → strat' u = strat u) (s : σ) :
    (G.toProtocol ℓ strat).Outcome s (G.realized strat' s ℓ) := by
  unfold realized
  refine G.rank_induction
    (C := fun s => (G.toProtocol ℓ strat).Outcome s (G.matchesOf (G.final strat' s) ℓ)) s ?_
  intro s ih
  cases hs : G.sched s with
  | none =>
    rw [G.final_none hs]
    exact FeedProtocol.Outcome.halt (G.toProtocol_step_none hs)
  | some ux =>
    obtain ⟨u, x⟩ := ux
    rw [G.final_some hs]
    by_cases hu : u = ℓ
    · subst hu
      have hrec := ih (G.update s u x (strat' u s x)) (G.rank_lt s u x _ hs)
      cases hb : strat' u s x
      · rw [hb] at hrec
        exact FeedProtocol.Outcome.pass (G.toProtocol_step_self hs) hrec
      · rw [hb] at hrec
        exact FeedProtocol.Outcome.like (G.toProtocol_step_self hs) hrec
    · have hrec := ih (G.update s u x (strat u s x)) (G.rank_lt s u x _ hs)
      rw [hagree u hu]
      exact FeedProtocol.Outcome.internal (G.toProtocol_step_other hs hu) hrec

omit [DecidableEq U] in
theorem run_ask_of_mem {x : U} {l p : SwipeTree U} {X : Finset U} [DecidableEq U]
    (h : x ∈ X) : (SwipeTree.ask x l p).run X = l.run X := by
  simp [SwipeTree.run, h]

omit [DecidableEq U] in
theorem run_ask_of_notMem {x : U} {l p : SwipeTree U} {X : Finset U} [DecidableEq U]
    (h : x ∉ X) : (SwipeTree.ask x l p).run X = p.run X := by
  simp [SwipeTree.run, h]

/-- If `ℓ` likes exactly the shown profiles in `X` and the others play `strat`, `ℓ`'s
realized matches are the leaf of `X` in the swipe tree. -/
theorem realized_run (ℓ : U) (strat strat' : U → σ → U → Bool)
    (hagree : ∀ u, u ≠ ℓ → strat' u = strat u) (X : Finset U)
    (hX : ∀ s x, strat' ℓ s x = decide (x ∈ X)) (s : σ) :
    G.realized strat' s ℓ = ((G.toProtocol ℓ strat).toTree s).run X := by
  unfold realized
  refine G.rank_induction
    (C := fun s => G.matchesOf (G.final strat' s) ℓ = ((G.toProtocol ℓ strat).toTree s).run X)
    s ?_
  intro s ih
  cases hs : G.sched s with
  | none =>
    rw [G.final_none hs, (G.toProtocol ℓ strat).toTree_halt (G.toProtocol_step_none hs)]
    rfl
  | some ux =>
    obtain ⟨u, x⟩ := ux
    rw [G.final_some hs]
    by_cases hu : u = ℓ
    · subst hu
      rw [(G.toProtocol u strat).toTree_ask (G.toProtocol_step_self hs), hX]
      by_cases hx : x ∈ X
      · rw [run_ask_of_mem hx, decide_eq_true hx]
        exact ih _ (G.rank_lt s u x true hs)
      · rw [run_ask_of_notMem hx, decide_eq_false hx]
        exact ih _ (G.rank_lt s u x false hs)
    · rw [(G.toProtocol ℓ strat).toTree_internal (G.toProtocol_step_other hs hu), hagree u hu]
      exact ih _ (G.rank_lt s u x _ hs)

end FeedMarket

/-- **Truthfulness in the whole market, under any clock.** Fix a market with any scheduler
and the strategies `strat` of the users other than `ℓ`. Suppose `ℓ` is matched with the
liked profiles inside a fixed set `S` of at most `k`. Then for every strategy `dev` of
`ℓ`, `ℓ`'s realized utility is at most its realized utility from swiping sincerely. -/
theorem market_sincere_dominant {U σ : Type*} [Fintype U] [DecidableEq U] (G : FeedMarket U σ)
    (ℓ : U) (strat : U → σ → U → Bool) {shown liked : σ → Finset U}
    (hS : (G.toProtocol ℓ strat).Sound shown liked) {s₀ : σ} (h0 : shown s₀ = ∅)
    (h1 : liked s₀ = ∅) {q : U → ℝ} (hq : ∀ x, 0 ≤ q x) {k : ℕ} {c d : ℝ} (hd : 0 ≤ d)
    {S : Finset U} (hSk : S.card ≤ k)
    (hform : ∀ X, ((G.toProtocol ℓ strat).toTree s₀).run X = X ∩ S)
    (dev sinc : U → σ → U → Bool) (hdev : ∀ u, u ≠ ℓ → dev u = strat u)
    (hsinc : ∀ u, u ≠ ℓ → sinc u = strat u) (hs : ∀ s x, sinc ℓ s x = decide (c < q x)) :
    twoCostUtil (topK q k) c d (G.realized dev s₀ ℓ) ≤
      twoCostUtil (topK q k) c d (G.realized sinc s₀ ℓ) := by
  have hs' : ∀ s x, sinc ℓ s x = decide (x ∈ sincereSet q c univ) := fun s x => by
    have hmem : x ∈ sincereSet q c univ ↔ c < q x := by simp [sincereSet]
    rw [hs]
    exact decide_eq_decide.mpr hmem.symm
  have hrun := G.realized_run ℓ strat sinc hsinc (sincereSet q c univ) hs' s₀
  have hreach := ((G.toProtocol ℓ strat).outcome_iff_reach s₀ _).mp
    (G.realized_outcome ℓ strat dev hdev s₀)
  obtain ⟨L, hL⟩ := SwipeTree.exists_run_of_reach
    ((G.toProtocol ℓ strat).valid_toTree hS h0 h1) hreach
  rw [hrun, hform, ← hL, hform]
  exact twoCost_sincere_best_topK hq hd hSk univ (subset_univ L)

/-! ### Part 2: the queue results depend on the clock -/

section QueueTiming

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]

/-- Expected conversations if responder `j` acts when only the initiators in `T j` have
swiped. `queueConv` is the case where every initiator has. -/
noncomputable def queueConvAt (kJ : J → ℕ) (θ : I → J → ℝ) (T : J → Finset I) : ℝ :=
  ∑ j, indepExp (T j) (fun i => θ i j) (fun A => min (A.card : ℝ) (kJ j))

theorem queueConvAt_univ (kJ : J → ℕ) (θ : I → J → ℝ) :
    queueConvAt kJ θ (fun _ => univ) = queueConv kJ θ := rfl

/-- Letting a responder wait for more initiators never lowers expected conversations. -/
theorem queueConvAt_le {kJ : J → ℕ} {θ : I → J → ℝ} (hθ : ∀ i j, 0 ≤ θ i j ∧ θ i j ≤ 1)
    (T : J → Finset I) : queueConvAt kJ θ T ≤ queueConv kJ θ := by
  unfold queueConvAt queueConv
  refine sum_le_sum fun j _ => ?_
  refine indepExp_le_of_subset_of_monotone (fun i _ => hθ i j) (subset_univ _) ?_
  intro A B hAB _
  exact min_le_min (by exact_mod_cast card_le_card hAB) le_rfl

omit [Fintype I] in
/-- A responder who acts before any initiator has swiped has no conversations. -/
theorem queueConvAt_empty (kJ : J → ℕ) (θ : I → J → ℝ) :
    queueConvAt kJ θ (fun _ => ∅) = 0 := by
  simp [queueConvAt, indepExp]

end QueueTiming

/-- **The queue's guarantee needs responders to act after initiators.** With one initiator
and one responder who are sure to like each other, the plan's LP objective is 1, but if
the responder looks at its queue first there are no conversations. So
`cK K * fluidConv ≤ queueConv` (`queueConv_ge`) has no analogue for an arbitrary clock. -/
theorem queue_guarantee_needs_order :
    ∃ (kJ : Unit → ℕ) (θ : Unit → Unit → ℝ) (T : Unit → Finset Unit),
      (∀ i j, 0 ≤ θ i j ∧ θ i j ≤ 1) ∧ queueConvAt kJ θ T < cK 1 * fluidConv kJ θ := by
  refine ⟨fun _ => 1, fun _ _ => 1, fun _ => ∅, fun _ _ => ⟨zero_le_one, le_rfl⟩, ?_⟩
  rw [queueConvAt_empty]
  have h1 : fluidConv (fun _ : Unit => 1) (fun (_ : Unit) (_ : Unit) => (1 : ℝ)) = 1 := by
    simp [fluidConv]
  have h2 : (0 : ℝ) < 1 - Real.exp (-1) := by
    have := Real.exp_lt_exp.mpr (show (-1 : ℝ) < 0 by norm_num)
    rw [Real.exp_zero] at this
    linarith
  have h3 := one_sub_exp_neg_one_le_cK (K := 1) le_rfl
  rw [h1]
  linarith

/-- **The bound `LP_1` needs the display to come before both swipes.** One initiator who
likes everyone, two responders who each accept with probability `1/2`. If the responders
swipe first and the platform then shows the initiator one responder who accepted, the
initiator is shown at most one profile, yet expected conversations are `3/4`, more than
`LP_1`'s objective at every plan that shows at most one profile. -/
theorem lp1_bound_needs_order :
    ∃ (w : Bool × Bool → ℝ) (A : Bool × Bool → Bool → Finset Unit),
      (∀ ω, 0 ≤ w ω) ∧ ∑ ω, w ω = 1 ∧
      (∀ ω, (univ.filter fun j => () ∈ A ω j).card ≤ 1) ∧
      ∀ x : Unit → Bool → ℝ, (∀ i j, 0 ≤ x i j) → (∀ i, ∑ j, x i j ≤ 1) →
        fluidConv (fun _ => 1) (fun i j => x i j * 1 * (1 / 2)) <
          ∑ j, ∑ ω, w ω * min ((A ω j).card : ℝ) ((1 : ℕ) : ℝ) := by
  refine ⟨fun _ => 1 / 4,
    fun ω j => if (j = true ∧ ω.1 = true) ∨ (j = false ∧ ω.1 = false ∧ ω.2 = true)
      then {()} else ∅, fun _ => by norm_num, ?_, ?_, ?_⟩
  · simp
  · decide
  · intro x hx0 hx1
    have hval : ∑ j : Bool, ∑ ω : Bool × Bool, (1 / 4 : ℝ) *
        min (((if (j = true ∧ ω.1 = true) ∨ (j = false ∧ ω.1 = false ∧ ω.2 = true)
          then ({()} : Finset Unit) else ∅).card : ℝ)) ((1 : ℕ) : ℝ) = 3 / 4 := by
      simp [Fintype.sum_prod_type]
      norm_num
    rw [hval]
    have hsum := hx1 ()
    rw [Fintype.sum_bool] at hsum
    have hb1 : min (x () true * 1 * (1 / 2)) ((1 : ℕ) : ℝ) ≤ x () true * 1 * (1 / 2) :=
      min_le_left _ _
    have hb2 : min (x () false * 1 * (1 / 2)) ((1 : ℕ) : ℝ) ≤ x () false * 1 * (1 / 2) :=
      min_le_left _ _
    simp only [fluidConv, Fintype.sum_bool, Finset.univ_unique, Finset.sum_singleton,
      PUnit.default_eq_unit]
    linarith

/-- A single match is worth its net value if kept, or costs `d` if dropped. -/
theorem twoCostUtil_topK_singleton {β : Type*} [DecidableEq β] {q : β → ℝ}
    (hq : ∀ x, 0 ≤ q x) {k : ℕ} (hk : 1 ≤ k) (c d : ℝ) (x : β) :
    twoCostUtil (topK q k) c d {x} = max (q x - c) (-d) := by
  apply le_antisymm
  · simpa using twoCostUtil_topK_le_sum hq k c d {x}
  · apply max_le
    · have h := le_twoCostUtil (topK q k) c d (subset_refl ({x} : Finset β))
      rw [topK_singleton hq hk] at h
      simpa using h
    · have h := le_twoCostUtil (topK q k) c d (empty_subset ({x} : Finset β))
      rw [topK_empty] at h
      simpa using h

/-- A two-round feed for a user who wants one partner. Round 1 shows profile `0`, who
would match. Round 2 shows profile `1`, who would also match, only if the user has no
match after round 1. -/
def refillRule (X : Finset (Fin 2)) : Finset (Fin 2) :=
  if 0 ∈ X then {0} else if 1 ∈ X then {1} else ∅

/-- **Refilling over rounds breaks truthfulness.** Each round shows one profile to a user
who wants one partner, so each round alone is exactly truthful. But the second round
depends on the user's first swipe: a user who values profile `0` at 2 and profile `1` at 5
(cost 1) gets 1 by swiping sincerely and 4 by passing on profile `0`. -/
theorem refill_not_truthful {d : ℝ} (hd : 0 ≤ d) :
    ∃ q : Fin 2 → ℝ, (∀ x, 0 ≤ q x) ∧ ∃ X' : Finset (Fin 2),
      twoCostUtil (topK q 1) 1 d (refillRule (sincereSet q 1 univ)) <
        twoCostUtil (topK q 1) 1 d (refillRule X') := by
  have hq : ∀ x : Fin 2, 0 ≤ (![2, 5] : Fin 2 → ℝ) x := by
    intro x; fin_cases x <;> simp
  refine ⟨![2, 5], hq, {1}, ?_⟩
  have h0 : (0 : Fin 2) ∈ sincereSet (![2, 5] : Fin 2 → ℝ) 1 univ := by
    simp [sincereSet]
  have hs : refillRule (sincereSet (![2, 5] : Fin 2 → ℝ) 1 univ) = {0} := by
    simp [refillRule, h0]
  have hd' : refillRule ({1} : Finset (Fin 2)) = {1} := by
    simp [refillRule]
  rw [hs, hd', twoCostUtil_topK_singleton hq le_rfl, twoCostUtil_topK_singleton hq le_rfl]
  have e0 : max ((![2, 5] : Fin 2 → ℝ) 0 - 1) (-d) = 1 := by
    rw [max_eq_left] <;> simp <;> linarith
  have e1 : max ((![2, 5] : Fin 2 → ℝ) 1 - 1) (-d) = 4 := by
    rw [max_eq_left] <;> simp <;> linarith
  rw [e0, e1]
  norm_num

end DatingAlgo
