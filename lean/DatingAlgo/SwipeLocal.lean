import DatingAlgo.TruthfulSwiping

/-!
# Swipe-local policies: Lemma 1′ and DSIC in general

Lemma 1′ and Theorem 5(a, b) of the vault note "Truthful Swiping with an LLM Oracle" for
every swipe-local two-period policy, not only SDH, and the counting step of
Proposition 5(b) (swipe budgets).

**Model.** Fix one realization of values, oracle answers and platform coins. A
*swipe-local* policy then consists of
* the period-1 displays `d ℓ`: the profiles `ℓ` sees in period 1;
* a period-2 rule `g r B ⊆ B`: which members of `r`'s backlog `B` it shows `r`.

A pair seen both ways in period 1 is a *mutual view* and matches iff both like. A one-way
period-1 display `x ∈ d ℓ` is an *initiation*: if `ℓ` likes `x`, then `ℓ` joins `x`'s
backlog, and the pair matches iff `x` is shown `ℓ` in period 2 and likes `ℓ` back. The
period-2 rule may depend on the backlog in any way, so DH-int, weighted DH-int,
credit-DH and SDH are all swipe-local: their period-2 rules use only the responder's
backlog and data no swipe changes (values, oracle answers, coins).

Strategies are `SwipeProfile`s: period-1 likes, and period-2 responses that may depend on
the display in any way, so users may react to what they see.

**Results.**
* `seen_update`, `matchSet_update`, `wouldMatch_update` (Lemma 1′): what `ℓ` sees does not
  depend on `ℓ`'s strategy, and `ℓ`'s matches are `D ∩ R`, where `D` is what `ℓ` likes
  among the profiles it sees and `R` does not depend on `ℓ`'s strategy.
* `swipeLocal_dsic` (Theorem 5): if the acceptable profiles `ℓ` sees are cost-separable,
  sincere swiping is a best response to every behavior of the others.
  `swipeLocal_dsic_additive` (Theorem 5(b)): DH-int, weighted DH-int and credit-DH are
  universally DSIC for additive users. `swipeLocal_dsic_topK`: top-`k` users who see at
  most `k` acceptable profiles.
* `matchSet_card_le_budget` (Proposition 5(b)): with at most `K` profiles shown and at
  most `L` likes per period, a user makes at most `min(K, L)` matches per period.
-/

namespace DatingAlgo

open Finset

/-- A swipe-local two-period policy, for a fixed realization of values, oracle answers
and coins. -/
structure SwipeLocalPolicy (U : Type*) where
  /-- Period-1 displays. -/
  d : U → Finset U
  /-- Period-2 rule: which members of a backlog to show. -/
  g : U → Finset U → Finset U
  g_subset : ∀ r B, g r B ⊆ B
  d_irrefl : ∀ u, u ∉ d u

namespace SwipeLocalPolicy

variable {U : Type*} [Fintype U] [DecidableEq U] (P : SwipeLocalPolicy U)

/-- `r`'s backlog: users who initiated toward `r` (one-way) and liked `r`. -/
def backlog (σ : SwipeProfile U) (r : U) : Finset U :=
  univ.filter fun s => r ∈ P.d s ∧ s ∉ P.d r ∧ σ.like1 s r = true

/-- `r`'s period-2 display. -/
def disp2 (σ : SwipeProfile U) (r : U) : Finset U :=
  P.g r (P.backlog σ r)

/-- The profiles `ℓ` sees over both periods. -/
def seen (σ : SwipeProfile U) (ℓ : U) : Finset U :=
  P.d ℓ ∪ P.disp2 σ ℓ

/-- `ℓ`'s matches: mutual views with two likes, initiations liked back in period 2, and
period-2 responses. -/
def matchSet (σ : SwipeProfile U) (ℓ : U) : Finset U :=
  ((P.d ℓ).filter fun x => ℓ ∈ P.d x ∧ σ.like1 ℓ x = true ∧ σ.like1 x ℓ = true) ∪
    ((P.d ℓ).filter fun x => ℓ ∉ P.d x ∧ σ.like1 ℓ x = true ∧ ℓ ∈ P.disp2 σ x ∧
      ℓ ∈ σ.resp x (P.disp2 σ x)) ∪
    (P.disp2 σ ℓ).filter fun x => x ∈ σ.resp ℓ (P.disp2 σ ℓ)

/-- What `ℓ` likes among the profiles it sees under strategy `(L, ρ)`. -/
def liked (σ : SwipeProfile U) (ℓ : U) (L : U → Bool) (ρ : Finset U → Finset U) :
    Finset U :=
  ((P.d ℓ).filter fun x => L x = true) ∪ (P.disp2 σ ℓ).filter fun x => x ∈ ρ (P.disp2 σ ℓ)

/-- The profiles that would match `ℓ` if `ℓ` liked them: in a mutual view, those who like
`ℓ`; for an initiation, those who would show and like `ℓ` back after `ℓ`'s like; and
everyone in `ℓ`'s period-2 display, who already liked `ℓ`. -/
def wouldMatch (σ : SwipeProfile U) (ℓ : U) : Finset U :=
  ((P.d ℓ).filter fun x => (ℓ ∈ P.d x ∧ σ.like1 x ℓ = true) ∨
      (ℓ ∉ P.d x ∧ ℓ ∈ P.disp2 (σ.update ℓ (fun _ => true) (σ.resp ℓ)) x ∧
        ℓ ∈ σ.resp x (P.disp2 (σ.update ℓ (fun _ => true) (σ.resp ℓ)) x))) ∪
    P.disp2 σ ℓ

/-- `r`'s backlog depends only on the likes of those who see `r` in period 1. -/
theorem backlog_congr {σ τ : SwipeProfile U} {r : U}
    (h : ∀ s, r ∈ P.d s → σ.like1 s r = τ.like1 s r) : P.backlog σ r = P.backlog τ r := by
  ext s
  simp only [backlog, mem_filter, mem_univ, true_and]
  exact and_congr_right fun h1 => by rw [h s h1]

/-- `r`'s period-2 display depends only on the likes of those who see `r` in period 1. -/
theorem disp2_congr {σ τ : SwipeProfile U} {r : U}
    (h : ∀ s, r ∈ P.d s → σ.like1 s r = τ.like1 s r) : P.disp2 σ r = P.disp2 τ r := by
  rw [disp2, disp2, P.backlog_congr h]

/-- A member of `r`'s period-2 display initiated toward `r`, liked `r`, and was not shown
to `r` in period 1. -/
theorem mem_disp2 {σ : SwipeProfile U} {r x : U} (hx : x ∈ P.disp2 σ r) :
    r ∈ P.d x ∧ x ∉ P.d r ∧ σ.like1 x r = true := by
  have := P.g_subset r _ hx
  simp only [backlog, mem_filter, mem_univ, true_and] at this
  exact this

/-- `ℓ`'s period-2 display does not depend on `ℓ`'s strategy. -/
theorem disp2_update_self (σ : SwipeProfile U) (ℓ : U) (L : U → Bool)
    (ρ : Finset U → Finset U) : P.disp2 (σ.update ℓ L ρ) ℓ = P.disp2 σ ℓ := by
  refine P.disp2_congr fun s hs => ?_
  have : s ≠ ℓ := fun h => P.d_irrefl ℓ (h ▸ hs)
  rw [SwipeProfile.update_like1_of_ne σ this]

/-- **Lemma 1′, first part.** What `ℓ` sees does not depend on `ℓ`'s strategy. -/
theorem seen_update (σ : SwipeProfile U) (ℓ : U) (L : U → Bool) (ρ : Finset U → Finset U) :
    P.seen (σ.update ℓ L ρ) ℓ = P.seen σ ℓ := by
  rw [seen, seen, P.disp2_update_self]

/-- **Lemma 1′, second part.** `R = wouldMatch σ ℓ` does not depend on `ℓ`'s strategy. -/
theorem wouldMatch_update (σ : SwipeProfile U) (ℓ : U) (L : U → Bool)
    (ρ : Finset U → Finset U) : P.wouldMatch (σ.update ℓ L ρ) ℓ = P.wouldMatch σ ℓ := by
  have hT : ∀ x, P.disp2 ((σ.update ℓ L ρ).update ℓ (fun _ => true)
      ((σ.update ℓ L ρ).resp ℓ)) x = P.disp2 (σ.update ℓ (fun _ => true) (σ.resp ℓ)) x :=
    fun x => P.disp2_congr fun s _ => by
      by_cases hs : s = ℓ <;> simp [SwipeProfile.update, hs]
  unfold wouldMatch
  rw [P.disp2_update_self]
  congr 1
  refine filter_congr fun x hx => ?_
  have hxℓ : x ≠ ℓ := fun h => P.d_irrefl ℓ (h ▸ hx)
  rw [SwipeProfile.update_like1_of_ne σ hxℓ, SwipeProfile.update_resp_of_ne σ hxℓ, hT x]

/-- **Lemma 1′ (one swipe, one event).** Whatever `ℓ` does, its matches are `D ∩ R`:
`D` is what it likes among the profiles it sees, and `R = wouldMatch σ ℓ` does not
depend on its strategy. The others' strategies are arbitrary and may react to what they
see. -/
theorem matchSet_update (σ : SwipeProfile U) (ℓ : U) (L : U → Bool)
    (ρ : Finset U → Finset U) :
    P.matchSet (σ.update ℓ L ρ) ℓ = P.liked σ ℓ L ρ ∩ P.wouldMatch σ ℓ := by
  -- After `ℓ` likes `x`, `x`'s period-2 display is as if `ℓ` liked everyone.
  have hD : ∀ x, L x = true → P.disp2 (σ.update ℓ L ρ) x =
      P.disp2 (σ.update ℓ (fun _ => true) (σ.resp ℓ)) x := fun x hx =>
    P.disp2_congr fun s _ => by by_cases hs : s = ℓ <;> simp [SwipeProfile.update, hs, hx]
  ext x
  simp only [matchSet, liked, wouldMatch, mem_union, mem_inter, mem_filter,
    P.disp2_update_self, SwipeProfile.update_like1_self, SwipeProfile.update_resp_self]
  constructor
  · rintro ((⟨hx1, hx2, hx3, hx4⟩ | ⟨hx1, hx2, hx3, hx4, hx5⟩) | ⟨hx1, hx2⟩)
    · have hxℓ : x ≠ ℓ := fun h => P.d_irrefl ℓ (h ▸ hx1)
      rw [SwipeProfile.update_like1_of_ne σ hxℓ] at hx4
      exact ⟨Or.inl ⟨hx1, hx3⟩, Or.inl ⟨hx1, Or.inl ⟨hx2, hx4⟩⟩⟩
    · have hxℓ : x ≠ ℓ := fun h => P.d_irrefl ℓ (h ▸ hx1)
      rw [SwipeProfile.update_resp_of_ne σ hxℓ, hD x hx3] at hx5
      rw [hD x hx3] at hx4
      exact ⟨Or.inl ⟨hx1, hx3⟩, Or.inl ⟨hx1, Or.inr ⟨hx2, hx4, hx5⟩⟩⟩
    · exact ⟨Or.inr ⟨hx1, hx2⟩, Or.inr hx1⟩
  · rintro ⟨⟨hx1, hx2⟩ | ⟨hx1, hx2⟩, ⟨hy1, ⟨hy2, hy3⟩ | ⟨hy2, hy3, hy4⟩⟩ | hy⟩
    · have hxℓ : x ≠ ℓ := fun h => P.d_irrefl ℓ (h ▸ hx1)
      rw [SwipeProfile.update_like1_of_ne σ hxℓ]
      exact Or.inl (Or.inl ⟨hx1, hy2, hx2, hy3⟩)
    · have hxℓ : x ≠ ℓ := fun h => P.d_irrefl ℓ (h ▸ hx1)
      rw [SwipeProfile.update_resp_of_ne σ hxℓ, hD x hx2]
      exact Or.inl (Or.inr ⟨hx1, hy2, hx2, hy3, hy4⟩)
    · exact absurd hx1 (P.mem_disp2 hy).2.1
    · exact absurd hy1 (P.mem_disp2 hx1).2.1
    · exact absurd hy1 (P.mem_disp2 hx1).2.1
    · exact Or.inr ⟨hx1, hx2⟩

/-- What `ℓ` likes is among what it sees. -/
theorem liked_subset_seen (σ : SwipeProfile U) (ℓ : U) (L : U → Bool)
    (ρ : Finset U → Finset U) : P.liked σ ℓ L ρ ⊆ P.seen σ ℓ :=
  union_subset_union (filter_subset _ _) (filter_subset _ _)

/-- Sincere play likes exactly the acceptable profiles seen. -/
theorem liked_sincere (σ : SwipeProfile U) (q : U → U → ℝ) (c : U → ℝ) (ℓ : U) :
    P.liked σ ℓ (sincereLike q c ℓ) (sincereResp q c ℓ) =
      sincereSet (q ℓ) (c ℓ) (P.seen σ ℓ) := by
  ext x
  simp only [liked, sincereSet, seen, sincereLike, sincereResp, mem_union, mem_filter,
    decide_eq_true_eq]
  tauto

/-- **Theorem 5: DSIC for swipe-local policies.** Suppose `ℓ`'s value is subadditive with
`v {x} = q ℓ x`, and the acceptable profiles `ℓ` sees are cost-separable. Then against
every behavior `σ` of the others, including strategies that react to what they see,
sincere swiping gives `ℓ` at least as much as any deviation `(L, ρ)`. -/
theorem swipeLocal_dsic {q : U → U → ℝ} {c : U → ℝ} {ℓ : U} {v : Finset U → ℝ}
    (hsub : ∀ S T, v (S ∪ T) ≤ v S + v T) (hsingle : ∀ x, v {x} = q ℓ x)
    (σ : SwipeProfile U) (hsep : CostSeparable v (c ℓ) (sincereSet (q ℓ) (c ℓ) (P.seen σ ℓ)))
    (L : U → Bool) (ρ : Finset U → Finset U) :
    swipeUtil v (c ℓ) (P.matchSet (σ.update ℓ L ρ) ℓ) ≤
      swipeUtil v (c ℓ) (P.matchSet (σ.update ℓ (sincereLike q c ℓ) (sincereResp q c ℓ)) ℓ) := by
  rw [P.matchSet_update, P.matchSet_update, P.liked_sincere]
  exact sincere_best hsub hsingle hsep _ (P.liked_subset_seen σ ℓ L ρ)

/-- **Theorem 5(b): additive users.** Under every swipe-local policy (DH-int, weighted
DH-int, credit-DH, SDH) sincere swiping is dominant for an additive user with
non-negative values, against every behavior of the others. -/
theorem swipeLocal_dsic_additive {q : U → U → ℝ} {c : U → ℝ} {ℓ : U}
    (hq : ∀ x, 0 ≤ q ℓ x) (σ : SwipeProfile U) (L : U → Bool) (ρ : Finset U → Finset U) :
    swipeUtil (fun S => ∑ x ∈ S, q ℓ x) (c ℓ) (P.matchSet (σ.update ℓ L ρ) ℓ) ≤
      swipeUtil (fun S => ∑ x ∈ S, q ℓ x) (c ℓ)
        (P.matchSet (σ.update ℓ (sincereLike q c ℓ) (sincereResp q c ℓ)) ℓ) := by
  refine P.swipeLocal_dsic (fun S T => ?_) (fun x => sum_singleton _ _) σ
    (costSeparable_sum (q ℓ) (c ℓ) _) L ρ
  have h := sum_union_inter (s₁ := S) (s₂ := T) (f := q ℓ)
  have h0 : 0 ≤ ∑ x ∈ S ∩ T, q ℓ x := sum_nonneg fun x _ => hq x
  linarith

/-- **Theorem 1, top-`k` corollary, for swipe-local policies.** A top-`k` user (`k ≥ 1`,
`c > 0`) who sees at most `k` acceptable profiles has sincere swiping as a best response. -/
theorem swipeLocal_dsic_topK {q : U → U → ℝ} {c : U → ℝ} {ℓ : U} (hq : ∀ x, 0 ≤ q ℓ x)
    {k : ℕ} (hk : 1 ≤ k) (hc : 0 < c ℓ) (σ : SwipeProfile U)
    (hcard : (sincereSet (q ℓ) (c ℓ) (P.seen σ ℓ)).card ≤ k)
    (L : U → Bool) (ρ : Finset U → Finset U) :
    swipeUtil (topK (q ℓ) k) (c ℓ) (P.matchSet (σ.update ℓ L ρ) ℓ) ≤
      swipeUtil (topK (q ℓ) k) (c ℓ)
        (P.matchSet (σ.update ℓ (sincereLike q c ℓ) (sincereResp q c ℓ)) ℓ) := by
  have hA : ∀ x ∈ sincereSet (q ℓ) (c ℓ) (P.seen σ ℓ), c ℓ < q ℓ x :=
    fun x hx => (mem_filter.mp hx).2
  exact P.swipeLocal_dsic (topK_union_le (q ℓ) k) (topK_singleton hq hk) σ
    ((costSeparable_topK_iff hq k hc hA).mpr hcard) L ρ

/-- Every match is a profile `ℓ` liked: in period 1 among `d ℓ`, or in period 2 among its
display. -/
theorem matchSet_subset (σ : SwipeProfile U) (ℓ : U) :
    P.matchSet σ ℓ ⊆ ((P.d ℓ).filter fun x => σ.like1 ℓ x = true) ∪
      (P.disp2 σ ℓ).filter fun x => x ∈ σ.resp ℓ (P.disp2 σ ℓ) := by
  intro x hx
  simp only [matchSet, mem_union, mem_filter] at hx ⊢
  rcases hx with (⟨h1, _, h3, _⟩ | ⟨h1, _, h3, _⟩) | h
  · exact Or.inl ⟨h1, h3⟩
  · exact Or.inl ⟨h1, h3⟩
  · exact Or.inr h

/-- **Proposition 5(b), counting step.** If `ℓ` is shown at most `K` profiles per period
and likes at most `L` per period, it makes at most `min(K, L)` matches in each period.
So a full-information policy facing budgets is a policy with caps `min(K, L)`. -/
theorem matchSet_card_le_budget (σ : SwipeProfile U) (ℓ : U) {K L : ℕ}
    (hd : (P.d ℓ).card ≤ K) (hg : (P.disp2 σ ℓ).card ≤ K)
    (h1 : ((P.d ℓ).filter fun x => σ.like1 ℓ x = true).card ≤ L)
    (h2 : ((P.disp2 σ ℓ).filter fun x => x ∈ σ.resp ℓ (P.disp2 σ ℓ)).card ≤ L) :
    (P.matchSet σ ℓ ∩ P.d ℓ).card ≤ min K L ∧ (P.matchSet σ ℓ ∩ P.disp2 σ ℓ).card ≤ min K L := by
  have hsub := P.matchSet_subset σ ℓ
  have h1' : P.matchSet σ ℓ ∩ P.d ℓ ⊆ (P.d ℓ).filter fun x => σ.like1 ℓ x = true := by
    intro x hx
    obtain ⟨hxM, hxd⟩ := mem_inter.mp hx
    rcases mem_union.mp (hsub hxM) with h | h
    · exact h
    · exact absurd hxd (P.mem_disp2 (mem_filter.mp h).1).2.1
  have h2' : P.matchSet σ ℓ ∩ P.disp2 σ ℓ ⊆
      (P.disp2 σ ℓ).filter fun x => x ∈ σ.resp ℓ (P.disp2 σ ℓ) := by
    intro x hx
    obtain ⟨hxM, hxg⟩ := mem_inter.mp hx
    rcases mem_union.mp (hsub hxM) with h | h
    · exact absurd (mem_filter.mp h).1 (P.mem_disp2 hxg).2.1
    · exact h
  refine ⟨le_min ?_ ?_, le_min ?_ ?_⟩
  · exact (card_le_card inter_subset_right).trans hd
  · exact (card_le_card h1').trans h1
  · exact (card_le_card inter_subset_right).trans hg
  · exact (card_le_card h2').trans h2

end SwipeLocalPolicy

end DatingAlgo
