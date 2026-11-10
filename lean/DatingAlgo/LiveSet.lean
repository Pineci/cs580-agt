import DatingAlgo.SwipeRegret

/-!
# The live-set theorem and the two-cost model

Theorems A and B of the vault note "The Live-Set Theorem for Truthful Swiping", for
top-`k` users (additive users are the case `k = |β|`).

**Model.** One user, a finite set `β` of profiles, yes/no swipes, and a platform that
cannot see the user's values `q`. A profile is *acceptable* if `q x > c`, and *sincere*
swiping likes exactly the acceptable profiles.

* **Two costs.** A kept match costs `c` and a dropped match costs `d`. The utility of a
  match set `S` is `twoCostUtil v c d S = max_{T ⊆ S} (v T - c |T| - d |S \ T|)`. With
  `d = c` and monotone `v` this is `swipeUtil v c S = v S - c |S|`
  (`twoCostUtil_eq_swipeUtil`), the model of `TruthfulSwiping.lean`.
* **Swipe trees.** With the platform's coins and the other users' strategies fixed, the
  user faces a `SwipeTree`: each node shows a profile not shown before on that path, the
  user likes or passes, and each leaf gives a match set contained in the liked profiles.
  The tree does not depend on `q`, but later nodes may depend on earlier swipes.
  `t.run X` is the leaf reached by liking exactly the shown members of `X`, and
  `t.Reach M` says some path ends in the match set `M`.

**Results.**
* `liveSet_iff`, `swipeTree_liveSet_iff` (Theorem A, top-`k`): for `d > 0`, sincere
  swiping is dominant iff there is a set `S` with `|S| ≤ k` and `M X = X ∩ S` for every
  `X`. The first is stated for any outcome rule `M` with `M X ⊆ X`, the second for swipe
  trees. Types range over value vectors within `δ` of `c`.
* `liveSet_iff_additive`: for additive users the live set is unrestricted, but the matches
  must still be `X ∩ S`.
* `liveSet_iff_zero_drop`: with `d = 0` and `k ≥ 1` the size restriction disappears.
* `own_swipe_independence` (corollary): whether a liked profile matches does not depend on
  the user's other swipes.
* `twoCost_sincere_best_topK` (the "if" direction, for every non-negative value vector).
* `twoCost_topK_regret_le`, `twoCost_topK_regret_attained` (Theorem B, top-`k`): under a
  live set `R` of any size, the best likes in hindsight beat sincere swiping by exactly
  `d (|M| - k)^+`, where `M` is the sincere match set. `twoCost_topK_eq_net` is the
  welfare identity behind it. With `d = c` this is Proposition 4(a) (`topK_regret_le`).

Not formalized here: Theorem A′ (platform coins), the matroid and general-class rows of
the note's table, Theorem B′ (general cost functions) and Proposition P.
-/

namespace DatingAlgo

open Finset

section TwoCost

variable {β : Type*}

/-- Two-cost utility of a match set `S`: the user keeps `T ⊆ S` at cost `c` each and
drops the rest at cost `d` each, choosing `T` to maximize `v T - c |T| - d |S \ T|`. -/
noncomputable def twoCostUtil (v : Finset β → ℝ) (c d : ℝ) (S : Finset β) : ℝ :=
  S.powerset.sup' ⟨∅, empty_mem_powerset S⟩
    fun T => v T - c * T.card - d * ((S.card : ℝ) - T.card)

/-- Keeping any `T ⊆ S` is a lower bound. -/
theorem le_twoCostUtil (v : Finset β → ℝ) (c d : ℝ) {S T : Finset β} (hT : T ⊆ S) :
    v T - c * T.card - d * ((S.card : ℝ) - T.card) ≤ twoCostUtil v c d S :=
  le_sup' (fun T => v T - c * T.card - d * ((S.card : ℝ) - T.card)) (mem_powerset.mpr hT)

/-- The two-cost utility is attained by some kept set. -/
theorem exists_twoCostUtil_eq (v : Finset β → ℝ) (c d : ℝ) (S : Finset β) :
    ∃ T ⊆ S, twoCostUtil v c d S = v T - c * T.card - d * ((S.card : ℝ) - T.card) := by
  obtain ⟨T, hT, hEq⟩ := exists_mem_eq_sup' (⟨∅, empty_mem_powerset S⟩ : S.powerset.Nonempty)
    (fun T => v T - c * T.card - d * ((S.card : ℝ) - T.card))
  exact ⟨T, mem_powerset.mp hT, hEq⟩

/-- No matches: the utility is `v ∅`. -/
theorem twoCostUtil_empty (v : Finset β → ℝ) (c d : ℝ) : twoCostUtil v c d ∅ = v ∅ := by
  obtain ⟨T, hT, hEq⟩ := exists_twoCostUtil_eq v c d ∅
  rw [hEq, subset_empty.mp hT]
  simp

/-- With `d = c` and a monotone valuation, the two-cost utility is the one-cost utility
`v S - c |S|` of `TruthfulSwiping.lean`. -/
theorem twoCostUtil_eq_swipeUtil {v : Finset β → ℝ} (hmono : ∀ S T, S ⊆ T → v S ≤ v T)
    (c : ℝ) (S : Finset β) : twoCostUtil v c c S = swipeUtil v c S := by
  unfold swipeUtil
  apply le_antisymm
  · obtain ⟨T, hT, hEq⟩ := exists_twoCostUtil_eq v c c S
    rw [hEq]
    linarith [hmono T S hT]
  · have h := le_twoCostUtil v c c (subset_refl S)
    linarith

/-- For a top-`k` user, a match set is worth at most the sum of its members' net values,
where a profile's net value is `max (q x - c) (-d)`: keep it or drop it. -/
theorem twoCostUtil_topK_le_sum [DecidableEq β] {q : β → ℝ} (hq : ∀ x, 0 ≤ q x) (k : ℕ)
    (c d : ℝ) (S : Finset β) :
    twoCostUtil (topK q k) c d S ≤ ∑ x ∈ S, max (q x - c) (-d) := by
  obtain ⟨T, hTS, hEq⟩ := exists_twoCostUtil_eq (topK q k) c d S
  rw [hEq]
  have h1 := topK_le_sum hq k T
  have h2 : ∑ x ∈ T, q x - c * T.card ≤ ∑ x ∈ T, max (q x - c) (-d) := by
    have h : ∑ x ∈ T, (q x - c) = ∑ x ∈ T, q x - c * T.card := by
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul]; ring
    rw [← h]
    exact sum_le_sum fun x _ => le_max_left _ _
  have h3 : -d * ((S.card : ℝ) - T.card) ≤ ∑ x ∈ S \ T, max (q x - c) (-d) := by
    have h : ∑ _x ∈ S \ T, (-d) = -d * ((S.card : ℝ) - T.card) := by
      rw [sum_const, nsmul_eq_mul, card_sdiff_of_subset hTS, Nat.cast_sub (card_le_card hTS)]
      ring
    rw [← h]
    exact sum_le_sum fun x _ => le_max_right _ _
  have h4 := sum_sdiff hTS (f := fun x => max (q x - c) (-d))
  linarith

/-- For a top-`k` user, keeping a set `T ⊆ S` of at most `k` profiles and dropping the
rest is a lower bound. -/
theorem sum_le_twoCostUtil_topK {q : β → ℝ} (hq : ∀ x, 0 ≤ q x) {k : ℕ} (c d : ℝ)
    {S T : Finset β} (hTS : T ⊆ S) (hTk : T.card ≤ k) :
    ∑ x ∈ T, (q x - c) - d * ((S.card : ℝ) - T.card) ≤ twoCostUtil (topK q k) c d S := by
  have h := le_twoCostUtil (topK q k) c d hTS
  rw [topK_eq_sum_of_card_le hq hTk] at h
  have h' : ∑ x ∈ T, (q x - c) = ∑ x ∈ T, q x - c * T.card := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul]; ring
  linarith

/-- **Condition (F2) for top-`k`.** If more than `k` profiles are matched and each is
worth at most `c + ε` with `k ε < min c d`, the utility is negative: some match must be
kept at a loss or dropped. -/
theorem twoCostUtil_topK_neg_of_flat {q : β → ℝ} {k : ℕ} {c d ε : ℝ} {S : Finset β}
    (hflat : ∀ x ∈ S, q x ≤ c + ε) (hk : k < S.card) (hε : 0 ≤ ε)
    (hsmall : k * ε < min c d) : twoCostUtil (topK q k) c d S < 0 := by
  obtain ⟨T, hTS, hEq⟩ := exists_twoCostUtil_eq (topK q k) c d S
  obtain ⟨W, hWT, hWk, hW⟩ := exists_topK_eq q k T
  rw [hEq, hW]
  have h1 : ∑ x ∈ W, q x ≤ W.card * (c + ε) := by
    have := sum_le_card_nsmul W q (c + ε) fun x hx => hflat x (hTS (hWT hx))
    rwa [nsmul_eq_mul] at this
  have hwt : (W.card : ℝ) ≤ T.card := by exact_mod_cast card_le_card hWT
  have hts : (T.card : ℝ) ≤ S.card := by exact_mod_cast card_le_card hTS
  have hwk : (W.card : ℝ) ≤ k := by exact_mod_cast hWk
  have hws : (W.card : ℝ) + 1 ≤ S.card := by exact_mod_cast (show W.card + 1 ≤ S.card by omega)
  have hm : 0 < min c d := lt_of_le_of_lt (mul_nonneg (Nat.cast_nonneg k) hε) hsmall
  have hc : min c d ≤ c := min_le_left c d
  have hd : min c d ≤ d := min_le_right c d
  have h2 : (W.card : ℝ) * ε ≤ k * ε := mul_le_mul_of_nonneg_right hwk hε
  have h3 : min c d * ((T.card : ℝ) - W.card) ≤ c * ((T.card : ℝ) - W.card) :=
    mul_le_mul_of_nonneg_right hc (by linarith)
  have h4 : min c d * ((S.card : ℝ) - T.card) ≤ d * ((S.card : ℝ) - T.card) :=
    mul_le_mul_of_nonneg_right hd (by linarith)
  have h5 : min c d * 1 ≤ min c d * ((S.card : ℝ) - W.card) :=
    mul_le_mul_of_nonneg_left (by linarith) hm.le
  nlinarith

/-- **Theorem A, "if" direction (top-`k`).** If the user's matches are `D ∩ S` for a live
set `S` with at most `k` members, then liking exactly the acceptable profiles is a best
choice, for every non-negative value vector and every drop cost `d ≥ 0`. -/
theorem twoCost_sincere_best_topK [DecidableEq β] {q : β → ℝ} (hq : ∀ x, 0 ≤ q x) {k : ℕ}
    {c d : ℝ} (hd : 0 ≤ d) {S : Finset β} (hS : S.card ≤ k) (N : Finset β) {D : Finset β}
    (hD : D ⊆ N) :
    twoCostUtil (topK q k) c d (D ∩ S) ≤ twoCostUtil (topK q k) c d (sincereSet q c N ∩ S) := by
  set B := sincereSet q c N ∩ S
  set g : β → ℝ := fun x => max (q x - c) (-d)
  have hBacc : ∀ x ∈ B, c < q x := fun x hx => (mem_filter.mp (mem_inter.mp hx).1).2
  have h1 := twoCostUtil_topK_le_sum hq k c d (D ∩ S)
  have h2 : ∑ x ∈ D ∩ S, g x ≤ ∑ x ∈ (D ∩ S).filter (fun x => c < q x), g x := by
    have hsplit := sum_filter_add_sum_filter_not (D ∩ S) (fun x => c < q x) g
    have hneg : ∑ x ∈ (D ∩ S).filter (fun x => ¬ c < q x), g x ≤ 0 :=
      sum_nonpos fun x hx => max_le (by linarith [not_lt.mp (mem_filter.mp hx).2]) (by linarith)
    linarith
  have hsub : (D ∩ S).filter (fun x => c < q x) ⊆ B := fun x hx => by
    obtain ⟨hxDS, hxq⟩ := mem_filter.mp hx
    obtain ⟨hxD, hxS⟩ := mem_inter.mp hxDS
    exact mem_inter.mpr ⟨mem_filter.mpr ⟨hD hxD, hxq⟩, hxS⟩
  have h3 : ∑ x ∈ (D ∩ S).filter (fun x => c < q x), g x ≤ ∑ x ∈ B, g x :=
    sum_le_sum_of_subset_of_nonneg hsub fun x hx _ =>
      le_trans (by linarith [hBacc x hx]) (le_max_left _ _)
  have h4 : ∑ x ∈ B, g x = ∑ x ∈ B, (q x - c) :=
    sum_congr rfl fun x hx => max_eq_left (by linarith [hBacc x hx])
  have hBk : B.card ≤ k := (card_le_card inter_subset_right).trans hS
  have h5 := sum_le_twoCostUtil_topK hq c d (subset_refl B) hBk
  linarith

/-- For a top-`k` user, no match set is worth more than the top-`k` net value of its
acceptable members. -/
theorem twoCostUtil_topK_le_net {q : β → ℝ} (k : ℕ) {c d : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (S : Finset β) :
    twoCostUtil (topK q k) c d S ≤ topK (fun x => q x - c) k (S.filter fun x => c < q x) := by
  obtain ⟨T, hTS, hEq⟩ := exists_twoCostUtil_eq (topK q k) c d S
  obtain ⟨W, hWT, hWk, hW⟩ := exists_topK_eq q k T
  rw [hEq, hW]
  have hwt : (W.card : ℝ) ≤ T.card := by exact_mod_cast card_le_card hWT
  have hts : (T.card : ℝ) ≤ S.card := by exact_mod_cast card_le_card hTS
  have h1 : ∑ x ∈ W, (q x - c) = ∑ x ∈ W, q x - c * W.card := by
    rw [sum_sub_distrib, sum_const, nsmul_eq_mul]; ring
  have h2 : ∑ x ∈ W, (q x - c) ≤ ∑ x ∈ W.filter (fun x => c < q x), (q x - c) := by
    have hsplit := sum_filter_add_sum_filter_not W (fun x => c < q x) (fun x => q x - c)
    have hneg : ∑ x ∈ W.filter (fun x => ¬ c < q x), (q x - c) ≤ 0 :=
      sum_nonpos fun x hx => by linarith [not_lt.mp (mem_filter.mp hx).2]
    linarith
  have h3 : ∑ x ∈ W.filter (fun x => c < q x), (q x - c) ≤
      topK (fun x => q x - c) k (S.filter fun x => c < q x) :=
    sum_le_topK (filter_subset_filter _ (hWT.trans hTS))
      ((card_le_card (filter_subset _ W)).trans hWk)
  have h4 : c * (W.card : ℝ) ≤ c * T.card := mul_le_mul_of_nonneg_left hwt hc
  have h5 : 0 ≤ d * ((S.card : ℝ) - T.card) := mul_nonneg hd (by linarith)
  linarith

/-- **Theorem B, welfare identity.** On a set `M` of acceptable profiles, a top-`k`
user's two-cost utility is its top-`k` net value minus `d` per match beyond the `k`-th. -/
theorem twoCost_topK_eq_net {q : β → ℝ} (hq : ∀ x, 0 ≤ q x) (k : ℕ) {c d : ℝ} (hd : 0 ≤ d)
    (hdc : d ≤ c) (M : Finset β) (hM : ∀ x ∈ M, c < q x) :
    twoCostUtil (topK q k) c d M = topK (fun x => q x - c) k M - d * (M.card - k : ℕ) := by
  apply le_antisymm
  · obtain ⟨T, hTM, hEq⟩ := exists_twoCostUtil_eq (topK q k) c d M
    obtain ⟨W, hWT, hWk, hW⟩ := exists_topK_eq q k T
    rw [hEq, hW]
    have hwt : (W.card : ℝ) ≤ T.card := by exact_mod_cast card_le_card hWT
    have h1 : ∑ x ∈ W, (q x - c) = ∑ x ∈ W, q x - c * W.card := by
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul]; ring
    have h2 : ∑ x ∈ W, (q x - c) ≤ topK (fun x => q x - c) k M :=
      sum_le_topK (hWT.trans hTM) hWk
    have h3 : ((M.card - k : ℕ) : ℝ) ≤ (M.card : ℝ) - W.card := by
      have hWM := card_le_card (hWT.trans hTM)
      have : ((M.card - k : ℕ) : ℝ) + W.card ≤ M.card := by
        exact_mod_cast (show M.card - k + W.card ≤ M.card by omega)
      linarith
    have h4 : d * ((T.card : ℝ) - W.card) ≤ c * ((T.card : ℝ) - W.card) :=
      mul_le_mul_of_nonneg_right hdc (by linarith)
    have h5 : d * ((M.card - k : ℕ) : ℝ) ≤ d * ((M.card : ℝ) - W.card) :=
      mul_le_mul_of_nonneg_left h3 hd
    nlinarith
  · obtain ⟨W, hWM, hWcard, hEq⟩ := exists_topK_eq_card hq k M
    have hWk : W.card ≤ k := by rw [hWcard]; exact min_le_left _ _
    have h := le_twoCostUtil (topK q k) c d hWM
    rw [topK_eq_sum_of_card_le hq hWk, ← hEq, hWcard] at h
    have hcast : ((M.card - k : ℕ) : ℝ) = (M.card : ℝ) - ((min k M.card : ℕ) : ℝ) := by
      rw [eq_sub_iff_add_eq, ← Nat.cast_add]
      congr 1
      omega
    rw [topK_sub_const hq k hM, hcast]
    linarith

/-- **Theorem B, upper bound (top-`k`).** Let the user's matches be `D ∩ R` for a live
set `R` of any size, and let `0 ≤ d ≤ c`. Every set of likes `D ⊆ N` gets at most the
sincere utility plus `d (|M| - k)^+`, where `M = A ∩ R` is the sincere match set. -/
theorem twoCost_topK_regret_le [DecidableEq β] {q : β → ℝ} (hq : ∀ x, 0 ≤ q x) (k : ℕ)
    {c d : ℝ} (hd : 0 ≤ d) (hdc : d ≤ c) (N R : Finset β) {D : Finset β} (hD : D ⊆ N) :
    twoCostUtil (topK q k) c d (D ∩ R) ≤
      twoCostUtil (topK q k) c d (sincereSet q c N ∩ R) +
        d * ((sincereSet q c N ∩ R).card - k : ℕ) := by
  set M := sincereSet q c N ∩ R
  have hMacc : ∀ x ∈ M, c < q x := fun x hx => (mem_filter.mp (mem_inter.mp hx).1).2
  have hFM : (D ∩ R).filter (fun x => c < q x) ⊆ M := fun x hx => by
    obtain ⟨hxDR, hxq⟩ := mem_filter.mp hx
    obtain ⟨hxD, hxR⟩ := mem_inter.mp hxDR
    exact mem_inter.mpr ⟨mem_filter.mpr ⟨hD hxD, hxq⟩, hxR⟩
  have h1 := twoCostUtil_topK_le_net (q := q) k (hd.trans hdc) hd (D ∩ R)
  have h2 := topK_mono (w := fun x => q x - c) (K := k) hFM
  rw [twoCost_topK_eq_net hq k hd hdc M hMacc]
  linarith

/-- **Theorem B, equality (top-`k`).** Liking only the `k` most valued acceptable
profiles in `R` attains the bound, so the regret of sincere swiping is exactly
`d (|M| - k)^+`. -/
theorem twoCost_topK_regret_attained [DecidableEq β] {q : β → ℝ} (hq : ∀ x, 0 ≤ q x) (k : ℕ)
    {c d : ℝ} (hd : 0 ≤ d) (hdc : d ≤ c) (N R : Finset β) :
    ∃ D ⊆ N, twoCostUtil (topK q k) c d (D ∩ R) =
      twoCostUtil (topK q k) c d (sincereSet q c N ∩ R) +
        d * ((sincereSet q c N ∩ R).card - k : ℕ) := by
  set M := sincereSet q c N ∩ R
  have hMacc : ∀ x ∈ M, c < q x := fun x hx => (mem_filter.mp (mem_inter.mp hx).1).2
  obtain ⟨W, hWM, hWcard, hEq⟩ := exists_topK_eq_card hq k M
  have hWk : W.card ≤ k := by rw [hWcard]; exact min_le_left _ _
  have hWN : W ⊆ N := fun x hx => (mem_filter.mp (mem_inter.mp (hWM hx)).1).1
  have hWR : W ∩ R = W := inter_eq_left.mpr fun x hx => (mem_inter.mp (hWM hx)).2
  have hWacc : ∀ x ∈ W, c < q x := fun x hx => hMacc x (hWM hx)
  refine ⟨W, hWN, ?_⟩
  have hz : W.card - k = 0 := Nat.sub_eq_zero_of_le hWk
  have hmin : min k W.card = W.card := min_eq_right hWk
  rw [hWR, twoCost_topK_eq_net hq k hd hdc M hMacc, twoCost_topK_eq_net hq k hd hdc W hWacc,
    hz, topK_sub_const hq k hWacc, topK_sub_const hq k hMacc, topK_eq_sum_of_card_le hq hWk,
    hEq, hmin, hWcard]
  simp

/-- **Theorem B at `d = 0`.** If dropping a match is free, sincere swiping is a best
choice under a live set of any size. -/
theorem twoCost_zero_drop_sincere_best [DecidableEq β] {q : β → ℝ} (hq : ∀ x, 0 ≤ q x)
    (k : ℕ) {c : ℝ} (hc : 0 ≤ c) (N R : Finset β) {D : Finset β} (hD : D ⊆ N) :
    twoCostUtil (topK q k) c 0 (D ∩ R) ≤ twoCostUtil (topK q k) c 0 (sincereSet q c N ∩ R) := by
  have h := twoCost_topK_regret_le hq k le_rfl hc N R hD
  simpa using h

end TwoCost

/-! ### Swipe trees -/

/-- What one user faces once the platform's coins and the others' strategies are fixed:
show a profile and branch on the swipe, or stop with a set of matches. -/
inductive SwipeTree (β : Type*) where
  | stop (M : Finset β) : SwipeTree β
  | ask (x : β) (like pass : SwipeTree β) : SwipeTree β

namespace SwipeTree

variable {β : Type*} [DecidableEq β]

/-- The match set reached by the user who likes exactly the shown profiles in `X`. -/
def run : SwipeTree β → Finset β → Finset β
  | stop M, _ => M
  | ask x like pass, X => if x ∈ X then run like X else run pass X

/-- `ValidFrom t shown liked`: below a node reached after showing `shown` and liking
`liked`, no profile is shown twice on a path and every leaf's matches were liked. -/
def ValidFrom : SwipeTree β → Finset β → Finset β → Prop
  | stop M, _, liked => M ⊆ liked
  | ask x like pass, shown, liked =>
      x ∉ shown ∧ ValidFrom like (insert x shown) (insert x liked) ∧
        ValidFrom pass (insert x shown) liked

/-- A swipe tree is valid if no path shows a profile twice and matches are liked
profiles. -/
def Valid (t : SwipeTree β) : Prop := t.ValidFrom ∅ ∅

/-- `t.Reach M`: some path through the tree, i.e. some strategy of the user, ends with
the match set `M`. -/
inductive Reach : SwipeTree β → Finset β → Prop
  | stop (M : Finset β) : Reach (stop M) M
  | like {x : β} {l p : SwipeTree β} {M : Finset β} : Reach l M → Reach (ask x l p) M
  | pass {x : β} {l p : SwipeTree β} {M : Finset β} : Reach p M → Reach (ask x l p) M

/-- The leaf of a set-strategy is reachable. -/
theorem reach_run (t : SwipeTree β) (X : Finset β) : t.Reach (t.run X) := by
  induction t with
  | stop M => exact Reach.stop M
  | ask x l p ihl ihp =>
    by_cases hx : x ∈ X
    · simp only [run, hx, ↓reduceIte]; exact Reach.like ihl
    · simp only [run, hx, ↓reduceIte]; exact Reach.pass ihp

theorem run_subset_of_validFrom {t : SwipeTree β} {shown liked X : Finset β}
    (ht : t.ValidFrom shown liked) (hX : liked ⊆ X) : t.run X ⊆ X := by
  induction t generalizing shown liked with
  | stop M => exact fun y hy => hX (ht hy)
  | ask x l p ihl ihp =>
    obtain ⟨_, hl, hp⟩ := ht
    by_cases hx : x ∈ X
    · simp only [run, hx, ↓reduceIte]
      exact ihl hl (insert_subset hx hX)
    · simp only [run, hx, ↓reduceIte]
      exact ihp hp hX

/-- In a valid tree, the matches of a set-strategy are among the profiles it likes. -/
theorem run_subset {t : SwipeTree β} (ht : t.Valid) (X : Finset β) : t.run X ⊆ X :=
  run_subset_of_validFrom ht (empty_subset X)

theorem exists_run_of_reach_aux {t : SwipeTree β} {shown liked M : Finset β}
    (ht : t.ValidFrom shown liked) (hM : t.Reach M) :
    ∃ L, Disjoint L shown ∧ ∀ Z ⊆ shown, t.run (L ∪ Z) = M := by
  induction t generalizing shown liked with
  | stop M' =>
    cases hM
    exact ⟨∅, disjoint_empty_left _, fun Z _ => rfl⟩
  | ask x l p ihl ihp =>
    obtain ⟨hx, hl, hp⟩ := ht
    cases hM with
    | like h =>
      obtain ⟨L, hL, hrun⟩ := ihl hl h
      refine ⟨insert x L, ?_, fun Z hZ => ?_⟩
      · rw [disjoint_insert_left]
        exact ⟨hx, hL.mono_right (subset_insert x shown)⟩
      · have hmem : x ∈ insert x L ∪ Z := mem_union_left _ (mem_insert_self x L)
        simp only [run, hmem, ↓reduceIte]
        have := hrun (insert x Z) (insert_subset_insert x hZ)
        rwa [union_insert, ← insert_union] at this
    | pass h =>
      obtain ⟨L, hL, hrun⟩ := ihp hp h
      refine ⟨L, hL.mono_right (subset_insert x shown), fun Z hZ => ?_⟩
      have hxL : x ∉ L := fun hxL => disjoint_left.mp hL hxL (mem_insert_self x shown)
      have hmem : x ∉ L ∪ Z := fun hmem => by
        rcases mem_union.mp hmem with h' | h'
        · exact hxL h'
        · exact hx (hZ h')
      simp only [run, hmem, ↓reduceIte]
      exact hrun Z (hZ.trans (subset_insert x shown))

/-- In a valid tree every path is the path of a set-strategy: the set it likes. -/
theorem exists_run_of_reach {t : SwipeTree β} (ht : t.Valid) {M : Finset β}
    (hM : t.Reach M) : ∃ L, t.run L = M := by
  obtain ⟨L, _, hrun⟩ := exists_run_of_reach_aux ht hM
  exact ⟨L, by simpa using hrun ∅ (subset_refl _)⟩

end SwipeTree

/-! ### Theorem A -/

section LiveSet

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- Steps 2 and 3 of Theorem A. Suppose every reachable match set containing `x` is worth
at least `q x - c - |β| ε` when its other members are worth at least `c - ε`. If sincere
swiping is dominant for all value vectors within `δ` of `c`, the matches are
`X ∩ M univ`. -/
private theorem liveSet_aux {k : ℕ} {c d δ : ℝ} (hc : 0 < c) (hd : 0 ≤ d) (hδ : 0 < δ)
    {M : Finset β → Finset β} (hM : ∀ X, M X ⊆ X)
    (hlow : ∀ q : β → ℝ, (∀ x, 0 ≤ q x) → ∀ X' x, x ∈ M X' → ∀ ε : ℝ, 0 ≤ ε →
      (∀ y ∈ M X', y ≠ x → c - ε ≤ q y) →
      q x - c - (Fintype.card β : ℝ) * ε ≤ twoCostUtil (topK q k) c d (M X'))
    (hdom : ∀ q : β → ℝ, (∀ x, |q x - c| < δ) → ∀ X',
      twoCostUtil (topK q k) c d (M X') ≤ twoCostUtil (topK q k) c d (M (sincereSet q c univ)))
    (X : Finset β) : M X = X ∩ M univ := by
  set n : ℝ := (Fintype.card β : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set a : ℝ := δ / 2 with ha
  set ε : ℝ := min δ c / (4 * (n + 1)) with hε
  have hmin : 0 < min δ c := lt_min hδ hc
  have hden : 0 < 4 * (n + 1) := by linarith
  have hε0 : 0 < ε := div_pos hmin hden
  have hεmin : ε * (4 * (n + 1)) = min δ c := div_mul_cancel₀ _ hden.ne'
  have hεδ : ε < δ := by nlinarith [min_le_left δ c]
  have hεc : ε ≤ c := by nlinarith [min_le_right δ c]
  have hnε : 2 * (n * ε) < a := by nlinarith [min_le_left δ c]
  -- A match set whose members are all worth `c + ε` is worth at most `n ε`.
  have hupper : ∀ (q : β → ℝ), (∀ x, 0 ≤ q x) → ∀ T : Finset β, (∀ y ∈ T, q y = c + ε) →
      twoCostUtil (topK q k) c d T ≤ n * ε := by
    intro q hq T hT
    have h1 := twoCostUtil_topK_le_sum hq k c d T
    have h2 : ∑ x ∈ T, max (q x - c) (-d) ≤ T.card * ε := by
      have := sum_le_card_nsmul T (fun x => max (q x - c) (-d)) ε fun x hx =>
        max_le (by rw [hT x hx]; linarith) (by linarith)
      rwa [nsmul_eq_mul] at this
    have h3 : (T.card : ℝ) * ε ≤ n * ε :=
      mul_le_mul_of_nonneg_right (by rw [hn]; exact_mod_cast card_le_univ T) hε0.le
    linarith
  -- Step 2: every match set lies inside `M univ`.
  have hstep2 : ∀ X' x, x ∈ M X' → x ∈ M univ := by
    intro X' x hx
    by_contra hxS
    set q : β → ℝ := fun y => if y = x then c + a else c + ε with hq
    have hq0 : ∀ y, 0 ≤ q y := fun y => by
      simp only [hq]; split_ifs <;> linarith
    have hball : ∀ y, |q y - c| < δ := fun y => by
      simp only [hq]; split_ifs
      · rw [abs_lt]; constructor <;> linarith
      · rw [abs_lt]; constructor <;> linarith
    have hacc : sincereSet q c univ = univ := by
      ext y
      simp only [sincereSet, mem_filter, mem_univ, true_and, hq, iff_true]
      split_ifs <;> linarith
    have h1 := hdom q hball X'
    rw [hacc] at h1
    have h2 := hlow q hq0 X' x hx ε hε0.le fun y _ hyx => by
      simp only [hq, hyx, ↓reduceIte]; linarith
    have h3 := hupper q hq0 (M univ) fun y hy => by
      have hyx : y ≠ x := fun h => hxS (h ▸ hy)
      simp only [hq, hyx, ↓reduceIte]
    have hqx : q x = c + a := by simp [hq]
    rw [hqx] at h2
    linarith
  -- Step 3.
  apply Subset.antisymm
  · exact fun y hy => mem_inter.mpr ⟨hM X hy, hstep2 X y hy⟩
  · intro x hx
    obtain ⟨hxX, hxS⟩ := mem_inter.mp hx
    by_contra hxM
    set q : β → ℝ := fun y => if y = x then c + a else if y ∈ X then c + ε else c - ε with hq
    have hq0 : ∀ y, 0 ≤ q y := fun y => by
      simp only [hq]; split_ifs <;> linarith
    have hball : ∀ y, |q y - c| < δ := fun y => by
      simp only [hq]; split_ifs
      · rw [abs_lt]; constructor <;> linarith
      · rw [abs_lt]; constructor <;> linarith
      · rw [abs_lt]; constructor <;> linarith
    have hacc : sincereSet q c univ = X := by
      ext y
      simp only [sincereSet, mem_filter, mem_univ, true_and, hq]
      by_cases hyx : y = x
      · simp only [hyx, ↓reduceIte]
        exact ⟨fun _ => hxX, fun _ => by linarith⟩
      · by_cases hyX : y ∈ X
        · simp only [hyx, hyX, ↓reduceIte]
          exact ⟨fun _ => trivial, fun _ => by linarith⟩
        · simp only [hyx, hyX, ↓reduceIte]
          exact ⟨fun h => by linarith, fun h => (h).elim⟩
    have h1 := hdom q hball univ
    rw [hacc] at h1
    have h2 := hlow q hq0 univ x hxS ε hε0.le fun y _ hyx => by
      simp only [hq, hyx, ↓reduceIte]; split_ifs <;> linarith
    have h3 := hupper q hq0 (M X) fun y hy => by
      have hyx : y ≠ x := fun h => hxM (h ▸ hy)
      simp only [hq, hyx, hM X hy, ↓reduceIte]
    have hqx : q x = c + a := by simp [hq]
    rw [hqx] at h2
    linarith

/-- **Theorem A, "only if" direction (top-`k`).** Let `M X ⊆ X` be the user's matches
when it likes exactly `X`, and let `d > 0`. If sincere swiping is dominant for every
value vector within `δ` of the cost `c`, then there is a live set `S` with at most `k`
members such that `M X = X ∩ S` for every `X`. -/
theorem liveSet_of_dominant {k : ℕ} {c d δ : ℝ} (hc : 0 < c) (hd : 0 < d) (hδ : 0 < δ)
    {M : Finset β → Finset β} (hM : ∀ X, M X ⊆ X)
    (hdom : ∀ q : β → ℝ, (∀ x, |q x - c| < δ) → ∀ X',
      twoCostUtil (topK q k) c d (M X') ≤ twoCostUtil (topK q k) c d (M (sincereSet q c univ))) :
    ∃ S : Finset β, S.card ≤ k ∧ ∀ X, M X = X ∩ S := by
  -- Step 1: no match set has more than `k` members.
  have hstep1 : ∀ X', (M X').card ≤ k := by
    intro X'
    by_contra hcard
    push Not at hcard
    set m : ℝ := min δ (min c d) with hm
    have hm0 : 0 < m := lt_min hδ (lt_min hc hd)
    have hden : 0 < 2 * ((k : ℝ) + 1) := by positivity
    set ε : ℝ := m / (2 * ((k : ℝ) + 1)) with hε
    have hε0 : 0 < ε := div_pos hm0 hden
    have hεm : ε * (2 * ((k : ℝ) + 1)) = m := div_mul_cancel₀ _ hden.ne'
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hmδ : m ≤ δ := min_le_left _ _
    have hmcd : m ≤ min c d := min_le_right _ _
    have hmc : m ≤ c := hmcd.trans (min_le_left _ _)
    have hεδ : ε < δ := by nlinarith
    have hεc : ε ≤ c := by nlinarith
    have hsmall : (k : ℝ) * ε < min c d := by nlinarith
    set q : β → ℝ := fun y => if y ∈ X' then c + ε else c - ε with hq
    have hball : ∀ y, |q y - c| < δ := fun y => by
      simp only [hq]; split_ifs
      · rw [abs_lt]; constructor <;> linarith
      · rw [abs_lt]; constructor <;> linarith
    have hacc : sincereSet q c univ = X' := by
      ext y
      simp only [sincereSet, mem_filter, mem_univ, true_and, hq]
      by_cases hy : y ∈ X'
      · simp only [hy, ↓reduceIte]
        exact ⟨fun _ => trivial, fun _ => by linarith⟩
      · simp only [hy, ↓reduceIte]
        exact ⟨fun h => by linarith, fun h => h.elim⟩
    have h1 := hdom q hball ∅
    rw [hacc, subset_empty.mp (hM ∅), twoCostUtil_empty, topK_empty] at h1
    have h2 := twoCostUtil_topK_neg_of_flat (q := q) (k := k) (c := c) (d := d) (ε := ε)
      (S := M X') (fun y hy => by simp only [hq, hM X' hy, ↓reduceIte]; exact le_rfl) hcard
      hε0.le hsmall
    linarith
  refine ⟨M univ, hstep1 univ, liveSet_aux hc hd.le hδ hM ?_ hdom⟩
  -- A match set of at most `k` profiles can be kept whole.
  intro q hq X' x hx ε hε hy
  have h1 := sum_le_twoCostUtil_topK hq c d (subset_refl (M X')) (hstep1 X')
  have h2 : q x - c - (Fintype.card β : ℝ) * ε ≤ ∑ y ∈ M X', (q y - c) := by
    rw [← add_sum_erase _ _ hx]
    have h3 : ((M X').erase x).card • (-ε) ≤ ∑ y ∈ (M X').erase x, (q y - c) :=
      card_nsmul_le_sum _ _ _ fun y hy' => by
        obtain ⟨hyx, hyM⟩ := mem_erase.mp hy'
        linarith [hy y hyM hyx]
    rw [nsmul_eq_mul] at h3
    have h4 : (((M X').erase x).card : ℝ) * ε ≤ (Fintype.card β : ℝ) * ε :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_univ _) hε
    linarith
  linarith

/-- **Theorem A (top-`k`), for outcome rules.** Let `M X ⊆ X` be the user's matches when
it likes exactly `X`, with `c > 0`, `d > 0` and types within `δ ≤ c` of the cost. Sincere
swiping is dominant iff the matches are the liked profiles inside a live set of at most
`k` profiles. -/
theorem liveSet_iff {k : ℕ} {c d δ : ℝ} (hc : 0 < c) (hd : 0 < d) (hδ : 0 < δ) (hδc : δ ≤ c)
    {M : Finset β → Finset β} (hM : ∀ X, M X ⊆ X) :
    (∀ q : β → ℝ, (∀ x, |q x - c| < δ) → ∀ X',
      twoCostUtil (topK q k) c d (M X') ≤ twoCostUtil (topK q k) c d (M (sincereSet q c univ)))
      ↔ ∃ S : Finset β, S.card ≤ k ∧ ∀ X, M X = X ∩ S := by
  refine ⟨liveSet_of_dominant hc hd hδ hM, ?_⟩
  rintro ⟨S, hS, hform⟩ q hq X'
  have hq0 : ∀ x, 0 ≤ q x := fun x => by
    have := (abs_lt.mp (hq x)).1
    linarith
  rw [hform, hform]
  exact twoCost_sincere_best_topK hq0 hd.le hS univ (subset_univ X')

omit [Fintype β] in
/-- **Corollary: own-swipe independence.** Under the live-set form, whether a liked
profile matches does not depend on the user's other swipes. -/
theorem own_swipe_independence {M : Finset β → Finset β} {S : Finset β}
    (hform : ∀ X, M X = X ∩ S) {X Y : Finset β} {x : β} (hX : x ∈ X) (hY : x ∈ Y) :
    x ∈ M X ↔ x ∈ M Y := by
  rw [hform, hform, mem_inter, mem_inter]
  exact ⟨fun h => ⟨hY, h.2⟩, fun h => ⟨hX, h.2⟩⟩

/-- **Theorem A for additive users.** The live set may be any set, but the matches must
still be the liked profiles inside a set that the user's swipes do not change. -/
theorem liveSet_iff_additive {c d δ : ℝ} (hc : 0 < c) (hd : 0 < d) (hδ : 0 < δ) (hδc : δ ≤ c)
    {M : Finset β → Finset β} (hM : ∀ X, M X ⊆ X) :
    (∀ q : β → ℝ, (∀ x, |q x - c| < δ) → ∀ X',
      twoCostUtil (fun T => ∑ x ∈ T, q x) c d (M X') ≤
        twoCostUtil (fun T => ∑ x ∈ T, q x) c d (M (sincereSet q c univ)))
      ↔ ∃ S : Finset β, ∀ X, M X = X ∩ S := by
  have hadd : ∀ q : β → ℝ, (∀ x, |q x - c| < δ) →
      topK q (Fintype.card β) = fun T => ∑ x ∈ T, q x := fun q hq => by
    funext T
    exact topK_eq_sum_of_card_le (fun x => by have := (abs_lt.mp (hq x)).1; linarith)
      (card_le_univ T)
  have h := liveSet_iff (k := Fintype.card β) hc hd hδ hδc hM
  constructor
  · intro hdom
    obtain ⟨S, _, hS⟩ := h.mp fun q hq X' => by rw [hadd q hq]; exact hdom q hq X'
    exact ⟨S, hS⟩
  · rintro ⟨S, hS⟩ q hq X'
    have := h.mpr ⟨S, card_le_univ S, hS⟩ q hq X'
    rwa [hadd q hq] at this

/-- **Theorem A at `d = 0`.** If dropping a match is free and `k ≥ 1`, sincere swiping is
dominant iff the matches are the liked profiles inside a live set of any size. -/
theorem liveSet_iff_zero_drop {k : ℕ} (hk : 1 ≤ k) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hδc : δ ≤ c) {M : Finset β → Finset β} (hM : ∀ X, M X ⊆ X) :
    (∀ q : β → ℝ, (∀ x, |q x - c| < δ) → ∀ X',
      twoCostUtil (topK q k) c 0 (M X') ≤ twoCostUtil (topK q k) c 0 (M (sincereSet q c univ)))
      ↔ ∃ S : Finset β, ∀ X, M X = X ∩ S := by
  constructor
  · intro hdom
    refine ⟨M univ, liveSet_aux hc le_rfl hδ hM ?_ hdom⟩
    -- Keep `x` alone and drop the rest for free.
    intro q hq X' x hx ε hε _
    have h1 := sum_le_twoCostUtil_topK (k := k) hq c 0 (singleton_subset_iff.mpr hx)
      (by rw [card_singleton]; exact hk)
    rw [sum_singleton] at h1
    have h2 : 0 ≤ (Fintype.card β : ℝ) * ε := mul_nonneg (Nat.cast_nonneg _) hε
    linarith
  · rintro ⟨S, hform⟩ q hq X'
    have hq0 : ∀ x, 0 ≤ q x := fun x => by
      have := (abs_lt.mp (hq x)).1
      linarith
    rw [hform, hform]
    exact twoCost_zero_drop_sincere_best hq0 k hc.le univ S (subset_univ X')

/-- **Theorem A (top-`k`), for swipe trees.** In a valid swipe tree, with `c > 0`,
`d > 0` and types within `δ ≤ c` of the cost: no path beats the sincere path, for every
type, iff there is a live set `S` of at most `k` profiles such that the user who likes
exactly `X` is matched with `X ∩ S`. -/
theorem swipeTree_liveSet_iff {k : ℕ} {c d δ : ℝ} (hc : 0 < c) (hd : 0 < d) (hδ : 0 < δ)
    (hδc : δ ≤ c) {t : SwipeTree β} (ht : t.Valid) :
    (∀ q : β → ℝ, (∀ x, |q x - c| < δ) → ∀ M', t.Reach M' →
      twoCostUtil (topK q k) c d M' ≤ twoCostUtil (topK q k) c d (t.run (sincereSet q c univ)))
      ↔ ∃ S : Finset β, S.card ≤ k ∧ ∀ X, t.run X = X ∩ S := by
  rw [← liveSet_iff hc hd hδ hδc (SwipeTree.run_subset ht)]
  constructor
  · exact fun h q hq X' => h q hq _ (SwipeTree.reach_run t X')
  · intro h q hq M' hM'
    obtain ⟨L, rfl⟩ := SwipeTree.exists_run_of_reach ht hM'
    exact h q hq L

end LiveSet

end DatingAlgo
