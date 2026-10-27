import DatingAlgo.TruthfulSwiping
import DatingAlgo.PoissonGap

/-!
# Regret of sincere swiping; Impossibility 1; Propositions 4, 5(c), 6(a); the T5 examples

Results of the vault note "Truthful Swiping with an LLM Oracle" about a single user whose
matches are `D ∩ R` (Lemma 1′): `D` is the set it likes among the profiles `N` it sees,
and `R` is the set of profiles that would match it, which its swipes do not change. As in
`TruthfulSwiping.lean`, `R` is arbitrary, so statements "for every `R`" hold whatever the
others do.

* `topK_regret_le`, `topK_regret_attained` (Proposition 4(a)): for a top-`k` user the
  best likes in hindsight beat sincere swiping by exactly `c (|M| - k)^+`, where `M` is
  the sincere match set. `topK_regret_expect` is the ε-Bayes–Nash form, and
  `topK_regret_worst` shows the regret reaches `c (|A| - k)^+` for some behavior of the
  others, so this route is not DSIC.
* `topK_util_eq_net` (Proposition 4(b)): on acceptable sets, a top-`k` user's utility is
  its top-`k` net value minus `c (|M| - k)^+`.
* `excess_le` (Proposition 4(c)): independent matches with mean at most `k` give
  `E(|M| - k)^+ ≤ k e^{-k} k^k / k!`.
* `impossibility1_no_dominant`, `impossibility1_values` (Impossibility 1, the 10/5
  example) and `like_gain_le`, `impossibility1_bn_example` (the Bayes–Nash failure).
* `zeroQuery_topK_dsic_iff` (Proposition 6(a)).
* `expost_not_dsic` (T5: ex post is weaker than DSIC).
* `budget_resp_le`, `budget_resp_attained` (Proposition 5(c)).
-/

namespace DatingAlgo

open Finset

section Regret

variable {β : Type*} [DecidableEq β]

omit [DecidableEq β] in
/-- With non-negative values, top-`k` value is at most the sum. -/
theorem topK_le_sum {q : β → ℝ} (hq : ∀ x, 0 ≤ q x) (k : ℕ) (S : Finset β) :
    topK q k S ≤ ∑ x ∈ S, q x := by
  obtain ⟨W, hWS, _, hEq⟩ := exists_topK_eq q k S
  rw [hEq]
  exact sum_le_sum_of_subset_of_nonneg hWS fun x _ _ => hq x

omit [DecidableEq β] in
/-- One profile is worth at most its value. -/
theorem topK_singleton_le {q : β → ℝ} (hq : ∀ x, 0 ≤ q x) (k : ℕ) (x : β) :
    topK q k {x} ≤ q x := by
  simpa using topK_le_sum hq k {x}

omit [DecidableEq β] in
/-- A top-`k` value is attained by a set of exactly `min(k, |M|)` elements. -/
theorem exists_topK_eq_card {q : β → ℝ} (hq : ∀ x, 0 ≤ q x) (k : ℕ) (M : Finset β) :
    ∃ W ⊆ M, W.card = min k M.card ∧ topK q k M = ∑ x ∈ W, q x := by
  obtain ⟨W0, hW0M, hW0k, hEq⟩ := exists_topK_eq q k M
  obtain ⟨W, hW0W, hWM, hWcard⟩ := exists_subsuperset_card_eq hW0M
    (le_min hW0k (card_le_card hW0M)) (min_le_right k M.card)
  refine ⟨W, hWM, hWcard, le_antisymm ?_ ?_⟩
  · rw [hEq]
    exact sum_le_sum_of_subset_of_nonneg hW0W fun x _ _ => hq x
  · exact sum_le_topK hWM (by rw [hWcard]; exact min_le_left _ _)

omit [DecidableEq β] in
/-- On profiles worth more than `c`, subtracting `c` from every value lowers top-`k`
value by `c` per slot filled: `min(k, |M|)` slots. -/
theorem topK_sub_const {q : β → ℝ} (hq : ∀ x, 0 ≤ q x) (k : ℕ) {c : ℝ} {M : Finset β}
    (hM : ∀ x ∈ M, c < q x) :
    topK (fun x => q x - c) k M = topK q k M - c * (min k M.card : ℕ) := by
  apply le_antisymm
  · obtain ⟨W', hW'M, hW'k, hEq⟩ := exists_topK_eq (fun x => q x - c) k M
    obtain ⟨W, hW'W, hWM, hWcard⟩ := exists_subsuperset_card_eq hW'M
      (le_min hW'k (card_le_card hW'M)) (min_le_right k M.card)
    have hWk : W.card ≤ k := by rw [hWcard]; exact min_le_left _ _
    have h1 : ∑ x ∈ W', (q x - c) ≤ ∑ x ∈ W, (q x - c) :=
      sum_le_sum_of_subset_of_nonneg hW'W fun x hx _ => (sub_pos.mpr (hM x (hWM hx))).le
    have h2 := sum_le_topK (w := q) hWM hWk
    have h3 : ∑ x ∈ W, (q x - c) = ∑ x ∈ W, q x - c * (min k M.card : ℕ) := by
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hWcard]; ring
    rw [hEq]
    linarith
  · obtain ⟨W, hWM, hWcard, hEq⟩ := exists_topK_eq_card hq k M
    have hWk : W.card ≤ k := by rw [hWcard]; exact min_le_left _ _
    have h := sum_le_topK (w := fun x => q x - c) hWM hWk
    have h3 : ∑ x ∈ W, (q x - c) = ∑ x ∈ W, q x - c * (min k M.card : ℕ) := by
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul, hWcard]; ring
    rw [hEq]
    linarith

/-- Dropping profiles worth at most their cost never lowers a top-`k` user's utility. -/
theorem swipeUtil_topK_le_filter {q : β → ℝ} (hq : ∀ x, 0 ≤ q x) (k : ℕ) (c : ℝ)
    (S : Finset β) :
    swipeUtil (topK q k) c S ≤ swipeUtil (topK q k) c (S.filter fun x => c < q x) := by
  have hsplit := filter_union_filter_not_eq (fun x => c < q x) S
  have hcard := card_filter_add_card_filter_not (s := S) (fun x => c < q x)
  have h1 := topK_union_le q k (S.filter fun x => c < q x) (S.filter fun x => ¬ c < q x)
  rw [hsplit] at h1
  have h2 := topK_le_sum hq k (S.filter fun x => ¬ c < q x)
  have h3 : ∑ x ∈ S.filter (fun x => ¬ c < q x), q x ≤
      ∑ x ∈ S.filter (fun x => ¬ c < q x), c :=
    sum_le_sum fun x hx => not_lt.mp (mem_filter.mp hx).2
  rw [sum_const, nsmul_eq_mul] at h3
  unfold swipeUtil
  rw [← hcard]
  push_cast
  linarith

omit [DecidableEq β] in
/-- **Proposition 4(b), per-user welfare identity.** On a set `M` of acceptable profiles,
a top-`k` user's utility is its top-`k` *net* value (values minus cost) minus the cost
of dates beyond the `k`-th. Summing over users gives
`W = U_k^net - ∑_ℓ c_ℓ (|M_ℓ| - k)^+`. -/
theorem topK_util_eq_net {q : β → ℝ} (hq : ∀ x, 0 ≤ q x) (k : ℕ) {c : ℝ} (M : Finset β)
    (hM : ∀ x ∈ M, c < q x) :
    swipeUtil (topK q k) c M = topK (fun x => q x - c) k M - c * (M.card - k : ℕ) := by
  have hcast : ((M.card - k : ℕ) : ℝ) = (M.card : ℝ) - ((min k M.card : ℕ) : ℝ) := by
    rw [eq_sub_iff_add_eq, ← Nat.cast_add]
    congr 1
    omega
  rw [topK_sub_const hq k hM, hcast]
  unfold swipeUtil
  ring

/-- **Proposition 4(a), upper bound.** For a top-`k` user with non-negative values and
`c > 0`, every set of likes `D ⊆ N` gets at most the sincere utility plus
`c (|M| - k)^+`, where `M = A ∩ R` is the sincere match set. -/
theorem topK_regret_le {q : β → ℝ} (hq : ∀ x, 0 ≤ q x) (k : ℕ) {c : ℝ} (hc : 0 < c)
    (N R : Finset β) {D : Finset β} (hD : D ⊆ N) :
    swipeUtil (topK q k) c (D ∩ R) ≤
      swipeUtil (topK q k) c (sincereSet q c N ∩ R) +
        c * ((sincereSet q c N ∩ R).card - k : ℕ) := by
  set M := sincereSet q c N ∩ R
  have hMacc : ∀ x ∈ M, c < q x := fun x hx => (mem_filter.mp (mem_inter.mp hx).1).2
  set F := (D ∩ R).filter fun x => c < q x
  have hFM : F ⊆ M := fun x hx => by
    obtain ⟨hxDR, hxq⟩ := mem_filter.mp hx
    obtain ⟨hxD, hxR⟩ := mem_inter.mp hxDR
    exact mem_inter.mpr ⟨mem_filter.mpr ⟨hD hxD, hxq⟩, hxR⟩
  have hFacc : ∀ x ∈ F, c < q x := fun x hx => (mem_filter.mp hx).2
  have h0 : 0 ≤ c * ((F.card - k : ℕ) : ℝ) := mul_nonneg hc.le (Nat.cast_nonneg _)
  calc swipeUtil (topK q k) c (D ∩ R) ≤ swipeUtil (topK q k) c F :=
        swipeUtil_topK_le_filter hq k c _
    _ = topK (fun x => q x - c) k F - c * (F.card - k : ℕ) := topK_util_eq_net hq k F hFacc
    _ ≤ topK (fun x => q x - c) k M := by
        linarith [topK_mono (w := fun x => q x - c) (K := k) hFM]
    _ = swipeUtil (topK q k) c M + c * (M.card - k : ℕ) := by
        rw [topK_util_eq_net hq k M hMacc]; ring

/-- **Proposition 4(a), equality.** Liking only the `k` most valued acceptable profiles
in `R` attains the bound, so the regret is exactly `c (|M| - k)^+`. -/
theorem topK_regret_attained {q : β → ℝ} (hq : ∀ x, 0 ≤ q x) (k : ℕ) {c : ℝ} (_hc : 0 < c)
    (N R : Finset β) :
    ∃ D ⊆ N, swipeUtil (topK q k) c (D ∩ R) =
      swipeUtil (topK q k) c (sincereSet q c N ∩ R) +
        c * ((sincereSet q c N ∩ R).card - k : ℕ) := by
  set M := sincereSet q c N ∩ R
  have hMacc : ∀ x ∈ M, c < q x := fun x hx => (mem_filter.mp (mem_inter.mp hx).1).2
  obtain ⟨W, hWM, hWcard, hEq⟩ := exists_topK_eq_card hq k M
  have hWk : W.card ≤ k := by rw [hWcard]; exact min_le_left _ _
  have hWN : W ⊆ N := fun x hx => (mem_filter.mp (mem_inter.mp (hWM hx)).1).1
  have hWR : W ∩ R = W := inter_eq_left.mpr fun x hx => (mem_inter.mp (hWM hx)).2
  refine ⟨W, hWN, ?_⟩
  rw [hWR, topK_util_eq_net hq k M hMacc, topK_sub_const hq k hMacc, hEq]
  unfold swipeUtil
  rw [topK_eq_sum_of_card_le hq hWk, hWcard]
  ring

/-- **Proposition 4(a), ε-Bayes–Nash.** Average over any finite distribution `μ` of
realizations (values, coins and the others' behavior). No deviation, even one that
depends on the realization, gains more than `c E(|M| - k)^+`. -/
theorem topK_regret_expect {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    (q : Ω → β → ℝ) (hq : ∀ ω x, 0 ≤ q ω x) (k : ℕ) {c : ℝ} (hc : 0 < c)
    (N R D : Ω → Finset β) (hD : ∀ ω, D ω ⊆ N ω) :
    ∑ ω, μ ω * swipeUtil (topK (q ω) k) c (D ω ∩ R ω) ≤
      ∑ ω, μ ω * swipeUtil (topK (q ω) k) c (sincereSet (q ω) c (N ω) ∩ R ω) +
        c * ∑ ω, μ ω * ((sincereSet (q ω) c (N ω) ∩ R ω).card - k : ℕ) := by
  rw [mul_sum, ← sum_add_distrib]
  refine sum_le_sum fun ω _ => ?_
  have h := topK_regret_le (hq ω) k hc (N ω) (R ω) (hD ω)
  have := mul_le_mul_of_nonneg_left h (hμ ω)
  linarith

/-- **Proposition 4(a): not DSIC.** If every acceptable profile seen would match (one
behavior of the others), the regret is `c (|A| - k)^+`, where `A` is the set of acceptable
profiles seen. -/
theorem topK_regret_worst {q : β → ℝ} (hq : ∀ x, 0 ≤ q x) (k : ℕ) {c : ℝ} (hc : 0 < c)
    (N : Finset β) :
    ∃ D ⊆ N, swipeUtil (topK q k) c (D ∩ sincereSet q c N) =
      swipeUtil (topK q k) c (sincereSet q c N ∩ sincereSet q c N) +
        c * ((sincereSet q c N).card - k : ℕ) := by
  simpa only [inter_self] using topK_regret_attained hq k hc N (sincereSet q c N)

/-- **Proposition 4(c).** If a user's matches are independent coin flips with expected
number at most `k`, the expected number of dates beyond the `k`-th is at most
`k e^{-k} k^k / k!`. This is `E(Poi(k) - k)^+ = k (1 - c_k)` (`poiMin_self`), about `0.37`
for `k = 1`. -/
theorem excess_le {α : Type*} [DecidableEq α] (U : Finset α) (p : α → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (k : ℕ) (hμ : ∑ i ∈ U, p i ≤ k) :
    indepExp U p (fun S => ((S.card - k : ℕ) : ℝ)) ≤
      k * (Real.exp (-(k : ℝ)) * (k : ℝ) ^ k / (k.factorial : ℝ)) := by
  have hcast : ∀ S ⊆ U, ((S.card - k : ℕ) : ℝ) =
      (S.card : ℝ) + (-1) * min (S.card : ℝ) k := by
    intro S _
    rcases le_total k S.card with h | h
    · rw [Nat.cast_sub h, min_eq_right (by exact_mod_cast h)]; ring
    · rw [Nat.sub_eq_zero_of_le h, min_eq_left (by exact_mod_cast h)]; simp
  rw [indepExp_congr hcast, indepExp_add, indepExp_const_mul, indepExp_card]
  have hgap := poissonBinomial_min_ge U p hp k
  have hμ0 : 0 ≤ ∑ i ∈ U, p i := sum_nonneg fun i hi => (hp i hi).1
  rw [min_eq_left hμ] at hgap
  have hc1 : cK k ≤ 1 := cK_le_one k
  have hcK : 1 - cK k = Real.exp (-(k : ℝ)) * (k : ℝ) ^ k / (k.factorial : ℝ) := by
    unfold cK; ring
  rw [← hcK]
  nlinarith

end Regret

section Impossibility1

/-- Top-1 value is at most any non-negative bound on the values. -/
theorem topK_one_le {β : Type*} {q : β → ℝ} {S : Finset β} {m : ℝ} (hm : 0 ≤ m)
    (h : ∀ x ∈ S, q x ≤ m) : topK q 1 S ≤ m := by
  obtain ⟨W, hWS, hW1, hEq⟩ := exists_topK_eq q 1 S
  rw [hEq]
  rcases W.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simpa using hm
  · have hW : W = {a} := eq_singleton_iff_unique_mem.mpr
      ⟨ha, fun b hb => card_le_one.mp hW1 b hb a ha⟩
    rw [hW, sum_singleton]
    exact h a (hWS ha)

/-- Top-1 value is at least the value of any member. -/
theorem le_topK_one {β : Type*} {q : β → ℝ} {S : Finset β} {x : β} (hx : x ∈ S) :
    q x ≤ topK q 1 S := by
  simpa using sum_le_topK (w := q) (K := 1) (singleton_subset_iff.mpr hx) (by simp)

/-- The four subsets of a two-element type. -/
theorem finset_fin_two (D : Finset (Fin 2)) : D = ∅ ∨ D = {0} ∨ D = {1} ∨ D = univ := by
  decide +revert

/-- The sender's values in the 10/5 example: `r₁ = 0` at 10, `r₂ = 1` at 5. -/
def tenFive : Fin 2 → ℝ := ![10, 5]

/-- **Impossibility 1, the 10/5 example, numbers.** A top-1 sender with cost 1. If both
`r₁, r₂` would like back, liking only `r₁` earns 9 and liking both earns 8. If only `r₂`
would, liking only `r₁` earns 0 and liking both earns 4. -/
theorem impossibility1_values :
    swipeUtil (topK tenFive 1) 1 ({0} ∩ univ) = 9 ∧
      swipeUtil (topK tenFive 1) 1 (univ ∩ univ) = 8 ∧
      swipeUtil (topK tenFive 1) 1 ({0} ∩ {1}) = 0 ∧
      swipeUtil (topK tenFive 1) 1 (univ ∩ {1}) = 4 := by
  have hnn : ∀ i, 0 ≤ tenFive i := fun i => by fin_cases i <;> norm_num [tenFive]
  have h0 : topK tenFive 1 {0} = 10 := by
    rw [topK_eq_sum_of_card_le hnn (by simp)]; simp [tenFive]
  have h1 : topK tenFive 1 {1} = 5 := by
    rw [topK_eq_sum_of_card_le hnn (by simp)]; simp [tenFive]
  have hu : topK tenFive 1 univ = 10 := le_antisymm
    (topK_one_le (by norm_num) fun i _ => by fin_cases i <;> norm_num [tenFive])
    (by simpa [tenFive] using le_topK_one (q := tenFive) (mem_univ (0 : Fin 2)))
  have e1 : ({0} : Finset (Fin 2)) ∩ univ = {0} := by decide
  have e2 : ({0} : Finset (Fin 2)) ∩ {1} = ∅ := by decide
  have e3 : (univ : Finset (Fin 2)) ∩ {1} = {1} := by decide
  simp only [swipeUtil, e1, e2, e3, inter_self, h0, h1, hu, topK_empty, card_singleton,
    card_empty, card_univ, Fintype.card_fin]
  norm_num

/-- **Impossibility 1: no swipe rule is dominant.** In the 10/5 example no set of likes
is a best response to every set `R` of profiles that would like back. -/
theorem impossibility1_no_dominant :
    ¬ ∃ D : Finset (Fin 2), ∀ R D' : Finset (Fin 2),
      swipeUtil (topK tenFive 1) 1 (D' ∩ R) ≤ swipeUtil (topK tenFive 1) 1 (D ∩ R) := by
  rintro ⟨D, hD⟩
  obtain ⟨v1, v2, v3, v4⟩ := impossibility1_values
  have h1 := hD univ {0}
  have h2 := hD {1} univ
  rw [v1] at h1
  rw [v4] at h2
  rcases finset_fin_two D with rfl | rfl | rfl | rfl
  · simp [swipeUtil, topK_empty] at h1; linarith
  · rw [v3] at h2; linarith
  · have e : ({1} : Finset (Fin 2)) ∩ univ = univ ∩ {1} := by decide
    rw [e, v4] at h1; linarith
  · rw [v2] at h1; linarith

variable {β : Type*} [DecidableEq β]

/-- If `S` already holds `k` profiles valued at least `q x`, adding `x` does not raise
top-`k` value. -/
theorem topK_insert_le_of_dominated {q : β → ℝ} {k : ℕ} {x : β} {S T : Finset β}
    (hxS : x ∉ S) (hTS : T ⊆ S) (hTk : T.card = k) (hdom : ∀ y ∈ T, q x ≤ q y) :
    topK q k (insert x S) ≤ topK q k S := by
  obtain ⟨W, hWS, hWk, hEq⟩ := exists_topK_eq q k (insert x S)
  rw [hEq]
  by_cases hxW : x ∈ W
  · have hW1 : 1 ≤ W.card := card_pos.mpr ⟨x, hxW⟩
    have hlt : (W.erase x).card < T.card := by rw [card_erase_of_mem hxW, hTk]; omega
    obtain ⟨y, hyT, hyW'⟩ := exists_mem_notMem_of_card_lt_card hlt
    have hyx : y ≠ x := fun h => hxS (h ▸ hTS hyT)
    have hsub : insert y (W.erase x) ⊆ S := insert_subset (hTS hyT) fun z hz => by
      obtain ⟨hzx, hzW⟩ := mem_erase.mp hz
      rcases mem_insert.mp (hWS hzW) with h | h
      · exact absurd h hzx
      · exact h
    have hcard : (insert y (W.erase x)).card ≤ k := by
      rw [card_insert_of_notMem hyW', card_erase_of_mem hxW]; omega
    calc ∑ i ∈ W, q i = q x + ∑ i ∈ W.erase x, q i := (add_sum_erase W q hxW).symm
      _ ≤ q y + ∑ i ∈ W.erase x, q i := by linarith [hdom y hyT]
      _ = ∑ i ∈ insert y (W.erase x), q i := (sum_insert hyW').symm
      _ ≤ topK q k S := sum_le_topK hsub hcard
  · refine sum_le_topK (fun z hz => ?_) hWk
    rcases mem_insert.mp (hWS hz) with h | h
    · exact absurd (h ▸ hz) hxW
    · exact h

/-- **Impossibility 1: not even Bayes–Nash, the bound.** A top-`k` user with `c > 0`
weighs liking an acceptable `x` on top of likes `D` (`x ∉ D`), averaging over a finite
distribution `μ` of the sets `R ω` of profiles that would like back. Suppose that in the
event `sat`, which has probability at least `π`, `x` would like back and `ℓ`'s other
matches already include `k` profiles valued at least `q x`. Then liking `x` gains at
most `(q x - c) - π c` in expectation. This is negative when `q x < c (1 + π)`. -/
theorem like_gain_le {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω)
    (hμ1 : ∑ ω, μ ω = 1) {q : β → ℝ} (hq : ∀ y, 0 ≤ q y) {k : ℕ} {c : ℝ} (hc : 0 < c)
    {x : β} (hcx : c < q x) {D : Finset β} (hxD : x ∉ D) (R : Ω → Finset β)
    (sat : Ω → Prop) [DecidablePred sat]
    (hsat : ∀ ω, sat ω → x ∈ R ω ∧ ∃ T ⊆ D ∩ R ω, T.card = k ∧ ∀ y ∈ T, q x ≤ q y)
    {π : ℝ} (hπ : π ≤ ∑ ω, if sat ω then μ ω else 0) :
    ∑ ω, μ ω * (swipeUtil (topK q k) c (insert x D ∩ R ω) -
      swipeUtil (topK q k) c (D ∩ R ω)) ≤ (q x - c) - π * c := by
  have hper : ∀ ω, swipeUtil (topK q k) c (insert x D ∩ R ω) -
      swipeUtil (topK q k) c (D ∩ R ω) ≤ if sat ω then -c else q x - c := by
    intro ω
    by_cases hxR : x ∈ R ω
    · rw [insert_inter_of_mem hxR]
      have hxS : x ∉ D ∩ R ω := fun h => hxD (mem_inter.mp h).1
      unfold swipeUtil
      rw [card_insert_of_notMem hxS]
      push_cast
      split_ifs with hs
      · obtain ⟨_, T, hT, hTk, hdom⟩ := hsat ω hs
        have := topK_insert_le_of_dominated hxS hT hTk hdom
        linarith
      · have h1 := topK_union_le q k {x} (D ∩ R ω)
        rw [← insert_eq] at h1
        have h2 := topK_singleton_le hq k x
        linarith
    · rw [insert_inter_of_notMem hxR]
      have hs : ¬ sat ω := fun h => hxR (hsat ω h).1
      simp only [hs, ↓reduceIte]
      linarith
  have hrw : ∀ ω, μ ω * (if sat ω then -c else q x - c) =
      μ ω * (q x - c) - (if sat ω then μ ω else 0) * q x := by
    intro ω; split_ifs <;> ring
  have hP0 : 0 ≤ ∑ ω, if sat ω then μ ω else 0 :=
    sum_nonneg fun ω _ => by split_ifs; exacts [hμ ω, le_refl 0]
  calc ∑ ω, μ ω * (swipeUtil (topK q k) c (insert x D ∩ R ω) -
        swipeUtil (topK q k) c (D ∩ R ω))
      ≤ ∑ ω, μ ω * (if sat ω then -c else q x - c) :=
        sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hper ω) (hμ ω)
    _ = (q x - c) - (∑ ω, if sat ω then μ ω else 0) * q x := by
        rw [sum_congr rfl fun ω _ => hrw ω, sum_sub_distrib, ← sum_mul, ← sum_mul, hμ1, one_mul]
    _ ≤ (q x - c) - π * c := by nlinarith

/-- The values in the Bayes–Nash example: `x = 0` at 1.05, and another profile `y = 1`
at 2. -/
noncomputable def bnValues : Fin 2 → ℝ := ![1.05, 2]

/-- **Impossibility 1, the Bayes–Nash example.** A top-1 user with cost 1 likes `y`
(valued 2) and weighs liking `x` (valued 1.05), who always likes back. With probability
0.3, `y` also likes back; otherwise only `x` would. Liking `x` changes expected utility
by `0.7 · 0.05 - 0.3 · 1 = -0.265`. -/
theorem impossibility1_bn_example :
    0.3 * (swipeUtil (topK bnValues 1) 1 ({0, 1} ∩ univ) -
        swipeUtil (topK bnValues 1) 1 ({1} ∩ univ)) +
      0.7 * (swipeUtil (topK bnValues 1) 1 ({0, 1} ∩ {0}) -
        swipeUtil (topK bnValues 1) 1 ({1} ∩ {0})) = -0.265 := by
  have hnn : ∀ i, 0 ≤ bnValues i := fun i => by fin_cases i <;> norm_num [bnValues]
  have h0 : topK bnValues 1 {0} = 1.05 := by
    rw [topK_eq_sum_of_card_le hnn (by simp)]; simp [bnValues]
  have h1 : topK bnValues 1 {1} = 2 := by
    rw [topK_eq_sum_of_card_le hnn (by simp)]; simp [bnValues]
  have hu : topK bnValues 1 univ = 2 := le_antisymm
    (topK_one_le (by norm_num) fun i _ => by fin_cases i <;> norm_num [bnValues])
    (by simpa [bnValues] using le_topK_one (q := bnValues) (mem_univ (1 : Fin 2)))
  have e1 : ({0, 1} : Finset (Fin 2)) ∩ univ = univ := by decide
  have e2 : ({1} : Finset (Fin 2)) ∩ univ = {1} := by decide
  have e3 : ({0, 1} : Finset (Fin 2)) ∩ {0} = {0} := by decide
  have e4 : ({1} : Finset (Fin 2)) ∩ {0} = ∅ := by decide
  simp only [swipeUtil, e1, e2, e3, e4, h0, h1, hu, topK_empty, card_singleton, card_empty,
    card_univ, Fintype.card_fin]
  norm_num

end Impossibility1

section Prop6

variable {β : Type*} [DecidableEq β]

/-- **Proposition 6(a): DSIC without queries.** Without queries, what a user sees does not
depend on its own values, so fix the profiles `N` it sees and the set `N' ⊆ N` of those
that can match it (any subset `R ⊆ N'` may turn out to like back, for some behavior of
the others). Each value is independent with `0 < φ < 1`: every profile has a possible
value `lo x ≤ c` and a possible value `hi x > c`, and by independence every combination
of these has positive probability. Then sincere swiping is dominant for a top-`k` user
(`k ≥ 1`, `c > 0`), for every such value combination and every `R ⊆ N'`, iff `|N'| ≤ k`. -/
theorem zeroQuery_topK_dsic_iff {k : ℕ} (hk : 1 ≤ k) {c : ℝ} (hc : 0 < c)
    {N N' : Finset β} (hN' : N' ⊆ N) (lo hi : β → ℝ) (hlo : ∀ x, 0 ≤ lo x ∧ lo x ≤ c)
    (hhi : ∀ x, c < hi x) :
    (∀ q : β → ℝ, (∀ x, q x = lo x ∨ q x = hi x) → ∀ R ⊆ N', ∀ D ⊆ N,
        swipeUtil (topK q k) c (D ∩ R) ≤ swipeUtil (topK q k) c (sincereSet q c N ∩ R)) ↔
      N'.card ≤ k := by
  -- On `R ⊆ N'`, sincere likes among `N` and among `N'` give the same matches.
  have hsame : ∀ q : β → ℝ, ∀ R ⊆ N', sincereSet q c N ∩ R = sincereSet q c N' ∩ R := by
    intro q R hR
    ext x
    simp only [sincereSet, mem_inter, mem_filter]
    exact ⟨fun ⟨⟨_, h2⟩, h3⟩ => ⟨⟨hR h3, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨⟨hN' h1, h2⟩, h3⟩⟩
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have hhi0 : ∀ x, 0 ≤ hi x := fun x => (hc.trans (hhi x)).le
    have hA : sincereSet hi c N' = N' := filter_true_of_mem fun x _ => hhi x
    have hns : ¬ CostSeparable (topK hi k) c (sincereSet hi c N') := fun hcs => by
      have := (costSeparable_topK_iff hhi0 k hc (A := sincereSet hi c N')
        fun x hx => (mem_filter.mp hx).2).mp hcs
      rw [hA] at this
      omega
    obtain ⟨R, D, hD, hlt'⟩ := sincere_not_best hns
    have hR' : R ∩ N' ⊆ N' := inter_subset_right
    have h1 := h hi (fun x => Or.inr rfl) (R ∩ N') hR' D (hD.trans hN')
    rw [hsame hi _ hR'] at h1
    have e1 : D ∩ (R ∩ N') = D ∩ R := by
      rw [← inter_assoc, inter_right_comm, inter_eq_left.mpr hD]
    have e2 : sincereSet hi c N' ∩ (R ∩ N') = sincereSet hi c N' ∩ R := by
      rw [← inter_assoc, inter_right_comm,
        inter_eq_left.mpr (show sincereSet hi c N' ⊆ N' from filter_subset _ _)]
    rw [e1, e2] at h1
    linarith
  · intro hcard q hq R hR D hD
    have hq0 : ∀ x, 0 ≤ q x := fun x => by
      rcases hq x with h | h
      · rw [h]; exact (hlo x).1
      · rw [h]; exact (hc.trans (hhi x)).le
    have hsep : CostSeparable (topK q k) c (sincereSet q c N') :=
      (costSeparable_topK_iff hq0 k hc fun x hx => (mem_filter.mp hx).2).mpr
        ((card_le_card (filter_subset _ _)).trans hcard)
    have e : D ∩ R = (D ∩ N') ∩ R := by
      rw [inter_assoc, inter_eq_right.mpr hR]
    rw [e, hsame q R hR]
    exact sincere_best (topK_union_le q k) (topK_singleton hq0 hk) hsep R inter_subset_right

end Prop6

section ExPost

/-- Values in the T5 example: `x₁ = 0` at 3, `x₂ = 1` at 2. -/
def expostValues : Fin 2 → ℝ := ![3, 2]

/-- **T5: ex post is weaker than DSIC.** A top-1 user with cost 1 is shown `x₁` (value 3)
and `x₂` (value 2), and the oracle knows `x₂` would pass. If `x₂` passes, as sincere play
says (`R = {x₁}`), sincere swiping earns 2 and no set of likes does better. If `x₂` likes
anyway (`R = {x₁, x₂}`), sincere swiping earns 1 and liking only `x₁` earns 2. -/
theorem expost_not_dsic :
    (swipeUtil (topK expostValues 1) 1 (sincereSet expostValues 1 univ ∩ {0}) = 2 ∧
      ∀ D : Finset (Fin 2), swipeUtil (topK expostValues 1) 1 (D ∩ {0}) ≤ 2) ∧
    swipeUtil (topK expostValues 1) 1 (sincereSet expostValues 1 univ ∩ univ) = 1 ∧
      swipeUtil (topK expostValues 1) 1 ({0} ∩ univ) = 2 := by
  have hnn : ∀ i, 0 ≤ expostValues i := fun i => by fin_cases i <;> norm_num [expostValues]
  have h0 : topK expostValues 1 {0} = 3 := by
    rw [topK_eq_sum_of_card_le hnn (by simp)]; simp [expostValues]
  have hu : topK expostValues 1 univ = 3 := le_antisymm
    (topK_one_le (by norm_num) fun i _ => by fin_cases i <;> norm_num [expostValues])
    (by simpa [expostValues] using le_topK_one (q := expostValues) (mem_univ (0 : Fin 2)))
  have hA : sincereSet expostValues 1 univ = univ :=
    filter_true_of_mem fun i _ => by fin_cases i <;> norm_num [expostValues]
  have e1 : (univ : Finset (Fin 2)) ∩ {0} = {0} := by decide
  have e2 : ({0} : Finset (Fin 2)) ∩ univ = {0} := by decide
  refine ⟨⟨?_, fun D => ?_⟩, ?_, ?_⟩
  · simp only [hA, e1, swipeUtil, h0, card_singleton]; norm_num
  · rcases subset_singleton_iff.mp (inter_subset_right : D ∩ {0} ⊆ {0}) with h | h
    · rw [h]; simp [swipeUtil, topK_empty]
    · rw [h]; simp only [swipeUtil, h0, card_singleton]; norm_num
  · simp only [hA, inter_self, swipeUtil, hu, card_univ, Fintype.card_fin]; norm_num
  · simp only [e2, swipeUtil, h0, card_singleton]; norm_num

end ExPost

section Budget

variable {β : Type*} [DecidableEq β]

omit [DecidableEq β] in
/-- **Proposition 5(c), period 2 under a budget.** In period 2 everyone shown has already
liked the responder, so each like is a sure match, and for an additive responder the
period-2 likes add `∑_S (q - c)` to whatever period 1 gave. With a budget of `L` likes,
no `S ⊆ B` with `|S| ≤ L` beats the `L` best positive net values. -/
theorem budget_resp_le (q : β → ℝ) (c : ℝ) (L : ℕ) {B S : Finset β} (hSB : S ⊆ B)
    (hSL : S.card ≤ L) :
    ∑ x ∈ S, (q x - c) ≤ topK (fun x => max (q x - c) 0) L B :=
  (sum_le_sum fun _ _ => le_max_left _ _).trans (sum_le_topK hSB hSL)

omit [DecidableEq β] in
/-- **Proposition 5(c), the best response.** Liking the `L` most valued acceptable
profiles in the backlog attains the bound, so it is dominant for an additive responder
and reveals a ranking. -/
theorem budget_resp_attained (q : β → ℝ) (c : ℝ) (L : ℕ) (B : Finset β) :
    ∃ S ⊆ B, S.card ≤ L ∧ (∀ x ∈ S, c < q x) ∧
      ∑ x ∈ S, (q x - c) = topK (fun x => max (q x - c) 0) L B := by
  obtain ⟨W, hWB, hWL, hEq⟩ := exists_topK_eq (fun x => max (q x - c) 0) L B
  refine ⟨W.filter fun x => c < q x, (filter_subset _ _).trans hWB,
    (card_le_card (filter_subset _ _)).trans hWL, fun x hx => (mem_filter.mp hx).2, ?_⟩
  rw [hEq, ← sum_filter_add_sum_filter_not W (fun x => c < q x)]
  have h0 : ∑ x ∈ W.filter (fun x => ¬ c < q x), max (q x - c) 0 = 0 :=
    sum_eq_zero fun x hx => max_eq_right (by linarith [not_lt.mp (mem_filter.mp hx).2])
  rw [h0, add_zero]
  exact sum_congr rfl fun x hx => (max_eq_left (by linarith [(mem_filter.mp hx).2])).symm

end Budget

end DatingAlgo
