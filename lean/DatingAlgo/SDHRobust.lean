import DatingAlgo.TruthfulSwiping

/-!
# SDH: robustness, budgets, and manipulable oracle reports

Results about SDH's two-period game in the vault note "Truthful Swiping with an LLM
Oracle":

* `sdh_robust` (Theorem 5(e)): if the users outside a set `Dev` are sincere, welfare is
  at least the sum of net weights `w_e` over planned pairs with neither end in `Dev`.
  Deviators can only break their own pairs, and since every user sees only acceptable
  planned partners inside its IR set, nobody's utility is negative.
* `sdh_budget_feasible` (Proposition 5(a)): with at most `L` planned out-arcs and `L`
  planned in-arcs per user, sincere swiping never likes more than `L` profiles in a
  period, whatever the others do, so a budget of `L` likes per period never binds.
* `report_manipulation` (T5): SDH is not DSIC in the values a user reports to the
  oracle.
-/

namespace DatingAlgo

open Finset

section Game

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- A user's matches are always among its planned partners. -/
theorem matchesOf_subset_planned (arcs : Finset (U × U)) (σ : SwipeProfile U) (ℓ : U) :
    matchesOf arcs σ ℓ ⊆ plannedPartners arcs ℓ := by
  intro x hx
  simp only [matchesOf, plannedPartners, mem_union, mem_filter, mem_univ, true_and] at hx ⊢
  rcases hx with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

/-- Summing over every user's out-arcs in `G` counts each arc of `G` once. -/
theorem sum_out_arcs (G : Finset (U × U)) (h : U → U → ℝ) :
    ∑ u, ∑ x ∈ univ.filter (fun x => (u, x) ∈ G), h u x = ∑ e ∈ G, h e.1 e.2 := by
  simp only [sum_filter]
  rw [← Fintype.sum_prod_type' (fun u x => if (u, x) ∈ G then h u x else 0), sum_ite_mem,
    univ_inter]

/-- Summing over every user's in-arcs in `G` counts each arc of `G` once. -/
theorem sum_in_arcs (G : Finset (U × U)) (h : U → U → ℝ) :
    ∑ u, ∑ x ∈ univ.filter (fun x => (x, u) ∈ G), h u x = ∑ e ∈ G, h e.2 e.1 := by
  simp only [sum_filter]
  rw [sum_comm, ← Fintype.sum_prod_type' (fun x u => if (x, u) ∈ G then h u x else 0),
    sum_ite_mem, univ_inter]

/-- **Theorem 5(e): robustness.** Planned arcs are oriented one way, with no self-pairs,
and every planned pair is mutually acceptable. Each user's value is additive on its
planned partners (true on its IR set for additive, top-`k` and cap-1 users). If every
user outside `Dev` swipes sincerely, then whatever the users in `Dev` do, welfare is at
least the sum of the net weights `(q a b - c a) + (q b a - c b)` of the planned pairs
with neither end in `Dev`. -/
theorem sdh_robust {arcs : Finset (U × U)} (hone : ∀ a b, (a, b) ∈ arcs → (b, a) ∉ arcs)
    (_hloop : ∀ a, (a, a) ∉ arcs) {q : U → U → ℝ} {c : U → ℝ}
    (hacc : ∀ a b, (a, b) ∈ arcs → c a < q a b ∧ c b < q b a)
    (v : U → Finset U → ℝ)
    (hadd : ∀ u T, T ⊆ plannedPartners arcs u → v u T = ∑ x ∈ T, q u x)
    (Dev : Finset U) (σ : SwipeProfile U)
    (hsinc : ∀ u, u ∉ Dev → σ.like1 u = sincereLike q c u ∧ σ.resp u = sincereResp q c u) :
    ∑ e ∈ arcs.filter (fun e => e.1 ∉ Dev ∧ e.2 ∉ Dev),
        ((q e.1 e.2 - c e.1) + (q e.2 e.1 - c e.2)) ≤
      ∑ u, swipeUtil (v u) (c u) (matchesOf arcs σ u) := by
  set G := arcs.filter (fun e => e.1 ∉ Dev ∧ e.2 ∉ Dev)
  -- Planned pairs with no deviator match.
  have hG : ∀ a b, (a, b) ∈ G → b ∈ matchesOf arcs σ a ∧ a ∈ matchesOf arcs σ b := by
    intro a b hab
    obtain ⟨harc, ha, hb⟩ := mem_filter.mp hab
    exact sdh_arc_matches harc (hsinc a ha).1 (hsinc b hb).2 (hacc a b harc).1
      (hacc a b harc).2
  -- Each user gets at least the net values of its good out- and in-arcs.
  have hu : ∀ u, ∑ x ∈ univ.filter (fun x => (u, x) ∈ G), (q u x - c u) +
      ∑ x ∈ univ.filter (fun x => (x, u) ∈ G), (q u x - c u) ≤
        swipeUtil (v u) (c u) (matchesOf arcs σ u) := by
    intro u
    have hM := matchesOf_subset_planned arcs σ u
    have hutil : swipeUtil (v u) (c u) (matchesOf arcs σ u) =
        ∑ x ∈ matchesOf arcs σ u, (q u x - c u) := by
      unfold swipeUtil
      rw [hadd u _ hM, sum_sub_distrib, sum_const, nsmul_eq_mul]
      ring
    rw [hutil, ← sum_union]
    · refine sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) (fun x hx _ => ?_)
      · rcases mem_union.mp hx with h | h
        · exact (hG u x (mem_filter.mp h).2).1
        · exact (hG x u (mem_filter.mp h).2).2
      · have := hM hx
        simp only [plannedPartners, mem_union, mem_filter, mem_univ, true_and] at this
        rcases this with h | h
        · exact (sub_pos.mpr (hacc u x h).1).le
        · exact (sub_pos.mpr (hacc x u h).2).le
    · rw [disjoint_left]
      intro x hx1 hx2
      exact hone u x (mem_filter.mp (mem_filter.mp hx1).2).1
        (mem_filter.mp (mem_filter.mp hx2).2).1
  calc ∑ e ∈ G, ((q e.1 e.2 - c e.1) + (q e.2 e.1 - c e.2))
      = ∑ e ∈ G, (q e.1 e.2 - c e.1) + ∑ e ∈ G, (q e.2 e.1 - c e.2) := sum_add_distrib
    _ = ∑ u, (∑ x ∈ univ.filter (fun x => (u, x) ∈ G), (q u x - c u) +
          ∑ x ∈ univ.filter (fun x => (x, u) ∈ G), (q u x - c u)) := by
        rw [sum_add_distrib]
        exact congrArg₂ (· + ·) (sum_out_arcs G fun u x => q u x - c u).symm
          (sum_in_arcs G fun u x => q u x - c u).symm
    _ ≤ ∑ u, swipeUtil (v u) (c u) (matchesOf arcs σ u) := sum_le_sum fun u _ => hu u

/-- **Proposition 5(a): budgets never bind under SDH.** If `ℓ` has at most `L` planned
out-arcs and at most `L` planned in-arcs, then sincere swiping likes at most `L`
profiles in period 1 and at most `L` in period 2, whatever the others do. -/
theorem sdh_budget_feasible {arcs : Finset (U × U)} {q : U → U → ℝ} {c : U → ℝ} {ℓ : U}
    {L : ℕ} (hout : (univ.filter fun r => (ℓ, r) ∈ arcs).card ≤ L)
    (hin : (univ.filter fun s => (s, ℓ) ∈ arcs).card ≤ L) (σ : SwipeProfile U) :
    (univ.filter fun r => (ℓ, r) ∈ arcs ∧ sincereLike q c ℓ r = true).card ≤ L ∧
      (sincereResp q c ℓ (display2 arcs σ ℓ)).card ≤ L := by
  constructor
  · refine (card_le_card fun r hr => ?_).trans hout
    simp only [mem_filter, mem_univ, true_and] at hr ⊢
    exact hr.1
  · refine (card_le_card fun s hs => ?_).trans hin
    simp only [sincereResp, display2, mem_filter, mem_univ, true_and] at hs ⊢
    exact hs.1.1

end Game

section Reports

/-- Net weights of the two candidate pairs `ℓ–x` (index 0) and `ℓ–y` (index 1) in the T5
example, computed from reported values. `ℓ` reports `rx` for `x` and 2 for `y`; `x`
values `ℓ` at 1.1, `y` values `ℓ` at 3, and all costs are 1. -/
noncomputable def reportWeights (rx : ℝ) : Fin 2 → ℝ := ![(rx - 1) + (1.1 - 1), (2 - 1) + (3 - 1)]

/-- SDH's selection for `ℓ` (cap 1): the capped set of pairs with the largest weight. -/
def IsBestCapped (w : Fin 2 → ℝ) (S : Finset (Fin 2)) : Prop :=
  S.card ≤ 1 ∧ ∀ T : Finset (Fin 2), T.card ≤ 1 → ∑ e ∈ T, w e ≤ ∑ e ∈ S, w e

/-- The subsets of `Fin 2` with at most one element. -/
theorem fin2_card_le_one : ∀ S : Finset (Fin 2), S.card ≤ 1 → S = ∅ ∨ S = {0} ∨ S = {1} := by
  decide

/-- **T5: SDH is not DSIC in oracle reports.** A top-1 user `ℓ` with cost 1 values `x` at
3 and `y` at 2. Reporting truthfully, the pairs weigh 2.1 and 3, SDH's only choice is
`ℓ–y`, and `ℓ` gets `2 - 1 = 1`. Reporting 5 for `x` makes `ℓ–x` weigh 4.1, SDH's only
choice is `ℓ–x`, and `ℓ` truly gets `3 - 1 = 2`. -/
theorem report_manipulation :
    (∀ S, IsBestCapped (reportWeights 3) S ↔ S = {1}) ∧
      (∀ S, IsBestCapped (reportWeights 5) S ↔ S = {0}) ∧
      ((2 : ℝ) - 1 < 3 - 1) := by
  refine ⟨fun S => ⟨fun ⟨hcard, hbest⟩ => ?_, ?_⟩, fun S => ⟨fun ⟨hcard, hbest⟩ => ?_, ?_⟩,
    by norm_num⟩
  · have h1 := hbest {1} (by simp)
    rcases fin2_card_le_one S hcard with rfl | rfl | rfl
    · norm_num [reportWeights] at h1
    · norm_num [reportWeights] at h1
    · rfl
  · rintro rfl
    refine ⟨by simp, fun T hT => ?_⟩
    rcases fin2_card_le_one T hT with rfl | rfl | rfl <;> norm_num [reportWeights]
  · have h0 := hbest {0} (by simp)
    rcases fin2_card_le_one S hcard with rfl | rfl | rfl
    · norm_num [reportWeights] at h0
    · rfl
    · norm_num [reportWeights] at h0
  · rintro rfl
    refine ⟨by simp, fun T hT => ?_⟩
    rcases fin2_card_le_one T hT with rfl | rfl | rfl <;> norm_num [reportWeights]

end Reports

end DatingAlgo
