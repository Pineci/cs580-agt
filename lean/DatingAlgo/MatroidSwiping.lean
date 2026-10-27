import DatingAlgo.TruthfulSwiping

/-!
# Truthful swiping for weighted-matroid-rank users

The matroid corollary of Theorem 1 and the matroid case of Theorems 3(a), 5(a) in the
vault note "Truthful Swiping with an LLM Oracle".

A weighted-matroid-rank user values a set `S` at the most valuable subset of `S` that is
independent in its matroid `M` (`wRank`). Top-`k` is the uniform matroid; "at most one
partner per city" is a partition matroid. The note's model has `v {x} = q x`, which for a
matroid means no loops (`∀ x, M.Indep {x}`).

* `wRank_union_le`, `wRank_singleton`, `wRank_eq_sum_of_indep`: weighted rank is
  subadditive, equals `q x` on a non-loop, and is additive on independent sets.
* `costSeparable_wRank_iff` (Theorem 1, matroid corollary): with `c > 0`, a set of
  acceptable profiles is cost-separable iff it is independent.
* `sdh_dsic_matroid` (Theorems 3(a), 5(a)): if a matroid-rank user's planned partners
  in SDH are independent (its IR family), sincere swiping is dominant.
-/

namespace DatingAlgo

open Finset

section WRank

variable {β : Type*} [DecidableEq β]

open Classical in
/-- Weighted matroid rank: the most valuable subset of `S` independent in `M`. -/
noncomputable def wRank (M : Matroid β) (q : β → ℝ) (S : Finset β) : ℝ :=
  (S.powerset.filter fun T : Finset β => M.Indep (↑T : Set β)).sup'
    ⟨∅, mem_filter.mpr ⟨empty_mem_powerset S, by simp⟩⟩ fun T : Finset β => ∑ x ∈ T, q x

omit [DecidableEq β] in
/-- Any independent subset of `S` is a lower bound. -/
theorem sum_le_wRank {M : Matroid β} {q : β → ℝ} {S T : Finset β} (hTS : T ⊆ S)
    (hT : M.Indep (T : Set β)) : ∑ x ∈ T, q x ≤ wRank M q S := by
  classical
  unfold wRank
  exact le_sup' (fun T : Finset β => ∑ x ∈ T, q x) (mem_filter.mpr ⟨mem_powerset.mpr hTS, hT⟩)

omit [DecidableEq β] in
/-- `wRank` is attained by an independent subset. -/
theorem exists_wRank_eq (M : Matroid β) (q : β → ℝ) (S : Finset β) :
    ∃ T ⊆ S, M.Indep (T : Set β) ∧ wRank M q S = ∑ x ∈ T, q x := by
  classical
  unfold wRank
  obtain ⟨T, hT, hEq⟩ := exists_mem_eq_sup'
    (⟨∅, mem_filter.mpr ⟨empty_mem_powerset S, by simp⟩⟩ :
      (S.powerset.filter fun T : Finset β => M.Indep (↑T : Set β)).Nonempty)
    fun T : Finset β => ∑ x ∈ T, q x
  obtain ⟨hTS, hTi⟩ := mem_filter.mp hT
  exact ⟨T, mem_powerset.mp hTS, hTi, hEq⟩

/-- Weighted matroid rank is subadditive (for non-negative values). -/
theorem wRank_union_le {M : Matroid β} {q : β → ℝ} (hq : ∀ x, 0 ≤ q x) (S T : Finset β) :
    wRank M q (S ∪ T) ≤ wRank M q S + wRank M q T := by
  obtain ⟨W, hW, hWi, hEq⟩ := exists_wRank_eq M q (S ∪ T)
  rw [hEq, ← sum_filter_add_sum_filter_not W (· ∈ S)]
  -- The members of `W` outside `S` lie in `W ∩ T`.
  have hWT : W.filter (· ∉ S) ⊆ W.filter (· ∈ T) := fun x hx => by
    obtain ⟨hxW, hxS⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨hxW, (mem_union.mp (hW hxW)).resolve_left hxS⟩
  refine add_le_add (sum_le_wRank (fun x hx => (mem_filter.mp hx).2)
    (hWi.subset (coe_subset.mpr (filter_subset _ _))))
    ((sum_le_sum_of_subset_of_nonneg hWT fun x _ _ => hq x).trans
      (sum_le_wRank (fun x hx => (mem_filter.mp hx).2)
        (hWi.subset (coe_subset.mpr (filter_subset _ _)))))

omit [DecidableEq β] in
/-- On an independent set, weighted rank is the sum of values. -/
theorem wRank_eq_sum_of_indep {M : Matroid β} {q : β → ℝ} (hq : ∀ x, 0 ≤ q x)
    {S : Finset β} (hS : M.Indep (S : Set β)) : wRank M q S = ∑ x ∈ S, q x := by
  apply le_antisymm
  · obtain ⟨W, hWS, _, hEq⟩ := exists_wRank_eq M q S
    rw [hEq]
    exact sum_le_sum_of_subset_of_nonneg hWS fun x _ _ => hq x
  · exact sum_le_wRank subset_rfl hS

omit [DecidableEq β] in
/-- A non-loop is worth its value. -/
theorem wRank_singleton {M : Matroid β} {q : β → ℝ} (hq : ∀ x, 0 ≤ q x) {x : β}
    (hx : M.Indep ({x} : Set β)) : wRank M q {x} = q x := by
  rw [wRank_eq_sum_of_indep hq (by rwa [coe_singleton]), sum_singleton]

/-- **Theorem 1, matroid corollary.** For a weighted-matroid-rank user with non-negative
values and `c > 0`, a set `A` of acceptable profiles (`q x > c`) is cost-separable iff it
is independent. If `A` contains a circuit, its least valued element adds nothing. -/
theorem costSeparable_wRank_iff {M : Matroid β} {q : β → ℝ} (hq : ∀ x, 0 ≤ q x) {c : ℝ}
    (hc : 0 < c) {A : Finset β} (hA : ∀ x ∈ A, c < q x) :
    CostSeparable (wRank M q) c A ↔ M.Indep (A : Set β) := by
  classical
  constructor
  · intro hsep
    by_contra hdep
    -- A dependent subset `C` of `A` of least size: all its proper subsets are independent.
    obtain ⟨C, hC, hCmin⟩ := exists_min_image
      (A.powerset.filter fun C : Finset β => ¬ M.Indep (↑C : Set β)) card
      ⟨A, mem_filter.mpr ⟨mem_powerset_self A, hdep⟩⟩
    obtain ⟨hCA, hCdep⟩ := mem_filter.mp hC
    rw [mem_powerset] at hCA
    have hsmall : ∀ D ⊆ C, D ≠ C → M.Indep (↑D : Set β) := by
      intro D hDC hDne
      by_contra hD
      have := hCmin D (mem_filter.mpr ⟨mem_powerset.mpr (hDC.trans hCA), hD⟩)
      exact absurd (card_lt_card (ssubset_of_subset_of_ne hDC hDne)) (not_lt.mpr this)
    have hCne : C.Nonempty := by
      rw [nonempty_iff_ne_empty]
      rintro rfl
      exact hCdep (by simp)
    obtain ⟨x, hxC, hxmin⟩ := exists_min_image C q hCne
    set T := C.erase x
    -- The best independent subset of `C` is worth no more than `T`.
    have hle : wRank M q (insert x T) ≤ wRank M q T := by
      rw [insert_erase hxC]
      obtain ⟨W, hWC, hWi, hEq⟩ := exists_wRank_eq M q C
      rw [hEq]
      obtain ⟨y, hyC, hyW⟩ := exists_of_ssubset (ssubset_of_subset_of_ne hWC
        (fun h => hCdep (h ▸ hWi)))
      by_cases hxW : x ∈ W
      · have hyx : y ≠ x := fun h => hyW (h ▸ hxW)
        have hsub : insert y (W.erase x) ⊆ T := insert_subset (mem_erase.mpr ⟨hyx, hyC⟩)
          (erase_subset_erase x hWC)
        have hind : M.Indep (↑(insert y (W.erase x)) : Set β) :=
          hsmall _ (hsub.trans (erase_subset x C))
            (fun h => notMem_erase x C (hsub (h ▸ hxC)))
        calc ∑ i ∈ W, q i = q x + ∑ i ∈ W.erase x, q i := (add_sum_erase W q hxW).symm
          _ ≤ q y + ∑ i ∈ W.erase x, q i := by linarith [hxmin y hyC]
          _ = ∑ i ∈ insert y (W.erase x), q i :=
              (sum_insert (fun h => hyW (mem_of_mem_erase h))).symm
          _ ≤ wRank M q T := sum_le_wRank hsub hind
      · exact sum_le_wRank (fun i hi => mem_erase.mpr ⟨fun h => hxW (h ▸ hi), hWC hi⟩) hWi
    have := hsep x (hCA hxC) T (erase_subset_erase x hCA)
    linarith
  · intro hind x hx T hT
    have hxT : x ∉ T := fun h => (mem_erase.mp (hT h)).1 rfl
    have hTA : T ⊆ A := hT.trans (erase_subset x A)
    have hins : insert x T ⊆ A := insert_subset hx hTA
    rw [wRank_eq_sum_of_indep hq (hind.subset (coe_subset.mpr hins)),
      wRank_eq_sum_of_indep hq (hind.subset (coe_subset.mpr hTA)), sum_insert hxT]
    linarith [hA x hx]

end WRank

section Game

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **Theorems 3(a), 5(a) for matroid users: SDH is DSIC.** A weighted-matroid-rank user
`ℓ` (loopless matroid, non-negative values, `c ℓ > 0`) whose planned partners in SDH are
independent (SDH's IR family for matroid users) has sincere swiping as a best response to
every behavior `σ` of the others, for every deviation `(L, ρ)`. -/
theorem sdh_dsic_matroid {arcs : Finset (U × U)}
    (hone : ∀ a b, (a, b) ∈ arcs → (b, a) ∉ arcs) (hloop : ∀ a, (a, a) ∉ arcs)
    {q : U → U → ℝ} (hq : ∀ a b, 0 ≤ q a b) {c : U → ℝ} {ℓ : U} (hc : 0 < c ℓ)
    (M : Matroid U) (hloopless : ∀ x, M.Indep ({x} : Set U))
    (hind : M.Indep ((plannedPartners arcs ℓ : Finset U) : Set U))
    (σ : SwipeProfile U) (L : U → Bool) (ρ : Finset U → Finset U) :
    swipeUtil (wRank M (q ℓ)) (c ℓ) (matchesOf arcs (σ.update ℓ L ρ) ℓ) ≤
      swipeUtil (wRank M (q ℓ)) (c ℓ)
        (matchesOf arcs (σ.update ℓ (sincereLike q c ℓ) (sincereResp q c ℓ)) ℓ) := by
  have hA : ∀ x ∈ sincereSet (q ℓ) (c ℓ) (plannedPartners arcs ℓ), c ℓ < q ℓ x :=
    fun x hx => (mem_filter.mp hx).2
  refine sdh_dsic hone hloop (wRank_union_le (hq ℓ))
    (fun x => wRank_singleton (hq ℓ) (hloopless x))
    ((costSeparable_wRank_iff (hq ℓ) hc hA).mpr (hind.subset ?_)) σ L ρ
  exact coe_subset.mpr (filter_subset _ _)

end Game

end DatingAlgo
