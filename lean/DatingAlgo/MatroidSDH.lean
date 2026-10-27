import DatingAlgo.ScreenedDH
import DatingAlgo.MatroidSwiping

/-!
# Screened DH for matroid users: Theorem 3(b) with `(1 - 1/e)²`

The matroid case of Theorem 3(b) in the vault note "Truthful Swiping with an LLM Oracle".
Each user's IR family is the independent sets of a matroid (for example at most one
partner per city, truncated at the user's capacity `b`).

**Model.** A `ScreenedMarket` supplies the pairs, value combinations, values and costs
(its caps are ignored here). `MatroidFamilies` gives each `i` a matroid on `J` and each
`j` a matroid on `I`. A match set is feasible (`MatOK`) if every user's partners are
independent in its matroid.
* `optIRM`: the expected best feasible set of acceptable pairs, knowing every value.
* The plan (the LP): `x e c ∈ [0, π e c]`, zero on unacceptable combinations, and every
  user's vector of pair totals `(∑_c x (i, j) c)_j` lies in its *matroid polytope*, the
  convex hull of the indicator vectors of independent sets (`matroidPolytope`).
* `sdhValueM τ`: query each pair independently with probability `τ e`, then take the best
  feasible set of pairs found acceptable.

**Results.**
* `matroid_correlation_gap`: for independent coins whose marginals lie in the matroid
  polytope, the expected rank of the random set is at least `(1 - 1/e) ∑ p` (the
  correlation gap of matroid rank functions).
* `prodExp_matroid_gap`: the same with independent random non-negative weights and
  weighted rank, by the layer cake (weighted rank is the integral of the rank of the
  superlevel sets).
* `optIRM_le_lpValue`, `exists_isLPOptimalM`: the LP bounds `OPT_IR` and has an optimum.
* `lpValue_le_sdhValueM`, `sdh_welfare_matroid` (Theorem 3(b), matroids):
  `SDH ≥ (1 - 1/e)² LP ≥ (1 - 1/e)² OPT_IR`.
* `welfare_eq_sum_wt_matroid`: on feasible sets, matroid-rank users' utilities are
  additive, so welfare is the sum of net weights.
* `sum_le_of_mem_matroidPolytope`: a user's planned total is at most its rank, which
  gives the table's `O(rank / p̂)` calls through Theorem 3(c)'s per-pair bound.
-/

namespace DatingAlgo

open Finset

section Polytope

variable {β : Type*} [DecidableEq β]

/-- Indicator vector of a finite set. -/
def indVec (T : Finset β) : β → ℝ := fun b => if b ∈ T then 1 else 0

/-- The matroid polytope: the convex hull of indicator vectors of independent sets. -/
def matroidPolytope (Mt : Matroid β) : Set (β → ℝ) :=
  convexHull ℝ {y | ∃ T : Finset β, Mt.Indep (↑T : Set β) ∧ y = indVec T}

/-- Scaling one coordinate of a point of the polytope by `α ∈ [0, 1]` stays in the
polytope: on a generator `1_T` it gives `α 1_T + (1 - α) 1_{T - e}`. -/
theorem scale_mem_matroidPolytope (Mt : Matroid β) {y : β → ℝ}
    (hy : y ∈ matroidPolytope Mt) (e : β) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    (fun b => if b = e then α * y b else y b) ∈ matroidPolytope Mt := by
  set φ : (β → ℝ) → β → ℝ := fun y b => if b = e then α * y b else y b with hφ
  have hconv : Convex ℝ (φ ⁻¹' matroidPolytope Mt) := by
    intro u hu v hv s t hs ht hst
    have h : φ (s • u + t • v) = s • φ u + t • φ v := by
      funext b
      simp only [hφ, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> ring
    rw [Set.mem_preimage, h]
    exact convex_convexHull ℝ _ hu hv hs ht hst
  have hsub : {y | ∃ T : Finset β, Mt.Indep (↑T : Set β) ∧ y = indVec T} ⊆
      φ ⁻¹' matroidPolytope Mt := by
    rintro _ ⟨T, hT, rfl⟩
    have hTe : Mt.Indep (↑(T.erase e) : Set β) := hT.subset (coe_subset.mpr (erase_subset e T))
    have h : φ (indVec T) = α • indVec T + (1 - α) • indVec (T.erase e) := by
      funext b
      simp only [hφ, indVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mem_erase]
      by_cases hb : b = e
      · subst hb
        split_ifs <;> simp_all
      · simp only [hb, ↓reduceIte, ne_eq, not_false_eq_true, true_and]
        split_ifs <;> ring
    rw [Set.mem_preimage, h]
    refine convex_convexHull ℝ _ ?_ ?_ hα0 (by linarith) (by ring)
    · exact subset_convexHull ℝ _ ⟨T, hT, rfl⟩
    · exact subset_convexHull ℝ _ ⟨T.erase e, hTe, rfl⟩
  exact convexHull_min hsub hconv hy

/-- The matroid polytope is closed downward in the non-negative orthant. -/
theorem matroidPolytope_downward [Fintype β] (Mt : Matroid β) {y z : β → ℝ}
    (hy : y ∈ matroidPolytope Mt) (hz0 : ∀ b, 0 ≤ z b) (hzy : ∀ b, z b ≤ y b) :
    z ∈ matroidPolytope Mt := by
  set α : β → ℝ := fun b => if y b = 0 then 0 else z b / y b with hα
  have hα01 : ∀ b, 0 ≤ α b ∧ α b ≤ 1 := by
    intro b
    simp only [hα]
    split_ifs with h
    · exact ⟨le_rfl, zero_le_one⟩
    · have hpos : 0 < y b := lt_of_le_of_ne ((hz0 b).trans (hzy b)) (Ne.symm h)
      exact ⟨div_nonneg (hz0 b) hpos.le, (div_le_one hpos).mpr (hzy b)⟩
  have hzα : ∀ b, z b = α b * y b := by
    intro b
    simp only [hα]
    split_ifs with h
    · rw [zero_mul]; exact le_antisymm (h ▸ hzy b) (hz0 b)
    · rw [div_mul_cancel₀ _ h]
  have key : ∀ s : Finset β,
      (fun b => if b ∈ s then α b * y b else y b) ∈ matroidPolytope Mt := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hy
    | insert a s ha ih =>
      convert scale_mem_matroidPolytope Mt ih a (hα01 a).1 (hα01 a).2 using 1
      funext b
      by_cases hb : b = a
      · subst hb; simp [ha]
      · simp [hb]
  convert key univ using 1
  funext b
  simp [hzα b]

/-- Points of the polytope lie in `[0, 1]`. -/
theorem matroidPolytope_mem_Icc (Mt : Matroid β) {y : β → ℝ}
    (hy : y ∈ matroidPolytope Mt) (b : β) : 0 ≤ y b ∧ y b ≤ 1 := by
  have hconv : Convex ℝ {y : β → ℝ | 0 ≤ y b ∧ y b ≤ 1} := by
    intro u hu v hv s t hs ht hst
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hu hv ⊢
    constructor
    · nlinarith [mul_nonneg hs hu.1, mul_nonneg ht hv.1]
    · nlinarith [mul_le_mul_of_nonneg_left hu.2 hs, mul_le_mul_of_nonneg_left hv.2 ht]
  refine convexHull_min ?_ hconv hy
  rintro _ ⟨T, -, rfl⟩
  simp only [Set.mem_ofPred_eq, indVec]
  split_ifs <;> norm_num

/-- A linear inequality that holds at every independent set holds on the polytope. -/
theorem sum_mul_le_of_mem_matroidPolytope [Fintype β] (Mt : Matroid β) (a : β → ℝ) (c : ℝ)
    (h : ∀ T : Finset β, Mt.Indep (↑T : Set β) → ∑ b ∈ T, a b ≤ c) {y : β → ℝ}
    (hy : y ∈ matroidPolytope Mt) : ∑ b, y b * a b ≤ c := by
  have hconv : Convex ℝ {y : β → ℝ | ∑ b, y b * a b ≤ c} := by
    intro u hu v hv s t hs ht hst
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hu hv ⊢
    have e1 : ∑ b, (s * u b + t * v b) * a b = s * ∑ b, u b * a b + t * ∑ b, v b * a b := by
      rw [mul_sum, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun b _ => by ring
    have e2 : s * c + t * c = c := by rw [← add_mul, hst, one_mul]
    rw [e1]
    nlinarith [mul_le_mul_of_nonneg_left hu hs, mul_le_mul_of_nonneg_left hv ht]
  refine convexHull_min ?_ hconv hy
  rintro _ ⟨T, hT, rfl⟩
  simp only [Set.mem_ofPred_eq, indVec, ite_mul, one_mul, zero_mul, sum_ite_mem, univ_inter]
  exact h T hT

/-- A point of the polytope sums to at most the size of the largest independent set. -/
theorem sum_le_of_mem_matroidPolytope [Fintype β] (Mt : Matroid β) {r : ℕ}
    (hr : ∀ T : Finset β, Mt.Indep (↑T : Set β) → T.card ≤ r) {y : β → ℝ}
    (hy : y ∈ matroidPolytope Mt) : ∑ b, y b ≤ r := by
  have := sum_mul_le_of_mem_matroidPolytope Mt (fun _ => 1) r
    (fun T hT => by simpa using hr T hT) hy
  simpa using this

/-- Averaging indicator vectors of independent sets stays in the matroid polytope. -/
theorem prodExp_mem_matroidPolytope {ι Ω : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Ω] (Mt : Matroid β) {μ : ι → Ω → ℝ} (hμ : IsDist μ)
    (T : (ι → Ω) → Finset β) (hT : ∀ ω, Mt.Indep (↑(T ω) : Set β)) :
    (fun b => prodExp μ fun ω => if b ∈ T ω then 1 else 0) ∈ matroidPolytope Mt := by
  have heq : (fun b => prodExp μ fun ω => if b ∈ T ω then 1 else 0) =
      ∑ ω : ι → Ω, (∏ e, μ e (ω e)) • indVec (T ω) := by
    funext b
    simp only [prodExp, indVec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  refine (convex_convexHull ℝ _).sum_mem (fun ω _ => prod_nonneg fun e _ => hμ.1 e _) ?_
    fun ω _ => subset_convexHull ℝ _ ⟨T ω, hT ω, rfl⟩
  rw [sum_prod_weight]
  simp [hμ.2]

/-- The matroid polytope is closed: it is the convex hull of finitely many points. -/
theorem isClosed_matroidPolytope [Fintype β] (Mt : Matroid β) :
    IsClosed (matroidPolytope Mt) := by
  have hfin : {y | ∃ T : Finset β, Mt.Indep (↑T : Set β) ∧ y = indVec T}.Finite :=
    (Set.finite_range (indVec (β := β))).subset fun y ⟨T, _, hy⟩ => ⟨T, hy.symm⟩
  exact hfin.isClosed_convexHull ℝ

/-! #### Rank -/

omit [DecidableEq β] in
/-- Weighted rank is monotone in the set. -/
theorem wRank_mono_set {Mt : Matroid β} {q : β → ℝ} {S S' : Finset β} (h : S ⊆ S') :
    wRank Mt q S ≤ wRank Mt q S' := by
  obtain ⟨T, hTS, hT, hEq⟩ := exists_wRank_eq Mt q S
  rw [hEq]
  exact sum_le_wRank (hTS.trans h) hT

omit [DecidableEq β] in
/-- Weighted rank is never negative: the empty set is independent. -/
theorem wRank_nonneg_set (Mt : Matroid β) (q : β → ℝ) (S : Finset β) : 0 ≤ wRank Mt q S := by
  have := sum_le_wRank (M := Mt) (q := q) (empty_subset S) (by simp)
  simpa using this

omit [DecidableEq β] in
/-- Weighted rank only sees the weights on the set. -/
theorem wRank_congr_set {Mt : Matroid β} {q q' : β → ℝ} {S : Finset β}
    (h : ∀ x ∈ S, q x = q' x) : wRank Mt q S = wRank Mt q' S := by
  apply le_antisymm
  · obtain ⟨T, hTS, hT, hEq⟩ := exists_wRank_eq Mt q S
    rw [hEq, sum_congr rfl fun x hx => h x (hTS hx)]
    exact sum_le_wRank hTS hT
  · obtain ⟨T, hTS, hT, hEq⟩ := exists_wRank_eq Mt q' S
    rw [hEq, ← sum_congr rfl fun x hx => h x (hTS hx)]
    exact sum_le_wRank hTS hT

omit [DecidableEq β] in
/-- Elements of weight zero don't change the weighted rank. -/
theorem wRank_le_filter_pos {Mt : Matroid β} {q : β → ℝ} {S : Finset β}
    (hq : ∀ x ∈ S, 0 ≤ q x) : wRank Mt q S ≤ wRank Mt q (S.filter fun x => 0 < q x) := by
  obtain ⟨T, hTS, hT, hEq⟩ := exists_wRank_eq Mt q S
  rw [hEq, ← sum_filter_of_ne (p := fun x => 0 < q x)
    (fun x hx hne => lt_of_le_of_ne (hq x (hTS hx)) (Ne.symm hne))]
  exact sum_le_wRank (fun x hx => mem_filter.mpr ⟨hTS (mem_filter.mp hx).1, (mem_filter.mp hx).2⟩)
    (hT.subset (coe_subset.mpr (filter_subset _ _)))

/-- Augmentation for finite independent sets: `B` extends by elements of `T` to an
independent set with at least `|T|` elements. -/
theorem exists_augment_card {Mt : Matroid β} {B T : Finset β} (hB : Mt.Indep (↑B : Set β))
    (hT : Mt.Indep (↑T : Set β)) :
    ∃ A ⊆ T \ B, Mt.Indep (↑(B ∪ A) : Set β) ∧ T.card ≤ B.card + A.card := by
  suffices H : ∀ n : ℕ, ∀ B : Finset β, Mt.Indep (↑B : Set β) → T.card ≤ B.card + n →
      ∃ A ⊆ T \ B, Mt.Indep (↑(B ∪ A) : Set β) ∧ T.card ≤ B.card + A.card from
    H T.card B hB (by omega)
  intro n
  induction n with
  | zero =>
    intro B hB h
    exact ⟨∅, empty_subset _, by simpa using hB, by simpa using h⟩
  | succ n ih =>
    intro B hB h
    by_cases hle : T.card ≤ B.card
    · exact ⟨∅, empty_subset _, by simpa using hB, by simpa using hle⟩
    · obtain ⟨e, heT, heB, hins⟩ := hB.augment_finset hT (by omega)
      have hins' : Mt.Indep (↑(insert e B) : Set β) := by simpa using hins
      obtain ⟨A, hA, hAi, hcard⟩ :=
        ih (insert e B) hins' (by rw [card_insert_of_notMem heB]; omega)
      have heA : e ∉ A := fun h => (mem_sdiff.mp (hA h)).2 (mem_insert_self e B)
      refine ⟨insert e A, fun x hx => ?_, ?_, ?_⟩
      · rcases mem_insert.mp hx with rfl | hx
        · exact mem_sdiff.mpr ⟨heT, heB⟩
        · have := mem_sdiff.mp (hA hx)
          exact mem_sdiff.mpr ⟨this.1, fun h => this.2 (mem_insert_of_mem h)⟩
      · rwa [union_insert, ← insert_union]
      · rw [card_insert_of_notMem heA]
        rw [card_insert_of_notMem heB] at hcard
        omega

/-- **Marginal gains of matroid rank.** For an independent `T`, the gains of adding each
element of `T` to `R` add up to at least `|T| - rank R`. -/
theorem card_sub_rank_le_sum {Mt : Matroid β} {T : Finset β} (hT : Mt.Indep (↑T : Set β))
    (R : Finset β) :
    (T.card : ℝ) - wRank Mt (fun _ => 1) R ≤
      ∑ b ∈ T, (wRank Mt (fun _ => 1) (insert b R) - wRank Mt (fun _ => 1) R) := by
  obtain ⟨B, hBR, hB, hEq⟩ := exists_wRank_eq Mt (fun _ => 1) R
  obtain ⟨A, hA, hAi, hcard⟩ := exists_augment_card hB hT
  have hAT : A ⊆ T := fun x hx => (mem_sdiff.mp (hA hx)).1
  have hRB : wRank Mt (fun _ => 1) R = B.card := by rw [hEq]; simp
  have hgain : ∀ b ∈ A, 1 ≤ wRank Mt (fun _ => 1) (insert b R) - wRank Mt (fun _ => 1) R := by
    intro b hb
    have hbB : b ∉ B := (mem_sdiff.mp (hA hb)).2
    have hi : Mt.Indep (↑(insert b B) : Set β) :=
      hAi.subset (coe_subset.mpr (insert_subset (mem_union_right _ hb) subset_union_left))
    have := sum_le_wRank (q := fun _ => (1 : ℝ)) (insert_subset_insert b hBR) hi
    rw [sum_const, card_insert_of_notMem hbB] at this
    rw [hRB]
    simp only [nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one] at this
    linarith
  have hnn : ∀ b ∈ T, 0 ≤ wRank Mt (fun _ => 1) (insert b R) - wRank Mt (fun _ => 1) R :=
    fun b _ => sub_nonneg.mpr (wRank_mono_set (subset_insert b R))
  have hc : (T.card : ℝ) ≤ B.card + A.card := by exact_mod_cast hcard
  calc (T.card : ℝ) - wRank Mt (fun _ => 1) R ≤ ∑ b ∈ A, (1 : ℝ) := by
        rw [hRB, sum_const, nsmul_eq_mul, mul_one]; linarith
    _ ≤ ∑ b ∈ A, (wRank Mt (fun _ => 1) (insert b R) - wRank Mt (fun _ => 1) R) :=
        sum_le_sum hgain
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hAT fun b hb _ => hnn b hb

/-- For `p` in the polytope, the `p`-weighted marginal gains of rank over `R` are at least
`∑ p - rank R`. -/
theorem sum_sub_rank_le_of_mem [Fintype β] {Mt : Matroid β} {p : β → ℝ}
    (hp : p ∈ matroidPolytope Mt) (R : Finset β) :
    ∑ b, p b - wRank Mt (fun _ => 1) R ≤
      ∑ b, p b * (wRank Mt (fun _ => 1) (insert b R) - wRank Mt (fun _ => 1) R) := by
  have h := sum_mul_le_of_mem_matroidPolytope Mt
    (fun b => 1 - (wRank Mt (fun _ => 1) (insert b R) - wRank Mt (fun _ => 1) R))
    (wRank Mt (fun _ => 1) R) (fun T hT => by
      have := card_sub_rank_le_sum hT R
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one]
      linarith) hp
  have e : ∑ b, p b * (1 - (wRank Mt (fun _ => 1) (insert b R) - wRank Mt (fun _ => 1) R)) =
      ∑ b, p b - ∑ b, p b * (wRank Mt (fun _ => 1) (insert b R) - wRank Mt (fun _ => 1) R) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun b _ => by ring
  linarith

/-! #### Tools for independent coins -/

/-- The union of two independent random sets is a random set: `e` is in `A ∪ B` with
probability `1 - (1 - q e)(1 - r e)`. -/
theorem indepExp_union_coins (U : Finset β) (q r : β → ℝ) (g : Finset β → ℝ) :
    indepExp U (fun e => 1 - (1 - q e) * (1 - r e)) g =
      indepExp U q (fun A => indepExp U r (fun B => g (A ∪ B))) := by
  induction U using Finset.induction_on generalizing g with
  | empty => simp [indepExp]
  | insert a U ha ih =>
    have hin : ∀ A : Finset β, indepExp (insert a U) r (fun B => g (A ∪ B)) =
        (1 - r a) * indepExp U r (fun B => g (A ∪ B)) +
          r a * indepExp U r (fun B => g (insert a (A ∪ B))) := by
      intro A
      rw [indepExp_insert ha]
      simp only [union_insert]
    simp only [hin]
    rw [indepExp_insert ha, indepExp_insert ha, ih, ih]
    simp only [insert_union, insert_idem]
    rw [indepExp_add, indepExp_add]
    simp only [indepExp_const_mul]
    ring

/-- Raising the coin probabilities raises the expectation of a monotone function. -/
theorem indepExp_mono_prob {U : Finset β} {p q : β → ℝ}
    (hq : ∀ i ∈ U, 0 ≤ q i ∧ q i ≤ 1) (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1)
    (hqp : ∀ i ∈ U, q i ≤ p i) {g : Finset β → ℝ} (hg : ∀ A B, A ⊆ B → g A ≤ g B) :
    indepExp U q g ≤ indepExp U p g := by
  induction U using Finset.induction_on generalizing g with
  | empty => simp [indepExp]
  | insert a U ha ih =>
    have hq' : ∀ i ∈ U, 0 ≤ q i ∧ q i ≤ 1 := fun i hi => hq i (mem_insert_of_mem hi)
    have hp' : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1 := fun i hi => hp i (mem_insert_of_mem hi)
    have hqp' : ∀ i ∈ U, q i ≤ p i := fun i hi => hqp i (mem_insert_of_mem hi)
    rw [indepExp_insert ha, indepExp_insert ha]
    have h1 := ih hq' hp' hqp' hg
    have h2 := ih hq' hp' hqp' (g := fun S => g (insert a S))
      (fun A B h => hg _ _ (insert_subset_insert a h))
    have h3 : indepExp U p g ≤ indepExp U p (fun S => g (insert a S)) :=
      indepExp_mono hp' fun S _ => hg _ _ (subset_insert a S)
    have hqa := hq a (mem_insert_self a U)
    have hqpa := hqp a (mem_insert_self a U)
    nlinarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hqa.2),
      mul_le_mul_of_nonneg_left h2 hqa.1, mul_le_mul_of_nonneg_right hqpa (sub_nonneg.mpr h3)]

/-- The probability that the random set is exactly `{e}`. -/
theorem indepExp_eq_singleton_prob {U : Finset β} {e : β} (he : e ∈ U) (p : β → ℝ) :
    indepExp U p (fun B => if B = {e} then 1 else 0) = p e * ∏ i ∈ U.erase e, (1 - p i) := by
  have h := indepExp_subset_disjoint p (U := U) (A := {e}) (B := U.erase e)
    (singleton_subset_iff.mpr he) (erase_subset e U)
    (disjoint_singleton_left.mpr (notMem_erase e U))
  rw [prod_singleton] at h
  rw [← h]
  refine indepExp_congr fun S hS => ?_
  have hiff : S = {e} ↔ ({e} ⊆ S ∧ Disjoint (U.erase e) S) := by
    constructor
    · rintro rfl
      exact ⟨subset_refl _, disjoint_singleton_right.mpr (notMem_erase e U)⟩
    · rintro ⟨h1, h2⟩
      ext x
      simp only [mem_singleton]
      constructor
      · intro hx
        by_contra hne
        exact disjoint_left.mp h2 (mem_erase.mpr ⟨hne, hS hx⟩) hx
      · rintro rfl
        exact singleton_subset_iff.mp h1
  simp only [hiff]

omit [DecidableEq β] in
/-- `∏ (1 - r i) ≥ 1 - ∑ r i` for `r i ∈ [0, 1]`. -/
theorem one_sub_sum_le_prod_coins {s : Finset β} {r : β → ℝ} (hr : ∀ i ∈ s, 0 ≤ r i ∧ r i ≤ 1) :
    1 - ∑ i ∈ s, r i ≤ ∏ i ∈ s, (1 - r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have ih' := ih fun i hi => hr i (mem_insert_of_mem hi)
    have hra := hr a (mem_insert_self a s)
    have hsum : 0 ≤ ∑ i ∈ s, r i := sum_nonneg fun i hi => (hr i (mem_insert_of_mem hi)).1
    nlinarith [mul_le_mul_of_nonneg_left ih' (sub_nonneg.mpr hra.2), mul_nonneg hra.1 hsum]

/-- **Correlation gap for matroid rank.** If each element is in a random set
independently with probability `p b`, and `p` lies in the matroid polytope, the expected
rank of the random set is at least `(1 - 1/e) ∑ p`. -/
theorem matroid_correlation_gap [Fintype β] (Mt : Matroid β) (p : β → ℝ)
    (hP : p ∈ matroidPolytope Mt) :
    (1 - Real.exp (-1)) * ∑ b, p b ≤ indepExp univ p (fun S => wRank Mt (fun _ => 1) S) := by
  set rk : Finset β → ℝ := fun S => wRank Mt (fun _ => 1) S with hrk
  set s := ∑ b, p b with hs
  have hp01 : ∀ b, 0 ≤ p b ∧ p b ≤ 1 := matroidPolytope_mem_Icc Mt hP
  have hs0 : 0 ≤ s := sum_nonneg fun b _ => (hp01 b).1
  have hmono : ∀ A B : Finset β, A ⊆ B → rk A ≤ rk B := fun A B h => wRank_mono_set h
  have hgain : ∀ A : Finset β, s - rk A ≤ ∑ b, p b * (rk (insert b A) - rk A) :=
    fun A => sum_sub_rank_le_of_mem hP A
  -- `N` rounds, each adding an independent random set with marginals `p / N`. Each round
  -- shrinks the gap `s - E[rank]` by a factor `1 - c / N`, with `c = 1 - s / N`.
  have hN : ∀ N : ℕ, 1 ≤ N → s ≤ N →
      (1 - Real.exp (-(1 - s / N))) * s ≤ indepExp univ p rk := by
    intro N hN1 hsN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    set c := 1 - s / N with hc
    have hsN' : s / N ≤ 1 := (div_le_one hNpos).mpr hsN
    have hc0 : 0 ≤ c := by linarith
    have hc1 : c ≤ 1 := by linarith [div_nonneg hs0 hNpos.le]
    have hcN : c / N ≤ 1 := (div_le_one hNpos).mpr (by linarith)
    set ρ : β → ℝ := fun b => p b / N with hρ
    have hρ01 : ∀ b ∈ (univ : Finset β), 0 ≤ ρ b ∧ ρ b ≤ 1 := fun b _ =>
      ⟨div_nonneg (hp01 b).1 hNpos.le, (div_le_one hNpos).mpr (by linarith [(hp01 b).2])⟩
    have hρsum : ∑ b, ρ b = s / N := by rw [hs, sum_div]
    set q : ℕ → β → ℝ := fun k b => 1 - (1 - ρ b) ^ k with hq
    have hq01 : ∀ k, ∀ b ∈ (univ : Finset β), 0 ≤ q k b ∧ q k b ≤ 1 := by
      intro k b hb
      have h0 : 0 ≤ 1 - ρ b := by linarith [(hρ01 b hb).2]
      have h1 : 1 - ρ b ≤ 1 := by linarith [(hρ01 b hb).1]
      exact ⟨by linarith [pow_le_one₀ h0 h1 (n := k)], by linarith [pow_nonneg h0 k]⟩
    have hEnn : ∀ k, 0 ≤ indepExp univ (q k) rk := by
      intro k
      have := indepExp_mono (hq01 k) (g := fun _ => (0 : ℝ)) (h := rk)
        fun S _ => wRank_nonneg_set _ _ _
      rwa [indepExp_const] at this
    -- One round: the gain is at least `(c / N) (s - E rank)`.
    have hinner : ∀ A : Finset β,
        (1 - c / N) * rk A + c / N * s ≤ indepExp univ ρ (fun B => rk (A ∪ B)) := by
      intro A
      have hpt : ∀ B ⊆ (univ : Finset β),
          rk A + ∑ b, (rk (insert b A) - rk A) * (if B = {b} then 1 else 0) ≤ rk (A ∪ B) := by
        intro B _
        by_cases hB : ∃ b0, B = {b0}
        · obtain ⟨b0, rfl⟩ := hB
          rw [sum_eq_single b0 (fun b _ hb => by simp [Ne.symm hb])
            (fun h => absurd (mem_univ b0) h)]
          rw [union_comm, ← insert_eq]
          simp
        · push Not at hB
          simp only [hB, ↓reduceIte, mul_zero, sum_const_zero, add_zero]
          exact hmono _ _ subset_union_left
      have hE := indepExp_mono hρ01 hpt
      rw [indepExp_add, indepExp_const, indepExp_sum] at hE
      simp only [indepExp_const_mul] at hE
      rw [sum_congr rfl fun b _ => by rw [indepExp_eq_singleton_prob (mem_univ b)]] at hE
      have hlow : ∀ b ∈ (univ : Finset β),
          (rk (insert b A) - rk A) * (ρ b * c) ≤
            (rk (insert b A) - rk A) * (ρ b * ∏ i ∈ univ.erase b, (1 - ρ i)) := by
        intro b _
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (hρ01 b (mem_univ b)).1)
          (sub_nonneg.mpr (hmono _ _ (subset_insert b A)))
        refine le_trans ?_ (one_sub_sum_le_prod_coins fun i hi => hρ01 i (mem_univ i))
        rw [hc, ← hρsum]
        linarith [sum_le_sum_of_subset_of_nonneg (erase_subset b univ)
          (fun i hi _ => (hρ01 i hi).1) (f := ρ)]
      have hsum : ∑ b, (rk (insert b A) - rk A) * (ρ b * c) =
          c / N * ∑ b, p b * (rk (insert b A) - rk A) := by
        rw [mul_sum]
        exact sum_congr rfl fun b _ => by simp only [hρ]; ring
      have := hgain A
      have h1 := sum_le_sum hlow
      rw [hsum] at h1
      nlinarith [mul_le_mul_of_nonneg_left this (div_nonneg hc0 hNpos.le)]
    have hstep : ∀ k, s - indepExp univ (q (k + 1)) rk ≤
        (1 - c / N) * (s - indepExp univ (q k) rk) := by
      intro k
      have hqk : q (k + 1) = fun b => 1 - (1 - q k b) * (1 - ρ b) := by
        funext b
        simp only [hq]
        ring
      rw [hqk, indepExp_union_coins]
      have h := indepExp_mono (hq01 k) fun A _ => hinner A
      rw [indepExp_add, indepExp_const_mul, indepExp_const] at h
      nlinarith
    have hiter : ∀ k, s - indepExp univ (q k) rk ≤ (1 - c / N) ^ k * s := by
      intro k
      induction k with
      | zero =>
        rw [pow_zero, one_mul]
        linarith [hEnn 0]
      | succ k ih =>
        calc s - indepExp univ (q (k + 1)) rk ≤ (1 - c / N) * (s - indepExp univ (q k) rk) :=
              hstep k
          _ ≤ (1 - c / N) * ((1 - c / N) ^ k * s) :=
              mul_le_mul_of_nonneg_left ih (by linarith)
          _ = (1 - c / N) ^ (k + 1) * s := by ring
    have hexp : (1 - c / N) ^ N ≤ Real.exp (-c) :=
      Real.one_sub_div_pow_le_exp_neg (by linarith)
    have hqN : indepExp univ (q N) rk ≤ indepExp univ p rk := by
      refine indepExp_mono_prob (hq01 N) (fun b _ => hp01 b) (fun b _ => ?_) hmono
      have hb := one_add_mul_le_pow (a := -ρ b) (by linarith [(hρ01 b (mem_univ b)).2]) N
      have : (N : ℝ) * -ρ b = -p b := by
        simp only [hρ]
        field_simp
      simp only [hq]
      rw [this, ← sub_eq_add_neg, ← sub_eq_add_neg] at hb
      linarith
    have := hiter N
    nlinarith [mul_le_mul_of_nonneg_right hexp hs0]
  -- Let `N → ∞`.
  have hlim : Filter.Tendsto (fun N : ℕ => (1 - Real.exp (-(1 - s / N))) * s) Filter.atTop
      (nhds ((1 - Real.exp (-(1 - 0))) * s)) := by
    refine Filter.Tendsto.mul_const s (tendsto_const_nhds.sub ?_)
    exact (Real.continuous_exp.tendsto _).comp
      ((tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat s)).neg)
  rw [sub_zero] at hlim
  refine le_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨max 1 ⌈s⌉₊, fun N hNN => ?_⟩)
  refine hN N (le_of_max_le_left hNN) ?_
  exact (Nat.le_ceil s).trans (by exact_mod_cast le_of_max_le_right hNN)

/-- Adding `m ≥ 0` to every weight adds at least `m · rank S`: extend a best independent
set to a basis of `S`. -/
theorem wRank_add_const_ge {Mt : Matroid β} {q : β → ℝ} {S : Finset β} {m : ℝ} (hm : 0 ≤ m)
    (hq : ∀ x ∈ S, 0 ≤ q x) :
    m * wRank Mt (fun _ => 1) S + wRank Mt q S ≤ wRank Mt (fun x => m + q x) S := by
  obtain ⟨B, hBS, hB, hEqB⟩ := exists_wRank_eq Mt q S
  obtain ⟨T, hTS, hT, hEqT⟩ := exists_wRank_eq Mt (fun _ => 1) S
  obtain ⟨A, hA, hAi, hcard⟩ := exists_augment_card hB hT
  have hAT : A ⊆ T := fun x hx => (mem_sdiff.mp (hA hx)).1
  have hdisj : Disjoint B A := disjoint_left.mpr fun x hxB hxA => (mem_sdiff.mp (hA hxA)).2 hxB
  have h1 := sum_le_wRank (q := fun x => m + q x) (union_subset hBS (hAT.trans hTS)) hAi
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, card_union_of_disjoint hdisj,
    sum_union hdisj] at h1
  have hA0 : 0 ≤ ∑ x ∈ A, q x := sum_nonneg fun x hx => hq x (hTS (hAT hx))
  rw [hEqB, hEqT, sum_const, nsmul_eq_mul, mul_one]
  have hc : (T.card : ℝ) ≤ B.card + A.card := by exact_mod_cast hcard
  push_cast at h1
  nlinarith [mul_le_mul_of_nonneg_left hc hm]

end Polytope

section RandomWeight

variable {J O : Type*} [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]

omit [DecidableEq O] in
/-- **Random-weight gap for matroids.** Coordinates `ω j` are independent with laws
`ρ j`, and element `j` gets weight `W j (ω j) ≥ 0`. If the probabilities of positive
weight lie in the matroid polytope, the expected weighted rank is at least `1 - 1/e`
times the expected total weight. -/
theorem prodExp_matroid_gap (Mt : Matroid J) {ρ : J → O → ℝ} (hρ : IsDist ρ)
    (W : J → O → ℝ) (hW : ∀ j o, 0 ≤ W j o)
    (hP : (fun j => ∑ o ∈ univ.filter (fun o => 0 < W j o), ρ j o) ∈ matroidPolytope Mt) :
    (1 - Real.exp (-1)) * prodExp ρ (fun ω => ∑ j, W j (ω j)) ≤
      prodExp ρ (fun ω => wRank Mt (fun j => W j (ω j)) univ) := by
  suffices H : ∀ n : ℕ, ∀ W : J → O → ℝ, (posVals W).card ≤ n → (∀ j o, 0 ≤ W j o) →
      (fun j => ∑ o ∈ univ.filter (fun o => 0 < W j o), ρ j o) ∈ matroidPolytope Mt →
      (1 - Real.exp (-1)) * prodExp ρ (fun ω => ∑ j, W j (ω j)) ≤
        prodExp ρ (fun ω => wRank Mt (fun j => W j (ω j)) univ) from
    H _ W le_rfl hW hP
  have hrhs : ∀ W : J → O → ℝ,
      0 ≤ prodExp ρ (fun ω => wRank Mt (fun j => W j (ω j)) univ) := fun W =>
    prodExp_nonneg hρ.1 fun ω => wRank_nonneg_set _ _ _
  -- With no positive values every weight is zero.
  have hzero : ∀ W : J → O → ℝ, (∀ j o, 0 ≤ W j o) → posVals W = ∅ →
      (1 - Real.exp (-1)) * prodExp ρ (fun ω => ∑ j, W j (ω j)) ≤
        prodExp ρ (fun ω => wRank Mt (fun j => W j (ω j)) univ) := by
    intro W hW h0
    have hW0 : ∀ j o, W j o = 0 := by
      intro j o
      refine le_antisymm (not_lt.mp fun hpos => ?_) (hW j o)
      have : W j o ∈ posVals W :=
        mem_filter.mpr ⟨mem_image.mpr ⟨(j, o), mem_univ _, rfl⟩, hpos⟩
      simp [h0] at this
    have hsum0 : prodExp ρ (fun ω => ∑ j, W j (ω j)) = 0 := by
      rw [prodExp_congr ρ (h := fun _ => 0) (fun ω => by simp [hW0]), prodExp_const hρ.2]
    rw [hsum0, mul_zero]
    exact hrhs W
  intro n
  induction n with
  | zero =>
    intro W hcard hW _
    exact hzero W hW (card_eq_zero.mp (Nat.le_zero.mp hcard))
  | succ n ih =>
    intro W hcard hW hP
    rcases (posVals W).eq_empty_or_nonempty with h0 | hne
    · exact hzero W hW h0
    set m := (posVals W).min' hne with hm_def
    have hm_mem : m ∈ posVals W := min'_mem _ hne
    have hm_pos : 0 < m := (mem_filter.mp hm_mem).2
    have hm_le : ∀ j o, 0 < W j o → m ≤ W j o := fun j o h =>
      min'_le _ _ (mem_filter.mpr ⟨mem_image.mpr ⟨(j, o), mem_univ _, rfl⟩, h⟩)
    -- Peel off `m` from every positive weight.
    set W' : J → O → ℝ := fun j o => if 0 < W j o then W j o - m else 0 with hW'_def
    have hW' : ∀ j o, 0 ≤ W' j o := fun j o => by
      simp only [hW'_def]
      split_ifs with h
      · linarith [hm_le j o h]
      · exact le_rfl
    have hW'pos : ∀ j o, 0 < W' j o → 0 < W j o := fun j o h => by
      simp only [hW'_def] at h
      split_ifs at h with h'
      · exact h'
      · exact absurd h (lt_irrefl 0)
    have hsplit : ∀ j o, W j o = m * (if 0 < W j o then 1 else 0) + W' j o := fun j o => by
      simp only [hW'_def]
      split_ifs with h
      · ring
      · simp only [mul_zero, zero_add]
        exact le_antisymm (not_lt.mp h) (hW j o)
    -- `W'` has fewer positive values.
    have hcard' : (posVals W').card ≤ n := by
      have hsub : posVals W' ⊆ ((posVals W).filter fun v => m < v).image fun v => v - m := by
        intro v hv
        obtain ⟨hv1, hvpos⟩ := mem_filter.mp hv
        obtain ⟨⟨j, o⟩, _, rfl⟩ := mem_image.mp hv1
        have hpos := hW'pos j o hvpos
        simp only [hW'_def, hpos, ↓reduceIte] at hvpos ⊢
        refine mem_image.mpr ⟨W j o, mem_filter.mpr ⟨mem_filter.mpr
          ⟨mem_image.mpr ⟨(j, o), mem_univ _, rfl⟩, hpos⟩, by linarith⟩, rfl⟩
      have hlt : ((posVals W).filter fun v => m < v).card < (posVals W).card :=
        card_lt_card (filter_ssubset.mpr ⟨m, hm_mem, lt_irrefl m⟩)
      have := (card_le_card hsub).trans card_image_le
      omega
    -- The positive-weight probabilities of `W'` are below those of `W`.
    have hP' : (fun j => ∑ o ∈ univ.filter (fun o => 0 < W' j o), ρ j o) ∈
        matroidPolytope Mt :=
      matroidPolytope_downward Mt hP (fun j => sum_nonneg fun o _ => hρ.1 j o) fun j =>
        sum_le_sum_of_subset_of_nonneg
          (fun o ho => mem_filter.mpr ⟨mem_univ _, hW'pos j o (mem_filter.mp ho).2⟩)
          (fun o _ _ => hρ.1 j o)
    have hIH := ih W' hcard' hW' hP'
    -- The coins "item `j` has positive weight".
    set p : J → ℝ := fun j => ∑ o ∈ univ.filter (fun o => 0 < W j o), ρ j o with hp_def
    have hcount : prodExp ρ (fun ω => ((univ.filter fun j => 0 < W j (ω j)).card : ℝ)) =
        ∑ j, p j := by
      rw [prodExp_filter hρ.2 (fun j o => 0 < W j o) (fun S => (S.card : ℝ)), indepExp_card]
    have hmin : (1 - Real.exp (-1)) * ∑ j, p j ≤ prodExp ρ
        (fun ω => wRank Mt (fun _ => 1) (univ.filter fun j => 0 < W j (ω j))) := by
      rw [prodExp_filter hρ.2 (fun j o => 0 < W j o) (fun S => wRank Mt (fun _ => 1) S)]
      exact matroid_correlation_gap Mt p hP
    -- Pointwise: each unit of rank among positive items earns `m`, plus the best under `W'`.
    have hpt : ∀ ω : J → O,
        m * wRank Mt (fun _ => 1) (univ.filter fun j => 0 < W j (ω j)) +
          wRank Mt (fun j => W' j (ω j)) univ ≤ wRank Mt (fun j => W j (ω j)) univ := by
      intro ω
      set P := univ.filter fun j => 0 < W j (ω j)
      have h1 : wRank Mt (fun j => W' j (ω j)) univ ≤ wRank Mt (fun j => W' j (ω j)) P := by
        refine (wRank_le_filter_pos fun j _ => hW' j (ω j)).trans
          (wRank_mono_set fun j hj => ?_)
        exact mem_filter.mpr ⟨mem_univ _, hW'pos j (ω j) (mem_filter.mp hj).2⟩
      have h2 := wRank_add_const_ge (Mt := Mt) (q := fun j => W' j (ω j)) (S := P) hm_pos.le
        fun j _ => hW' j (ω j)
      have h3 : wRank Mt (fun j => m + W' j (ω j)) P = wRank Mt (fun j => W j (ω j)) P :=
        wRank_congr_set fun j hj => by
          have := hsplit j (ω j)
          simp only [(mem_filter.mp hj).2, ↓reduceIte, mul_one] at this
          exact this.symm
      have h4 : wRank Mt (fun j => W j (ω j)) P ≤ wRank Mt (fun j => W j (ω j)) univ :=
        wRank_mono_set (subset_univ _)
      linarith
    have hE := prodExp_mono hρ.1 hpt
    rw [prodExp_add, prodExp_const_mul] at hE
    -- Expected total weight splits the same way.
    have htot : prodExp ρ (fun ω => ∑ j, W j (ω j)) =
        m * ∑ j, p j + prodExp ρ (fun ω => ∑ j, W' j (ω j)) := by
      rw [← hcount, ← prodExp_const_mul, ← prodExp_add]
      refine prodExp_congr ρ fun ω => ?_
      rw [show ((univ.filter fun j => 0 < W j (ω j)).card : ℝ) =
          ∑ j, (if 0 < W j (ω j) then 1 else 0) by rw [sum_boole], mul_sum,
        ← sum_add_distrib]
      exact sum_congr rfl fun j _ => hsplit j (ω j)
    rw [htot, mul_add]
    have : (1 - Real.exp (-1)) * (m * ∑ j, p j) = m * ((1 - Real.exp (-1)) * ∑ j, p j) := by
      ring
    nlinarith [mul_le_mul_of_nonneg_left hmin hm_pos.le]

/-- **Random-weight gap for matroids, functions of independent columns.** As
`prodExp_columns_gap`, with weighted rank in place of top-`K`. -/
theorem prodExp_columns_matroid_gap {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω]
    [DecidableEq Ω] (Mt : Matroid J) {μ : I × J → Ω → ℝ} (hμ : IsDist μ)
    (F : J → (I → Ω) → O) (W : J → O → ℝ) (hW : ∀ j o, 0 ≤ W j o)
    (hP : (fun j => prodExp μ (fun ω => if 0 < W j (F j (fun i => ω (i, j))) then 1 else 0)) ∈
      matroidPolytope Mt) :
    (1 - Real.exp (-1)) * prodExp μ (fun ω => ∑ j, W j (F j (fun i => ω (i, j)))) ≤
      prodExp μ (fun ω => wRank Mt (fun j => W j (F j (fun i => ω (i, j)))) univ) := by
  have hβ := isDist_curry (J := J) hμ
  have hρ := isDist_map hβ F
  have hconv : ∀ g : (J → O) → ℝ,
      prodExp μ (fun ω => g (fun j => F j (fun i => ω (i, j)))) =
        prodExp (fun j o => ∑ b ∈ univ.filter (fun b => F j b = o),
          ∏ i, μ (i, j) (b i)) g := by
    intro g
    rw [prodExp_curry]
    exact prodExp_map (fun (j : J) (b : I → Ω) => ∏ i, μ (i, j) (b i)) F g
  rw [hconv (fun y => ∑ j, W j (y j)), hconv (fun y => wRank Mt (fun j => W j (y j)) univ)]
  refine prodExp_matroid_gap Mt hρ W hW ?_
  convert hP using 1
  funext j
  rw [hconv (fun y => if 0 < W j (y j) then 1 else 0),
    prodExp_coord hρ.2 j (fun o => if 0 < W j o then 1 else 0), sum_filter]
  simp

end RandomWeight

/-- Matroid IR families: `i`'s feasible partner sets are the independent sets of
`matI i`, and `j`'s those of `matJ j`. -/
structure MatroidFamilies (I J : Type*) where
  matI : I → Matroid J
  matJ : J → Matroid I

namespace ScreenedMarket

variable {I J C : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype C] [DecidableEq C] (M : ScreenedMarket I J C) (F : MatroidFamilies I J)

/-- Every user's partners in `S` are independent in its matroid. -/
def MatOK (S : Finset (I × J)) : Prop :=
  (∀ i, (F.matI i).Indep (↑(univ.filter fun j => (i, j) ∈ S) : Set J)) ∧
    ∀ j, (F.matJ j).Indep (↑(univ.filter fun i => (i, j) ∈ S) : Set I)

noncomputable instance (S : Finset (I × J)) : Decidable (MatOK F S) := Classical.dec _

/-- The best total weight of a feasible match set inside `Fs`. -/
noncomputable def bestMatchM (Fs : Finset (I × J)) (w : I × J → ℝ) : ℝ :=
  (Fs.powerset.filter (MatOK F)).sup'
    ⟨∅, mem_filter.mpr ⟨empty_mem_powerset Fs, by simp [MatOK]⟩⟩ fun S => ∑ e ∈ S, w e

/-- `OPT_IR` for matroid users. -/
noncomputable def optIRM : ℝ :=
  prodExp M.π fun ω =>
    bestMatchM F (univ.filter fun e => M.Acc e (ω e)) fun e => M.wt e (ω e)

/-- Feasible plans for matroid users. -/
def LPFeasibleM (x : I × J → C → ℝ) : Prop :=
  (∀ e c, 0 ≤ x e c ∧ x e c ≤ M.π e c) ∧ (∀ e c, ¬ M.Acc e c → x e c = 0) ∧
    (∀ i, (fun j => ∑ c, x (i, j) c) ∈ matroidPolytope (F.matI i)) ∧
      ∀ j, (fun i => ∑ c, x (i, j) c) ∈ matroidPolytope (F.matJ j)

/-- An optimal plan for matroid users. -/
def IsLPOptimalM (x : I × J → C → ℝ) : Prop :=
  M.LPFeasibleM F x ∧ ∀ x', M.LPFeasibleM F x' → M.lpValue x' ≤ M.lpValue x

/-- SDH's expected welfare for matroid users with query probabilities `τ`. -/
noncomputable def sdhValueM (τ : I × J → ℝ) : ℝ :=
  prodExp (M.screenLaw τ) fun ω =>
    bestMatchM F (univ.filter fun e => (ω e).2 = true ∧ M.Acc e (ω e).1)
      fun e => M.wt e (ω e).1

/-! #### Feasible match sets -/

omit [Fintype C] [DecidableEq C] in
/-- Subsets of feasible match sets are feasible. -/
theorem MatOK.subset {S T : Finset (I × J)} (hS : MatOK F S) (hTS : T ⊆ S) : MatOK F T :=
  ⟨fun i => (hS.1 i).subset (coe_subset.mpr fun _ hj =>
      mem_filter.mpr ⟨mem_univ _, hTS (mem_filter.mp hj).2⟩),
    fun j => (hS.2 j).subset (coe_subset.mpr fun _ hi =>
      mem_filter.mpr ⟨mem_univ _, hTS (mem_filter.mp hi).2⟩)⟩

omit [Fintype C] [DecidableEq C] in
/-- The best feasible set inside `Fs` is attained. -/
theorem exists_bestMatchM_eq (Fs : Finset (I × J)) (w : I × J → ℝ) :
    ∃ S, S ⊆ Fs ∧ MatOK F S ∧ bestMatchM F Fs w = ∑ e ∈ S, w e := by
  unfold bestMatchM
  obtain ⟨S, hS, hEq⟩ := exists_mem_eq_sup' (⟨∅, mem_filter.mpr ⟨empty_mem_powerset Fs, by
    simp [MatOK]⟩⟩ : (Fs.powerset.filter (MatOK F)).Nonempty) (fun S => ∑ e ∈ S, w e)
  obtain ⟨hSF, hSok⟩ := mem_filter.mp hS
  exact ⟨S, mem_powerset.mp hSF, hSok, hEq⟩

omit [Fintype C] [DecidableEq C] in
/-- Every feasible set inside `Fs` is a lower bound. -/
theorem sum_le_bestMatchM {Fs S : Finset (I × J)} (w : I × J → ℝ) (hSF : S ⊆ Fs)
    (hS : MatOK F S) : ∑ e ∈ S, w e ≤ bestMatchM F Fs w := by
  unfold bestMatchM
  exact le_sup' (fun S => ∑ e ∈ S, w e) (mem_filter.mpr ⟨mem_powerset.mpr hSF, hS⟩)

/-! #### The LP bounds `OPT_IR` -/

/-- The marginals of an optimal feasible set form a feasible plan whose value is
`OPT_IR`. -/
theorem exists_lpValue_eq_optIRM (hπ : IsDist M.π) :
    ∃ x, M.LPFeasibleM F x ∧ M.lpValue x = M.optIRM F := by
  choose opt hoptF hoptOK hval using fun ω : I × J → C =>
    exists_bestMatchM_eq F (univ.filter fun e => M.Acc e (ω e)) fun e => M.wt e (ω e)
  set x : I × J → C → ℝ := fun e c =>
    prodExp M.π fun ω => if e ∈ opt ω ∧ ω e = c then 1 else 0 with hx_def
  have hsumc : ∀ (S : Finset (I × J)) (ω : I × J → C) (e : I × J),
      ∑ c, (if e ∈ S ∧ ω e = c then (1 : ℝ) else 0) = if e ∈ S then 1 else 0 := by
    intro S ω e
    by_cases he : e ∈ S <;> simp [he]
  have hrow : ∀ i, (fun j => ∑ c, x (i, j) c) =
      fun j => prodExp M.π fun ω => if j ∈ univ.filter (fun j => (i, j) ∈ opt ω) then 1 else 0 := by
    intro i
    funext j
    simp only [hx_def]
    rw [← prodExp_sum]
    refine prodExp_congr _ fun ω => ?_
    rw [hsumc]
    simp
  have hcol : ∀ j, (fun i => ∑ c, x (i, j) c) =
      fun i => prodExp M.π fun ω => if i ∈ univ.filter (fun i => (i, j) ∈ opt ω) then 1 else 0 := by
    intro j
    funext i
    simp only [hx_def]
    rw [← prodExp_sum]
    refine prodExp_congr _ fun ω => ?_
    rw [hsumc]
    simp
  refine ⟨x, ⟨fun e c => ⟨?_, ?_⟩, fun e c hc => ?_, fun i => ?_, fun j => ?_⟩, ?_⟩
  · exact prodExp_nonneg hπ.1 fun ω => by split_ifs <;> norm_num
  · calc x e c ≤ prodExp M.π (fun ω => if ω e = c then 1 else 0) :=
          prodExp_mono hπ.1 fun ω => by split_ifs <;> simp_all
      _ = M.π e c := by
          rw [prodExp_coord hπ.2 e (fun o => if o = c then 1 else 0)]
          simp
  · refine (prodExp_congr _ (h := fun _ => 0) fun ω => ?_).trans (prodExp_const hπ.2 0)
    split_ifs with h
    · exact absurd (h.2 ▸ (mem_filter.mp (hoptF ω h.1)).2) hc
    · rfl
  · rw [hrow i]
    exact prodExp_mem_matroidPolytope (F.matI i) hπ _ fun ω => (hoptOK ω).1 i
  · rw [hcol j]
    exact prodExp_mem_matroidPolytope (F.matJ j) hπ _ fun ω => (hoptOK ω).2 j
  · unfold lpValue optIRM
    simp only [hx_def]
    simp_rw [← prodExp_const_mul, ← prodExp_sum]
    refine prodExp_congr _ fun ω => ?_
    rw [hval ω, ← sum_filter_add_sum_filter_not univ (· ∈ opt ω)]
    have hin : ∀ e, ∑ c, M.wt e c * (if e ∈ opt ω ∧ ω e = c then 1 else 0) =
        if e ∈ opt ω then M.wt e (ω e) else 0 := by
      intro e
      by_cases he : e ∈ opt ω <;> simp [he]
    simp_rw [hin]
    rw [sum_ite_of_false (fun e he => (mem_filter.mp he).2), sum_const_zero, add_zero,
      sum_ite_of_true (fun e he => (mem_filter.mp he).2)]
    exact (sum_congr (by ext e; simp) fun _ _ => rfl)

/-- **The LP bounds `OPT_IR`** (matroid users). -/
theorem optIRM_le_lpValue (hπ : IsDist M.π) {x : I × J → C → ℝ}
    (hx : M.IsLPOptimalM F x) : M.optIRM F ≤ M.lpValue x := by
  obtain ⟨x', hx', hEq⟩ := M.exists_lpValue_eq_optIRM F hπ
  exact hEq ▸ hx.2 x' hx'

omit [DecidableEq C] in
/-- The feasible plans form a closed set. -/
theorem isClosed_lpFeasibleM : IsClosed {x : I × J → C → ℝ | M.LPFeasibleM F x} := by
  simp only [LPFeasibleM, Set.ofPred_and, Set.ofPred_forall]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
  · exact isClosed_iInter fun e => isClosed_iInter fun c =>
      (isClosed_le continuous_const (by fun_prop)).inter
        (isClosed_le (by fun_prop) continuous_const)
  · exact isClosed_iInter fun e => isClosed_iInter fun c => isClosed_iInter fun _ =>
      isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_iInter fun i => (isClosed_matroidPolytope _).preimage (by fun_prop)
  · exact isClosed_iInter fun j => (isClosed_matroidPolytope _).preimage (by fun_prop)

omit [DecidableEq C] in
/-- The matroid LP has an optimal plan. -/
theorem exists_isLPOptimalM (hπ : IsDist M.π) : ∃ x, M.IsLPOptimalM F x := by
  have hbox : IsCompact (Set.univ.pi fun e : I × J =>
      Set.univ.pi fun c : C => Set.Icc 0 (M.π e c)) :=
    isCompact_univ_pi fun e => isCompact_univ_pi fun c => isCompact_Icc
  have hcpt : IsCompact {x : I × J → C → ℝ | M.LPFeasibleM F x} :=
    hbox.of_isClosed_subset (M.isClosed_lpFeasibleM F) fun x hx =>
      Set.mem_univ_pi.mpr fun e => Set.mem_univ_pi.mpr fun c => hx.1 e c
  have h0 : M.LPFeasibleM F fun _ _ => 0 := by
    refine ⟨fun e c => ⟨le_rfl, hπ.1 e c⟩, fun _ _ _ => rfl, fun i => ?_, fun j => ?_⟩
    · have : (fun _ : J => (0 : ℝ)) ∈ matroidPolytope (F.matI i) :=
        subset_convexHull ℝ _ ⟨∅, by simp, by funext b; simp [indVec]⟩
      simpa using this
    · have : (fun _ : I => (0 : ℝ)) ∈ matroidPolytope (F.matJ j) :=
        subset_convexHull ℝ _ ⟨∅, by simp, by funext b; simp [indVec]⟩
      simpa using this
  have hcont : Continuous M.lpValue := by unfold lpValue; fun_prop
  obtain ⟨x, hx, hmax⟩ := hcpt.exists_isMaxOn ⟨_, h0⟩ hcont.continuousOn
  exact ⟨x, hx, fun x' hx' => hmax hx'⟩

/-! #### The two-stage selection for matroid users

As for size caps (`lpValue_le_candidates`), on the thinned candidates: each `J`-side user
keeps its best independent set of candidates (`sel1M`), then each `I`-side user its best
independent set of what was kept for it (`sel2M`). The result (`twoStageM`) is
feasible: rows are independent by construction, and each column is a subset of an
independent set. -/

/-- Stage 1: column `j`'s best independent set of candidates with positive weight. -/
noncomputable def sel1M (j : J) (b : I → Option C) : Finset I :=
  (Classical.choose
    (exists_wRank_eq (F.matJ j) (fun i => M.candWt (i, j) (b i)) univ)).filter
    fun i => 0 < M.candWt (i, j) (b i)

omit [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype C] [DecidableEq C] in
/-- Stage 1 keeps an independent set of positive-weight candidates worth the weighted
rank. -/
theorem sel1M_spec (j : J) (b : I → Option C) :
    (F.matJ j).Indep (↑(M.sel1M F j b) : Set I) ∧
      (∀ i ∈ M.sel1M F j b, 0 < M.candWt (i, j) (b i)) ∧
        ∑ i ∈ M.sel1M F j b, M.candWt (i, j) (b i) =
          wRank (F.matJ j) (fun i => M.candWt (i, j) (b i)) univ := by
  obtain ⟨_, hind, hEq⟩ :=
    Classical.choose_spec (exists_wRank_eq (F.matJ j) (fun i => M.candWt (i, j) (b i)) univ)
  refine ⟨hind.subset (coe_subset.mpr (filter_subset _ _)), fun i hi => (mem_filter.mp hi).2, ?_⟩
  rw [hEq, sel1M, sum_filter_of_ne]
  intro i _ hne
  exact lt_of_le_of_ne (M.candWt_nonneg _ _) (Ne.symm hne)

/-- What stage 1 passes on to row `i` from column `j`. -/
noncomputable def keptM (i : I) (j : J) (b : I → Option C) : Option C :=
  if i ∈ M.sel1M F j b then b i else none

/-- Stage 2: row `i`'s best independent set of what it was passed, with positive weight. -/
noncomputable def sel2M (i : I) (y : J → Option C) : Finset J :=
  (Classical.choose
    (exists_wRank_eq (F.matI i) (fun j => M.candWt (i, j) (y j)) univ)).filter
    fun j => 0 < M.candWt (i, j) (y j)

omit [Fintype I] [DecidableEq I] [DecidableEq J] [Fintype C] [DecidableEq C] in
/-- Stage 2 keeps an independent set of positive-weight pairs worth the weighted rank. -/
theorem sel2M_spec (i : I) (y : J → Option C) :
    (F.matI i).Indep (↑(M.sel2M F i y) : Set J) ∧
      (∀ j ∈ M.sel2M F i y, 0 < M.candWt (i, j) (y j)) ∧
        ∑ j ∈ M.sel2M F i y, M.candWt (i, j) (y j) =
          wRank (F.matI i) (fun j => M.candWt (i, j) (y j)) univ := by
  obtain ⟨_, hind, hEq⟩ :=
    Classical.choose_spec (exists_wRank_eq (F.matI i) (fun j => M.candWt (i, j) (y j)) univ)
  refine ⟨hind.subset (coe_subset.mpr (filter_subset _ _)), fun j hj => (mem_filter.mp hj).2, ?_⟩
  rw [hEq, sel2M, sum_filter_of_ne]
  intro j _ hne
  exact lt_of_le_of_ne (M.candWt_nonneg _ _) (Ne.symm hne)

/-- Row `i`'s view after stage 1. -/
noncomputable def rowViewM (η : I × J → Option C) (i : I) : J → Option C :=
  fun j => M.keptM F i j fun i' => η (i', j)

/-- The two-stage selection. -/
noncomputable def twoStageM (η : I × J → Option C) : Finset (I × J) :=
  univ.filter fun e => e.2 ∈ M.sel2M F e.1 (M.rowViewM F η e.1)

omit [DecidableEq J] [Fintype C] in
/-- A pair kept in stage 2 was kept in stage 1. -/
theorem mem_sel1M_of_mem_sel2M {η : I × J → Option C} {i : I} {j : J}
    (h : j ∈ M.sel2M F i (M.rowViewM F η i)) :
    i ∈ M.sel1M F j (fun i' => η (i', j)) ∧ M.rowViewM F η i j = η (i, j) := by
  have hpos := (M.sel2M_spec F i _).2.1 j h
  by_contra hcon
  have : M.rowViewM F η i j = none := by
    simp only [rowViewM, keptM]
    split_ifs with h1
    · exact absurd ⟨h1, by simp [rowViewM, keptM, h1]⟩ hcon
    · rfl
  rw [this, candWt_none] at hpos
  exact lt_irrefl 0 hpos

omit [Fintype C] in
theorem twoStageM_matOK (η : I × J → Option C) : MatOK F (M.twoStageM F η) := by
  constructor
  · intro i
    have h : (univ.filter fun j => (i, j) ∈ M.twoStageM F η) =
        M.sel2M F i (M.rowViewM F η i) := by
      ext j
      simp [twoStageM]
    rw [h]
    exact (M.sel2M_spec F i _).1
  · intro j
    refine (M.sel1M_spec F j fun i' => η (i', j)).1.subset (coe_subset.mpr fun i hi => ?_)
    simp only [twoStageM, mem_filter, mem_univ, true_and] at hi
    exact (M.mem_sel1M_of_mem_sel2M F hi).1

omit [Fintype C] in
/-- The two-stage selection is worth the sum of the rows' stage-2 values. -/
theorem sum_twoStageM (η : I × J → Option C) :
    ∑ e ∈ M.twoStageM F η, M.candWt e (η e) =
      ∑ i, wRank (F.matI i) (fun j => M.candWt (i, j) (M.rowViewM F η i j)) univ := by
  rw [twoStageM, sum_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  rw [← (M.sel2M_spec F i _).2.2, ← sum_filter]
  refine sum_congr (by ext j; simp) fun j hj => ?_
  rw [(M.mem_sel1M_of_mem_sel2M F hj).2]

omit [Fintype J] [DecidableEq J] [Fintype C] [DecidableEq C] in
/-- Stage 1 passes on exactly the column's best value. -/
theorem sum_rowViewM (η : I × J → Option C) (j : J) :
    ∑ i, M.candWt (i, j) (M.rowViewM F η i j) =
      wRank (F.matJ j) (fun i => M.candWt (i, j) (η (i, j))) univ := by
  rw [← (M.sel1M_spec F j _).2.2, ← sum_filter_add_sum_filter_not univ
    (· ∈ M.sel1M F j fun i' => η (i', j))]
  have h2 : ∑ i ∈ univ.filter (fun i => i ∉ M.sel1M F j fun i' => η (i', j)),
      M.candWt (i, j) (M.rowViewM F η i j) = 0 :=
    sum_eq_zero fun i hi => by
      simp only [rowViewM, keptM, (mem_filter.mp hi).2, ↓reduceIte, candWt_none]
  rw [h2, add_zero]
  refine sum_congr (by ext i; simp) fun i hi => ?_
  simp only [rowViewM, keptM, hi, ↓reduceIte]

/-- `M` with caps that never bind. The size-cap lemmas on thinning only use a plan's
bounds, so they apply to matroid plans through this market. -/
def looseCaps : ScreenedMarket I J C :=
  { M with capI := fun _ => Fintype.card J, capJ := fun _ => Fintype.card I }

omit [DecidableEq C] in
/-- A matroid plan is feasible for the loose caps. -/
theorem lpFeasible_looseCaps (hπ : IsDist M.π) {x : I × J → C → ℝ}
    (hx : M.LPFeasibleM F x) : M.looseCaps.LPFeasible x := by
  have hle : ∀ e, ∑ c, x e c ≤ 1 := fun e => by
    rw [← hπ.2 e]
    exact sum_le_sum fun c _ => (hx.1 e c).2
  refine ⟨hx.1, hx.2.1, fun i => ?_, fun j => ?_⟩
  · calc ∑ j, ∑ c, x (i, j) c ≤ ∑ _j : J, (1 : ℝ) := sum_le_sum fun j _ => hle (i, j)
      _ = M.looseCaps.capI i := by simp [looseCaps]
  · calc ∑ i, ∑ c, x (i, j) c ≤ ∑ _i : I, (1 : ℝ) := sum_le_sum fun i _ => hle (i, j)
      _ = M.looseCaps.capJ j := by simp [looseCaps]

/-- **Theorem 3(b) for matroids, on the thinned candidates.** The best feasible set of
candidates is worth at least `(1 - 1/e)² · LP` in expectation. -/
theorem lpValue_le_candidatesM (hπ : IsDist M.π) {x : I × J → C → ℝ}
    (hx : M.LPFeasibleM F x) :
    (1 - Real.exp (-1)) ^ 2 * M.lpValue x ≤
      prodExp (candLaw x) (fun η => bestMatchM F univ fun e => M.candWt e (η e)) := by
  have hx' := M.lpFeasible_looseCaps F hπ hx
  have hν : IsDist (candLaw x) := M.looseCaps.isDist_candLaw hπ hx'
  have hκ := one_sub_exp_neg_one_nonneg
  have hpos : ∀ e, prodExp (candLaw x) (fun η => if 0 < M.candWt e (η e) then 1 else 0) ≤
      ∑ c, x e c := fun e => M.looseCaps.prodExp_candWt_pos_le hπ hx' e
  have hval : ∀ e, prodExp (candLaw x) (fun η => M.candWt e (η e)) = ∑ c, x e c * M.wt e c :=
    fun e => M.looseCaps.prodExp_candWt hπ hx' e
  -- Row values after stage 1.
  set A : I → ℝ := fun i =>
    prodExp (candLaw x) (fun η => ∑ j, M.candWt (i, j) (M.rowViewM F η i j)) with hA_def
  set B : J → ℝ := fun j =>
    prodExp (candLaw x) (fun η => ∑ i, M.candWt (i, j) (η (i, j))) with hB_def
  -- The best feasible set beats the two-stage selection.
  have h1 : ∑ i, prodExp (candLaw x)
      (fun η => wRank (F.matI i) (fun j => M.candWt (i, j) (M.rowViewM F η i j)) univ) ≤
      prodExp (candLaw x) (fun η => bestMatchM F univ fun e => M.candWt e (η e)) := by
    rw [← prodExp_sum]
    refine prodExp_mono hν.1 fun η => ?_
    rw [← M.sum_twoStageM F]
    exact sum_le_bestMatchM F _ (subset_univ _) (M.twoStageM_matOK F η)
  -- Stage 2: each row keeps `1 - 1/e` of what it was passed.
  have h2 : ∀ i, (1 - Real.exp (-1)) * A i ≤ prodExp (candLaw x)
      (fun η => wRank (F.matI i) (fun j => M.candWt (i, j) (M.rowViewM F η i j)) univ) := by
    intro i
    refine prodExp_columns_matroid_gap (F.matI i) hν (fun j b => M.keptM F i j b)
      (fun j o => M.candWt (i, j) o) (fun j o => M.candWt_nonneg _ _) ?_
    refine matroidPolytope_downward _ (hx.2.2.1 i)
      (fun j => prodExp_nonneg hν.1 fun η => by split_ifs <;> norm_num) fun j => ?_
    refine le_trans (prodExp_mono hν.1 fun η => ?_) (hpos (i, j))
    by_cases hmem : i ∈ M.sel1M F j (fun i' => η (i', j))
    · simp only [keptM, hmem, ↓reduceIte]
      exact le_rfl
    · simp only [keptM, hmem, ↓reduceIte, candWt_none, lt_irrefl]
      split_ifs <;> norm_num
  -- Stage 1 output equals the columns' values.
  have h3 : ∑ i, A i = ∑ j, prodExp (candLaw x)
      (fun η => wRank (F.matJ j) (fun i => M.candWt (i, j) (η (i, j))) univ) := by
    simp only [hA_def]
    rw [← prodExp_sum, ← prodExp_sum]
    refine prodExp_congr _ fun η => ?_
    rw [sum_comm]
    exact sum_congr rfl fun j _ => M.sum_rowViewM F η j
  -- Stage 1: each column keeps `1 - 1/e` of its candidates.
  have h4 : ∀ j, (1 - Real.exp (-1)) * B j ≤ prodExp (candLaw x)
      (fun η => wRank (F.matJ j) (fun i => M.candWt (i, j) (η (i, j))) univ) := by
    intro j
    simp only [hB_def]
    rw [prodExp_column hν.2 j (fun b => ∑ i, M.candWt (i, j) (b i)),
      prodExp_column hν.2 j (fun b => wRank (F.matJ j) (fun i => M.candWt (i, j) (b i)) univ)]
    have hνj : IsDist (fun i o => candLaw x (i, j) o) := ⟨fun i o => hν.1 _ o, fun i => hν.2 _⟩
    refine prodExp_matroid_gap (F.matJ j) hνj (fun i o => M.candWt (i, j) o)
      (fun i o => M.candWt_nonneg _ _) ?_
    refine matroidPolytope_downward _ (hx.2.2.2 j)
      (fun i => sum_nonneg fun o _ => hν.1 _ o) fun i => ?_
    have := hpos (i, j)
    rw [prodExp_coord hν.2 (i, j) (fun o => if 0 < M.candWt (i, j) o then 1 else 0)] at this
    rw [sum_filter]
    simpa [mul_ite, mul_one, mul_zero] using this
  -- The columns' candidates carry the LP's value.
  have h5 : ∑ j, B j = M.lpValue x := by
    simp only [hB_def]
    rw [lpValue, Fintype.sum_prod_type, sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [prodExp_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [hval (i, j)]
    exact sum_congr rfl fun c _ => mul_comm _ _
  calc (1 - Real.exp (-1)) ^ 2 * M.lpValue x =
        (1 - Real.exp (-1)) * ∑ j, (1 - Real.exp (-1)) * B j := by
        rw [← h5, mul_sum, mul_sum]; exact sum_congr rfl fun j _ => by ring
    _ ≤ (1 - Real.exp (-1)) * ∑ i, A i :=
        mul_le_mul_of_nonneg_left (h3 ▸ sum_le_sum fun j _ => h4 j) hκ
    _ = ∑ i, (1 - Real.exp (-1)) * A i := mul_sum _ _ _
    _ ≤ _ := (sum_le_sum fun i _ => h2 i).trans h1

/-! #### Thinning: SDH's found pairs contain the candidates -/

/-- Forgetting the keep coin gives SDH's screening (matroid users). -/
theorem sdhValueM_eq_thin (x : I × J → C → ℝ) (τ : I × J → ℝ) :
    M.sdhValueM F τ = prodExp (M.thinLaw x τ) fun ω =>
      bestMatchM F (univ.filter fun e => (ω e).2.1 = true ∧ M.Acc e (ω e).1)
        fun e => M.wt e (ω e).1 := by
  rw [prodExp_map (M.thinLaw x τ) (fun _ o => (o.1, o.2.1)) (fun ω =>
      bestMatchM F (univ.filter fun e => (ω e).2 = true ∧ M.Acc e (ω e).1)
        fun e => M.wt e (ω e).1)]
  unfold sdhValueM
  congr 1
  funext e o
  obtain ⟨c, q⟩ := o
  rw [sum_filter, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [Prod.mk.injEq]
  rw [sum_eq_single c (fun c' _ hc' => by simp [hc']) (fun h => absurd (mem_univ c) h)]
  simp only [true_and]
  rw [sum_eq_single q (fun q' _ hq' => by simp [hq']) (fun h => absurd (mem_univ q) h)]
  simp only [↓reduceIte, Fintype.sum_bool, thinLaw, screenLaw, Bool.false_eq_true]
  ring

omit [Fintype C] [DecidableEq C] in
/-- Every candidate is found, with the same weight. -/
theorem bestMatchM_cand_le (ω : I × J → C × Bool × Bool) :
    bestMatchM F univ (fun e => M.candWt e (M.candOf e (ω e))) ≤
      bestMatchM F (univ.filter fun e => (ω e).2.1 = true ∧ M.Acc e (ω e).1)
        fun e => M.wt e (ω e).1 := by
  obtain ⟨S, -, hS, hEq⟩ :=
    exists_bestMatchM_eq F univ fun e => M.candWt e (M.candOf e (ω e))
  rw [hEq, ← sum_filter_of_ne (p := fun e => 0 < M.candWt e (M.candOf e (ω e)))
    (fun e _ hne => lt_of_le_of_ne (M.candWt_nonneg _ _) (Ne.symm hne))]
  have hpos : ∀ e, 0 < M.candWt e (M.candOf e (ω e)) →
      ((ω e).2.1 = true ∧ M.Acc e (ω e).1) ∧
        M.candWt e (M.candOf e (ω e)) = M.wt e (ω e).1 := by
    intro e h
    unfold candOf at h ⊢
    split_ifs at h ⊢ with hc
    · refine ⟨⟨hc.1, hc.2.2⟩, ?_⟩
      simp [candWt, hc.2.2]
    · exact absurd h (lt_irrefl 0)
  calc ∑ e ∈ S.filter _, M.candWt e (M.candOf e (ω e))
      = ∑ e ∈ S.filter (fun e => 0 < M.candWt e (M.candOf e (ω e))), M.wt e (ω e).1 :=
        sum_congr rfl fun e he => (hpos e (mem_filter.mp he).2).2
    _ ≤ _ := sum_le_bestMatchM F _ (fun e he => mem_filter.mpr ⟨mem_univ _,
        (hpos e (mem_filter.mp he).2).1⟩) (hS.subset F (filter_subset _ _))

/-- **Theorem 3(b) for matroids, main step.** For every feasible plan `x` and query
probabilities with `x e c ≤ τ e · π e c`, SDH earns at least `(1 - 1/e)²` times the
plan's value. -/
theorem lpValue_le_sdhValueM (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasibleM F x)
    {τ : I × J → ℝ} (hτ : ∀ e, 0 ≤ τ e ∧ τ e ≤ 1) (hτx : ∀ e c, x e c ≤ τ e * M.π e c) :
    (1 - Real.exp (-1)) ^ 2 * M.lpValue x ≤ M.sdhValueM F τ := by
  have hx' := M.lpFeasible_looseCaps F hπ hx
  refine (M.lpValue_le_candidatesM F hπ hx).trans ?_
  have hthin : prodExp (M.thinLaw x τ)
      (fun ω => bestMatchM F univ fun e => M.candWt e (M.candOf e (ω e))) =
      prodExp (candLaw x) (fun η => bestMatchM F univ fun e => M.candWt e (η e)) :=
    M.looseCaps.candidates_eq_thin hπ hx' hτ hτx
      (fun η => bestMatchM F univ fun e => M.candWt e (η e))
  have hdist : ∀ e o, 0 ≤ M.thinLaw x τ e o := (M.looseCaps.isDist_thinLaw hπ hx' hτ hτx).1
  rw [← hthin, M.sdhValueM_eq_thin F x τ]
  exact prodExp_mono hdist fun ω => M.bestMatchM_cand_le F ω

/-- **Theorem 3(b) for matroids.** SDH run on an optimal plan earns at least
`(1 - 1/e)² OPT_IR`. -/
theorem sdh_welfare_matroid [Nonempty C] (hπ : IsDist M.π) {x : I × J → C → ℝ}
    (hx : M.IsLPOptimalM F x) :
    (1 - Real.exp (-1)) ^ 2 * M.optIRM F ≤ M.sdhValueM F (M.sdhTau x) := by
  have hspec : (∀ e, 0 ≤ M.sdhTau x e ∧ M.sdhTau x e ≤ 1) ∧
      ∀ e c, x e c ≤ M.sdhTau x e * M.π e c :=
    M.looseCaps.sdhTau_spec (M.lpFeasible_looseCaps F hπ hx.1)
  calc (1 - Real.exp (-1)) ^ 2 * M.optIRM F ≤ (1 - Real.exp (-1)) ^ 2 * M.lpValue x :=
        mul_le_mul_of_nonneg_left (M.optIRM_le_lpValue F hπ hx) (sq_nonneg _)
    _ ≤ _ := M.lpValue_le_sdhValueM F hπ hx.1 hspec.1 hspec.2

omit [Fintype C] [DecidableEq C] in
/-- **Welfare on feasible sets is the sum of net weights** for weighted-matroid-rank users
with non-negative values: each user's partners are independent, where weighted rank is
additive. -/
theorem welfare_eq_sum_wt_matroid (ω : I × J → C) (hvI : ∀ e c, 0 ≤ M.valI e c)
    (hvJ : ∀ e c, 0 ≤ M.valJ e c) {S : Finset (I × J)} (hS : MatOK F S) :
    (∑ i, (wRank (F.matI i) (fun j => M.valI (i, j) (ω (i, j)))
          (univ.filter fun j => (i, j) ∈ S) -
        M.costI i * (univ.filter fun j => (i, j) ∈ S).card)) +
      (∑ j, (wRank (F.matJ j) (fun i => M.valJ (i, j) (ω (i, j)))
          (univ.filter fun i => (i, j) ∈ S) -
        M.costJ j * (univ.filter fun i => (i, j) ∈ S).card)) =
      ∑ e ∈ S, M.wt e (ω e) := by
  have hI : ∀ i, wRank (F.matI i) (fun j => M.valI (i, j) (ω (i, j)))
        (univ.filter fun j => (i, j) ∈ S) -
      M.costI i * (univ.filter fun j => (i, j) ∈ S).card =
      ∑ j ∈ univ.filter (fun j => (i, j) ∈ S), (M.valI (i, j) (ω (i, j)) - M.costI i) := by
    intro i
    rw [wRank_eq_sum_of_indep (fun j => hvI _ _) (hS.1 i), sum_sub_distrib, sum_const,
      nsmul_eq_mul, mul_comm]
  have hJ : ∀ j, wRank (F.matJ j) (fun i => M.valJ (i, j) (ω (i, j)))
        (univ.filter fun i => (i, j) ∈ S) -
      M.costJ j * (univ.filter fun i => (i, j) ∈ S).card =
      ∑ i ∈ univ.filter (fun i => (i, j) ∈ S), (M.valJ (i, j) (ω (i, j)) - M.costJ j) := by
    intro j
    rw [wRank_eq_sum_of_indep (fun i => hvJ _ _) (hS.2 j), sum_sub_distrib, sum_const,
      nsmul_eq_mul, mul_comm]
  simp_rw [hI, hJ, sum_filter]
  rw [sum_comm (s := (univ : Finset J)) (t := (univ : Finset I)), ← sum_add_distrib]
  have hR : ∑ e ∈ S, M.wt e (ω e) =
      ∑ i, ∑ j, if (i, j) ∈ S then M.wt (i, j) (ω (i, j)) else 0 := by
    rw [← Fintype.sum_prod_type (f := fun e => if e ∈ S then M.wt e (ω e) else 0), sum_ite_mem,
      univ_inter]
  rw [hR]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  split_ifs <;> simp [wt]

end ScreenedMarket

end DatingAlgo
