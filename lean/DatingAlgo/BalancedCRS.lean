import DatingAlgo.SelectionRule
import Mathlib.Topology.Sion

/-!
# A `c_K`-balanced selection rule exists

When each `e` is a candidate independently with probability `y e` and `∑ y ≤ K`, some
rule for cap `K` keeps every `e` with probability at least `c_K · y e`, where
`c_K = 1 - e^{-K} K^K / K!` (`cK`). This is the existence of a `c_K`-balanced
contention-resolution scheme for the rank-`K` uniform matroid.

**Proof** (Chekuri, Vondrák and Zenklusen). Consider the zero-sum game in which the
designer picks a rule `ψ` (one law on capped subsets of `A` for each candidate set `A`;
`ruleSet`) and an adversary picks weights `w ≥ 0` with `∑ w = 1` (`weightSimplex`). The
designer's payoff `crsPayoff y c_K w ψ = ∑_e w_e (Pr_ψ[e kept] - c_K y_e)` is continuous,
linear in `w` and affine in `ψ`, and both strategy sets are compact and convex, so Sion's
minimax theorem (`Sion.exists_isSaddlePointOn`) gives a saddle point `(w*, ψ*)`. Against
`w*` the designer can keep a best `K` of the candidates (`exists_bestResponse`), earning
`E[top_K w*(A)] - c_K ∑ w* y ≥ 0` by the `c_K` correlation gap (`indepExp_topK_gap`, from
`prodExp_randomWeight_gap`). So `ψ*` earns at least `0` against every `w`, in particular
against each point mass on `e`, which says `Pr[e kept] ≥ c_K y_e`.
-/

namespace DatingAlgo

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Linearity -/

omit [Fintype α] in
/-- `indepExp` is linear in the function. -/
theorem indepExp_linComb (U : Finset α) (p : α → ℝ) (g h : Finset α → ℝ) (a b : ℝ) :
    indepExp U p (fun S => a * g S + b * h S) = a * indepExp U p g + b * indepExp U p h := by
  unfold indepExp
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun S _ => by ring

/-- A weighted sum of `indepExp`s is the `indepExp` of the weighted sum. -/
theorem sum_mul_indepExp (U : Finset α) (p : α → ℝ) (w : α → ℝ) (g : α → Finset α → ℝ) :
    ∑ e, w e * indepExp U p (g e) = indepExp U p (fun S => ∑ e, w e * g e S) := by
  unfold indepExp
  simp_rw [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun S _ => sum_congr rfl fun e _ => by ring

/-- `ruleKeep` is linear in the rule. -/
theorem ruleKeep_linComb (ψ₁ ψ₂ : Finset α → Finset α → ℝ) (a b : ℝ) (A : Finset α) (e : α) :
    ruleKeep (a • ψ₁ + b • ψ₂) A e = a * ruleKeep ψ₁ A e + b * ruleKeep ψ₂ A e := by
  unfold ruleKeep
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun T _ => by ring

/-! ### The correlation gap over independent candidates -/

/-- Zeroing the weights outside `S` and taking the best `K` of everything is the same as
taking the best `K` of `S`. -/
theorem topK_indicator (w : α → ℝ) (K : ℕ) (S : Finset α) :
    topK (fun j => if j ∈ S then w j else 0) K univ = topK w K S := by
  apply le_antisymm
  · obtain ⟨T, -, hTK, hEq⟩ := exists_topK_eq (fun j => if j ∈ S then w j else 0) K univ
    rw [hEq, sum_ite_mem]
    exact sum_le_topK inter_subset_right ((card_le_card inter_subset_left).trans hTK)
  · obtain ⟨T, hTS, hTK, hEq⟩ := exists_topK_eq w K S
    rw [hEq]
    refine le_trans (le_of_eq ?_) (sum_le_topK (subset_univ T) hTK)
    rw [sum_ite_mem, inter_eq_left.mpr hTS]

/-- **The `c_K` correlation gap over independent candidates.** If each `e` is a candidate
independently with probability `y e` and `∑ y ≤ K`, the best `K` candidates are worth,
in expectation, at least `c_K ∑ w y`. This is `prodExp_randomWeight_gap` with coin
outcomes. -/
theorem indepExp_topK_gap (K : ℕ) {y w : α → ℝ} (hy : ∀ e, 0 ≤ y e ∧ y e ≤ 1)
    (hK : ∑ e, y e ≤ K) (hw : ∀ e, 0 ≤ w e) :
    cK K * ∑ e, w e * y e ≤ indepExp univ y (fun A => topK w K A) := by
  set ρ : α → Bool → ℝ := fun j b => if b then y j else 1 - y j
  have hρ : IsDist ρ :=
    ⟨fun j b => by cases b <;> simp [ρ, (hy j).1, (hy j).2], fun j => by simp [ρ]⟩
  set W : α → Bool → ℝ := fun j b => if b then w j else 0
  have hW : ∀ j b, 0 ≤ W j b := fun j b => by cases b <;> simp [W, hw j]
  have hKW : ∑ j, ∑ o ∈ univ.filter (fun o => 0 < W j o), ρ j o ≤ K := by
    refine le_trans (sum_le_sum fun j _ => ?_) hK
    calc ∑ o ∈ univ.filter (fun o => 0 < W j o), ρ j o ≤ ∑ o ∈ {true}, ρ j o :=
          sum_le_sum_of_subset_of_nonneg (fun o ho => by cases o <;> simp_all [W])
            (fun o _ _ => hρ.1 j o)
      _ = y j := by simp [ρ]
  have hgap := prodExp_randomWeight_gap hρ K W hW hKW
  have hL : prodExp ρ (fun ω => ∑ j, W j (ω j)) = ∑ e, w e * y e := by
    rw [prodExp_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [prodExp_coord hρ.2 j (W j)]
    simp [ρ, W, mul_comm]
  have hR : prodExp ρ (fun ω => topK (fun j => W j (ω j)) K univ) =
      indepExp univ y (fun A => topK w K A) := by
    have := prodExp_filter hρ.2 (fun j b => b = true) (fun A => topK w K A)
    rw [show (fun e => ∑ o ∈ univ.filter (fun o => o = true), ρ e o) = y from
      funext fun e => by rw [sum_filter, Fintype.sum_bool]; simp [ρ]] at this
    rw [← this]
    refine prodExp_congr ρ fun ω => ?_
    rw [← topK_indicator w K (univ.filter fun e => ω e = true)]
    refine topK_congr fun j _ => ?_
    simp [W]
  rw [hL, hR] at hgap
  exact hgap

/-! ### The game -/

/-- The designer's best response to weights `w`: a deterministic rule that keeps a
best-`K` subset of the candidates. -/
theorem exists_bestResponse (K : ℕ) (w : α → ℝ) :
    ∃ ψ, IsRule K ψ ∧ ∀ A, ∑ e, w e * ruleKeep ψ A e = topK w K A := by
  choose T hTA hTK hT using fun A : Finset α => exists_topK_eq w K A
  refine ⟨fun A S => if S = T A then 1 else 0,
    fun A => ⟨fun S => by dsimp only; split_ifs <;> norm_num, by simp, fun S hS => ?_⟩,
    fun A => ?_⟩
  · have : S = T A := by
      by_contra h
      simp [h] at hS
    subst this
    exact ⟨hTA A, hTK A⟩
  · have hk : ∀ e, ruleKeep (fun A S => if S = T A then (1 : ℝ) else 0) A e =
        if e ∈ T A then 1 else 0 := by
      intro e
      unfold ruleKeep
      rw [sum_eq_single (T A)]
      · simp
      · intro S _ hS
        simp [hS]
      · simp
    simp only [hk, mul_ite, mul_one, mul_zero]
    rw [sum_ite_mem, univ_inter, hT A]

/-- The adversary's strategies: weights `w ≥ 0` with `∑ w = 1`. -/
def weightSimplex (α : Type*) [Fintype α] : Set (α → ℝ) :=
  {w | (∀ e, 0 ≤ w e) ∧ ∑ e, w e = 1}

/-- The designer's strategies: rules for cap `K`. -/
def ruleSet (α : Type*) [Fintype α] (K : ℕ) : Set (Finset α → Finset α → ℝ) :=
  {ψ | IsRule K ψ}

/-- The designer's payoff against weights `w`: `∑_e w_e (Pr_ψ[e kept] - γ y_e)`. -/
noncomputable def crsPayoff (y : α → ℝ) (γ : ℝ) (w : α → ℝ)
    (ψ : Finset α → Finset α → ℝ) : ℝ :=
  ∑ e, w e * (indepExp univ y (fun A => ruleKeep ψ A e) - γ * y e)

omit [DecidableEq α] in
/-- The adversary's strategies form a convex set. -/
theorem convex_weightSimplex : Convex ℝ (weightSimplex α) := by
  intro w₁ hw₁ w₂ hw₂ a b ha hb hab
  refine ⟨fun e => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hw₁.1 e)) (mul_nonneg hb (hw₂.1 e))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, hw₁.2, hw₂.2]
    linarith

omit [DecidableEq α] in
/-- The adversary's strategies form a compact set: closed, inside the cube `[0, 1]^α`. -/
theorem isCompact_weightSimplex : IsCompact (weightSimplex α) := by
  refine IsCompact.of_isClosed_subset
    (isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1)) ?_ ?_
  · have : weightSimplex α = (⋂ e, {w : α → ℝ | 0 ≤ w e}) ∩ {w | ∑ e, w e = 1} := by
      ext w
      simp [weightSimplex]
    rw [this]
    exact (isClosed_iInter fun e => isClosed_le continuous_const (continuous_apply e)).inter
      (isClosed_eq (by fun_prop) continuous_const)
  · intro w hw
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
    exact fun e => ⟨hw.1 e, hw.2 ▸ single_le_sum (fun i _ => hw.1 i) (mem_univ e)⟩

omit [DecidableEq α] in
/-- Mixing two rules gives a rule. -/
theorem convex_ruleSet (K : ℕ) : Convex ℝ (ruleSet α K) := by
  intro ψ₁ h₁ ψ₂ h₂ a b ha hb hab A
  obtain ⟨n₁, s₁, t₁⟩ := h₁ A
  obtain ⟨n₂, s₂, t₂⟩ := h₂ A
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine ⟨fun T => add_nonneg (mul_nonneg ha (n₁ T)) (mul_nonneg hb (n₂ T)), ?_,
    fun T hT => ?_⟩
  · rw [sum_add_distrib, ← mul_sum, ← mul_sum, s₁, s₂]
    linarith
  · by_cases h : ψ₁ A T = 0
    · refine t₂ T fun h' => hT ?_
      simp [h, h']
    · exact t₁ T h

/-- The rules form a compact set: closed, with every entry in `[0, 1]`. -/
theorem isCompact_ruleSet (K : ℕ) : IsCompact (ruleSet α K) := by
  refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ =>
    isCompact_univ_pi fun _ => isCompact_Icc (a := (0 : ℝ)) (b := 1)) ?_ ?_
  · have : ruleSet α K = ⋂ A, ((⋂ T, {ψ : Finset α → Finset α → ℝ | 0 ≤ ψ A T}) ∩
        ({ψ | ∑ T, ψ A T = 1} ∩ ⋂ T, {ψ | ψ A T ≠ 0 → T ⊆ A ∧ T.card ≤ K})) := by
      ext ψ
      simp only [ruleSet, IsRule, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]
    rw [this]
    refine isClosed_iInter fun A => (isClosed_iInter fun T => ?_).inter
      ((isClosed_eq (by fun_prop) continuous_const).inter (isClosed_iInter fun T => ?_))
    · exact isClosed_le continuous_const (by fun_prop)
    · by_cases h : T ⊆ A ∧ T.card ≤ K
      · simp [h]
      · simp only [h, imp_false, not_not]
        exact isClosed_eq (by fun_prop) continuous_const
  · intro ψ hψ
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
    exact fun A T => ⟨(hψ A).1 T,
      (hψ A).2.1 ▸ single_le_sum (fun i _ => (hψ A).1 i) (mem_univ T)⟩

/-- The payoff is linear in the weights. -/
theorem crsPayoff_linComb_left (y : α → ℝ) (γ : ℝ) (w₁ w₂ : α → ℝ)
    (ψ : Finset α → Finset α → ℝ) (a b : ℝ) :
    crsPayoff y γ (a • w₁ + b • w₂) ψ = a * crsPayoff y γ w₁ ψ + b * crsPayoff y γ w₂ ψ := by
  unfold crsPayoff
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun e _ => by ring

/-- The payoff is affine in the rule. -/
theorem crsPayoff_linComb_right (y : α → ℝ) (γ : ℝ) (w : α → ℝ)
    (ψ₁ ψ₂ : Finset α → Finset α → ℝ) {a b : ℝ} (hab : a + b = 1) :
    crsPayoff y γ w (a • ψ₁ + b • ψ₂) = a * crsPayoff y γ w ψ₁ + b * crsPayoff y γ w ψ₂ := by
  unfold crsPayoff
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun e _ => ?_
  rw [show (fun A => ruleKeep (a • ψ₁ + b • ψ₂) A e) =
      fun A => a * ruleKeep ψ₁ A e + b * ruleKeep ψ₂ A e from
    funext fun A => ruleKeep_linComb ψ₁ ψ₂ a b A e, indepExp_linComb]
  linear_combination (w e * γ * y e) * hab

/-- The payoff is continuous in the weights. -/
theorem continuous_crsPayoff_left (y : α → ℝ) (γ : ℝ) (ψ : Finset α → Finset α → ℝ) :
    Continuous fun w => crsPayoff y γ w ψ := by
  unfold crsPayoff
  fun_prop

/-- The payoff is continuous in the rule. -/
theorem continuous_crsPayoff_right (y : α → ℝ) (γ : ℝ) (w : α → ℝ) :
    Continuous fun ψ => crsPayoff y γ w ψ := by
  unfold crsPayoff indepExp ruleKeep
  fun_prop

/-- **A `c_K`-balanced rule exists** for cap `K` whenever the expected number of
candidates is at most `K`. -/
theorem exists_balanced_rule (K : ℕ) {y : α → ℝ} (hy : ∀ e, 0 ≤ y e ∧ y e ≤ 1)
    (hK : ∑ e, y e ≤ K) : ∃ ψ, IsRule K ψ ∧ IsBalanced y (cK K) ψ := by
  rcases isEmpty_or_nonempty α with hα | hα
  · obtain ⟨ψ, hψ, -⟩ := exists_bestResponse K (0 : α → ℝ)
    exact ⟨ψ, hψ, fun e => isEmptyElim e⟩
  obtain ⟨e₀⟩ := hα
  have hsingle : ∀ e, (Pi.single e 1 : α → ℝ) ∈ weightSimplex α := fun e =>
    ⟨fun e' => by by_cases h : e' = e <;> simp [h], by simp⟩
  have hX : (weightSimplex α).Nonempty := ⟨Pi.single e₀ 1, hsingle e₀⟩
  have hY : (ruleSet α K).Nonempty := by
    obtain ⟨ψ, hψ, -⟩ := exists_bestResponse K (0 : α → ℝ)
    exact ⟨ψ, hψ⟩
  obtain ⟨w, hw, ψ, hψ, hsad⟩ := Sion.exists_isSaddlePointOn (f := crsPayoff y (cK K))
    hX convex_weightSimplex isCompact_weightSimplex
    (fun ψ _ => (continuous_crsPayoff_left y _ ψ).lowerSemicontinuous.lowerSemicontinuousOn _)
    (fun ψ _ => ConvexOn.quasiconvexOn ⟨convex_weightSimplex,
      fun w₁ _ w₂ _ a b _ _ _ => (crsPayoff_linComb_left y _ w₁ w₂ ψ a b).le⟩)
    (convex_ruleSet K) hY (isCompact_ruleSet K)
    (fun w _ => (continuous_crsPayoff_right y _ w).upperSemicontinuous.upperSemicontinuousOn _)
    (fun w _ => ConcaveOn.quasiconcaveOn ⟨convex_ruleSet K,
      fun ψ₁ _ ψ₂ _ a b _ _ hab => (crsPayoff_linComb_right y _ w ψ₁ ψ₂ hab).ge⟩)
  -- The best response to `w` earns at least `0`, by the correlation gap.
  obtain ⟨ψbr, hψbr, hbr⟩ := exists_bestResponse K w
  have hval : 0 ≤ crsPayoff y (cK K) w ψbr := by
    have hsplit : crsPayoff y (cK K) w ψbr =
        ∑ e, w e * indepExp univ y (fun A => ruleKeep ψbr A e) - cK K * ∑ e, w e * y e := by
      unfold crsPayoff
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun e _ => by ring
    rw [hsplit, sum_mul_indepExp univ y w (fun e A => ruleKeep ψbr A e),
      show (fun S => ∑ e, w e * ruleKeep ψbr S e) = fun S => topK w K S from funext hbr]
    linarith [indepExp_topK_gap K hy hK hw.1]
  -- So `ψ` earns at least `0` against every point mass.
  refine ⟨ψ, hψ, fun e => ?_⟩
  have h1 := hsad (Pi.single e 1) (hsingle e) ψbr hψbr
  have h2 : crsPayoff y (cK K) (Pi.single e 1) ψ =
      indepExp univ y (fun A => ruleKeep ψ A e) - cK K * y e := by
    simp [crsPayoff, Pi.single_apply]
  linarith

end DatingAlgo
