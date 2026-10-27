import DatingAlgo.ScreenedDH
import DatingAlgo.EdgeColoring
import DatingAlgo.TruthfulSwiping

/-!
# Theorem 2: the price of individual rationality

Theorem 2 of the vault note "Truthful Swiping with an LLM Oracle", and its combination
with Theorem 3 ("What it gives against full information").

**(a) The bound, on the note's instance.** A top-`k` user `a` with cost 1 has `b`
admirers and values each at `1 + ε`; each admirer values `a` at `H`, has cost 1 and no
other partner. When `a` matches `m` admirers, welfare is
`m (H - 1) + ((1 + ε) min(m, k) - m)` (`irWelfare`). In any equilibrium of any mechanism
in which sincere swiping is an equilibrium (dominant, ex post or Bayes–Nash, with or
without audits), `a` can pass on everyone, so `a`'s expected utility is at least 0. That
is the only property of the mechanism the proof uses, so the theorem takes any
distribution of `m` with `E[u_a] ≥ 0`.
* `thm2a_welfare_le`: then `E W ≤ (1 + ε) k (H - 1) + ε k`.
* `thm2a`: for every `δ > 0` and large `H`, `E W ≤ ((1 + ε) k / b + δ) · W(b)`, where
  `W(b)`, showing `a` all `b` admirers (Lemma R), is a lower bound on `OPT_FI`.

**(b)–(d) The guarantees**, for a `ScreenedMarket`. `optFI` is the expected best welfare
over match sets of acceptable pairs that give each user at most its cap (`withCaps b`:
every cap `b`; by Lemma R these are the match sets a design with capacity `b` can show).
Users' values may depend on the realization.
* `optFI_topK_le` (b): for top-`k` users with `1 ≤ k ≤ b`, `OPT_FI ≤ (b/k) OPT_IR`, where
  `OPT_IR` caps every user at `k`. This sharpens the note's `⌈b/k⌉` (`optFI_topK_le_ceil`)
  and matches (a). The proof splits an optimal set with König's edge-coloring theorem.
* `optFI_subadditive_le` (c): for subadditive users, `OPT_FI ≤ b · OPT_IR` with cap 1.
* `optFI_additive` (d): for additive users, `OPT_FI = OPT_IR` when the caps agree.
* `sdh_vs_optFI_topK`, `sdh_vs_optFI_subadditive`: SDH gets `c_k² (k/b)` and `c_1² / b`
  of `OPT_FI`.
-/

namespace DatingAlgo

open Finset

section Instance

/-- `a`'s utility in Theorem 2(a)'s instance with `m` matches. -/
noncomputable def irUtilA (k : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  (1 + ε) * min (m : ℝ) k - m

/-- Welfare in Theorem 2(a)'s instance when `a` matches `m` admirers. -/
noncomputable def irWelfare (k : ℕ) (ε H : ℝ) (m : ℕ) : ℝ :=
  m * (H - 1) + irUtilA k ε m

/-- **Theorem 2(a), any equilibrium.** Over any finite distribution `μ` of `a`'s number of
matches in which `a`'s expected utility is at least 0, expected welfare is at most
`(1 + ε) k (H - 1) + ε k`. -/
theorem thm2a_welfare_le {Ω : Type*} [Fintype Ω] (μ : Ω → ℝ) (hμ0 : ∀ ω, 0 ≤ μ ω)
    (hμ1 : ∑ ω, μ ω = 1) (m : Ω → ℕ) (k : ℕ) {ε H : ℝ} (hε : 0 ≤ ε) (hH : 1 ≤ H)
    (hIR : 0 ≤ ∑ ω, μ ω * irUtilA k ε (m ω)) :
    ∑ ω, μ ω * irWelfare k ε H (m ω) ≤ (1 + ε) * k * (H - 1) + ε * k := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hEk : ∑ ω, μ ω * ((1 + ε) * k) = (1 + ε) * k := by rw [← sum_mul, hμ1, one_mul]
  have hEu : ∑ ω, μ ω * irUtilA k ε (m ω) =
      ∑ ω, μ ω * ((1 + ε) * min (m ω : ℝ) k) - ∑ ω, μ ω * (m ω : ℝ) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun ω _ => by unfold irUtilA; ring
  have hmin : ∑ ω, μ ω * ((1 + ε) * min (m ω : ℝ) k) ≤ ∑ ω, μ ω * ((1 + ε) * k) :=
    sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)) (hμ0 ω)
  have hu : ∑ ω, μ ω * irUtilA k ε (m ω) ≤ ε * k := by
    calc ∑ ω, μ ω * irUtilA k ε (m ω) ≤ ∑ ω, μ ω * (ε * k) := by
          refine sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (hμ0 ω)
          unfold irUtilA
          have h1 := min_le_left (m ω : ℝ) k
          have h2 := min_le_right (m ω : ℝ) k
          nlinarith
      _ = ε * k := by rw [← sum_mul, hμ1, one_mul]
  have hW : ∑ ω, μ ω * irWelfare k ε H (m ω) =
      (H - 1) * ∑ ω, μ ω * (m ω : ℝ) + ∑ ω, μ ω * irUtilA k ε (m ω) := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun ω _ => by unfold irWelfare; ring
  have hm : ∑ ω, μ ω * (m ω : ℝ) ≤ (1 + ε) * k := by linarith
  rw [hW]
  nlinarith [mul_le_mul_of_nonneg_left hm (by linarith : (0 : ℝ) ≤ H - 1)]

/-- **Theorem 2(a).** For top-`k` users with `1 ≤ k ≤ b` and any `ε ≥ 0`, `δ > 0`: once
`H` is large, every mechanism in which `a`'s expected utility is at least 0 earns at most
`((1 + ε) k / b + δ)` times the welfare of showing `a` all `b` admirers, hence of
`OPT_FI`. -/
theorem thm2a {k b : ℕ} (hk : 1 ≤ k) (hkb : k ≤ b) {ε : ℝ} (hε : 0 ≤ ε) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ H₀ : ℝ, ∀ H ≥ H₀, ∀ (Ω : Type) [Fintype Ω] (μ : Ω → ℝ), (∀ ω, 0 ≤ μ ω) →
      ∑ ω, μ ω = 1 → ∀ m : Ω → ℕ, 0 ≤ ∑ ω, μ ω * irUtilA k ε (m ω) →
        ∑ ω, μ ω * irWelfare k ε H (m ω) ≤ ((1 + ε) * k / b + δ) * irWelfare k ε H b := by
  have hb : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hkb' : (k : ℝ) ≤ b := by exact_mod_cast hkb
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hδb : 0 < δ * b := mul_pos hδ hb
  refine ⟨2 + (ε * k + (1 + ε) * k) / (δ * b), fun H hH Ω _ μ hμ0 hμ1 m hIR => ?_⟩
  have hq : (ε * k + (1 + ε) * k) / (δ * b) * (δ * b) = ε * k + (1 + ε) * k :=
    div_mul_cancel₀ _ hδb.ne'
  have hq0 : 0 ≤ (ε * k + (1 + ε) * k) / (δ * b) := div_nonneg (by positivity) hδb.le
  refine (thm2a_welfare_le μ hμ0 hμ1 m k hε (by linarith) hIR).trans ?_
  have hWb : irWelfare k ε H b = b * (H - 1) + (1 + ε) * k - b := by
    unfold irWelfare irUtilA
    rw [min_eq_right hkb']
    ring
  have hkey : ε * k + (1 + ε) * k + δ * b ≤ δ * b * (H - 1) := by nlinarith
  have hexp : ((1 + ε) * k / b + δ) * (b * (H - 1) + (1 + ε) * k - b) =
      (1 + ε) * k * (H - 1) + ((1 + ε) * k) ^ 2 / b - (1 + ε) * k + δ * b * (H - 1) +
        δ * ((1 + ε) * k) - δ * b := by
    field_simp
    ring
  have hsq : 0 ≤ ((1 + ε) * k) ^ 2 / b := by positivity
  have hδk : 0 ≤ δ * ((1 + ε) * k) := by positivity
  rw [hWb, hexp]
  linarith

end Instance

namespace ScreenedMarket

variable {I J C : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype C] [DecidableEq C] (M : ScreenedMarket I J C)

/-- The same market with every cap equal to `b`. -/
def withCaps (b : ℕ) : ScreenedMarket I J C :=
  { M with capI := fun _ => b, capJ := fun _ => b }

/-- The best value of `g` over capped subsets of `F`. -/
noncomputable def bestBy (F : Finset (I × J)) (g : Finset (I × J) → ℝ) : ℝ :=
  (F.powerset.filter M.CapOK).sup'
    ⟨∅, mem_filter.mpr ⟨empty_mem_powerset F, by simp [CapOK]⟩⟩ g

/-- Users' total utility from match set `S`, for value functions `vI`, `vJ`. -/
def welfare (vI : I → Finset J → ℝ) (vJ : J → Finset I → ℝ) (S : Finset (I × J)) : ℝ :=
  (∑ i, (vI i (univ.filter fun j => (i, j) ∈ S) -
      M.costI i * (univ.filter fun j => (i, j) ∈ S).card)) +
    ∑ j, (vJ j (univ.filter fun i => (i, j) ∈ S) -
      M.costJ j * (univ.filter fun i => (i, j) ∈ S).card)

/-- `OPT_FI`: the expected best welfare over capped sets of acceptable pairs, knowing
every value. The value functions may depend on the realization `ω`. -/
noncomputable def optFI (vI : (I × J → C) → I → Finset J → ℝ)
    (vJ : (I × J → C) → J → Finset I → ℝ) : ℝ :=
  prodExp M.π fun ω =>
    M.bestBy (univ.filter fun e => M.Acc e (ω e)) (M.welfare (vI ω) (vJ ω))

/-- Top-`k` values of `I`-side users under realization `ω`. -/
noncomputable def topKI (k : ℕ) (ω : I × J → C) (i : I) (T : Finset J) : ℝ :=
  topK (fun j => M.valI (i, j) (ω (i, j))) k T

/-- Top-`k` values of `J`-side users under realization `ω`. -/
noncomputable def topKJ (k : ℕ) (ω : I × J → C) (j : J) (T : Finset I) : ℝ :=
  topK (fun i => M.valJ (i, j) (ω (i, j))) k T

omit [Fintype I] [Fintype J] [Fintype C] [DecidableEq C] in
/-- The best capped set is never negative: the empty set is capped. -/
theorem bestMatch_nonneg (F : Finset (I × J)) (w : I × J → ℝ) : 0 ≤ M.bestMatch F w := by
  simpa using M.sum_le_bestMatch w (empty_subset F) (by simp [CapOK])

omit [DecidableEq C] in
/-- `OPT_IR` is never negative. -/
theorem optIR_nonneg (hπ : IsDist M.π) : 0 ≤ M.optIR :=
  prodExp_nonneg hπ.1 fun _ => M.bestMatch_nonneg _ _

omit [Fintype I] [Fintype J] [Fintype C] [DecidableEq C] in
/-- The best value of `g` over capped subsets of `F` is attained. -/
theorem exists_bestBy_eq (F : Finset (I × J)) (g : Finset (I × J) → ℝ) :
    ∃ S, S ⊆ F ∧ M.CapOK S ∧ M.bestBy F g = g S := by
  unfold bestBy
  obtain ⟨S, hS, hEq⟩ := exists_mem_eq_sup' (⟨∅, mem_filter.mpr ⟨empty_mem_powerset F, by
    simp [CapOK]⟩⟩ : (F.powerset.filter M.CapOK).Nonempty) g
  obtain ⟨hSF, hScap⟩ := mem_filter.mp hS
  exact ⟨S, mem_powerset.mp hSF, hScap, hEq⟩

omit [Fintype C] [DecidableEq C] in
/-- If every user's value is at most the sum of its values for single partners, welfare
is at most the total net weight. -/
theorem welfare_le_sum_wt (ω : I × J → C) {vI : I → Finset J → ℝ} {vJ : J → Finset I → ℝ}
    (hvI : ∀ i T, vI i T ≤ ∑ j ∈ T, M.valI (i, j) (ω (i, j)))
    (hvJ : ∀ j T, vJ j T ≤ ∑ i ∈ T, M.valJ (i, j) (ω (i, j))) (S : Finset (I × J)) :
    M.welfare vI vJ S ≤ ∑ e ∈ S, M.wt e (ω e) := by
  have hcap : (M.withCaps S.card).CapOK S :=
    ⟨fun _ => card_filter_le _ _, fun _ => card_filter_le _ _⟩
  have h := (M.withCaps S.card).welfare_eq_sum_wt ω
    (fun i T => ∑ j ∈ T, M.valI (i, j) (ω (i, j))) (fun j T => ∑ i ∈ T, M.valJ (i, j) (ω (i, j)))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) hcap
  refine le_trans ?_ (le_of_eq h)
  exact add_le_add (sum_le_sum fun i _ => sub_le_sub_right (hvI i _) _)
    (sum_le_sum fun j _ => sub_le_sub_right (hvJ j _) _)

omit [Fintype C] [DecidableEq C] in
/-- On a set with every degree at most `b`, the total net weight of acceptable pairs is at
most `b/k` times the best set with every degree at most `k`. -/
theorem sum_wt_le_bestMatch (ω : I × J → C) {k b : ℕ} (hk : 1 ≤ k) (hkb : k ≤ b)
    {S : Finset (I × J)} (hS : (M.withCaps b).CapOK S) (hacc : ∀ e ∈ S, M.Acc e (ω e)) :
    ∑ e ∈ S, M.wt e (ω e) ≤
      (b / k) * (M.withCaps k).bestMatch (univ.filter fun e => M.Acc e (ω e))
        (fun e => M.wt e (ω e)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  obtain ⟨T, hTS, hTI, hTJ, hT⟩ :=
    exists_degCap_subset S hkb (fun i => hS.1 i) (fun j => hS.2 j) fun e => M.wt e (ω e)
  have hTF : T ⊆ univ.filter fun e => M.Acc e (ω e) :=
    fun e he => mem_filter.mpr ⟨mem_univ _, hacc e (hTS he)⟩
  have hTbest := (M.withCaps k).sum_le_bestMatch (fun e => M.wt e (ω e)) hTF ⟨hTI, hTJ⟩
  have h1 : ∑ e ∈ S, M.wt e (ω e) ≤ (b / k) * ∑ e ∈ T, M.wt e (ω e) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hk0]
    linarith
  exact h1.trans (mul_le_mul_of_nonneg_left hTbest (by positivity))

omit [Fintype C] [DecidableEq C] in
/-- **Theorem 2(b), one realization.** For top-`k` users with non-negative values and
`1 ≤ k ≤ b`, any match set of acceptable pairs with every user at most `b` matches has
welfare at most `b/k` times the best set with every user at most `k` matches. -/
theorem welfare_topK_le (ω : I × J → C) {k b : ℕ} (hk : 1 ≤ k) (hkb : k ≤ b)
    (hvI : ∀ e c, 0 ≤ M.valI e c) (hvJ : ∀ e c, 0 ≤ M.valJ e c) {S : Finset (I × J)}
    (hS : (M.withCaps b).CapOK S) (hacc : ∀ e ∈ S, M.Acc e (ω e)) :
    M.welfare (M.topKI k ω) (M.topKJ k ω) S ≤
      (b / k) * (M.withCaps k).bestMatch (univ.filter fun e => M.Acc e (ω e))
        (fun e => M.wt e (ω e)) := by
  refine le_trans ?_ (M.sum_wt_le_bestMatch ω hk hkb hS hacc)
  refine M.welfare_le_sum_wt ω (fun i T => ?_) (fun j T => ?_) S
  · obtain ⟨W, hWT, _, hEq⟩ := exists_topK_eq (fun j => M.valI (i, j) (ω (i, j))) k T
    unfold topKI
    rw [hEq]
    exact sum_le_sum_of_subset_of_nonneg hWT fun _ _ _ => hvI _ _
  · obtain ⟨W, hWT, _, hEq⟩ := exists_topK_eq (fun i => M.valJ (i, j) (ω (i, j))) k T
    unfold topKJ
    rw [hEq]
    exact sum_le_sum_of_subset_of_nonneg hWT fun _ _ _ => hvJ _ _

omit [DecidableEq C] in
/-- **Theorem 2(b).** For top-`k` users with non-negative values and `1 ≤ k ≤ b`,
`OPT_FI ≤ (b/k) OPT_IR`: the full-information optimum with caps `b` is at most `b/k`
times the best outcome that gives no user more than `k` matches. -/
theorem optFI_topK_le (hπ : IsDist M.π) {k b : ℕ} (hk : 1 ≤ k) (hkb : k ≤ b)
    (hvI : ∀ e c, 0 ≤ M.valI e c) (hvJ : ∀ e c, 0 ≤ M.valJ e c) :
    (M.withCaps b).optFI (M.topKI k) (M.topKJ k) ≤ (b / k) * (M.withCaps k).optIR := by
  unfold optFI optIR
  rw [← prodExp_const_mul]
  refine prodExp_mono hπ.1 fun ω => ?_
  obtain ⟨S, hSF, hScap, hEq⟩ := (M.withCaps b).exists_bestBy_eq
    (univ.filter fun e => M.Acc e (ω e)) (M.welfare (M.topKI k ω) (M.topKJ k ω))
  rw [show (M.withCaps b).bestBy (univ.filter fun e => (M.withCaps b).Acc e (ω e))
      ((M.withCaps b).welfare (M.topKI k ω) (M.topKJ k ω)) =
      M.welfare (M.topKI k ω) (M.topKJ k ω) S from hEq]
  exact M.welfare_topK_le ω hk hkb hvI hvJ hScap fun e he => (mem_filter.mp (hSF he)).2

omit [DecidableEq C] in
/-- **Theorem 2(b), the note's form.** `OPT_IR ≥ OPT_FI / ⌈b/k⌉`. -/
theorem optFI_topK_le_ceil (hπ : IsDist M.π) {k b : ℕ} (hk : 1 ≤ k) (hkb : k ≤ b)
    (hvI : ∀ e c, 0 ≤ M.valI e c) (hvJ : ∀ e c, 0 ≤ M.valJ e c) :
    (M.withCaps b).optFI (M.topKI k) (M.topKJ k) ≤
      (⌈(b : ℝ) / k⌉₊ : ℝ) * (M.withCaps k).optIR :=
  (M.optFI_topK_le hπ hk hkb hvI hvJ).trans
    (mul_le_mul_of_nonneg_right (Nat.le_ceil _) ((M.withCaps k).optIR_nonneg hπ))

omit [DecidableEq C] in
/-- **Theorem 2(c).** For subadditive users (`v (S ∪ T) ≤ v S + v T`, `v ∅ = 0`,
`v {x}` the value of `x`), the full-information optimum with caps `b ≥ 1` is at most `b`
times the best matching (`OPT_IR` with cap 1). -/
theorem optFI_subadditive_le (hπ : IsDist M.π) {b : ℕ} (hb : 1 ≤ b)
    (vI : (I × J → C) → I → Finset J → ℝ) (vJ : (I × J → C) → J → Finset I → ℝ)
    (hsubI : ∀ ω i S T, vI ω i (S ∪ T) ≤ vI ω i S + vI ω i T)
    (hsubJ : ∀ ω j S T, vJ ω j (S ∪ T) ≤ vJ ω j S + vJ ω j T)
    (hzeroI : ∀ ω i, vI ω i ∅ = 0) (hzeroJ : ∀ ω j, vJ ω j ∅ = 0)
    (hsingleI : ∀ ω i j, vI ω i {j} = M.valI (i, j) (ω (i, j)))
    (hsingleJ : ∀ ω i j, vJ ω j {i} = M.valJ (i, j) (ω (i, j))) :
    (M.withCaps b).optFI vI vJ ≤ b * (M.withCaps 1).optIR := by
  have hI : ∀ ω i (T : Finset J), vI ω i T ≤ ∑ j ∈ T, M.valI (i, j) (ω (i, j)) := by
    intro ω i T
    induction T using Finset.induction_on with
    | empty => simp [hzeroI]
    | insert j T hj ih =>
      rw [sum_insert hj, ← hsingleI ω i j, insert_eq]
      exact (hsubI ω i {j} T).trans (add_le_add le_rfl ih)
  have hJ : ∀ ω j (T : Finset I), vJ ω j T ≤ ∑ i ∈ T, M.valJ (i, j) (ω (i, j)) := by
    intro ω j T
    induction T using Finset.induction_on with
    | empty => simp [hzeroJ]
    | insert i T hi ih =>
      rw [sum_insert hi, ← hsingleJ ω i j, insert_eq]
      exact (hsubJ ω j {i} T).trans (add_le_add le_rfl ih)
  unfold optFI optIR
  rw [← prodExp_const_mul]
  refine prodExp_mono hπ.1 fun ω => ?_
  obtain ⟨S, hSF, hScap, hEq⟩ := (M.withCaps b).exists_bestBy_eq
    (univ.filter fun e => M.Acc e (ω e)) (M.welfare (vI ω) (vJ ω))
  rw [show (M.withCaps b).bestBy (univ.filter fun e => (M.withCaps b).Acc e (ω e))
      ((M.withCaps b).welfare (vI ω) (vJ ω)) = M.welfare (vI ω) (vJ ω) S from hEq]
  have h := M.sum_wt_le_bestMatch ω le_rfl hb hScap fun e he => (mem_filter.mp (hSF he)).2
  rw [Nat.cast_one, div_one] at h
  exact (M.welfare_le_sum_wt ω (hI ω) (hJ ω) S).trans h

omit [DecidableEq C] in
/-- **Theorem 2(d).** For additive users there is no price: `OPT_FI = OPT_IR` when the IR
caps are the design's caps. -/
theorem optFI_additive :
    M.optFI (fun ω i T => ∑ j ∈ T, M.valI (i, j) (ω (i, j)))
      (fun ω j T => ∑ i ∈ T, M.valJ (i, j) (ω (i, j))) = M.optIR := by
  unfold optFI optIR
  refine prodExp_congr _ fun ω => ?_
  unfold bestBy bestMatch
  exact sup'_congr _ rfl fun S hS =>
    M.welfare_eq_sum_wt ω _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) (mem_filter.mp hS).2

/-- **SDH against full information, top-`k` (Theorems 2(b) and 3(b)).** SDH with IR caps
`k`, run on an optimal plan, earns at least `c_k² (k/b) OPT_FI`. -/
theorem sdh_vs_optFI_topK [Nonempty C] (hπ : IsDist M.π) {k b : ℕ} (hk : 1 ≤ k)
    (hkb : k ≤ b) (hvI : ∀ e c, 0 ≤ M.valI e c) (hvJ : ∀ e c, 0 ≤ M.valJ e c)
    {x : I × J → C → ℝ} (hx : (M.withCaps k).IsLPOptimal x) :
    cK k ^ 2 * (k / b) * (M.withCaps b).optFI (M.topKI k) (M.topKJ k) ≤
      (M.withCaps k).sdhValue ((M.withCaps k).sdhTau x) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have h1 : (k / b : ℝ) * (M.withCaps b).optFI (M.topKI k) (M.topKJ k) ≤
      (M.withCaps k).optIR := by
    calc (k / b : ℝ) * (M.withCaps b).optFI (M.topKI k) (M.topKJ k)
        ≤ (k / b) * ((b / k) * (M.withCaps k).optIR) :=
          mul_le_mul_of_nonneg_left (M.optFI_topK_le hπ hk hkb hvI hvJ) (by positivity)
      _ = (M.withCaps k).optIR := by field_simp
  calc cK k ^ 2 * (k / b) * (M.withCaps b).optFI (M.topKI k) (M.topKJ k)
      = cK k ^ 2 * ((k / b) * (M.withCaps b).optFI (M.topKI k) (M.topKJ k)) := by ring
    _ ≤ cK k ^ 2 * (M.withCaps k).optIR := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ ≤ _ := (M.withCaps k).sdh_welfare hπ hx k (fun _ => le_rfl) fun _ => le_rfl

/-- **SDH against full information, subadditive users (Theorems 2(c) and 3(b)).** SDH with
IR cap 1, run on an optimal plan, earns at least `c_1² / b · OPT_FI`. -/
theorem sdh_vs_optFI_subadditive [Nonempty C] (hπ : IsDist M.π) {b : ℕ} (hb : 1 ≤ b)
    (vI : (I × J → C) → I → Finset J → ℝ) (vJ : (I × J → C) → J → Finset I → ℝ)
    (hsubI : ∀ ω i S T, vI ω i (S ∪ T) ≤ vI ω i S + vI ω i T)
    (hsubJ : ∀ ω j S T, vJ ω j (S ∪ T) ≤ vJ ω j S + vJ ω j T)
    (hzeroI : ∀ ω i, vI ω i ∅ = 0) (hzeroJ : ∀ ω j, vJ ω j ∅ = 0)
    (hsingleI : ∀ ω i j, vI ω i {j} = M.valI (i, j) (ω (i, j)))
    (hsingleJ : ∀ ω i j, vJ ω j {i} = M.valJ (i, j) (ω (i, j)))
    {x : I × J → C → ℝ} (hx : (M.withCaps 1).IsLPOptimal x) :
    cK 1 ^ 2 / b * (M.withCaps b).optFI vI vJ ≤
      (M.withCaps 1).sdhValue ((M.withCaps 1).sdhTau x) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have h1 : (M.withCaps b).optFI vI vJ / b ≤ (M.withCaps 1).optIR := by
    rw [div_le_iff₀ hb0, mul_comm]
    exact M.optFI_subadditive_le hπ hb vI vJ hsubI hsubJ hzeroI hzeroJ hsingleI hsingleJ
  calc cK 1 ^ 2 / b * (M.withCaps b).optFI vI vJ
      = cK 1 ^ 2 * ((M.withCaps b).optFI vI vJ / b) := by ring
    _ ≤ cK 1 ^ 2 * (M.withCaps 1).optIR := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ ≤ _ := (M.withCaps 1).sdh_welfare hπ hx 1 (fun _ => le_rfl) fun _ => le_rfl

end ScreenedMarket

end DatingAlgo
