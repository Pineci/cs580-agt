import DatingAlgo.ScreenedDH
import DatingAlgo.UniformRule
import DatingAlgo.BalancedCRS

/-!
# Max-min screened DH

The max-min version of screened DH from the vault note "Max-Min Match Quality and
Egalitarian Matching": plan to maximize the worst-off user's expected surplus instead of
the total, then screen and select as SDH does. The market, plans and screening are those
of `ScreenedDH.lean`. Utilities are additive within caps: a user's utility from a capped
set is the sum of its surpluses `value - cost`. That covers additive users, and top-`k`
users with cap at most `k` (`welfare_eq_sum_wt`).

**Correction to the note.** The note claims every user keeps a `c_K^2` share of its planned
surplus "because contention resolution holds user by user". SDH's guarantee
(`lpValue_le_sdhValue`) is on total weight only, and SDH's selection, the best capped set
of found pairs, can starve a user: `MaxMinCounterexample.lean` gives a market where the
worst-off user gets `θ*/3 < c_1^2 θ*`. A per-user guarantee needs a selection that
protects every pair, which is what this file proves:

* **Benchmark.** `exists_plan_of_policy`: every full-information policy (any law over
  capped sets of acceptable pairs, chosen knowing all values) induces a feasible plan
  with the same expected surplus for every user. So `floor_le_maxMin`: no such policy
  guarantees every user more than the max-min LP value `θ*`.
* **Mechanism.** `mmUtilI` and `mmUtilJ`: screen and thin as SDH's analysis does
  (`thinLaw`: query pair `e` with probability `τ e`, keep a found pair in combination `c`
  with probability `x e c / (τ e π e c)`), then stage 1: each responder `j` keeps a set
  drawn by its rule `ψ1 j` from its candidates; stage 2: each initiator `i` keeps a set
  drawn by `ψ2 i` from the pairs stage 1 passed to it.
* **Composition.** `mmUtilI_ge`, `mmUtilJ_ge`: if every stage-1 rule is `γ1`-balanced and
  every stage-2 rule is `γ2`-balanced (`IsBalanced`), every user gets at least
  `γ1 γ2` times its planned surplus.
* **Random order.** `mmsdh_quarter`: with uniformly random selection at both stages,
  every user gets at least `1/4` of its planned surplus, so with a max-min optimal plan
  the worst-off user gets at least `θ*/4 ≥ OPT_min/4` (`mmsdh_quarter_maxMin`).
* **The note's constant.** `mmsdh_cK`: with `c_K`-balanced rules at both stages
  (`exists_balanced_rule`), every user gets at least `c_K^2` times its planned surplus,
  for `K` at most every cap; `mmsdh_cK_maxMin` gives `c_K^2 θ* ≥ c_K^2 OPT_min`.

**Truthfulness.** MM-SDH shows each user only its selected partners, a capped set of
acceptable pairs chosen from oracle answers and coins. `sdh_dsic` (`TruthfulSwiping.lean`)
holds for every such planned set, so sincere swiping stays dominant.
-/

namespace DatingAlgo

open Finset

/-! ### Independence tools -/

section Tools

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

/-- The expectation of a product of functions of different coordinates is the product of
their expectations. -/
theorem prodExp_prod (μ : ι → Ω → ℝ) (φ : ι → Ω → ℝ) :
    prodExp μ (fun ω => ∏ k, φ k (ω k)) = ∏ k, ∑ o, μ k o * φ k o := by
  unfold prodExp
  rw [← sum_prod_weight (fun k o => μ k o * φ k o)]
  exact sum_congr rfl fun ω _ => prod_mul_distrib.symm

/-- Splitting a product over all coordinates into `k₀`, a set `S` avoiding `k₀`, and the
rest. -/
theorem prod_split (k₀ : ι) {S : Finset ι} (hS : S ⊆ univ.erase k₀) (f a b : ι → ℝ) :
    ∏ k, (if k = k₀ then f k else if k ∈ S then a k else b k) =
      f k₀ * ((∏ k ∈ S, a k) * ∏ k ∈ univ.erase k₀ \ S, b k) := by
  have h1 : ∏ k ∈ univ.erase k₀, (if k = k₀ then f k else if k ∈ S then a k else b k) =
      ∏ k ∈ univ.erase k₀, (if k ∈ S then a k else b k) :=
    prod_congr rfl fun k hk => ite_eq_right (ne_of_mem_erase hk)
  rw [← mul_prod_erase univ _ (mem_univ k₀), ite_eq_left rfl, h1, prod_ite, filter_mem_eq_inter,
    inter_eq_right.mpr hS, ← sdiff_eq_filter]

/-- **One coordinate against the coins of the others.** If the coins of the coordinates
other than `k₀` have probabilities `P k (ω k)` that depend on their own coordinate only,
then averaging over `ω` turns them into coins with the averaged probabilities, and the
factor `F (ω k₀)` separates. -/
theorem prodExp_mul_indepExp {μ : ι → Ω → ℝ} (hμ : ∀ k, ∑ o, μ k o = 1) (k₀ : ι)
    (F : Ω → ℝ) (P : ι → Ω → ℝ) (h : Finset ι → ℝ) :
    prodExp μ (fun ω => F (ω k₀) * indepExp (univ.erase k₀) (fun k => P k (ω k)) h) =
      (∑ o, μ k₀ o * F o) * indepExp (univ.erase k₀) (fun k => ∑ o, μ k o * P k o) h := by
  unfold indepExp
  simp_rw [mul_sum]
  rw [prodExp_sum]
  refine sum_congr rfl fun S hS => ?_
  have hS' := mem_powerset.mp hS
  have hpt : ∀ ω : ι → Ω, F (ω k₀) * (((∏ k ∈ S, P k (ω k)) *
      ∏ k ∈ univ.erase k₀ \ S, (1 - P k (ω k))) * h S) =
      h S * ∏ k, (fun k o => if k = k₀ then F o else if k ∈ S then P k o else 1 - P k o)
        k (ω k) := by
    intro ω
    rw [prod_split k₀ hS' (fun k => F (ω k)) (fun k => P k (ω k)) (fun k => 1 - P k (ω k))]
    ring
  rw [prodExp_congr μ hpt, prodExp_const_mul, prodExp_prod μ
    (fun k o => if k = k₀ then F o else if k ∈ S then P k o else 1 - P k o)]
  have hfac : ∀ k, ∑ o, μ k o *
      (fun k o => if k = k₀ then F o else if k ∈ S then P k o else 1 - P k o) k o =
      if k = k₀ then ∑ o, μ k o * F o else if k ∈ S then ∑ o, μ k o * P k o
        else 1 - ∑ o, μ k o * P k o := by
    intro k
    split_ifs <;> simp [*, mul_sub, sum_sub_distrib, hμ k]
  rw [prod_congr rfl fun k _ => hfac k, prod_split k₀ hS' (fun k => ∑ o, μ k o * F o)]
  ring

omit [Fintype ι] [Fintype Ω] in
/-- With coins that are certain, `indepExp` is the value at the set of sure elements. -/
theorem indepExp_indicator (U S₀ : Finset ι) (h : Finset ι → ℝ) :
    indepExp U (fun k => if k ∈ S₀ then 1 else 0) h = h (U.filter (· ∈ S₀)) := by
  unfold indepExp
  rw [sum_eq_single (U.filter (· ∈ S₀))]
  · have h1 : ∏ k ∈ U.filter (· ∈ S₀), (if k ∈ S₀ then (1 : ℝ) else 0) = 1 :=
      prod_eq_one fun k hk => ite_eq_left (mem_filter.mp hk).2
    have h2 : ∏ k ∈ U \ U.filter (· ∈ S₀), (1 - if k ∈ S₀ then (1 : ℝ) else 0) = 1 :=
      prod_eq_one fun k hk => by
        have hk' := mem_sdiff.mp hk
        have : k ∉ S₀ := fun h => hk'.2 (mem_filter.mpr ⟨hk'.1, h⟩)
        simp [this]
    rw [h1, h2, one_mul, one_mul]
  · intro S hS hne
    have hSU := mem_powerset.mp hS
    by_cases hsub : S ⊆ S₀
    · obtain ⟨k, hk, hkS⟩ : ∃ k ∈ U.filter (· ∈ S₀), k ∉ S := by
        by_contra hcon
        push Not at hcon
        exact hne (Subset.antisymm (fun k hk => mem_filter.mpr ⟨hSU hk, hsub hk⟩) hcon)
      have hk' := mem_filter.mp hk
      rw [prod_eq_zero (i := k) (mem_sdiff.mpr ⟨hk'.1, hkS⟩) (by simp [hk'.2]), mul_zero,
        zero_mul]
    · obtain ⟨k, hkS, hk0⟩ := not_subset.mp hsub
      rw [prod_eq_zero (i := k) hkS (by simp [hk0]), zero_mul, zero_mul]
  · intro hcon
    exact absurd (mem_powerset.mpr (filter_subset _ _)) hcon

omit [Fintype Ω] in
/-- Splitting off a coordinate that `F` needs: if `F B = 0` whenever `k₀ ∉ B`, only the
outcomes with `k₀` in count. -/
theorem indepExp_univ_split {p : ι → ℝ} {F : Finset ι → ℝ} (k₀ : ι)
    (hF : ∀ B, k₀ ∉ B → F B = 0) :
    indepExp univ p F = p k₀ * indepExp (univ.erase k₀) p (fun B => F (insert k₀ B)) := by
  have h0 : indepExp (univ.erase k₀) p F = 0 := by
    rw [indepExp_congr (h := fun _ => 0)
      (fun S hS => hF S fun h => notMem_erase k₀ univ (hS h)), indepExp_const]
  conv_lhs => rw [← insert_erase (mem_univ k₀)]
  rw [indepExp_insert (notMem_erase k₀ univ), h0, mul_zero, zero_add]

omit [Fintype ι] [Fintype Ω] in
/-- `indepExp` of a function with values in `[0, 1]`, with probabilities in `[0, 1]`, is in
`[0, 1]`. -/
theorem indepExp_mem_Icc {U : Finset ι} {p : ι → ℝ} (hp : ∀ k ∈ U, 0 ≤ p k ∧ p k ≤ 1)
    {g : Finset ι → ℝ} (hg : ∀ S, 0 ≤ g S ∧ g S ≤ 1) :
    0 ≤ indepExp U p g ∧ indepExp U p g ≤ 1 := by
  constructor
  · calc (0 : ℝ) = indepExp U p (fun _ => 0) := (indepExp_const U p 0).symm
      _ ≤ _ := indepExp_mono hp fun S _ => (hg S).1
  · calc indepExp U p g ≤ indepExp U p (fun _ => 1) := indepExp_mono hp fun S _ => (hg S).2
      _ = 1 := indepExp_const U p 1

end Tools

/-! ### Facts about rules -/

section Rules

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A rule never keeps a non-candidate. -/
theorem ruleKeep_eq_zero {K : ℕ} {ψ : Finset α → Finset α → ℝ} (hψ : IsRule K ψ)
    {A : Finset α} {e : α} (he : e ∉ A) : ruleKeep ψ A e = 0 :=
  sum_eq_zero fun T _ => by
    by_cases heT : e ∈ T
    · have hT : ψ A T = 0 := by
        by_contra h
        exact he (((hψ A).2.2 T h).1 heT)
      rw [hT, zero_mul]
    · rw [ite_eq_right heT, mul_zero]

/-- A keep probability is a probability. -/
theorem ruleKeep_mem {K : ℕ} {ψ : Finset α → Finset α → ℝ} (hψ : IsRule K ψ)
    (A : Finset α) (e : α) : 0 ≤ ruleKeep ψ A e ∧ ruleKeep ψ A e ≤ 1 := by
  refine ⟨sum_nonneg fun T _ => mul_nonneg ((hψ A).1 T) (by split_ifs <;> norm_num), ?_⟩
  calc ruleKeep ψ A e ≤ ∑ T, ψ A T :=
        sum_le_sum fun T _ => by split_ifs <;> simp [(hψ A).1 T]
    _ = 1 := (hψ A).2.1

/-- Balance with a constant implies balance with any smaller one. -/
theorem IsBalanced.mono {y : α → ℝ} {γ γ' : ℝ} {ψ : Finset α → Finset α → ℝ}
    (h : IsBalanced y γ ψ) (hγ : γ' ≤ γ) (hy : ∀ e, 0 ≤ y e) : IsBalanced y γ' ψ :=
  fun e => (mul_le_mul_of_nonneg_right hγ (hy e)).trans (h e)

end Rules

namespace ScreenedMarket

variable {I J C : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype C] [DecidableEq C] (M : ScreenedMarket I J C)

/-! ### Planned surplus and the max-min program -/

/-- Initiator `i`'s planned surplus under plan `x`. -/
def lpSurplusI (x : I × J → C → ℝ) (i : I) : ℝ :=
  ∑ j, ∑ c, (M.valI (i, j) c - M.costI i) * x (i, j) c

/-- Responder `j`'s planned surplus under plan `x`. -/
def lpSurplusJ (x : I × J → C → ℝ) (j : J) : ℝ :=
  ∑ i, ∑ c, (M.valJ (i, j) c - M.costJ j) * x (i, j) c

/-- `x` is an optimal plan of the max-min program with value `θ`: it is feasible, gives
every user at least `θ`, and no feasible plan gives every user more than `θ`. -/
def IsMaxMinOptimal (x : I × J → C → ℝ) (θ : ℝ) : Prop :=
  M.LPFeasible x ∧ (∀ i, θ ≤ M.lpSurplusI x i) ∧ (∀ j, θ ≤ M.lpSurplusJ x j) ∧
    ∀ x' θ', M.LPFeasible x' → (∀ i, θ' ≤ M.lpSurplusI x' i) →
      (∀ j, θ' ≤ M.lpSurplusJ x' j) → θ' ≤ θ

/-! ### The benchmark: full-information policies -/

/-- A full-information policy: knowing every pair's combination `ω`, it picks a match set
with law `P ω`, supported on capped sets of acceptable pairs. -/
def IsFIPolicy (P : (I × J → C) → Finset (I × J) → ℝ) : Prop :=
  ∀ ω, (∀ S, 0 ≤ P ω S) ∧ ∑ S, P ω S = 1 ∧
    ∀ S, P ω S ≠ 0 → M.CapOK S ∧ ∀ e ∈ S, M.Acc e (ω e)

/-- Initiator `i`'s expected utility under policy `P`. -/
noncomputable def polUtilI (P : (I × J → C) → Finset (I × J) → ℝ) (i : I) : ℝ :=
  prodExp M.π fun ω => ∑ S, P ω S *
    ∑ e ∈ S.filter (fun e => e.1 = i), (M.valI e (ω e) - M.costI i)

/-- Responder `j`'s expected utility under policy `P`. -/
noncomputable def polUtilJ (P : (I × J → C) → Finset (I × J) → ℝ) (j : J) : ℝ :=
  prodExp M.π fun ω => ∑ S, P ω S *
    ∑ e ∈ S.filter (fun e => e.2 = j), (M.valJ e (ω e) - M.costJ j)

omit [Fintype I] [Fintype C] [DecidableEq C] in
/-- Summing over one initiator's pairs in a set. -/
theorem sum_filter_fst (S : Finset (I × J)) (i : I) (f : I × J → ℝ) :
    ∑ e ∈ S.filter (fun e => e.1 = i), f e = ∑ j, if (i, j) ∈ S then f (i, j) else 0 := by
  rw [← sum_filter]
  refine sum_nbij' (fun e => e.2) (fun j => (i, j)) ?_ ?_ ?_ ?_ ?_
  · intro e he
    obtain ⟨heS, hei⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_univ _, by rw [← hei]; exact heS⟩
  · intro j hj
    exact mem_filter.mpr ⟨(mem_filter.mp hj).2, rfl⟩
  · intro e he
    obtain ⟨_, hei⟩ := mem_filter.mp he
    ext <;> simp [hei]
  · intro j _
    rfl
  · intro e he
    obtain ⟨_, hei⟩ := mem_filter.mp he
    rw [← hei]

omit [Fintype J] [Fintype C] [DecidableEq C] in
/-- Summing over one responder's pairs in a set. -/
theorem sum_filter_snd (S : Finset (I × J)) (j : J) (f : I × J → ℝ) :
    ∑ e ∈ S.filter (fun e => e.2 = j), f e = ∑ i, if (i, j) ∈ S then f (i, j) else 0 := by
  rw [← sum_filter]
  refine sum_nbij' (fun e => e.1) (fun i => (i, j)) ?_ ?_ ?_ ?_ ?_
  · intro e he
    obtain ⟨heS, hej⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_univ _, by rw [← hej]; exact heS⟩
  · intro i hi
    exact mem_filter.mpr ⟨(mem_filter.mp hi).2, rfl⟩
  · intro e he
    obtain ⟨_, hej⟩ := mem_filter.mp he
    ext <;> simp [hej]
  · intro i _
    rfl
  · intro e he
    obtain ⟨_, hej⟩ := mem_filter.mp he
    rw [← hej]

/-- **The max-min LP bounds the benchmark, user by user.** Setting `x e c` to the
probability that the policy matches `e` in combination `c` gives a feasible plan with
the policy's expected surplus for every user. -/
theorem exists_plan_of_policy (hπ : IsDist M.π) {P : (I × J → C) → Finset (I × J) → ℝ}
    (hP : M.IsFIPolicy P) :
    ∃ x, M.LPFeasible x ∧ (∀ i, M.lpSurplusI x i = M.polUtilI P i) ∧
      ∀ j, M.lpSurplusJ x j = M.polUtilJ P j := by
  -- `q ω e`: the probability that the policy matches `e` when the combinations are `ω`.
  set q : (I × J → C) → I × J → ℝ := fun ω e => ∑ S, P ω S * if e ∈ S then 1 else 0 with hq
  have hq0 : ∀ ω e, 0 ≤ q ω e := fun ω e =>
    sum_nonneg fun S _ => mul_nonneg ((hP ω).1 S) (by split_ifs <;> norm_num)
  have hq1 : ∀ ω e, q ω e ≤ 1 := fun ω e => by
    calc q ω e ≤ ∑ S, P ω S := sum_le_sum fun S _ => by split_ifs <;> simp [(hP ω).1 S]
      _ = 1 := (hP ω).2.1
  have hqacc : ∀ ω e, ¬ M.Acc e (ω e) → q ω e = 0 := fun ω e he => sum_eq_zero fun S _ => by
    by_cases heS : e ∈ S
    · have hS : P ω S = 0 := by
        by_contra h
        exact he (((hP ω).2.2 S h).2 e heS)
      rw [hS, zero_mul]
    · rw [ite_eq_right heS, mul_zero]
  have hrow : ∀ ω i, ∑ j, q ω (i, j) ≤ M.capI i := fun ω i => by
    calc ∑ j, q ω (i, j) = ∑ S, P ω S * ((S.filter fun e => e.1 = i).card : ℝ) := by
          simp only [hq, card_filter_fst, mul_sum]
          exact sum_comm
      _ ≤ ∑ S, P ω S * M.capI i := sum_le_sum fun S _ => by
          by_cases hS : P ω S = 0
          · rw [hS, zero_mul, zero_mul]
          · exact mul_le_mul_of_nonneg_left (by exact_mod_cast ((hP ω).2.2 S hS).1.1 i)
              ((hP ω).1 S)
      _ = M.capI i := by rw [← sum_mul, (hP ω).2.1, one_mul]
  have hcol : ∀ ω j, ∑ i, q ω (i, j) ≤ M.capJ j := fun ω j => by
    calc ∑ i, q ω (i, j) = ∑ S, P ω S * ((S.filter fun e => e.2 = j).card : ℝ) := by
          simp only [hq, card_filter_snd, mul_sum]
          exact sum_comm
      _ ≤ ∑ S, P ω S * M.capJ j := sum_le_sum fun S _ => by
          by_cases hS : P ω S = 0
          · rw [hS, zero_mul, zero_mul]
          · exact mul_le_mul_of_nonneg_left (by exact_mod_cast ((hP ω).2.2 S hS).1.2 j)
              ((hP ω).1 S)
      _ = M.capJ j := by rw [← sum_mul, (hP ω).2.1, one_mul]
  -- The plan: `x e c = Pr[e is matched and has combination c]`.
  set x : I × J → C → ℝ := fun e c => prodExp M.π fun ω => if ω e = c then q ω e else 0
    with hx
  have hsum : ∀ e, ∑ c, x e c = prodExp M.π (fun ω => q ω e) := fun e => by
    simp only [hx]
    rw [← prodExp_sum]
    exact prodExp_congr _ fun ω => by simp
  have hval : ∀ e (v : C → ℝ), ∑ c, v c * x e c = prodExp M.π (fun ω => v (ω e) * q ω e) :=
    fun e v => by
      simp only [hx]
      simp_rw [← prodExp_const_mul]
      rw [← prodExp_sum]
      exact prodExp_congr _ fun ω => by simp [mul_ite]
  refine ⟨x, ⟨fun e c => ⟨?_, ?_⟩, fun e c hc => ?_, fun i => ?_, fun j => ?_⟩,
    fun i => ?_, fun j => ?_⟩
  · exact prodExp_nonneg hπ.1 fun ω => by split_ifs; exacts [hq0 ω e, le_rfl]
  · calc x e c ≤ prodExp M.π (fun ω => (fun o => if o = c then (1 : ℝ) else 0) (ω e)) :=
          prodExp_mono hπ.1 fun ω => by
            simp only
            split_ifs
            exacts [hq1 ω e, le_rfl]
      _ = M.π e c := by
          rw [prodExp_coord hπ.2 e (fun o => if o = c then (1 : ℝ) else 0)]
          simp
  · calc x e c = prodExp M.π (fun _ => 0) :=
          prodExp_congr _ fun ω => by
            split_ifs with h
            · exact hqacc ω e fun hacc => hc (h ▸ hacc)
            · rfl
      _ = 0 := prodExp_const hπ.2 0
  · calc ∑ j, ∑ c, x (i, j) c = prodExp M.π (fun ω => ∑ j, q ω (i, j)) := by
          simp only [hsum]
          exact (prodExp_sum _ _ _).symm
      _ ≤ prodExp M.π (fun _ => (M.capI i : ℝ)) := prodExp_mono hπ.1 fun ω => hrow ω i
      _ = M.capI i := prodExp_const hπ.2 _
  · calc ∑ i, ∑ c, x (i, j) c = prodExp M.π (fun ω => ∑ i, q ω (i, j)) := by
          simp only [hsum]
          exact (prodExp_sum _ _ _).symm
      _ ≤ prodExp M.π (fun _ => (M.capJ j : ℝ)) := prodExp_mono hπ.1 fun ω => hcol ω j
      _ = M.capJ j := prodExp_const hπ.2 _
  · unfold lpSurplusI polUtilI
    simp only [hval (_, _) fun c => M.valI _ c - M.costI i]
    rw [← prodExp_sum]
    refine prodExp_congr _ fun ω => ?_
    simp only [hq, mul_sum, sum_filter_fst]
    rw [sum_comm]
    refine sum_congr rfl fun S _ => sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  · unfold lpSurplusJ polUtilJ
    simp only [hval (_, _) fun c => M.valJ _ c - M.costJ j]
    rw [← prodExp_sum]
    refine prodExp_congr _ fun ω => ?_
    simp only [hq, mul_sum, sum_filter_snd]
    rw [sum_comm]
    refine sum_congr rfl fun S _ => sum_congr rfl fun i _ => ?_
    split_ifs <;> ring

/-- **`OPT_min ≤ θ*`.** No full-information policy guarantees every user more than the
max-min LP value. -/
theorem floor_le_maxMin (hπ : IsDist M.π) {x : I × J → C → ℝ} {θ : ℝ}
    (hopt : M.IsMaxMinOptimal x θ) {P : (I × J → C) → Finset (I × J) → ℝ}
    (hP : M.IsFIPolicy P) {θP : ℝ} (hI : ∀ i, θP ≤ M.polUtilI P i)
    (hJ : ∀ j, θP ≤ M.polUtilJ P j) : θP ≤ θ := by
  obtain ⟨x', hx', hI', hJ'⟩ := M.exists_plan_of_policy hπ hP
  exact hopt.2.2.2 x' θP hx' (fun i => (hI' i).symm ▸ hI i) fun j => (hJ' j).symm ▸ hJ j

/-! ### The mechanism -/

/-- Pair `e` is a candidate: found, kept, and acceptable in its combination. -/
def IsCand (e : I × J) (o : Option C) : Prop :=
  ∃ c, o = some c ∧ M.Acc e c

noncomputable instance (e : I × J) : DecidablePred (M.IsCand e) := fun _ => Classical.dec _

/-- Responder `j`'s candidates. -/
noncomputable def candCol (η : I × J → Option C) (j : J) : Finset I :=
  univ.filter fun i => M.IsCand (i, j) (η (i, j))

/-- What a candidate pair is worth to its initiator. -/
noncomputable def gainI (e : I × J) (o : Option C) : ℝ :=
  o.elim 0 fun c => if M.Acc e c then M.valI e c - M.costI e.1 else 0

/-- What a candidate pair is worth to its responder. -/
noncomputable def gainJ (e : I × J) (o : Option C) : ℝ :=
  o.elim 0 fun c => if M.Acc e c then M.valJ e c - M.costJ e.2 else 0

/-- **Initiator `i`'s expected utility under max-min SDH** with plan `x`, query
probabilities `τ`, stage-1 rules `ψ1` and stage-2 rules `ψ2`:
1. screen and thin (`thinLaw`), giving each pair's candidate `candOf`;
2. each responder `j` keeps `T j`, drawn by `ψ1 j` from its candidates;
3. each initiator `i'` keeps `T' i'`, drawn by `ψ2 i'` from `{j | i' ∈ T j}`;
4. `i` matches the `j ∈ T' i` and gains their surpluses. -/
noncomputable def mmUtilI (x : I × J → C → ℝ) (τ : I × J → ℝ)
    (ψ1 : J → Finset I → Finset I → ℝ) (ψ2 : I → Finset J → Finset J → ℝ) (i : I) : ℝ :=
  prodExp (M.thinLaw x τ) fun ω =>
    prodExp (fun j T => ψ1 j (M.candCol (fun e => M.candOf e (ω e)) j) T) fun T =>
      prodExp (fun i' T' => ψ2 i' (univ.filter fun j => i' ∈ T j) T') fun T' =>
        ∑ j ∈ T' i, M.gainI (i, j) (M.candOf (i, j) (ω (i, j)))

/-- **Responder `j`'s expected utility under max-min SDH**; see `mmUtilI`. -/
noncomputable def mmUtilJ (x : I × J → C → ℝ) (τ : I × J → ℝ)
    (ψ1 : J → Finset I → Finset I → ℝ) (ψ2 : I → Finset J → Finset J → ℝ) (j : J) : ℝ :=
  prodExp (M.thinLaw x τ) fun ω =>
    prodExp (fun j' T => ψ1 j' (M.candCol (fun e => M.candOf e (ω e)) j') T) fun T =>
      prodExp (fun i' T' => ψ2 i' (univ.filter fun j' => i' ∈ T j') T') fun T' =>
        ∑ i ∈ univ.filter (fun i => j ∈ T' i), M.gainJ (i, j) (M.candOf (i, j) (ω (i, j)))

/-- The probability that stage 1 passes pair `(i, j)` on to `i`: `j`'s candidates arrive
independently, `i'` with probability `∑_c x (i', j) c`, and `ψ1 j` keeps `i`. -/
noncomputable def stage1Keep (x : I × J → C → ℝ) (ψ1 : J → Finset I → Finset I → ℝ)
    (i : I) (j : J) : ℝ :=
  indepExp univ (fun i' => ∑ c, x (i', j) c) fun A => ruleKeep (ψ1 j) A i

/-! ### One pair at a time

Screening and thinning only matter through the candidates (`candidates_eq_thin`), so the
utilities are averages over `candLaw x` of the utilities given the candidates. Those are
sums over pairs of `pairVal`, and a pair's value factors exactly as
`E[gain] · κ₁ · κ₂`, where `κ₁` and `κ₂` are the chances that the stages keep the pair
given that it reaches them (`expect_pairVal`). Balance bounds `κ₁` and `κ₂` below. -/

/-- Initiator `i`'s utility given the candidates `η`, averaged over both stages. -/
noncomputable def candUtilI (ψ1 : J → Finset I → Finset I → ℝ)
    (ψ2 : I → Finset J → Finset J → ℝ) (i : I) (η : I × J → Option C) : ℝ :=
  prodExp (fun j T => ψ1 j (M.candCol η j) T) fun T =>
    prodExp (fun i' T' => ψ2 i' (univ.filter fun j => i' ∈ T j) T') fun T' =>
      ∑ j ∈ T' i, M.gainI (i, j) (η (i, j))

/-- Responder `j`'s utility given the candidates `η`, averaged over both stages. -/
noncomputable def candUtilJ (ψ1 : J → Finset I → Finset I → ℝ)
    (ψ2 : I → Finset J → Finset J → ℝ) (j : J) (η : I × J → Option C) : ℝ :=
  prodExp (fun j' T => ψ1 j' (M.candCol η j') T) fun T =>
    prodExp (fun i' T' => ψ2 i' (univ.filter fun j' => i' ∈ T j') T') fun T' =>
      ∑ i ∈ univ.filter (fun i => j ∈ T' i), M.gainJ (i, j) (η (i, j))

/-- Pair `(i, j)`'s value `g` given the candidates `η`, counted when both stages keep
the pair. -/
noncomputable def pairVal (ψ1 : J → Finset I → Finset I → ℝ)
    (ψ2 : I → Finset J → Finset J → ℝ) (i : I) (j : J) (g : Option C → ℝ)
    (η : I × J → Option C) : ℝ :=
  prodExp (fun j' T => ψ1 j' (M.candCol η j') T) fun T =>
    prodExp (fun i' T' => ψ2 i' (univ.filter fun j' => i' ∈ T j') T') fun T' =>
      if j ∈ T' i then g (η (i, j)) else 0

theorem mmUtilI_eq (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasible x)
    {τ : I × J → ℝ} (hτ : ∀ e, 0 ≤ τ e ∧ τ e ≤ 1) (hτx : ∀ e c, x e c ≤ τ e * M.π e c)
    (ψ1 : J → Finset I → Finset I → ℝ) (ψ2 : I → Finset J → Finset J → ℝ) (i : I) :
    M.mmUtilI x τ ψ1 ψ2 i = prodExp (candLaw x) (M.candUtilI ψ1 ψ2 i) := by
  unfold mmUtilI
  exact M.candidates_eq_thin hπ hx hτ hτx (M.candUtilI ψ1 ψ2 i)

theorem mmUtilJ_eq (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasible x)
    {τ : I × J → ℝ} (hτ : ∀ e, 0 ≤ τ e ∧ τ e ≤ 1) (hτx : ∀ e c, x e c ≤ τ e * M.π e c)
    (ψ1 : J → Finset I → Finset I → ℝ) (ψ2 : I → Finset J → Finset J → ℝ) (j : J) :
    M.mmUtilJ x τ ψ1 ψ2 j = prodExp (candLaw x) (M.candUtilJ ψ1 ψ2 j) := by
  unfold mmUtilJ
  exact M.candidates_eq_thin hπ hx hτ hτx (M.candUtilJ ψ1 ψ2 j)

omit [Fintype C] [DecidableEq C] in
theorem candUtilI_eq (ψ1 : J → Finset I → Finset I → ℝ)
    (ψ2 : I → Finset J → Finset J → ℝ) (i : I) (η : I × J → Option C) :
    M.candUtilI ψ1 ψ2 i η = ∑ j, M.pairVal ψ1 ψ2 i j (M.gainI (i, j)) η := by
  unfold candUtilI pairVal
  have h2 : ∀ T : J → Finset I,
      (prodExp (fun i' T' => ψ2 i' (univ.filter fun j => i' ∈ T j) T') fun T' =>
        ∑ j ∈ T' i, M.gainI (i, j) (η (i, j))) =
      ∑ j, prodExp (fun i' T' => ψ2 i' (univ.filter fun j => i' ∈ T j) T') fun T' =>
        if j ∈ T' i then M.gainI (i, j) (η (i, j)) else 0 := by
    intro T
    calc _ = prodExp (fun i' T' => ψ2 i' (univ.filter fun j => i' ∈ T j) T') (fun T' =>
          ∑ j, if j ∈ T' i then M.gainI (i, j) (η (i, j)) else 0) :=
          prodExp_congr _ fun T' => by rw [sum_ite_mem, univ_inter]
      _ = _ := prodExp_sum _ _ _
  rw [prodExp_congr _ h2, prodExp_sum]

omit [Fintype C] [DecidableEq C] in
theorem candUtilJ_eq (ψ1 : J → Finset I → Finset I → ℝ)
    (ψ2 : I → Finset J → Finset J → ℝ) (j : J) (η : I × J → Option C) :
    M.candUtilJ ψ1 ψ2 j η = ∑ i, M.pairVal ψ1 ψ2 i j (M.gainJ (i, j)) η := by
  unfold candUtilJ pairVal
  have h2 : ∀ T : J → Finset I,
      (prodExp (fun i' T' => ψ2 i' (univ.filter fun j' => i' ∈ T j') T') fun T' =>
        ∑ i ∈ univ.filter (fun i => j ∈ T' i), M.gainJ (i, j) (η (i, j))) =
      ∑ i, prodExp (fun i' T' => ψ2 i' (univ.filter fun j' => i' ∈ T j') T') fun T' =>
        if j ∈ T' i then M.gainJ (i, j) (η (i, j)) else 0 := by
    intro T
    calc _ = prodExp (fun i' T' => ψ2 i' (univ.filter fun j' => i' ∈ T j') T') (fun T' =>
          ∑ i, if j ∈ T' i then M.gainJ (i, j) (η (i, j)) else 0) :=
          prodExp_congr _ fun T' => sum_filter _ _
      _ = _ := prodExp_sum _ _ _
  rw [prodExp_congr _ h2, prodExp_sum]

omit [Fintype C] [DecidableEq C] in
/-- Given the candidates, a pair counts with the chance that stage 1 keeps it, times the
chance that stage 2 keeps it given that stage 1 did. -/
theorem pairVal_eq {ψ1 : J → Finset I → Finset I → ℝ} {ψ2 : I → Finset J → Finset J → ℝ}
    (h1r : ∀ j, IsRule (M.capJ j) (ψ1 j)) (h2r : ∀ i, IsRule (M.capI i) (ψ2 i))
    (i₀ : I) (j₀ : J) (g : Option C → ℝ) (η : I × J → Option C) :
    M.pairVal ψ1 ψ2 i₀ j₀ g η = g (η (i₀, j₀)) * (ruleKeep (ψ1 j₀) (M.candCol η j₀) i₀ *
      indepExp (univ.erase j₀) (fun j => ruleKeep (ψ1 j) (M.candCol η j) i₀)
        (fun B => ruleKeep (ψ2 i₀) (insert j₀ B) j₀)) := by
  unfold pairVal
  have hin : ∀ T : J → Finset I,
      (prodExp (fun i' T' => ψ2 i' (univ.filter fun j' => i' ∈ T j') T') fun T' =>
        if j₀ ∈ T' i₀ then g (η (i₀, j₀)) else 0) =
      g (η (i₀, j₀)) * ruleKeep (ψ2 i₀) (univ.filter fun j' => i₀ ∈ T j') j₀ := by
    intro T
    calc _ = prodExp (fun i' T' => ψ2 i' (univ.filter fun j' => i' ∈ T j') T') (fun T' =>
          g (η (i₀, j₀)) * (fun B : Finset J => if j₀ ∈ B then (1 : ℝ) else 0) (T' i₀)) :=
          prodExp_congr _ fun T' => by simp only [mul_ite, mul_one, mul_zero]
      _ = _ := by
          rw [prodExp_const_mul, prodExp_coord (fun i' => ((h2r i') _).2.1) i₀
            (fun B : Finset J => if j₀ ∈ B then (1 : ℝ) else 0)]
          rfl
  rw [prodExp_congr _ hin, prodExp_const_mul]
  congr 1
  rw [prodExp_filter (fun j => ((h1r j) _).2.1) (fun j T => i₀ ∈ T)
    (fun B => ruleKeep (ψ2 i₀) B j₀),
    indepExp_univ_split j₀ (fun B hB => ruleKeep_eq_zero (h2r i₀) hB)]
  have hq : ∀ j, ∑ T ∈ univ.filter (fun T => i₀ ∈ T), ψ1 j (M.candCol η j) T =
      ruleKeep (ψ1 j) (M.candCol η j) i₀ := fun j => by
    rw [sum_filter]
    simp only [ruleKeep, mul_ite, mul_one, mul_zero]
  simp only [hq]

omit [DecidableEq I] [DecidableEq J] [DecidableEq C] in
/-- A pair is a candidate with the probability the plan uses it. -/
theorem sum_candLaw_isCand {x : I × J → C → ℝ} (hx : M.LPFeasible x) (e : I × J) :
    ∑ o ∈ univ.filter (M.IsCand e), candLaw x e o = ∑ c, x e c := by
  rw [sum_filter, Fintype.sum_option]
  have hnone : ¬ M.IsCand e none := fun ⟨c, hc, _⟩ => Option.some_ne_none c hc.symm
  rw [ite_eq_right hnone, zero_add]
  refine sum_congr rfl fun c _ => ?_
  by_cases hc : M.Acc e c
  · rw [ite_eq_left ⟨c, rfl, hc⟩]
    rfl
  · have hnc : ¬ M.IsCand e (some c) := fun ⟨c', hc', hacc⟩ => hc (Option.some_injective _ hc' ▸ hacc)
    rw [ite_eq_right hnc, hx.2.1 e c hc]

omit [DecidableEq I] [DecidableEq J] [DecidableEq C] in
/-- A pair's candidate probability is a probability. -/
theorem sum_x_mem (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasible x)
    (e : I × J) : 0 ≤ ∑ c, x e c ∧ ∑ c, x e c ≤ 1 :=
  ⟨sum_nonneg fun c _ => (hx.1 e c).1, M.sum_x_le_one hπ hx e⟩

omit [DecidableEq J] [DecidableEq C] in
/-- Stage 1 passes a pair on at most as often as it is a candidate. -/
theorem stage1Keep_mem (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasible x)
    {ψ1 : J → Finset I → Finset I → ℝ} (h1r : ∀ j, IsRule (M.capJ j) (ψ1 j)) (i : I)
    (j : J) : 0 ≤ stage1Keep x ψ1 i j ∧ stage1Keep x ψ1 i j ≤ ∑ c, x (i, j) c := by
  have hp : ∀ i' ∈ (univ : Finset I), 0 ≤ ∑ c, x (i', j) c ∧ ∑ c, x (i', j) c ≤ 1 :=
    fun i' _ => M.sum_x_mem hπ hx (i', j)
  refine ⟨(indepExp_mem_Icc hp fun A => ruleKeep_mem (h1r j) A i).1, ?_⟩
  calc stage1Keep x ψ1 i j
      ≤ indepExp univ (fun i' => ∑ c, x (i', j) c) (fun A => if i ∈ A then 1 else 0) :=
        indepExp_mono hp fun A _ => by
          by_cases hiA : i ∈ A
          · rw [ite_eq_left hiA]; exact (ruleKeep_mem (h1r j) A i).2
          · rw [ite_eq_right hiA, ruleKeep_eq_zero (h1r j) hiA]
    _ = ∑ c, x (i, j) c := indepExp_mem (mem_univ i) _

omit [DecidableEq C] in
/-- **A pair's expected value factors** as its expected gain times `κ₁`, the chance stage 1
keeps it given that it is a candidate, times `κ₂`, the chance stage 2 keeps it given
that stage 1 passed it on. -/
theorem expect_pairVal (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasible x)
    {ψ1 : J → Finset I → Finset I → ℝ} {ψ2 : I → Finset J → Finset J → ℝ}
    (h1r : ∀ j, IsRule (M.capJ j) (ψ1 j)) (h2r : ∀ i, IsRule (M.capI i) (ψ2 i))
    (i₀ : I) (j₀ : J) {g : Option C → ℝ} (hgc : ∀ o, g o ≠ 0 → M.IsCand (i₀, j₀) o) :
    prodExp (candLaw x) (M.pairVal ψ1 ψ2 i₀ j₀ g) =
      (∑ c, x (i₀, j₀) c * g (some c)) *
        indepExp (univ.erase i₀) (fun i => ∑ c, x (i, j₀) c)
          (fun A => ruleKeep (ψ1 j₀) (insert i₀ A) i₀) *
        indepExp (univ.erase j₀) (stage1Keep x ψ1 i₀)
          (fun B => ruleKeep (ψ2 i₀) (insert j₀ B) j₀) := by
  have hν := M.isDist_candLaw hπ hx
  have hcol : ∀ j, ∑ b : I → Option C, ∏ i, candLaw x (i, j) (b i) = 1 :=
    (isDist_curry hν).2
  -- The candidates of one column, as a set.
  set R : Finset I → ℝ := fun A => ruleKeep (ψ1 j₀) (insert i₀ A) i₀ with hR
  set h' : Finset J → ℝ := fun B => ruleKeep (ψ2 i₀) (insert j₀ B) j₀ with hh'
  set F : (I → Option C) → ℝ := fun b =>
    g (b i₀) * ruleKeep (ψ1 j₀) (univ.filter fun i => M.IsCand (i, j₀) (b i)) i₀ with hF
  set P : J → (I → Option C) → ℝ := fun j b =>
    ruleKeep (ψ1 j) (univ.filter fun i => M.IsCand (i, j) (b i)) i₀ with hP
  -- Regroup the pairs into independent columns.
  rw [prodExp_congr _ (M.pairVal_eq h1r h2r i₀ j₀ g), prodExp_curry]
  have hcurry : ∀ β : J → I → Option C,
      g (β j₀ i₀) * (ruleKeep (ψ1 j₀) (M.candCol (fun e => β e.2 e.1) j₀) i₀ *
        indepExp (univ.erase j₀) (fun j => ruleKeep (ψ1 j) (M.candCol (fun e => β e.2 e.1) j) i₀)
          h') = F (β j₀) * indepExp (univ.erase j₀) (fun j => P j (β j)) h' :=
    fun β => (mul_assoc _ _ _).symm
  rw [prodExp_congr _ hcurry, prodExp_mul_indepExp hcol j₀ F P h']
  -- Stage 1 for the other columns: each passes `i₀` on with probability `stage1Keep`.
  have hother : ∀ j, ∑ b : I → Option C, (∏ i, candLaw x (i, j) (b i)) * P j b =
      stage1Keep x ψ1 i₀ j := by
    intro j
    change prodExp (fun i o => candLaw x (i, j) o) (fun b =>
      ruleKeep (ψ1 j) (univ.filter fun i => M.IsCand (i, j) (b i)) i₀) = _
    rw [prodExp_filter (fun i => hν.2 (i, j)) (fun i o => M.IsCand (i, j) o)
      (fun A => ruleKeep (ψ1 j) A i₀)]
    simp only [M.sum_candLaw_isCand hx]
    rfl
  -- Stage 1 for column `j₀`: the pair against the other candidates of its column.
  have hown : ∑ b : I → Option C, (∏ i, candLaw x (i, j₀) (b i)) * F b =
      (∑ c, x (i₀, j₀) c * g (some c)) *
        indepExp (univ.erase i₀) (fun i => ∑ c, x (i, j₀) c) R := by
    change prodExp (fun i o => candLaw x (i, j₀) o) F = _
    have hpt : ∀ b : I → Option C, F b = g (b i₀) * indepExp (univ.erase i₀)
        (fun i => (fun i o => if M.IsCand (i, j₀) o then (1 : ℝ) else 0) i (b i)) R := by
      intro b
      by_cases hg : g (b i₀) = 0
      · simp only [hF, hg, zero_mul]
      have hc := hgc _ hg
      set A := univ.filter fun i => M.IsCand (i, j₀) (b i) with hA
      have hfun : (fun i => (fun i o => if M.IsCand (i, j₀) o then (1 : ℝ) else 0) i (b i)) =
          fun i => if i ∈ A then 1 else 0 := by
        funext i
        simp [hA]
      have hins : insert i₀ ((univ.erase i₀).filter (· ∈ A)) = A := by
        ext k
        by_cases hk : k = i₀
        · subst hk
          simp [hA, hc]
        · simp [hk]
      rw [hfun, indepExp_indicator, hR]
      simp only [hF, ← hA, hins]
    rw [prodExp_congr _ hpt, prodExp_mul_indepExp (μ := fun i o => candLaw x (i, j₀) o)
      (fun i => hν.2 (i, j₀)) i₀ g (fun i o => if M.IsCand (i, j₀) o then (1 : ℝ) else 0) R]
    congr 1
    · rw [Fintype.sum_option]
      have hnone : g none = 0 := by
        by_contra h
        obtain ⟨c, hc, _⟩ := hgc none h
        exact Option.some_ne_none c hc.symm
      simp only [hnone, mul_zero, zero_add]
      rfl
    · congr 1
      funext i
      rw [← M.sum_candLaw_isCand hx (i, j₀), sum_filter]
      simp only [mul_ite, mul_one, mul_zero]
  rw [hown]
  simp only [hother]

omit [DecidableEq C] in
/-- **The pair bound.** If every stage-1 rule is `γ1`-balanced and every stage-2 rule is
`γ2`-balanced, a pair counts at least `γ1 γ2` times its planned value. -/
theorem pairVal_ge (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasible x)
    {ψ1 : J → Finset I → Finset I → ℝ} {ψ2 : I → Finset J → Finset J → ℝ} {γ1 γ2 : ℝ}
    (hγ1 : 0 ≤ γ1) (hγ2 : 0 ≤ γ2)
    (h1 : ∀ j, IsRule (M.capJ j) (ψ1 j) ∧ IsBalanced (fun i => ∑ c, x (i, j) c) γ1 (ψ1 j))
    (h2 : ∀ i, IsRule (M.capI i) (ψ2 i) ∧ IsBalanced (stage1Keep x ψ1 i) γ2 (ψ2 i))
    (i₀ : I) (j₀ : J) {g : Option C → ℝ} (hg0 : ∀ o, 0 ≤ g o)
    (hgc : ∀ o, g o ≠ 0 → M.IsCand (i₀, j₀) o) :
    γ1 * γ2 * ∑ c, x (i₀, j₀) c * g (some c) ≤
      prodExp (candLaw x) (M.pairVal ψ1 ψ2 i₀ j₀ g) := by
  have h1r := fun j => (h1 j).1
  have h2r := fun i => (h2 i).1
  rw [M.expect_pairVal hπ hx h1r h2r i₀ j₀ hgc]
  set y : I → ℝ := fun i => ∑ c, x (i, j₀) c with hy
  set z := stage1Keep x ψ1 i₀ with hz
  set Eg := ∑ c, x (i₀, j₀) c * g (some c) with hEg
  set κ1 := indepExp (univ.erase i₀) y (fun A => ruleKeep (ψ1 j₀) (insert i₀ A) i₀) with hκ1
  set κ2 := indepExp (univ.erase j₀) z (fun B => ruleKeep (ψ2 i₀) (insert j₀ B) j₀) with hκ2
  have hyp : ∀ i ∈ (univ : Finset I), 0 ≤ y i ∧ y i ≤ 1 := fun i _ => M.sum_x_mem hπ hx (i, j₀)
  have hzp : ∀ j ∈ (univ : Finset J), 0 ≤ z j ∧ z j ≤ 1 := fun j _ =>
    ⟨(M.stage1Keep_mem hπ hx h1r i₀ j).1,
      (M.stage1Keep_mem hπ hx h1r i₀ j).2.trans (M.sum_x_mem hπ hx (i₀, j)).2⟩
  have hκ1n : 0 ≤ κ1 := (indepExp_mem_Icc (fun i hi => hyp i (mem_univ i))
    fun A => ruleKeep_mem (h1r j₀) _ _).1
  have hκ2n : 0 ≤ κ2 := (indepExp_mem_Icc (fun j hj => hzp j (mem_univ j))
    fun B => ruleKeep_mem (h2r i₀) _ _).1
  have hEgn : 0 ≤ Eg := sum_nonneg fun c _ => mul_nonneg (hx.1 _ c).1 (hg0 _)
  -- The balance conditions, split at the pair.
  have hsplit1 : indepExp univ y (fun A => ruleKeep (ψ1 j₀) A i₀) = y i₀ * κ1 :=
    indepExp_univ_split i₀ fun A hA => ruleKeep_eq_zero (h1r j₀) hA
  have hb1 : γ1 * y i₀ ≤ y i₀ * κ1 := hsplit1 ▸ (h1 j₀).2 i₀
  have hzj : z j₀ = y i₀ * κ1 := hsplit1
  have hb2 : γ2 * z j₀ ≤ z j₀ * κ2 :=
    (indepExp_univ_split (p := z) j₀ fun B hB => ruleKeep_eq_zero (h2r i₀) hB) ▸ (h2 i₀).2 j₀
  rcases (hyp i₀ (mem_univ _)).1.eq_or_lt with hy0 | hy0
  · -- The plan never uses the pair.
    have hx0 : ∀ c, x (i₀, j₀) c = 0 :=
      fun c => (sum_eq_zero_iff_of_nonneg fun c _ => (hx.1 _ c).1).mp hy0.symm c (mem_univ c)
    have : Eg = 0 := sum_eq_zero fun c _ => by rw [hx0 c, zero_mul]
    rw [this]
    simp
  have hk1 : γ1 ≤ κ1 := le_of_mul_le_mul_left (by linarith) hy0
  rcases (hzp j₀ (mem_univ _)).1.eq_or_lt with hz0 | hz0
  · -- Stage 1 never passes the pair on, so `κ₁ = 0` and `γ1 = 0`.
    have hκ10 : κ1 = 0 := by
      rcases mul_eq_zero.mp (hzj ▸ hz0.symm) with h | h
      · linarith
      · exact h
    have : γ1 = 0 := le_antisymm (hκ10 ▸ hk1) hγ1
    rw [this, hκ10]
    simp
  have hk2 : γ2 ≤ κ2 := le_of_mul_le_mul_left (by linarith) hz0
  calc γ1 * γ2 * Eg ≤ κ1 * κ2 * Eg :=
        mul_le_mul_of_nonneg_right (mul_le_mul hk1 hk2 hγ2 hκ1n) hEgn
    _ = Eg * κ1 * κ2 := by ring

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype C] [DecidableEq C] in
theorem gainI_nonneg (e : I × J) (o : Option C) : 0 ≤ M.gainI e o := by
  cases o with
  | none => exact le_rfl
  | some c =>
    simp only [gainI, Option.elim]
    split_ifs with h
    · linarith [h.1]
    · exact le_rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype C] [DecidableEq C] in
theorem gainJ_nonneg (e : I × J) (o : Option C) : 0 ≤ M.gainJ e o := by
  cases o with
  | none => exact le_rfl
  | some c =>
    simp only [gainJ, Option.elim]
    split_ifs with h
    · linarith [h.2]
    · exact le_rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype C] [DecidableEq C] in
theorem isCand_of_gainI_ne (e : I × J) (o : Option C) (h : M.gainI e o ≠ 0) :
    M.IsCand e o := by
  cases o with
  | none => exact absurd rfl h
  | some c =>
    by_cases hc : M.Acc e c
    · exact ⟨c, rfl, hc⟩
    · simp [gainI, hc] at h

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype C] [DecidableEq C] in
theorem isCand_of_gainJ_ne (e : I × J) (o : Option C) (h : M.gainJ e o ≠ 0) :
    M.IsCand e o := by
  cases o with
  | none => exact absurd rfl h
  | some c =>
    by_cases hc : M.Acc e c
    · exact ⟨c, rfl, hc⟩
    · simp [gainJ, hc] at h

/-! ### Composition: balanced stages give every user its share -/

/-- **Every initiator gets `γ1 γ2` of its planned surplus** when every stage-1 rule is
`γ1`-balanced for its candidates and every stage-2 rule is `γ2`-balanced for what
stage 1 passes on. -/
theorem mmUtilI_ge (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasible x)
    {τ : I × J → ℝ} (hτ : ∀ e, 0 ≤ τ e ∧ τ e ≤ 1) (hτx : ∀ e c, x e c ≤ τ e * M.π e c)
    {ψ1 : J → Finset I → Finset I → ℝ} {ψ2 : I → Finset J → Finset J → ℝ} {γ1 γ2 : ℝ}
    (hγ1 : 0 ≤ γ1) (hγ2 : 0 ≤ γ2)
    (h1 : ∀ j, IsRule (M.capJ j) (ψ1 j) ∧ IsBalanced (fun i => ∑ c, x (i, j) c) γ1 (ψ1 j))
    (h2 : ∀ i, IsRule (M.capI i) (ψ2 i) ∧ IsBalanced (stage1Keep x ψ1 i) γ2 (ψ2 i))
    (i : I) : γ1 * γ2 * M.lpSurplusI x i ≤ M.mmUtilI x τ ψ1 ψ2 i := by
  rw [M.mmUtilI_eq hπ hx hτ hτx, prodExp_congr _ (M.candUtilI_eq ψ1 ψ2 i), prodExp_sum]
  unfold lpSurplusI
  rw [mul_sum]
  refine sum_le_sum fun j _ => le_trans (le_of_eq ?_)
    (M.pairVal_ge hπ hx hγ1 hγ2 h1 h2 i j (M.gainI_nonneg _) (M.isCand_of_gainI_ne _))
  congr 1
  refine sum_congr rfl fun c _ => ?_
  by_cases hc : M.Acc (i, j) c
  · simp only [gainI, Option.elim, hc, ↓reduceIte]
    ring
  · simp only [gainI, Option.elim, hc, ↓reduceIte, hx.2.1 _ c hc, mul_zero]

/-- **Every responder gets `γ1 γ2` of its planned surplus**; see `mmUtilI_ge`. -/
theorem mmUtilJ_ge (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasible x)
    {τ : I × J → ℝ} (hτ : ∀ e, 0 ≤ τ e ∧ τ e ≤ 1) (hτx : ∀ e c, x e c ≤ τ e * M.π e c)
    {ψ1 : J → Finset I → Finset I → ℝ} {ψ2 : I → Finset J → Finset J → ℝ} {γ1 γ2 : ℝ}
    (hγ1 : 0 ≤ γ1) (hγ2 : 0 ≤ γ2)
    (h1 : ∀ j, IsRule (M.capJ j) (ψ1 j) ∧ IsBalanced (fun i => ∑ c, x (i, j) c) γ1 (ψ1 j))
    (h2 : ∀ i, IsRule (M.capI i) (ψ2 i) ∧ IsBalanced (stage1Keep x ψ1 i) γ2 (ψ2 i))
    (j : J) : γ1 * γ2 * M.lpSurplusJ x j ≤ M.mmUtilJ x τ ψ1 ψ2 j := by
  rw [M.mmUtilJ_eq hπ hx hτ hτx, prodExp_congr _ (M.candUtilJ_eq ψ1 ψ2 j), prodExp_sum]
  unfold lpSurplusJ
  rw [mul_sum]
  refine sum_le_sum fun i _ => le_trans (le_of_eq ?_)
    (M.pairVal_ge hπ hx hγ1 hγ2 h1 h2 i j (M.gainJ_nonneg _) (M.isCand_of_gainJ_ne _))
  congr 1
  refine sum_congr rfl fun c _ => ?_
  by_cases hc : M.Acc (i, j) c
  · simp only [gainJ, Option.elim, hc, ↓reduceIte]
    ring
  · simp only [gainJ, Option.elim, hc, ↓reduceIte, hx.2.1 _ c hc, mul_zero]

/-! ### Random order: a quarter for everyone -/

/-- **Random order gives every user a quarter of its planned surplus.** Both stages keep
a uniformly random capped subset (`uniformRule`). -/
theorem mmsdh_quarter (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasible x)
    {τ : I × J → ℝ} (hτ : ∀ e, 0 ≤ τ e ∧ τ e ≤ 1) (hτx : ∀ e c, x e c ≤ τ e * M.π e c) :
    (∀ i, M.lpSurplusI x i / 4 ≤ M.mmUtilI x τ (fun j => uniformRule (M.capJ j))
      (fun i => uniformRule (M.capI i)) i) ∧
    ∀ j, M.lpSurplusJ x j / 4 ≤ M.mmUtilJ x τ (fun j => uniformRule (M.capJ j))
      (fun i => uniformRule (M.capI i)) j := by
  have hy : ∀ j i, 0 ≤ ∑ c, x (i, j) c ∧ ∑ c, x (i, j) c ≤ 1 :=
    fun j i => M.sum_x_mem hπ hx (i, j)
  have h1 : ∀ j, IsRule (M.capJ j) (uniformRule (α := I) (M.capJ j)) ∧
      IsBalanced (fun i => ∑ c, x (i, j) c) (1 / 2) (uniformRule (M.capJ j)) :=
    fun j => ⟨isRule_uniformRule _, uniformRule_balanced (hy j) (hx.2.2.2 j)⟩
  have h2 : ∀ i, IsRule (M.capI i) (uniformRule (α := J) (M.capI i)) ∧
      IsBalanced (stage1Keep x (fun j => uniformRule (M.capJ j)) i) (1 / 2)
        (uniformRule (M.capI i)) := by
    intro i
    have hs := M.stage1Keep_mem hπ hx (fun j => (h1 j).1) i
    exact ⟨isRule_uniformRule _, uniformRule_balanced
      (fun j => ⟨(hs j).1, (hs j).2.trans (hy j i).2⟩)
      ((sum_le_sum fun j _ => (hs j).2).trans (hx.2.2.1 i))⟩
  refine ⟨fun i => ?_, fun j => ?_⟩
  · have := M.mmUtilI_ge hπ hx hτ hτx (by norm_num) (by norm_num) h1 h2 i
    linarith
  · have := M.mmUtilJ_ge hπ hx hτ hτx (by norm_num) (by norm_num) h1 h2 j
    linarith

/-- **MM-SDH with random order: the worst-off user gets `θ*/4 ≥ OPT_min/4`.** Run on a
max-min optimal plan, every user gets at least a quarter of `θ*`, which is at least any
floor a full-information policy guarantees. -/
theorem mmsdh_quarter_maxMin (hπ : IsDist M.π) {x : I × J → C → ℝ} {θ : ℝ}
    (hopt : M.IsMaxMinOptimal x θ) {τ : I × J → ℝ} (hτ : ∀ e, 0 ≤ τ e ∧ τ e ≤ 1)
    (hτx : ∀ e c, x e c ≤ τ e * M.π e c) {P : (I × J → C) → Finset (I × J) → ℝ}
    (hP : M.IsFIPolicy P) {θP : ℝ} (hI : ∀ i, θP ≤ M.polUtilI P i)
    (hJ : ∀ j, θP ≤ M.polUtilJ P j) :
    θP / 4 ≤ θ / 4 ∧
      (∀ i, θ / 4 ≤ M.mmUtilI x τ (fun j => uniformRule (M.capJ j))
        (fun i => uniformRule (M.capI i)) i) ∧
      ∀ j, θ / 4 ≤ M.mmUtilJ x τ (fun j => uniformRule (M.capJ j))
        (fun i => uniformRule (M.capI i)) j := by
  have hθP := M.floor_le_maxMin hπ hopt hP hI hJ
  obtain ⟨hI', hJ'⟩ := M.mmsdh_quarter hπ hopt.1 hτ hτx
  refine ⟨by linarith, fun i => ?_, fun j => ?_⟩
  · linarith [hopt.2.1 i, hI' i]
  · linarith [hopt.2.2.1 j, hJ' j]

/-! ### Balanced rules: the note's `c_K^2` -/

/-- **Balanced rules give every user `c_K^2` of its planned surplus**, for `K` at most
every cap. The rules depend on the plan (each is balanced for the candidate
probabilities it faces), but not on any value or swipe, so the policy stays
swipe-local. -/
theorem mmsdh_cK (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasible x)
    {τ : I × J → ℝ} (hτ : ∀ e, 0 ≤ τ e ∧ τ e ≤ 1) (hτx : ∀ e c, x e c ≤ τ e * M.π e c)
    (K : ℕ) (hKI : ∀ i, K ≤ M.capI i) (hKJ : ∀ j, K ≤ M.capJ j) :
    ∃ ψ1 : J → Finset I → Finset I → ℝ, ∃ ψ2 : I → Finset J → Finset J → ℝ,
      (∀ j, IsRule (M.capJ j) (ψ1 j)) ∧ (∀ i, IsRule (M.capI i) (ψ2 i)) ∧
      (∀ i, cK K ^ 2 * M.lpSurplusI x i ≤ M.mmUtilI x τ ψ1 ψ2 i) ∧
      ∀ j, cK K ^ 2 * M.lpSurplusJ x j ≤ M.mmUtilJ x τ ψ1 ψ2 j := by
  have hy : ∀ j i, 0 ≤ ∑ c, x (i, j) c ∧ ∑ c, x (i, j) c ≤ 1 :=
    fun j i => M.sum_x_mem hπ hx (i, j)
  -- Stage 1: a balanced rule for each responder's candidates.
  choose ψ1 hψ1 using fun j => exists_balanced_rule (α := I) (M.capJ j) (hy j) (hx.2.2.2 j)
  have hs := fun i => M.stage1Keep_mem hπ hx (fun j => (hψ1 j).1) i
  -- Stage 2: a balanced rule for what stage 1 passes on to each initiator.
  choose ψ2 hψ2 using fun i => exists_balanced_rule (α := J) (M.capI i) (y := stage1Keep x ψ1 i)
    (fun j => ⟨(hs i j).1, (hs i j).2.trans (hy j i).2⟩)
    ((sum_le_sum fun j _ => (hs i j).2).trans (hx.2.2.1 i))
  have h1 : ∀ j, IsRule (M.capJ j) (ψ1 j) ∧
      IsBalanced (fun i => ∑ c, x (i, j) c) (cK K) (ψ1 j) :=
    fun j => ⟨(hψ1 j).1, (hψ1 j).2.mono (cK_mono (hKJ j)) fun i => (hy j i).1⟩
  have h2 : ∀ i, IsRule (M.capI i) (ψ2 i) ∧ IsBalanced (stage1Keep x ψ1 i) (cK K) (ψ2 i) :=
    fun i => ⟨(hψ2 i).1, (hψ2 i).2.mono (cK_mono (hKI i)) fun j => (hs i j).1⟩
  refine ⟨ψ1, ψ2, fun j => (hψ1 j).1, fun i => (hψ2 i).1, fun i => ?_, fun j => ?_⟩
  · rw [sq]
    exact M.mmUtilI_ge hπ hx hτ hτx (cK_nonneg K) (cK_nonneg K) h1 h2 i
  · rw [sq]
    exact M.mmUtilJ_ge hπ hx hτ hτx (cK_nonneg K) (cK_nonneg K) h1 h2 j

/-- **MM-SDH with balanced rules: the worst-off user gets `c_K^2 θ* ≥ c_K^2 OPT_min`.**
This is the note's claimed guarantee, for a selection that protects every pair. -/
theorem mmsdh_cK_maxMin (hπ : IsDist M.π) {x : I × J → C → ℝ} {θ : ℝ}
    (hopt : M.IsMaxMinOptimal x θ) {τ : I × J → ℝ} (hτ : ∀ e, 0 ≤ τ e ∧ τ e ≤ 1)
    (hτx : ∀ e c, x e c ≤ τ e * M.π e c) (K : ℕ) (hKI : ∀ i, K ≤ M.capI i)
    (hKJ : ∀ j, K ≤ M.capJ j) {P : (I × J → C) → Finset (I × J) → ℝ}
    (hP : M.IsFIPolicy P) {θP : ℝ} (hI : ∀ i, θP ≤ M.polUtilI P i)
    (hJ : ∀ j, θP ≤ M.polUtilJ P j) :
    ∃ ψ1 : J → Finset I → Finset I → ℝ, ∃ ψ2 : I → Finset J → Finset J → ℝ,
      (∀ j, IsRule (M.capJ j) (ψ1 j)) ∧ (∀ i, IsRule (M.capI i) (ψ2 i)) ∧
      cK K ^ 2 * θP ≤ cK K ^ 2 * θ ∧
      (∀ i, cK K ^ 2 * θ ≤ M.mmUtilI x τ ψ1 ψ2 i) ∧
      ∀ j, cK K ^ 2 * θ ≤ M.mmUtilJ x τ ψ1 ψ2 j := by
  obtain ⟨ψ1, ψ2, h1, h2, hI', hJ'⟩ := M.mmsdh_cK hπ hopt.1 hτ hτx K hKI hKJ
  have hθP := M.floor_le_maxMin hπ hopt hP hI hJ
  have hc2 : 0 ≤ cK K ^ 2 := sq_nonneg _
  exact ⟨ψ1, ψ2, h1, h2, mul_le_mul_of_nonneg_left hθP hc2,
    fun i => (mul_le_mul_of_nonneg_left (hopt.2.1 i) hc2).trans (hI' i),
    fun j => (mul_le_mul_of_nonneg_left (hopt.2.2.1 j) hc2).trans (hJ' j)⟩

end ScreenedMarket

end DatingAlgo
