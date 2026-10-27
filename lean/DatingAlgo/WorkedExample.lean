import DatingAlgo.ScreenedDH

/-!
# SDH's worked example, and the continuous-values remark

The "Worked example" section and the "Continuous values" remark of the vault note
"Truthful Swiping with an LLM Oracle".

**Worked example.** Ann (the one `I`-user) and Bo, Cy, Dee (`J = Fin 3`), all top-1 with
cost 1, two-directional with `K = 1`, so every IR cap is 1. Ann values Bo at 4, Cy at
2.5 and Dee at 2, each with probability 1/2 (combination `true`), otherwise 0. Bo, Cy and
Dee value Ann at 2.
* `annPlan_optimal`, `annPlan_value`: the plan `x = (1/2, 1/2, 0)` is optimal, with
  `LP = 3.25`.
* `annTau`: `τ = (1, 1, 0)`.
* `ann_sdhValue`: SDH earns 2.625. `ann_optIR`: `OPT_IR = 2.875`.
* `ann_calls`: Ann is asked first and is charged 2 calls, meeting Theorem 3(c)'s bound
  `b'/p̂ = 1/(1/2)`.

**Continuous values.**
* `continuous_example`: the note's table for Ann's value uniform on `[0, 4]`: each way of
  using the pair with total probability 1/4 has expected weight 7/8, 3/4 or 5/8.
* `pairValue_concave`: a pair's best plan value `F_e(t)` for total `t` is concave (shown
  for finitely many combinations).
* `sdhTau_eq_one_of_full`: if the plan uses some combination every time it occurs, the
  pair is always queried (`τ_e = 1`). With continuous weights every used pair is like this.

The note's claim that Theorem 3(b) holds unchanged for continuous priors is not
formalized: the framework here has only finitely many value combinations per pair.
-/

namespace DatingAlgo

open Finset

/-- Ann's values when she likes the partner: Bo 4, Cy 2.5, Dee 2. -/
noncomputable def annValues : Fin 3 → ℝ := ![4, 2.5, 2]

/-- The worked example's market. -/
noncomputable def annMarket : ScreenedMarket Unit (Fin 3) Bool where
  π _ _ := 1 / 2
  valI e c := if c then annValues e.2 else 0
  valJ _ _ := 2
  costI _ := 1
  costJ _ := 1
  capI _ := 1
  capJ _ := 1

/-- The plan: use Bo and Cy whenever acceptable, never Dee. -/
noncomputable def annPlan : Unit × Fin 3 → Bool → ℝ :=
  fun e c => if c = true ∧ e.2 ≠ 2 then 1 / 2 else 0

theorem annMarket_isDist : IsDist annMarket.π :=
  ⟨fun e o => by norm_num [annMarket], fun e => by norm_num [annMarket]⟩

/-- A pair is acceptable exactly under combination `true`. -/
theorem ann_acc (e : Unit × Fin 3) (c : Bool) : annMarket.Acc e c ↔ c = true := by
  obtain ⟨⟨⟩, j⟩ := e
  cases c <;> fin_cases j <;> norm_num [ScreenedMarket.Acc, annMarket, annValues]

/-- The net weight is Ann's value under `true` and 0 under `false`. -/
theorem ann_wt (e : Unit × Fin 3) (c : Bool) :
    annMarket.wt e c = if c then annValues e.2 else 0 := by
  cases c <;> norm_num [ScreenedMarket.wt, annMarket]

/-- The plan is optimal. -/
theorem annPlan_optimal : annMarket.IsLPOptimal annPlan := by
  refine ⟨⟨fun e c => ?_, fun e c hc => ?_, fun i => ?_, fun j => ?_⟩, fun x' hx' => ?_⟩
  · unfold annPlan
    split_ifs <;> norm_num [annMarket]
  · have : c = false := by simpa [ann_acc] using hc
    simp [annPlan, this]
  · norm_num [annPlan, annMarket, Fin.sum_univ_three]
  · fin_cases j <;> norm_num [annPlan, annMarket]
  · obtain ⟨hbox, -, hcap, -⟩ := hx'
    have h0 := fun j c => (hbox ((), j) c).1
    have h1 := fun j c => (hbox ((), j) c).2
    have hc := hcap ()
    simp only [annMarket, Fin.sum_univ_three, Fintype.sum_bool, Nat.cast_one] at h1 hc
    simp only [ScreenedMarket.lpValue, ann_wt, Fintype.sum_prod_type, Fintype.sum_unique,
      Fin.sum_univ_three, Fintype.sum_bool]
    norm_num [annPlan, annValues]
    linarith [h0 0 false, h0 1 false, h0 2 false, h0 2 true, h1 0 true]

/-- `LP = 3.25`. -/
theorem annPlan_value : annMarket.lpValue annPlan = 3.25 := by
  simp only [ScreenedMarket.lpValue, ann_wt, Fintype.sum_prod_type, Fintype.sum_unique,
    Fin.sum_univ_three, Fintype.sum_bool]
  norm_num [annPlan, annValues]

/-- `τ = (1, 1, 0)`. -/
theorem annTau : annMarket.sdhTau annPlan = fun e => if e.2 ≠ 2 then 1 else 0 := by
  funext e
  obtain ⟨⟨⟩, j⟩ := e
  refine le_antisymm (sup'_le _ _ fun c _ => ?_) (le_sup'_of_le _ (mem_univ true) ?_) <;>
    fin_cases j <;> (try cases c) <;> norm_num [annPlan, annMarket]

/-- Every pair contains Ann, whose cap is 1, so a capped set has at most one pair. -/
theorem ann_capOK (S : Finset (Unit × Fin 3)) : annMarket.CapOK S ↔ S.card ≤ 1 := by
  have hfst : ∀ i : Unit, S.filter (fun e => e.1 = i) = S := fun i =>
    filter_true_of_mem fun e _ => Subsingleton.elim _ _
  constructor
  · intro h
    simpa [hfst, annMarket] using h.1 ()
  · intro h
    refine ⟨fun i => ?_, fun j => ?_⟩
    · simpa [hfst, annMarket] using h
    · exact (card_filter_le _ _).trans (by simpa [annMarket] using h)

/-- `bestMatch` only sees the weights on the ground set. -/
theorem ScreenedMarket.bestMatch_congr {I J C : Type*} [DecidableEq I] [DecidableEq J]
    (M : ScreenedMarket I J C) (F : Finset (I × J)) {w w' : I × J → ℝ}
    (h : ∀ e ∈ F, w e = w' e) : M.bestMatch F w = M.bestMatch F w' := by
  unfold ScreenedMarket.bestMatch
  refine sup'_congr _ rfl fun S hS => sum_congr rfl fun e he => h e ?_
  exact (mem_powerset.mp (mem_filter.mp hS).1) he

/-- The best capped set within `F` is Ann's favourite partner in `F`. -/
theorem ann_bestMatch (F : Finset (Unit × Fin 3)) :
    annMarket.bestMatch F (fun e => annValues e.2) =
      if ((), 0) ∈ F then 4 else if ((), 1) ∈ F then 2.5 else if ((), 2) ∈ F then 2 else 0 := by
  apply le_antisymm
  · obtain ⟨S, hSF, hS, hEq⟩ := annMarket.exists_bestMatch_eq F (fun e => annValues e.2)
    rw [hEq]
    obtain ⟨e, he⟩ := card_le_one_iff_subset_singleton.mp ((ann_capOK S).mp hS)
    rcases subset_singleton_iff.mp he with rfl | rfl
    · split_ifs <;> norm_num
    · have heF := hSF (mem_singleton_self e)
      obtain ⟨⟨⟩, j⟩ := e
      rw [sum_singleton]
      fin_cases j <;> split_ifs <;> simp_all [annValues] <;> norm_num
  · have hle : ∀ e ∈ F, annValues e.2 ≤ annMarket.bestMatch F (fun e => annValues e.2) :=
      fun e he => by
        simpa using annMarket.sum_le_bestMatch (fun e => annValues e.2)
          (singleton_subset_iff.mpr he) ((ann_capOK _).mpr (card_singleton e).le)
    have h0 : 0 ≤ annMarket.bestMatch F (fun e => annValues e.2) := by
      simpa using annMarket.sum_le_bestMatch (fun e => annValues e.2) (empty_subset F)
        ((ann_capOK _).mpr (by simp))
    split_ifs with h1 h2 h3
    · simpa [annValues] using hle _ h1
    · simpa [annValues] using hle _ h2
    · simpa [annValues] using hle _ h3
    · exact h0

/-- An expectation over the three pairs' outcomes, written out. -/
theorem prodExp_unitFin3 {Ω : Type*} [Fintype Ω] (μ : Unit × Fin 3 → Ω → ℝ)
    (g : (Unit × Fin 3 → Ω) → ℝ) :
    prodExp μ g = ∑ a, ∑ b, ∑ c,
      μ ((), 0) a * μ ((), 1) b * μ ((), 2) c * g (fun e => ![a, b, c] e.2) := by
  let E : (Unit × Fin 3 → Ω) ≃ Ω × Ω × Ω :=
    { toFun := fun ω => (ω ((), 0), ω ((), 1), ω ((), 2))
      invFun := fun t e => ![t.1, t.2.1, t.2.2] e.2
      left_inv := fun ω => by
        funext e
        obtain ⟨⟨⟩, j⟩ := e
        fin_cases j <;> rfl
      right_inv := fun t => rfl }
  unfold prodExp
  refine (Fintype.sum_equiv E _ (fun t => μ ((), 0) t.1 * μ ((), 1) t.2.1 * μ ((), 2) t.2.2 *
    g (fun e => ![t.1, t.2.1, t.2.2] e.2)) fun ω => ?_).trans ?_
  · have hω : (fun e : Unit × Fin 3 => ![(E ω).1, (E ω).2.1, (E ω).2.2] e.2) = ω := E.left_inv ω
    rw [hω, Fintype.prod_prod_type, Fintype.prod_unique, Fin.prod_univ_three]
    rfl
  · simp only [Fintype.sum_prod_type]

/-- SDH earns 2.625. -/
theorem ann_sdhValue : annMarket.sdhValue (annMarket.sdhTau annPlan) = 2.625 := by
  have hG : ∀ ω : Unit × Fin 3 → Bool × Bool,
      annMarket.bestMatch (univ.filter fun e => (ω e).2 = true ∧ annMarket.Acc e (ω e).1)
        (fun e => annMarket.wt e (ω e).1) =
      if (ω ((), 0)).2 ∧ (ω ((), 0)).1 then 4 else
        if (ω ((), 1)).2 ∧ (ω ((), 1)).1 then 2.5 else
          if (ω ((), 2)).2 ∧ (ω ((), 2)).1 then 2 else 0 := by
    intro ω
    rw [annMarket.bestMatch_congr _ (w' := fun e => annValues e.2) fun e he => by
      simp [ann_wt, (ann_acc e _).mp (mem_filter.mp he).2.2], ann_bestMatch]
    simp [ann_acc]
  unfold ScreenedMarket.sdhValue
  rw [prodExp_congr _ hG, prodExp_unitFin3, annTau]
  norm_num [ScreenedMarket.screenLaw, annMarket, Fintype.sum_bool, Fintype.sum_prod_type]

/-- `OPT_IR = 2.875`: it also falls back on Dee. -/
theorem ann_optIR : annMarket.optIR = 2.875 := by
  have hG : ∀ ω : Unit × Fin 3 → Bool,
      annMarket.bestMatch (univ.filter fun e => annMarket.Acc e (ω e))
        (fun e => annMarket.wt e (ω e)) =
      if ω ((), 0) then 4 else if ω ((), 1) then 2.5 else if ω ((), 2) then 2 else 0 := by
    intro ω
    rw [annMarket.bestMatch_congr _ (w' := fun e => annValues e.2) fun e he => by
      simp [ann_wt, (ann_acc e _).mp (mem_filter.mp he).2], ann_bestMatch]
    simp [ann_acc]
  unfold ScreenedMarket.optIR
  rw [prodExp_congr _ hG, prodExp_unitFin3]
  norm_num [annMarket, Fintype.sum_bool]

/-- Ann accepts each partner with probability 1/2. -/
theorem ann_phiI (e : Unit × Fin 3) : annMarket.phiI e = 1 / 2 := by
  obtain ⟨⟨⟩, j⟩ := e
  rw [ScreenedMarket.phiI, sum_filter, Fintype.sum_bool]
  fin_cases j <;> norm_num [annMarket, annValues]

/-- Bo, Cy and Dee always accept Ann. -/
theorem ann_phiJ (e : Unit × Fin 3) : annMarket.phiJ e = 1 := by
  rw [ScreenedMarket.phiJ, sum_filter, Fintype.sum_bool]
  norm_num [annMarket]

/-- Ann is charged 2 calls. -/
theorem ann_calls : ∑ j, annMarket.callsI (annMarket.sdhTau annPlan) ((), j) = 2 := by
  simp only [ScreenedMarket.callsI, ann_phiI, ann_phiJ, annTau]
  norm_num [Fin.sum_univ_three]

/-- **Continuous values, the example.** Ann's value `q` is uniform on `[0, 4]` (density
1/4), Bo values Ann at 2, costs are 1, so the pair's net weight is `q`. Using the pair
with total probability 1/4 by querying always and keeping `q > 3`, by querying with
probability 1/2 and keeping `q > 2`, or by querying with probability 1/3 and keeping every
acceptable `q` gives expected weight 7/8, 3/4 and 5/8. -/
theorem continuous_example :
    ((∫ q in (3 : ℝ)..4, q / 4) = 7 / 8 ∧ (∫ _ in (3 : ℝ)..4, (1 : ℝ) / 4) = 1 / 4) ∧
    ((1 / 2 : ℝ) * (∫ q in (2 : ℝ)..4, q / 4) = 3 / 4 ∧
      (1 / 2 : ℝ) * (∫ _ in (2 : ℝ)..4, (1 : ℝ) / 4) = 1 / 4) ∧
    ((1 / 3 : ℝ) * (∫ q in (1 : ℝ)..4, q / 4) = 5 / 8 ∧
      (1 / 3 : ℝ) * (∫ _ in (1 : ℝ)..4, (1 : ℝ) / 4) = 1 / 4) := by
  norm_num [intervalIntegral.integral_div, integral_id]

/-- A pair's best plan value `F_e(t)`: the most weight a plan can get from the pair with
total probability `t`, using combination `c` at most as often as it occurs (`π c`). -/
noncomputable def pairValue {C : Type*} [Fintype C] (w π : C → ℝ) (t : ℝ) : ℝ :=
  sSup {v | ∃ y : C → ℝ, (∀ c, 0 ≤ y c ∧ y c ≤ π c) ∧ ∑ c, y c = t ∧ v = ∑ c, w c * y c}

/-- **Continuous values: `F_e` is concave** on `[0, ∑ π]`. -/
theorem pairValue_concave {C : Type*} [Fintype C] (w π : C → ℝ) (hπ : ∀ c, 0 ≤ π c) :
    ConcaveOn ℝ (Set.Icc 0 (∑ c, π c)) (pairValue w π) := by
  set S : ℝ → Set ℝ := fun t =>
    {v | ∃ y : C → ℝ, (∀ c, 0 ≤ y c ∧ y c ≤ π c) ∧ ∑ c, y c = t ∧ v = ∑ c, w c * y c}
  have hF : ∀ t, pairValue w π t = sSup (S t) := fun t => rfl
  have hbdd : ∀ t, BddAbove (S t) := fun t => by
    refine ⟨∑ c, |w c| * π c, ?_⟩
    rintro v ⟨y, hy, -, rfl⟩
    exact sum_le_sum fun c _ => (mul_le_mul_of_nonneg_right (le_abs_self _) (hy c).1).trans
      (mul_le_mul_of_nonneg_left (hy c).2 (abs_nonneg _))
  -- Scaling `π` down to total `t` is feasible.
  have hne : ∀ t ∈ Set.Icc 0 (∑ c, π c), (S t).Nonempty := by
    rintro t ⟨ht0, ht1⟩
    have hP : 0 ≤ ∑ c, π c := sum_nonneg fun c _ => hπ c
    have hr0 : 0 ≤ t / ∑ c, π c := div_nonneg ht0 hP
    have hr1 : t / ∑ c, π c ≤ 1 := div_le_one_of_le₀ ht1 hP
    refine ⟨_, fun c => t / (∑ c, π c) * π c,
      fun c => ⟨mul_nonneg hr0 (hπ c), mul_le_of_le_one_left (hπ c) hr1⟩, ?_, rfl⟩
    rw [← mul_sum]
    rcases hP.eq_or_lt with h | h
    · rw [← h] at ht1 ⊢
      simp only [div_zero, zero_mul]
      linarith
    · exact div_mul_cancel₀ t h.ne'
  refine ⟨convex_Icc 0 _, fun t1 ht1 t2 ht2 a b ha hb hab => ?_⟩
  rw [hF, hF, hF, ← Real.sSup_smul_of_nonneg ha, ← Real.sSup_smul_of_nonneg hb,
    ← csSup_add (hne t1 ht1).smul_set ((hbdd t1).smul_of_nonneg ha) (hne t2 ht2).smul_set
      ((hbdd t2).smul_of_nonneg hb)]
  refine csSup_le_csSup (hbdd _) ((hne t1 ht1).smul_set.add (hne t2 ht2).smul_set) ?_
  -- The convex combination of two plans is a plan for the convex combination of totals.
  rintro _ ⟨_, ⟨_, ⟨y1, hy1, hs1, rfl⟩, rfl⟩, _, ⟨_, ⟨y2, hy2, hs2, rfl⟩, rfl⟩, rfl⟩
  refine ⟨fun c => a * y1 c + b * y2 c, fun c => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact add_nonneg (mul_nonneg ha (hy1 c).1) (mul_nonneg hb (hy2 c).1)
  · calc a * y1 c + b * y2 c ≤ a * π c + b * π c :=
          add_le_add (mul_le_mul_of_nonneg_left (hy1 c).2 ha)
            (mul_le_mul_of_nonneg_left (hy2 c).2 hb)
      _ = π c := by rw [← add_mul, hab, one_mul]
  · rw [sum_add_distrib, ← mul_sum, ← mul_sum, hs1, hs2, smul_eq_mul, smul_eq_mul]
  · simp only [smul_eq_mul, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun c _ => by ring

/-- **Continuous values: full use means always queried.** If a feasible plan uses some
combination `c` with `π e c > 0` every time it occurs, SDH queries the pair with
probability 1. -/
theorem sdhTau_eq_one_of_full {I J C : Type*} [Fintype I] [Fintype J] [Fintype C]
    [Nonempty C] (M : ScreenedMarket I J C) {x : I × J → C → ℝ} (hx : M.LPFeasible x)
    {e : I × J} {c : C} (hπ : 0 < M.π e c) (hfull : x e c = M.π e c) : M.sdhTau x e = 1 := by
  refine le_antisymm ((M.sdhTau_spec hx).1 e).2 ?_
  refine le_sup'_of_le (fun c => x e c / M.π e c) (mem_univ c) ?_
  rw [hfull, div_self hπ.ne']

end DatingAlgo
