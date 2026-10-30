import DatingAlgo.BudgetedSDH

/-!
# Query budgets in screened DH: priors with finite means

Theorem Q of the vault note "Query Budgets in Screened DH" for priors that are arbitrary
laws on value pairs with finite means: continuous priors, discrete ones, or mixtures.
`BudgetedSDH.lean` has the finite-combination version.

**Model (`ContMarket`).** Pair `e = (i, j)` has values `s = (q_ij, q_ji) ∈ ℝ²` with law `μ e`,
independent across pairs (`Measure.pi μ`). Net values `wI e s = s.1 - costI i`,
`wJ e s = s.2 - costJ j`; `e` is acceptable at `s` when both are positive.

**Plan (`ContFeasible`).** Query probabilities `τ e ∈ [0, 1]` and measurable use rules
`y e s ∈ [0, τ e]`, zero where `e` is unacceptable, with each user's expected matches
`∑ ∫ y` within its cap and its expected calls `∑ callsI τ` within its budget.
`lpSurplusI y i = ∑_j ∫ wI · y`.

**Mechanism.** Query `e` with probability `τ e` and keep a found pair with values `s` with
probability `y e s / τ e`. So given the values `ω`, the candidates are independent and `e`
is one with probability `y e (ω e)`. Then responders and initiators select with rules
`ψ1`, `ψ2` that see only the candidate sets (MM-SDH's two stages). `contUtilI` and
`contUtilJ` are the users' expected utilities.

**Results.**
* `contCallsI_eq` (Q(b)): expected calls are `∑ callsI τ`, within budget.
* `contUtil_ge` (Q(c)): with `γ1`-balanced stage-1 and `γ2`-balanced stage-2 rules,
  every user gets at least `γ1 γ2` times its planned surplus; `contUtil_quarter` (random
  order, `1/4`) and `contUtil_cK` (balanced rules, `c_K^2`).
* `contSDH_welfare` (Q(d)): SDH's own selection, the best capped set of found pairs, earns
  at least `c_K^2` times the plan's value. With SDH's plan this is Theorem 3(b) of the
  truthful-swiping note for continuous priors. Key step `rules_le_bestMatch`: the rule
  stages select a capped set of found pairs.
* `exists_contPlan_of_policy` (Q(e)): every budgeted screened policy, described by the
  chances `q e ω` and `m e ω` that it queries and matches `e` given all values, with `q`
  non-anticipating, induces a feasible plan with the policy's expected surplus for every
  user.
* `cont_objective_quarter`, `cont_objective_cK` (Q(f)): for every monotone, positively
  homogeneous objective, Q-SDH run on an `ε`-optimal plan gets `γ (W(policy) - ε)`.

**How continuous priors reduce to the discrete case.** The rules never see values, so a
user's expected utility involves each pair only through three numbers: `∫ y`, `∫ wI y` and
`∫ wJ y` (`integral_prodExp_bern`, Fubini for products of one-coordinate functions). These
are the numbers of a discrete *surrogate* market with one value combination per pair
(`surrogate`), to which `pairVal_ge` from `MaxMinSDH.lean` applies. The benchmark uses
`measurePreserving_update`: redrawing one pair's values from its own law leaves the joint
law unchanged.
-/

namespace DatingAlgo

open Finset MeasureTheory

/-! ### Measure-theory tools -/

section Tools

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : Type*} [MeasurableSpace S]
  (μ : ι → Measure S) [∀ e, IsProbabilityMeasure (μ e)]

/-- The Bernoulli law on `Option Unit`: `some ()` with probability `t`. -/
def bern (t : ℝ) (o : Option Unit) : ℝ :=
  o.elim (1 - t) fun _ => t

/-- **Resampling one coordinate.** Replacing coordinate `e` of a draw from `Measure.pi μ` by
an independent draw from `μ e` leaves the law unchanged. -/
theorem measurePreserving_update (e : ι) :
    MeasurePreserving (fun p : (ι → S) × S => Function.update p.1 e p.2)
      ((Measure.pi μ).prod (μ e)) (Measure.pi μ) := by
  refine ⟨measurable_update', (Measure.pi_eq fun A hA => ?_).symm⟩
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hA)]
  have hset : (fun p : (ι → S) × S => Function.update p.1 e p.2) ⁻¹' Set.pi Set.univ A =
      Set.pi Set.univ (Function.update A e Set.univ) ×ˢ A e := by
    ext ⟨ω, s⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, by simpa using h e⟩
      by_cases hi : i = e
      · subst hi
        simp
      · simpa [Function.update_of_ne hi] using h i
    · rintro ⟨h1, h2⟩ i
      by_cases hi : i = e
      · subst hi
        simpa using h2
      · simpa [Function.update_of_ne hi] using h1 i
  rw [hset, Measure.prod_prod, Measure.pi_pi, ← mul_prod_erase univ _ (mem_univ e),
    ← mul_prod_erase univ (fun i => μ i (A i)) (mem_univ e)]
  simp only [Function.update_self, measure_univ, one_mul]
  rw [mul_comm]
  congr 1
  exact prod_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_erase hi)]

omit [DecidableEq ι] in
/-- The expectation of a function of one coordinate. -/
theorem integral_coord (e : ι) {f : S → ℝ} (hf : AEStronglyMeasurable f (μ e)) :
    ∫ ω, f (ω e) ∂(Measure.pi μ) = ∫ s, f s ∂(μ e) := by
  have h := measurePreserving_eval μ e
  conv_rhs => rw [← h.map_eq]
  rw [integral_map h.measurable.aemeasurable (by rw [h.map_eq]; exact hf)]

/-- **Resampling, integrated.** For a measurable `h` of all coordinates with values in
`[0, 1]` and an integrable `f` of coordinate `e`,
`E[h(ω) f(ω e)] = ∫ f(s) E[h(ω with ω e := s)] dμ_e(s)`. -/
theorem integral_mul_coord_eq (e : ι) {h : (ι → S) → ℝ} (hh : Measurable h)
    (h01 : ∀ ω, 0 ≤ h ω ∧ h ω ≤ 1) {f : S → ℝ} (hf : Integrable f (μ e)) :
    ∫ ω, h ω * f (ω e) ∂(Measure.pi μ) =
      ∫ s, f s * ∫ ω, h (Function.update ω e s) ∂(Measure.pi μ) ∂(μ e) := by
  have hΦ := measurePreserving_update μ e
  have hfe : Integrable (fun ω : ι → S => f (ω e)) (Measure.pi μ) :=
    (measurePreserving_eval μ e).integrable_comp_of_integrable hf
  have hG : Integrable (fun ω => h ω * f (ω e)) (Measure.pi μ) :=
    hfe.bdd_mul hh.aestronglyMeasurable (c := 1)
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h01 ω])
  have hGΦ : Integrable (fun p : (ι → S) × S => h (Function.update p.1 e p.2) * f p.2)
      ((Measure.pi μ).prod (μ e)) := by
    have := hΦ.integrable_comp_of_integrable hG
    simpa [Function.comp_def, Function.update_self] using this
  calc ∫ ω, h ω * f (ω e) ∂(Measure.pi μ)
      = ∫ p, h (Function.update p.1 e p.2) * f p.2 ∂((Measure.pi μ).prod (μ e)) := by
        conv_lhs => rw [← hΦ.map_eq]
        rw [integral_map hΦ.measurable.aemeasurable
          (by rw [hΦ.map_eq]; exact hG.aestronglyMeasurable)]
        simp [Function.update_self]
    _ = ∫ s, ∫ ω, h (Function.update ω e s) * f s ∂(Measure.pi μ) ∂(μ e) :=
        integral_prod_symm _ hGΦ
    _ = ∫ s, f s * ∫ ω, h (Function.update ω e s) ∂(Measure.pi μ) ∂(μ e) := by
        refine integral_congr_ae (ae_of_all _ fun s => ?_)
        simp only
        rw [integral_mul_const, mul_comm]

/-- **Coarsening.** Candidates are independent given the values, coordinate `e` being one
with probability `p e (ω e)`. Then a function `K` of the candidate pattern, times a gain
`g` of coordinate `e₀` counted when `e₀` is a candidate, has an expectation that depends on
each coordinate only through `∫ p e` and `∫ g · p e₀`. -/
theorem integral_prodExp_bern (p : ι → S → ℝ) (hp : ∀ e, Measurable (p e))
    (hp01 : ∀ e s, 0 ≤ p e s ∧ p e s ≤ 1) (e₀ : ι) {g : S → ℝ} (hg : Integrable g (μ e₀))
    (K : (ι → Option Unit) → ℝ) :
    Integrable (fun ω => prodExp (fun e => bern (p e (ω e)))
        (fun η => (η e₀).elim 0 (fun _ => g (ω e₀)) * K η)) (Measure.pi μ) ∧
    ∫ ω, prodExp (fun e => bern (p e (ω e)))
        (fun η => (η e₀).elim 0 (fun _ => g (ω e₀)) * K η) ∂(Measure.pi μ) =
      ∑ η : ι → Option Unit, (∏ e, if e = e₀ then (η e).elim 0 (fun _ => ∫ s, g s * p e s ∂(μ e))
        else bern (∫ s, p e s ∂(μ e)) (η e)) * K η := by
  have hpi : ∀ e, Integrable (p e) (μ e) := fun e =>
    (integrable_const (1 : ℝ)).mono' (hp e).aestronglyMeasurable
      (ae_of_all _ fun s => by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hp01 e s])
  -- The gain and the candidate coins combine into one factor per coordinate.
  set F : (ι → Option Unit) → ι → S → ℝ := fun η e s =>
    if e = e₀ then (η e).elim 0 (fun _ => g s * p e s) else bern (p e s) (η e) with hF
  have hpt : ∀ ω : ι → S, prodExp (fun e => bern (p e (ω e)))
      (fun η => (η e₀).elim 0 (fun _ => g (ω e₀)) * K η) =
      ∑ η, K η * ∏ e, F η e (ω e) := fun ω => by
    unfold prodExp
    refine sum_congr rfl fun η _ => ?_
    rw [← mul_prod_erase univ _ (mem_univ e₀),
      ← mul_prod_erase univ (fun e => F η e (ω e)) (mem_univ e₀)]
    have hrest : ∏ e ∈ univ.erase e₀, F η e (ω e) =
        ∏ e ∈ univ.erase e₀, bern (p e (ω e)) (η e) :=
      prod_congr rfl fun e he => by simp [hF, ne_of_mem_erase he]
    rw [hrest]
    simp only [hF, ↓reduceIte]
    cases η e₀ <;> simp [bern]
    ring
  -- Each factor away from `e₀` is a probability.
  have hbern : ∀ (t : ℝ) (o : Option Unit), 0 ≤ t → t ≤ 1 → 0 ≤ bern t o ∧ bern t o ≤ 1 :=
    fun t o h0 h1 => by cases o <;> simp [bern] <;> constructor <;> linarith
  have hFm : ∀ η e, e ≠ e₀ → Measurable (F η e) := fun η e he => by
    simp only [hF, he, ↓reduceIte]
    cases η e with
    | none => exact measurable_const.sub (hp e)
    | some _ => exact hp e
  have hF0 : ∀ η, Integrable (F η e₀) (μ e₀) := fun η => by
    simp only [hF, ↓reduceIte]
    cases η e₀ with
    | none => exact integrable_zero _ _ _
    | some _ =>
      exact hg.mul_bdd (hp e₀).aestronglyMeasurable (c := 1)
        (ae_of_all _ fun s => by
          rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hp01 e₀ s])
  have hint : ∀ η, Integrable (fun ω => K η * ∏ e, F η e (ω e)) (Measure.pi μ) := fun η => by
    refine Integrable.const_mul ?_ _
    have hsplit : (fun ω : ι → S => ∏ e, F η e (ω e)) =
        fun ω => (∏ e ∈ univ.erase e₀, F η e (ω e)) * F η e₀ (ω e₀) := by
      funext ω
      rw [← mul_prod_erase univ _ (mem_univ e₀), mul_comm]
    rw [hsplit]
    refine ((measurePreserving_eval μ e₀).integrable_comp_of_integrable (hF0 η)).bdd_mul
      ?_ (c := 1) (ae_of_all _ fun ω => ?_)
    · exact (Finset.measurable_prod _ fun e he =>
        (hFm η e (ne_of_mem_erase he)).comp (measurable_pi_apply e)).aestronglyMeasurable
    · rw [norm_prod]
      refine prod_le_one₀ (fun e _ => norm_nonneg _) fun e he => ?_
      have hne := ne_of_mem_erase he
      have := hbern (p e (ω e)) (η e) (hp01 e (ω e)).1 (hp01 e (ω e)).2
      simp only [hF, hne, ↓reduceIte, Real.norm_eq_abs, abs_le]
      constructor <;> linarith
  have hFint : ∀ η e, ∫ s, F η e s ∂(μ e) = if e = e₀ then
      (η e).elim 0 (fun _ => ∫ s, g s * p e s ∂(μ e)) else bern (∫ s, p e s ∂(μ e)) (η e) :=
    fun η e => by
      by_cases he : e = e₀
      · subst he
        simp only [hF, ↓reduceIte]
        cases η e <;> simp
      · simp only [hF, he, ↓reduceIte]
        cases η e with
        | none => simp [bern, integral_sub (integrable_const (1 : ℝ)) (hpi e)]
        | some _ => simp [bern]
  have hfun : (fun ω : ι → S => prodExp (fun e => bern (p e (ω e)))
      (fun η => (η e₀).elim 0 (fun _ => g (ω e₀)) * K η)) =
      fun ω : ι → S => ∑ η, K η * ∏ e, F η e (ω e) := funext hpt
  refine ⟨hfun ▸ integrable_finsetSum _ fun η _ => hint η, ?_⟩
  rw [hfun, integral_finsetSum _ fun η _ => hint η]
  refine sum_congr rfl fun η _ => ?_
  rw [integral_const_mul, integral_fintype_prod_eq_prod, mul_comm]
  simp only [hFint]

/-- Monotonicity of `prodExp` that only needs the inequality where the law is positive. -/
theorem prodExp_le_of_support {Ω : Type*} [Fintype Ω] {ν : ι → Ω → ℝ} (hν : ∀ e o, 0 ≤ ν e o)
    {g h : (ι → Ω) → ℝ} (hgh : ∀ ω, (∀ e, ν e (ω e) ≠ 0) → g ω ≤ h ω) :
    prodExp ν g ≤ prodExp ν h := by
  unfold prodExp
  refine sum_le_sum fun ω _ => ?_
  by_cases hz : ∀ e, ν e (ω e) ≠ 0
  · exact mul_le_mul_of_nonneg_left (hgh ω hz) (prod_nonneg fun e _ => hν e _)
  · push Not at hz
    obtain ⟨e, he⟩ := hz
    rw [prod_eq_zero (mem_univ e) he, zero_mul, zero_mul]

end Tools

/-! ### The market and the plan -/

/-- A market whose priors are laws on value pairs. -/
structure ContMarket (I J : Type*) where
  μ : I × J → Measure (ℝ × ℝ)
  costI : I → ℝ
  costJ : J → ℝ
  capI : I → ℕ
  capJ : J → ℕ

namespace ContMarket

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  (M : ContMarket I J)

/-- Pair `e` is acceptable at values `s`. -/
def Acc (e : I × J) (s : ℝ × ℝ) : Prop :=
  M.costI e.1 < s.1 ∧ M.costJ e.2 < s.2

/-- `i`'s net value. -/
def wI (e : I × J) (s : ℝ × ℝ) : ℝ := s.1 - M.costI e.1

/-- `j`'s net value. -/
def wJ (e : I × J) (s : ℝ × ℝ) : ℝ := s.2 - M.costJ e.2

/-- The priors are probability laws with finite means. -/
def Regular : Prop :=
  (∀ e, IsProbabilityMeasure (M.μ e)) ∧
    ∀ e, Integrable (fun s : ℝ × ℝ => s.1) (M.μ e) ∧ Integrable (fun s : ℝ × ℝ => s.2) (M.μ e)

/-- Probability that `i` accepts `j`. -/
noncomputable def phiI (e : I × J) : ℝ := (M.μ e {s | M.costI e.1 < s.1}).toReal

/-- Probability that `j` accepts `i`. -/
noncomputable def phiJ (e : I × J) : ℝ := (M.μ e {s | M.costJ e.2 < s.2}).toReal

/-- Expected calls charged to `i` for pair `e`: the side less likely to accept is asked
first, the other side only after a yes. -/
noncomputable def callsI (τ : I × J → ℝ) (e : I × J) : ℝ :=
  τ e * if M.phiI e ≤ M.phiJ e then 1 else M.phiJ e

/-- Expected calls charged to `j` for pair `e`. -/
noncomputable def callsJ (τ : I × J → ℝ) (e : I × J) : ℝ :=
  τ e * if M.phiI e ≤ M.phiJ e then M.phiI e else 1

/-- Calls charged to `i` when `e` is queried and has values `s`. -/
noncomputable def chargeI (e : I × J) (s : ℝ × ℝ) : ℝ :=
  if M.phiI e ≤ M.phiJ e then 1 else if M.costJ e.2 < s.2 then 1 else 0

/-- Calls charged to `j` when `e` is queried and has values `s`. -/
noncomputable def chargeJ (e : I × J) (s : ℝ × ℝ) : ℝ :=
  if M.phiI e ≤ M.phiJ e then (if M.costI e.1 < s.1 then 1 else 0) else 1

/-- Feasible plans of the query-aware program. -/
def ContFeasible (QI : I → ℝ) (QJ : J → ℝ) (y : I × J → ℝ × ℝ → ℝ) (τ : I × J → ℝ) : Prop :=
  (∀ e, Measurable (y e)) ∧ (∀ e s, 0 ≤ y e s ∧ y e s ≤ τ e) ∧ (∀ e, τ e ≤ 1) ∧
    (∀ e s, ¬ M.Acc e s → y e s = 0) ∧
    (∀ i, ∑ j, ∫ s, y (i, j) s ∂(M.μ (i, j)) ≤ M.capI i) ∧
    (∀ j, ∑ i, ∫ s, y (i, j) s ∂(M.μ (i, j)) ≤ M.capJ j) ∧
    (∀ i, ∑ j, M.callsI τ (i, j) ≤ QI i) ∧ ∀ j, ∑ i, M.callsJ τ (i, j) ≤ QJ j

/-- `i`'s planned surplus. -/
noncomputable def lpSurplusI (y : I × J → ℝ × ℝ → ℝ) (i : I) : ℝ :=
  ∑ j, ∫ s, M.wI (i, j) s * y (i, j) s ∂(M.μ (i, j))

/-- `j`'s planned surplus. -/
noncomputable def lpSurplusJ (y : I × J → ℝ × ℝ → ℝ) (j : J) : ℝ :=
  ∑ i, ∫ s, M.wJ (i, j) s * y (i, j) s ∂(M.μ (i, j))

/-- The planned surpluses as one vector. -/
noncomputable def lpVec (y : I × J → ℝ × ℝ → ℝ) : I ⊕ J → ℝ :=
  Sum.elim (M.lpSurplusI y) (M.lpSurplusJ y)

/-! ### The mechanism -/

/-- Responder `j`'s candidates in the candidate pattern `η`. -/
def colC (η : I × J → Option Unit) (j : J) : Finset I :=
  univ.filter fun i => (η (i, j)).isSome

/-- **`i`'s expected utility under Q-SDH**: average over the values `ω`, then over the
candidates (independent given `ω`, `e` with probability `y e (ω e)`), then over the two
selection stages; `i` gains the net values of the partners it keeps. -/
noncomputable def contUtilI (y : I × J → ℝ × ℝ → ℝ) (ψ1 : J → Finset I → Finset I → ℝ)
    (ψ2 : I → Finset J → Finset J → ℝ) (i : I) : ℝ :=
  ∫ ω, prodExp (fun e => bern (y e (ω e))) (fun η =>
    prodExp (fun j T => ψ1 j (colC η j) T) fun T =>
      prodExp (fun i' T' => ψ2 i' (univ.filter fun j => i' ∈ T j) T') fun T' =>
        ∑ j ∈ T' i, M.wI (i, j) (ω (i, j))) ∂(Measure.pi M.μ)

/-- **`j`'s expected utility under Q-SDH**; see `contUtilI`. -/
noncomputable def contUtilJ (y : I × J → ℝ × ℝ → ℝ) (ψ1 : J → Finset I → Finset I → ℝ)
    (ψ2 : I → Finset J → Finset J → ℝ) (j : J) : ℝ :=
  ∫ ω, prodExp (fun e => bern (y e (ω e))) (fun η =>
    prodExp (fun j' T => ψ1 j' (colC η j') T) fun T =>
      prodExp (fun i' T' => ψ2 i' (univ.filter fun j' => i' ∈ T j') T') fun T' =>
        ∑ i ∈ univ.filter (fun i => j ∈ T' i), M.wJ (i, j) (ω (i, j))) ∂(Measure.pi M.μ)

/-- `i`'s expected calls under Q-SDH: pair `e` is queried with probability `τ e`,
independently of its values. -/
noncomputable def contCallsI (τ : I × J → ℝ) (i : I) : ℝ :=
  ∫ ω, ∑ j, τ (i, j) * M.chargeI (i, j) (ω (i, j)) ∂(Measure.pi M.μ)

/-- `j`'s expected calls under Q-SDH. -/
noncomputable def contCallsJ (τ : I × J → ℝ) (j : J) : ℝ :=
  ∫ ω, ∑ i, τ (i, j) * M.chargeJ (i, j) (ω (i, j)) ∂(Measure.pi M.μ)

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem measurable_chargeI (e : I × J) : Measurable (M.chargeI e) := by
  unfold chargeI
  by_cases h : M.phiI e ≤ M.phiJ e
  · simp only [h, ↓reduceIte]
    exact measurable_const
  · simp only [h, ↓reduceIte]
    exact Measurable.ite (measurableSet_lt measurable_const measurable_snd) measurable_const
      measurable_const

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem measurable_chargeJ (e : I × J) : Measurable (M.chargeJ e) := by
  unfold chargeJ
  by_cases h : M.phiI e ≤ M.phiJ e
  · simp only [h, ↓reduceIte]
    exact Measurable.ite (measurableSet_lt measurable_const measurable_fst) measurable_const
      measurable_const
  · simp only [h, ↓reduceIte]
    exact measurable_const

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem chargeI_mem (e : I × J) (s : ℝ × ℝ) : 0 ≤ M.chargeI e s ∧ M.chargeI e s ≤ 1 := by
  unfold chargeI
  split_ifs <;> norm_num

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem chargeJ_mem (e : I × J) (s : ℝ × ℝ) : 0 ≤ M.chargeJ e s ∧ M.chargeJ e s ≤ 1 := by
  unfold chargeJ
  split_ifs <;> norm_num

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- One query's expected charge to `i`. -/
theorem integral_chargeI (hM : M.Regular) (e : I × J) :
    ∫ s, M.chargeI e s ∂(M.μ e) = if M.phiI e ≤ M.phiJ e then 1 else M.phiJ e := by
  have := hM.1 e
  unfold chargeI
  by_cases h : M.phiI e ≤ M.phiJ e
  · simp [h]
  · simp only [h, ↓reduceIte]
    rw [show (fun s : ℝ × ℝ => if M.costJ e.2 < s.2 then (1 : ℝ) else 0) =
        Set.indicator {s | M.costJ e.2 < s.2} 1 from by
      funext s
      simp [Set.indicator]]
    rw [integral_indicator_one (measurableSet_lt measurable_const measurable_snd)]
    rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- One query's expected charge to `j`. -/
theorem integral_chargeJ (hM : M.Regular) (e : I × J) :
    ∫ s, M.chargeJ e s ∂(M.μ e) = if M.phiI e ≤ M.phiJ e then M.phiI e else 1 := by
  have := hM.1 e
  unfold chargeJ
  by_cases h : M.phiI e ≤ M.phiJ e
  · simp only [h, ↓reduceIte]
    rw [show (fun s : ℝ × ℝ => if M.costI e.1 < s.1 then (1 : ℝ) else 0) =
        Set.indicator {s | M.costI e.1 < s.1} 1 from by
      funext s
      simp [Set.indicator]]
    rw [integral_indicator_one (measurableSet_lt measurable_const measurable_fst)]
    rfl
  · simp [h]

omit [DecidableEq I] [DecidableEq J] in
/-- A bounded measurable function of one coordinate is integrable. -/
theorem integrable_coord (hM : M.Regular) (e : I × J) {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (h01 : ∀ s, 0 ≤ f s ∧ f s ≤ 1) :
    Integrable (fun ω : I × J → ℝ × ℝ => f (ω e)) (Measure.pi M.μ) := by
  have := hM.1
  refine (measurePreserving_eval M.μ e).integrable_comp_of_integrable ?_
  exact (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable (ae_of_all _ fun s => by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h01 s])

omit [DecidableEq I] [DecidableEq J] in
/-- **Theorem Q(b) for `i`.** -/
theorem contCallsI_eq (hM : M.Regular) (τ : I × J → ℝ) (i : I) :
    M.contCallsI τ i = ∑ j, M.callsI τ (i, j) := by
  have := hM.1
  unfold contCallsI
  rw [integral_finsetSum _ fun j _ =>
    (M.integrable_coord hM (i, j) (M.measurable_chargeI (i, j)) (M.chargeI_mem (i, j))).const_mul _]
  refine sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_coord M.μ (i, j) (M.measurable_chargeI (i, j)).aestronglyMeasurable,
    M.integral_chargeI hM]
  rfl

omit [DecidableEq I] [DecidableEq J] in
/-- **Theorem Q(b) for `j`.** -/
theorem contCallsJ_eq (hM : M.Regular) (τ : I × J → ℝ) (j : J) :
    M.contCallsJ τ j = ∑ i, M.callsJ τ (i, j) := by
  have := hM.1
  unfold contCallsJ
  rw [integral_finsetSum _ fun i _ =>
    (M.integrable_coord hM (i, j) (M.measurable_chargeJ (i, j)) (M.chargeJ_mem (i, j))).const_mul _]
  refine sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_coord M.μ (i, j) (M.measurable_chargeJ (i, j)).aestronglyMeasurable,
    M.integral_chargeJ hM]
  rfl

/-! ### The surrogate market -/

/-- Probability that `e` is a candidate. -/
noncomputable def candP (y : I × J → ℝ × ℝ → ℝ) (e : I × J) : ℝ := ∫ s, y e s ∂(M.μ e)

/-- `i`'s expected gain from `e`, counted when `e` is a candidate. -/
noncomputable def gainIP (y : I × J → ℝ × ℝ → ℝ) (e : I × J) : ℝ :=
  ∫ s, M.wI e s * y e s ∂(M.μ e)

/-- `j`'s expected gain from `e`, counted when `e` is a candidate. -/
noncomputable def gainJP (y : I × J → ℝ × ℝ → ℝ) (e : I × J) : ℝ :=
  ∫ s, M.wJ e s * y e s ∂(M.μ e)

/-- **The surrogate market**: one value combination per pair, which always occurs and is
worth `gainIP / candP` to `i` and `gainJP / candP` to `j` (or `1` if `e` is never a
candidate). -/
noncomputable def surrogate (y : I × J → ℝ × ℝ → ℝ) : ScreenedMarket I J Unit where
  π _ _ := 1
  valI e _ := M.costI e.1 + if 0 < M.candP y e then M.gainIP y e / M.candP y e else 1
  valJ e _ := M.costJ e.2 + if 0 < M.candP y e then M.gainJP y e / M.candP y e else 1
  costI := M.costI
  costJ := M.costJ
  capI := M.capI
  capJ := M.capJ

/-- The surrogate plan: use `e` with probability `candP`. -/
noncomputable def surPlan (y : I × J → ℝ × ℝ → ℝ) : I × J → Unit → ℝ :=
  fun e _ => M.candP y e

section Surrogate

variable {M} {QI : I → ℝ} {QJ : J → ℝ} {y : I × J → ℝ × ℝ → ℝ} {τ : I × J → ℝ}

omit [DecidableEq I] [DecidableEq J] in
theorem y_mem (hy : M.ContFeasible QI QJ y τ) (e : I × J) (s : ℝ × ℝ) :
    0 ≤ y e s ∧ y e s ≤ 1 :=
  ⟨(hy.2.1 e s).1, (hy.2.1 e s).2.trans (hy.2.2.1 e)⟩

omit [DecidableEq I] [DecidableEq J] in
theorem integrable_y (hM : M.Regular) (hy : M.ContFeasible QI QJ y τ) (e : I × J) :
    Integrable (y e) (M.μ e) := by
  have := hM.1 e
  exact (integrable_const (1 : ℝ)).mono' (hy.1 e).aestronglyMeasurable (ae_of_all _ fun s => by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [y_mem hy e s])

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem integrable_wI (hM : M.Regular) (e : I × J) : Integrable (M.wI e) (M.μ e) := by
  have := hM.1 e
  exact (hM.2 e).1.sub (integrable_const _)

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem integrable_wJ (hM : M.Regular) (e : I × J) : Integrable (M.wJ e) (M.μ e) := by
  have := hM.1 e
  exact (hM.2 e).2.sub (integrable_const _)

omit [DecidableEq I] [DecidableEq J] in
theorem integrable_wI_mul (hM : M.Regular) (hy : M.ContFeasible QI QJ y τ) (e : I × J) :
    Integrable (fun s => M.wI e s * y e s) (M.μ e) :=
  (integrable_wI hM e).mul_bdd (hy.1 e).aestronglyMeasurable (c := 1) (ae_of_all _ fun s => by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [y_mem hy e s])

omit [DecidableEq I] [DecidableEq J] in
theorem integrable_wJ_mul (hM : M.Regular) (hy : M.ContFeasible QI QJ y τ) (e : I × J) :
    Integrable (fun s => M.wJ e s * y e s) (M.μ e) :=
  (integrable_wJ hM e).mul_bdd (hy.1 e).aestronglyMeasurable (c := 1) (ae_of_all _ fun s => by
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [y_mem hy e s])

omit [DecidableEq I] [DecidableEq J] in
theorem wI_mul_nonneg (hy : M.ContFeasible QI QJ y τ) (e : I × J) (s : ℝ × ℝ) :
    0 ≤ M.wI e s * y e s := by
  by_cases h : M.Acc e s
  · exact mul_nonneg (by unfold wI; linarith [h.1]) (hy.2.1 e s).1
  · rw [hy.2.2.2.1 e s h, mul_zero]

omit [DecidableEq I] [DecidableEq J] in
theorem wJ_mul_nonneg (hy : M.ContFeasible QI QJ y τ) (e : I × J) (s : ℝ × ℝ) :
    0 ≤ M.wJ e s * y e s := by
  by_cases h : M.Acc e s
  · exact mul_nonneg (by unfold wJ; linarith [h.2]) (hy.2.1 e s).1
  · rw [hy.2.2.2.1 e s h, mul_zero]

omit [DecidableEq I] [DecidableEq J] in
theorem candP_mem (hM : M.Regular) (hy : M.ContFeasible QI QJ y τ) (e : I × J) :
    0 ≤ M.candP y e ∧ M.candP y e ≤ 1 := by
  have := hM.1 e
  refine ⟨integral_nonneg fun s => (hy.2.1 e s).1, ?_⟩
  calc M.candP y e ≤ ∫ _, (1 : ℝ) ∂(M.μ e) :=
        integral_mono (integrable_y hM hy e) (integrable_const 1) fun s => (y_mem hy e s).2
    _ = 1 := by simp

omit [DecidableEq I] [DecidableEq J] in
/-- A pair that is never a candidate gains nothing. -/
theorem gainP_eq_zero (hM : M.Regular) (hy : M.ContFeasible QI QJ y τ) (e : I × J)
    (h : M.candP y e = 0) : M.gainIP y e = 0 ∧ M.gainJP y e = 0 := by
  have := hM.1 e
  have hy0 : y e =ᵐ[M.μ e] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun s => (hy.2.1 e s).1) (integrable_y hM hy e)).mp h
  constructor
  · unfold gainIP
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hy0] with s hs
    simp [hs]
  · unfold gainJP
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hy0] with s hs
    simp [hs]

omit [DecidableEq I] [DecidableEq J] in
/-- A pair that is sometimes a candidate gains something: it is only used when acceptable. -/
theorem gainP_pos (hM : M.Regular) (hy : M.ContFeasible QI QJ y τ) (e : I × J)
    (h : 0 < M.candP y e) : 0 < M.gainIP y e ∧ 0 < M.gainJP y e := by
  have := hM.1 e
  have hacc : ∀ s, y e s ≠ 0 → M.Acc e s := fun s hs => by
    by_contra hn
    exact hs (hy.2.2.2.1 e s hn)
  have hpos : 0 < (M.μ e) (Function.support (y e)) :=
    (integral_pos_iff_support_of_nonneg (fun s => (hy.2.1 e s).1) (integrable_y hM hy e)).mp h
  have hI : Function.support (fun s => M.wI e s * y e s) = Function.support (y e) := by
    ext s
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or]
    refine ⟨fun h => h.2, fun hs => ⟨ne_of_gt ?_, hs⟩⟩
    unfold wI
    linarith [(hacc s hs).1]
  have hJ : Function.support (fun s => M.wJ e s * y e s) = Function.support (y e) := by
    ext s
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or]
    refine ⟨fun h => h.2, fun hs => ⟨ne_of_gt ?_, hs⟩⟩
    unfold wJ
    linarith [(hacc s hs).2]
  constructor
  · unfold gainIP
    rw [integral_pos_iff_support_of_nonneg (fun s => wI_mul_nonneg hy e s)
      (integrable_wI_mul hM hy e), hI]
    exact hpos
  · unfold gainJP
    rw [integral_pos_iff_support_of_nonneg (fun s => wJ_mul_nonneg hy e s)
      (integrable_wJ_mul hM hy e), hJ]
    exact hpos

omit [DecidableEq I] [DecidableEq J] in
/-- Every surrogate pair is acceptable, so the surrogate's candidates are the candidates. -/
theorem surrogate_acc (hM : M.Regular) (hy : M.ContFeasible QI QJ y τ) (e : I × J) :
    (M.surrogate y).Acc e () := by
  simp only [ScreenedMarket.Acc, surrogate, lt_add_iff_pos_right]
  constructor <;> split_ifs with h
  · exact div_pos (gainP_pos hM hy e h).1 h
  · exact one_pos
  · exact div_pos (gainP_pos hM hy e h).2 h
  · exact one_pos

omit [DecidableEq I] [DecidableEq J] in
/-- The surrogate's value of a candidate, times the candidate probability, is the expected
gain. -/
theorem candP_mul_wbar (hM : M.Regular) (hy : M.ContFeasible QI QJ y τ) (e : I × J) :
    M.candP y e * (if 0 < M.candP y e then M.gainIP y e / M.candP y e else 1) = M.gainIP y e ∧
      M.candP y e * (if 0 < M.candP y e then M.gainJP y e / M.candP y e else 1) =
        M.gainJP y e := by
  split_ifs with h
  · exact ⟨mul_div_cancel₀ _ h.ne', mul_div_cancel₀ _ h.ne'⟩
  · have h0 : M.candP y e = 0 := le_antisymm (not_lt.mp h) (candP_mem hM hy e).1
    rw [h0, zero_mul, (gainP_eq_zero hM hy e h0).1, (gainP_eq_zero hM hy e h0).2]
    exact ⟨rfl, rfl⟩

omit [DecidableEq I] [DecidableEq J] in
/-- The surrogate plan is feasible for the surrogate market. -/
theorem surPlan_feasible (hM : M.Regular) (hy : M.ContFeasible QI QJ y τ) :
    (M.surrogate y).LPFeasible (M.surPlan y) := by
  refine ⟨fun e _ => ?_, fun e c hc => absurd (surrogate_acc hM hy e) hc, fun i => ?_,
    fun j => ?_⟩
  · exact candP_mem hM hy e
  · simpa [surPlan, surrogate, candP] using hy.2.2.2.2.1 i
  · simpa [surPlan, surrogate, candP] using hy.2.2.2.2.2.1 j

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem isDist_surrogate : IsDist (M.surrogate y).π :=
  ⟨fun _ _ => zero_le_one, fun _ => by simp [surrogate]⟩

omit [DecidableEq I] [DecidableEq J] in
/-- The surrogate's planned surpluses are the continuous plan's. -/
theorem lpSurplus_surrogate (hM : M.Regular) (hy : M.ContFeasible QI QJ y τ) :
    (∀ i, (M.surrogate y).lpSurplusI (M.surPlan y) i = M.lpSurplusI y i) ∧
      ∀ j, (M.surrogate y).lpSurplusJ (M.surPlan y) j = M.lpSurplusJ y j := by
  refine ⟨fun i => ?_, fun j => ?_⟩
  · unfold ScreenedMarket.lpSurplusI lpSurplusI
    refine sum_congr rfl fun j _ => ?_
    simp only [Finset.univ_unique, Finset.sum_singleton, surrogate, surPlan, add_sub_cancel_left]
    rw [mul_comm]
    exact (candP_mul_wbar hM hy (i, j)).1
  · unfold ScreenedMarket.lpSurplusJ lpSurplusJ
    refine sum_congr rfl fun i _ => ?_
    simp only [Finset.univ_unique, Finset.sum_singleton, surrogate, surPlan, add_sub_cancel_left]
    rw [mul_comm]
    exact (candP_mul_wbar hM hy (i, j)).2

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- The surrogate's candidate law is the Bernoulli law with the candidate probability. -/
theorem candLaw_surPlan (e : I × J) (o : Option Unit) :
    ScreenedMarket.candLaw (M.surPlan y) e o = bern (M.candP y e) o := by
  cases o <;> simp [ScreenedMarket.candLaw, bern, surPlan]

/-- The chance that both selection stages keep `(i, j)`, given the candidate pattern `η`. -/
noncomputable def keep2 (ψ1 : J → Finset I → Finset I → ℝ) (ψ2 : I → Finset J → Finset J → ℝ)
    (i : I) (j : J) (η : I × J → Option Unit) : ℝ :=
  ruleKeep (ψ1 j) (colC η j) i *
    indepExp (univ.erase j) (fun j' => ruleKeep (ψ1 j') (colC η j') i)
      (fun B => ruleKeep (ψ2 i) (insert j B) j)

/-- A pair that is not a candidate is never kept. -/
theorem keep2_none {ψ1 : J → Finset I → Finset I → ℝ} {ψ2 : I → Finset J → Finset J → ℝ}
    (h1r : ∀ j, IsRule (M.capJ j) (ψ1 j)) (i : I) (j : J) {η : I × J → Option Unit}
    (h : η (i, j) = none) : keep2 ψ1 ψ2 i j η = 0 := by
  have hn : i ∉ colC η j := by simp [colC, h]
  simp only [keep2, ruleKeep_eq_zero (h1r j) hn, zero_mul]

omit [DecidableEq I] [DecidableEq J] in
/-- The surrogate's candidates are the candidates. -/
theorem candCol_surrogate (hM : M.Regular) (hy : M.ContFeasible QI QJ y τ)
    (η : I × J → Option Unit) (j : J) : (M.surrogate y).candCol η j = colC η j := by
  refine Finset.filter_congr fun i' _ => ?_
  simp only [ScreenedMarket.IsCand, Option.isSome_iff_exists]
  constructor
  · rintro ⟨c, hc, -⟩
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, hc, surrogate_acc hM hy (i', j)⟩

/-- `pairVal_eq` in the surrogate market. -/
theorem pairVal_surrogate (hM : M.Regular) (hy : M.ContFeasible QI QJ y τ)
    {ψ1 : J → Finset I → Finset I → ℝ} {ψ2 : I → Finset J → Finset J → ℝ}
    (h1r : ∀ j, IsRule (M.capJ j) (ψ1 j)) (h2r : ∀ i, IsRule (M.capI i) (ψ2 i))
    (i : I) (j : J) (g : Option Unit → ℝ) (η : I × J → Option Unit) :
    (M.surrogate y).pairVal ψ1 ψ2 i j g η = g (η (i, j)) * keep2 ψ1 ψ2 i j η := by
  rw [(M.surrogate y).pairVal_eq h1r h2r i j g η]
  simp only [candCol_surrogate hM hy, keep2]

/-- Given the values `ω`, `i`'s utility is a sum over its pairs of one-pair terms. -/
theorem contUtilI_integrand (hM : M.Regular) (hy : M.ContFeasible QI QJ y τ)
    {ψ1 : J → Finset I → Finset I → ℝ} {ψ2 : I → Finset J → Finset J → ℝ}
    (h1r : ∀ j, IsRule (M.capJ j) (ψ1 j)) (h2r : ∀ i, IsRule (M.capI i) (ψ2 i)) (i : I)
    (ω : I × J → ℝ × ℝ) :
    prodExp (fun e => bern (y e (ω e))) (fun η =>
      prodExp (fun j T => ψ1 j (colC η j) T) fun T =>
        prodExp (fun i' T' => ψ2 i' (univ.filter fun j => i' ∈ T j) T') fun T' =>
          ∑ j ∈ T' i, M.wI (i, j) (ω (i, j))) =
      ∑ j, prodExp (fun e => bern (y e (ω e)))
        (fun η => (η (i, j)).elim 0 (fun _ => M.wI (i, j) (ω (i, j))) * keep2 ψ1 ψ2 i j η) := by
  rw [← prodExp_sum]
  refine prodExp_congr _ fun η => ?_
  have h2 : ∀ T : J → Finset I,
      (prodExp (fun i' T' => ψ2 i' (univ.filter fun j => i' ∈ T j) T') fun T' =>
        ∑ j ∈ T' i, M.wI (i, j) (ω (i, j))) =
      ∑ j, prodExp (fun i' T' => ψ2 i' (univ.filter fun j => i' ∈ T j) T') fun T' =>
        if j ∈ T' i then M.wI (i, j) (ω (i, j)) else 0 := fun T => by
    rw [← prodExp_sum]
    exact prodExp_congr _ fun T' => by rw [sum_ite_mem, univ_inter]
  rw [prodExp_congr _ h2, prodExp_sum]
  refine sum_congr rfl fun j _ => ?_
  have hval := pairVal_surrogate hM hy h1r h2r i j (fun _ => M.wI (i, j) (ω (i, j))) η
  simp only [ScreenedMarket.pairVal, candCol_surrogate hM hy] at hval
  rw [hval]
  cases h : η (i, j) with
  | none => simp [keep2_none (ψ2 := ψ2) h1r i j h]
  | some _ => simp

/-- Given the values `ω`, `j`'s utility is a sum over its pairs of one-pair terms. -/
theorem contUtilJ_integrand (hM : M.Regular) (hy : M.ContFeasible QI QJ y τ)
    {ψ1 : J → Finset I → Finset I → ℝ} {ψ2 : I → Finset J → Finset J → ℝ}
    (h1r : ∀ j, IsRule (M.capJ j) (ψ1 j)) (h2r : ∀ i, IsRule (M.capI i) (ψ2 i)) (j : J)
    (ω : I × J → ℝ × ℝ) :
    prodExp (fun e => bern (y e (ω e))) (fun η =>
      prodExp (fun j' T => ψ1 j' (colC η j') T) fun T =>
        prodExp (fun i' T' => ψ2 i' (univ.filter fun j' => i' ∈ T j') T') fun T' =>
          ∑ i ∈ univ.filter (fun i => j ∈ T' i), M.wJ (i, j) (ω (i, j))) =
      ∑ i, prodExp (fun e => bern (y e (ω e)))
        (fun η => (η (i, j)).elim 0 (fun _ => M.wJ (i, j) (ω (i, j))) * keep2 ψ1 ψ2 i j η) := by
  rw [← prodExp_sum]
  refine prodExp_congr _ fun η => ?_
  have h2 : ∀ T : J → Finset I,
      (prodExp (fun i' T' => ψ2 i' (univ.filter fun j' => i' ∈ T j') T') fun T' =>
        ∑ i ∈ univ.filter (fun i => j ∈ T' i), M.wJ (i, j) (ω (i, j))) =
      ∑ i, prodExp (fun i' T' => ψ2 i' (univ.filter fun j' => i' ∈ T j') T') fun T' =>
        if j ∈ T' i then M.wJ (i, j) (ω (i, j)) else 0 := fun T => by
    rw [← prodExp_sum]
    exact prodExp_congr _ fun T' => sum_filter _ _
  rw [prodExp_congr _ h2, prodExp_sum]
  refine sum_congr rfl fun i _ => ?_
  have hval := pairVal_surrogate hM hy h1r h2r i j (fun _ => M.wJ (i, j) (ω (i, j))) η
  simp only [ScreenedMarket.pairVal, candCol_surrogate hM hy] at hval
  rw [hval]
  cases h : η (i, j) with
  | none => simp [keep2_none (ψ2 := ψ2) h1r i j h]
  | some _ => simp

/-- `i`'s utility given the values is integrable. -/
theorem integrable_contUtilI (hM : M.Regular) (hy : M.ContFeasible QI QJ y τ)
    {ψ1 : J → Finset I → Finset I → ℝ} {ψ2 : I → Finset J → Finset J → ℝ}
    (h1r : ∀ j, IsRule (M.capJ j) (ψ1 j)) (h2r : ∀ i, IsRule (M.capI i) (ψ2 i)) (i : I) :
    Integrable (fun ω : I × J → ℝ × ℝ => prodExp (fun e => bern (y e (ω e))) (fun η =>
      prodExp (fun j T => ψ1 j (colC η j) T) fun T =>
        prodExp (fun i' T' => ψ2 i' (univ.filter fun j => i' ∈ T j) T') fun T' =>
          ∑ j ∈ T' i, M.wI (i, j) (ω (i, j)))) (Measure.pi M.μ) := by
  have := hM.1
  rw [funext (contUtilI_integrand hM hy h1r h2r i)]
  exact integrable_finsetSum _ fun j _ =>
    (integral_prodExp_bern M.μ y hy.1 (y_mem hy) (i, j) (integrable_wI hM (i, j))
      (keep2 ψ1 ψ2 i j)).1

/-- `j`'s utility given the values is integrable. -/
theorem integrable_contUtilJ (hM : M.Regular) (hy : M.ContFeasible QI QJ y τ)
    {ψ1 : J → Finset I → Finset I → ℝ} {ψ2 : I → Finset J → Finset J → ℝ}
    (h1r : ∀ j, IsRule (M.capJ j) (ψ1 j)) (h2r : ∀ i, IsRule (M.capI i) (ψ2 i)) (j : J) :
    Integrable (fun ω : I × J → ℝ × ℝ => prodExp (fun e => bern (y e (ω e))) (fun η =>
      prodExp (fun j' T => ψ1 j' (colC η j') T) fun T =>
        prodExp (fun i' T' => ψ2 i' (univ.filter fun j' => i' ∈ T j') T') fun T' =>
          ∑ i ∈ univ.filter (fun i => j ∈ T' i), M.wJ (i, j) (ω (i, j)))) (Measure.pi M.μ) := by
  have := hM.1
  rw [funext (contUtilJ_integrand hM hy h1r h2r j)]
  exact integrable_finsetSum _ fun i _ =>
    (integral_prodExp_bern M.μ y hy.1 (y_mem hy) (i, j) (integrable_wJ hM (i, j))
      (keep2 ψ1 ψ2 i j)).1

/-- **The reduction for `i`.** Q-SDH's expected utility for `i` is MM-SDH's in the
surrogate market. -/
theorem contUtilI_eq (hM : M.Regular) (hy : M.ContFeasible QI QJ y τ)
    {ψ1 : J → Finset I → Finset I → ℝ} {ψ2 : I → Finset J → Finset J → ℝ}
    (h1r : ∀ j, IsRule (M.capJ j) (ψ1 j)) (h2r : ∀ i, IsRule (M.capI i) (ψ2 i)) (i : I) :
    M.contUtilI y ψ1 ψ2 i = (M.surrogate y).mmUtilI (M.surPlan y) (fun _ => 1) ψ1 ψ2 i := by
  have := hM.1
  set M' := M.surrogate y with hM'
  have hx' := surPlan_feasible hM hy
  rw [M'.mmUtilI_eq isDist_surrogate hx' (fun _ => ⟨zero_le_one, le_rfl⟩)
    (fun e c => by simpa [M', surrogate] using (hx'.1 e c).2) ψ1 ψ2 i]
  rw [prodExp_congr _ (M'.candUtilI_eq ψ1 ψ2 i), prodExp_sum]
  unfold contUtilI
  rw [integral_congr_ae (ae_of_all _ (contUtilI_integrand hM hy h1r h2r i)),
    integral_finsetSum _ fun j _ => (integral_prodExp_bern M.μ y hy.1 (y_mem hy) (i, j)
      (integrable_wI hM (i, j)) (keep2 ψ1 ψ2 i j)).1]
  refine sum_congr rfl fun j _ => ?_
  rw [(integral_prodExp_bern M.μ y hy.1 (y_mem hy) (i, j) (integrable_wI hM (i, j))
      (keep2 ψ1 ψ2 i j)).2,
    prodExp_congr _ fun η => pairVal_surrogate hM hy h1r h2r i j (M'.gainI (i, j)) η]
  unfold prodExp
  refine sum_congr rfl fun η _ => ?_
  rw [← mul_prod_erase univ _ (mem_univ (i, j)),
    ← mul_prod_erase univ (fun e => ScreenedMarket.candLaw (M.surPlan y) e (η e)) (mem_univ (i, j))]
  have hrest : ∏ e ∈ univ.erase (i, j), (if e = (i, j) then
      (η e).elim 0 (fun _ => ∫ s, M.wI (i, j) s * y e s ∂(M.μ e))
      else bern (∫ s, y e s ∂(M.μ e)) (η e)) =
      ∏ e ∈ univ.erase (i, j), ScreenedMarket.candLaw (M.surPlan y) e (η e) :=
    prod_congr rfl fun e he => by
      simp only [ne_of_mem_erase he, ↓reduceIte, candLaw_surPlan]
      rfl
  rw [hrest, candLaw_surPlan]
  simp only [↓reduceIte]
  cases h : η (i, j) with
  | none => simp [bern, ScreenedMarket.gainI]
  | some u =>
    have hacc : M'.Acc (i, j) u := surrogate_acc hM hy (i, j)
    set wb := (if 0 < M.candP y (i, j) then M.gainIP y (i, j) / M.candP y (i, j) else 1)
      with hwb
    have hg : M'.gainI (i, j) (some u) = wb := by
      simp only [ScreenedMarket.gainI, Option.elim, hacc, ↓reduceIte]
      simp only [hM', surrogate, add_sub_cancel_left, hwb]
    have hw : M.candP y (i, j) * wb = M.gainIP y (i, j) := (candP_mul_wbar hM hy (i, j)).1
    simp only [Option.elim, bern, hg]
    rw [show (∫ s, M.wI (i, j) s * y (i, j) s ∂M.μ (i, j)) = M.gainIP y (i, j) from rfl, ← hw]
    ring

/-- **The reduction for `j`.** -/
theorem contUtilJ_eq (hM : M.Regular) (hy : M.ContFeasible QI QJ y τ)
    {ψ1 : J → Finset I → Finset I → ℝ} {ψ2 : I → Finset J → Finset J → ℝ}
    (h1r : ∀ j, IsRule (M.capJ j) (ψ1 j)) (h2r : ∀ i, IsRule (M.capI i) (ψ2 i)) (j : J) :
    M.contUtilJ y ψ1 ψ2 j = (M.surrogate y).mmUtilJ (M.surPlan y) (fun _ => 1) ψ1 ψ2 j := by
  have := hM.1
  set M' := M.surrogate y with hM'
  have hx' := surPlan_feasible hM hy
  rw [M'.mmUtilJ_eq isDist_surrogate hx' (fun _ => ⟨zero_le_one, le_rfl⟩)
    (fun e c => by simpa [M', surrogate] using (hx'.1 e c).2) ψ1 ψ2 j]
  rw [prodExp_congr _ (M'.candUtilJ_eq ψ1 ψ2 j), prodExp_sum]
  unfold contUtilJ
  rw [integral_congr_ae (ae_of_all _ (contUtilJ_integrand hM hy h1r h2r j)),
    integral_finsetSum _ fun i _ => (integral_prodExp_bern M.μ y hy.1 (y_mem hy) (i, j)
      (integrable_wJ hM (i, j)) (keep2 ψ1 ψ2 i j)).1]
  refine sum_congr rfl fun i _ => ?_
  rw [(integral_prodExp_bern M.μ y hy.1 (y_mem hy) (i, j) (integrable_wJ hM (i, j))
      (keep2 ψ1 ψ2 i j)).2,
    prodExp_congr _ fun η => pairVal_surrogate hM hy h1r h2r i j (M'.gainJ (i, j)) η]
  unfold prodExp
  refine sum_congr rfl fun η _ => ?_
  rw [← mul_prod_erase univ _ (mem_univ (i, j)),
    ← mul_prod_erase univ (fun e => ScreenedMarket.candLaw (M.surPlan y) e (η e)) (mem_univ (i, j))]
  have hrest : ∏ e ∈ univ.erase (i, j), (if e = (i, j) then
      (η e).elim 0 (fun _ => ∫ s, M.wJ (i, j) s * y e s ∂(M.μ e))
      else bern (∫ s, y e s ∂(M.μ e)) (η e)) =
      ∏ e ∈ univ.erase (i, j), ScreenedMarket.candLaw (M.surPlan y) e (η e) :=
    prod_congr rfl fun e he => by
      simp only [ne_of_mem_erase he, ↓reduceIte, candLaw_surPlan]
      rfl
  rw [hrest, candLaw_surPlan]
  simp only [↓reduceIte]
  cases h : η (i, j) with
  | none => simp [bern, ScreenedMarket.gainJ]
  | some u =>
    have hacc : M'.Acc (i, j) u := surrogate_acc hM hy (i, j)
    set wb := (if 0 < M.candP y (i, j) then M.gainJP y (i, j) / M.candP y (i, j) else 1)
      with hwb
    have hg : M'.gainJ (i, j) (some u) = wb := by
      simp only [ScreenedMarket.gainJ, Option.elim, hacc, ↓reduceIte]
      simp only [hM', surrogate, add_sub_cancel_left, hwb]
    have hw : M.candP y (i, j) * wb = M.gainJP y (i, j) := (candP_mul_wbar hM hy (i, j)).2
    simp only [Option.elim, bern, hg]
    rw [show (∫ s, M.wJ (i, j) s * y (i, j) s ∂M.μ (i, j)) = M.gainJP y (i, j) from rfl, ← hw]
    ring

end Surrogate

/-! ### The guarantees -/

/-- **Theorem Q(c).** If every stage-1 rule is `γ1`-balanced and every stage-2 rule is
`γ2`-balanced for the candidate probabilities, every user gets at least `γ1 γ2` times its
planned surplus. -/
theorem contUtil_ge (hM : M.Regular) {QI : I → ℝ} {QJ : J → ℝ} {y : I × J → ℝ × ℝ → ℝ}
    {τ : I × J → ℝ} (hy : M.ContFeasible QI QJ y τ) {ψ1 : J → Finset I → Finset I → ℝ}
    {ψ2 : I → Finset J → Finset J → ℝ} {γ1 γ2 : ℝ} (hγ1 : 0 ≤ γ1) (hγ2 : 0 ≤ γ2)
    (h1 : ∀ j, IsRule (M.capJ j) (ψ1 j) ∧ IsBalanced (fun i => M.candP y (i, j)) γ1 (ψ1 j))
    (h2 : ∀ i, IsRule (M.capI i) (ψ2 i) ∧
      IsBalanced (ScreenedMarket.stage1Keep (M.surPlan y) ψ1 i) γ2 (ψ2 i)) :
    (∀ i, γ1 * γ2 * M.lpSurplusI y i ≤ M.contUtilI y ψ1 ψ2 i) ∧
      ∀ j, γ1 * γ2 * M.lpSurplusJ y j ≤ M.contUtilJ y ψ1 ψ2 j := by
  have hx' := surPlan_feasible hM hy
  have hτx : ∀ e c, M.surPlan y e c ≤ (fun _ => (1 : ℝ)) e * (M.surrogate y).π e c :=
    fun e c => by simpa [surrogate] using (hx'.1 e c).2
  have h1' : ∀ j, IsRule ((M.surrogate y).capJ j) (ψ1 j) ∧
      IsBalanced (fun i => ∑ c, M.surPlan y (i, j) c) γ1 (ψ1 j) := fun j =>
    ⟨(h1 j).1, by simpa [surPlan] using (h1 j).2⟩
  obtain ⟨hlI, hlJ⟩ := lpSurplus_surrogate hM hy
  refine ⟨fun i => ?_, fun j => ?_⟩
  · rw [contUtilI_eq hM hy (fun j => (h1 j).1) (fun i => (h2 i).1), ← hlI i]
    exact (M.surrogate y).mmUtilI_ge isDist_surrogate hx' (fun _ => ⟨zero_le_one, le_rfl⟩) hτx
      hγ1 hγ2 h1' h2 i
  · rw [contUtilJ_eq hM hy (fun j => (h1 j).1) (fun i => (h2 i).1), ← hlJ j]
    exact (M.surrogate y).mmUtilJ_ge isDist_surrogate hx' (fun _ => ⟨zero_le_one, le_rfl⟩) hτx
      hγ1 hγ2 h1' h2 j

/-- **Theorem Q(c) with random order:** every user gets at least a quarter of its planned
surplus. -/
theorem contUtil_quarter (hM : M.Regular) {QI : I → ℝ} {QJ : J → ℝ}
    {y : I × J → ℝ × ℝ → ℝ} {τ : I × J → ℝ} (hy : M.ContFeasible QI QJ y τ) :
    (∀ i, M.lpSurplusI y i / 4 ≤ M.contUtilI y (fun j => uniformRule (M.capJ j))
      (fun i => uniformRule (M.capI i)) i) ∧
    ∀ j, M.lpSurplusJ y j / 4 ≤ M.contUtilJ y (fun j => uniformRule (M.capJ j))
      (fun i => uniformRule (M.capI i)) j := by
  have hx' := surPlan_feasible hM hy
  have hτx : ∀ e c, M.surPlan y e c ≤ (fun _ => (1 : ℝ)) e * (M.surrogate y).π e c :=
    fun e c => by simpa [surrogate] using (hx'.1 e c).2
  have hq := (M.surrogate y).mmsdh_quarter isDist_surrogate hx'
    (fun _ => ⟨zero_le_one, le_rfl⟩) hτx
  have hr1 : ∀ j, IsRule (M.capJ j) (uniformRule (α := I) (M.capJ j)) :=
    fun j => isRule_uniformRule _
  have hr2 : ∀ i, IsRule (M.capI i) (uniformRule (α := J) (M.capI i)) :=
    fun i => isRule_uniformRule _
  obtain ⟨hlI, hlJ⟩ := lpSurplus_surrogate hM hy
  refine ⟨fun i => ?_, fun j => ?_⟩
  · rw [contUtilI_eq hM hy hr1 hr2, ← hlI i]
    exact hq.1 i
  · rw [contUtilJ_eq hM hy hr1 hr2, ← hlJ j]
    exact hq.2 j

/-- **Theorem Q(c) with balanced rules:** every user gets at least `c_K^2` times its planned
surplus, for `K` at most every cap. -/
theorem contUtil_cK (hM : M.Regular) {QI : I → ℝ} {QJ : J → ℝ}
    {y : I × J → ℝ × ℝ → ℝ} {τ : I × J → ℝ} (hy : M.ContFeasible QI QJ y τ)
    (K : ℕ) (hKI : ∀ i, K ≤ M.capI i) (hKJ : ∀ j, K ≤ M.capJ j) :
    ∃ ψ1 : J → Finset I → Finset I → ℝ, ∃ ψ2 : I → Finset J → Finset J → ℝ,
      (∀ j, IsRule (M.capJ j) (ψ1 j)) ∧ (∀ i, IsRule (M.capI i) (ψ2 i)) ∧
      (∀ i, cK K ^ 2 * M.lpSurplusI y i ≤ M.contUtilI y ψ1 ψ2 i) ∧
      ∀ j, cK K ^ 2 * M.lpSurplusJ y j ≤ M.contUtilJ y ψ1 ψ2 j := by
  have hx' := surPlan_feasible hM hy
  have hτx : ∀ e c, M.surPlan y e c ≤ (fun _ => (1 : ℝ)) e * (M.surrogate y).π e c :=
    fun e c => by simpa [surrogate] using (hx'.1 e c).2
  obtain ⟨ψ1, ψ2, hr1, hr2, hI, hJ⟩ := (M.surrogate y).mmsdh_cK isDist_surrogate hx'
    (fun _ => ⟨zero_le_one, le_rfl⟩) hτx K hKI hKJ
  obtain ⟨hlI, hlJ⟩ := lpSurplus_surrogate hM hy
  refine ⟨ψ1, ψ2, hr1, hr2, fun i => ?_, fun j => ?_⟩
  · rw [contUtilI_eq hM hy hr1 hr2, ← hlI i]
    exact hI i
  · rw [contUtilJ_eq hM hy hr1 hr2, ← hlJ j]
    exact hJ j

/-! ### Total welfare with SDH's own selection -/

noncomputable instance (e : I × J) (s : ℝ × ℝ) : Decidable (M.Acc e s) := Classical.dec _

/-- `M` with only its caps: `bestMatch` and `CapOK` use nothing else. -/
def capsMarket : ScreenedMarket I J Unit where
  π _ _ := 1
  valI _ _ := 0
  valJ _ _ := 0
  costI := M.costI
  costJ := M.costJ
  capI := M.capI
  capJ := M.capJ

/-- The chance that `e` is found acceptable when it has values `s` and is queried with
probability `τ e`. -/
noncomputable def foundP (τ : I × J → ℝ) (e : I × J) (s : ℝ × ℝ) : ℝ :=
  if M.Acc e s then τ e else 0

/-- **SDH's welfare with a query-aware plan.** Each pair is queried independently with
probability `τ e`, so given the values `ω` it is found acceptable with probability
`foundP τ e (ω e)`. SDH takes the best capped set of found pairs with their true net
weights (SDH's step 3). -/
noncomputable def contSDHValue (τ : I × J → ℝ) : ℝ :=
  ∫ ω, prodExp (fun e b => if b then M.foundP τ e (ω e) else 1 - M.foundP τ e (ω e))
    (fun b => M.capsMarket.bestMatch (univ.filter fun e => b e = true)
      (fun e => M.wI e (ω e) + M.wJ e (ω e))) ∂(Measure.pi M.μ)

section MaxWeight

variable {M} {QI : I → ℝ} {QJ : J → ℝ} {y : I × J → ℝ × ℝ → ℝ} {τ : I × J → ℝ}

omit [Fintype I] [Fintype J] in
theorem bestMatch_caps_nonneg (F : Finset (I × J)) (w : I × J → ℝ) :
    0 ≤ M.capsMarket.bestMatch F w := by
  have h := M.capsMarket.sum_le_bestMatch w (empty_subset F) (by simp [ScreenedMarket.CapOK])
  simpa using h

theorem bestMatch_caps_le (F : Finset (I × J)) (w : I × J → ℝ) :
    M.capsMarket.bestMatch F w ≤ ∑ e, |w e| := by
  unfold ScreenedMarket.bestMatch
  refine Finset.sup'_le _ _ fun S _ => ?_
  calc ∑ e ∈ S, w e ≤ ∑ e ∈ S, |w e| := sum_le_sum fun e _ => le_abs_self _
    _ ≤ ∑ e, |w e| := sum_le_sum_of_subset_of_nonneg (subset_univ S) fun e _ _ => abs_nonneg _

omit [Fintype I] [Fintype J] in
theorem measurable_bestMatch_caps {δ : Type*} [MeasurableSpace δ] (F : Finset (I × J))
    {w : I × J → δ → ℝ} (hw : ∀ e, Measurable (w e)) :
    Measurable fun ω => M.capsMarket.bestMatch F (fun e => w e ω) := by
  have H : (F.powerset.filter M.capsMarket.CapOK).Nonempty :=
    ⟨∅, mem_filter.mpr ⟨empty_mem_powerset F, by simp [ScreenedMarket.CapOK]⟩⟩
  have hfun : (fun ω => M.capsMarket.bestMatch F (fun e => w e ω)) =
      (F.powerset.filter M.capsMarket.CapOK).sup' H (fun S ω => ∑ e ∈ S, w e ω) := by
    funext ω
    rw [Finset.sup'_apply]
    rfl
  rw [hfun]
  exact Finset.measurable_sup' H fun S _ => Finset.measurable_sum _ fun e _ => hw e

/-- **Selection by rules never beats SDH's best capped set.** Given the candidates `η`,
the users' total utility from the two rule stages is at most the best capped set of the
found pairs `F ⊇` candidates. -/
theorem rules_le_bestMatch {ψ1 : J → Finset I → Finset I → ℝ}
    {ψ2 : I → Finset J → Finset J → ℝ} (h1r : ∀ j, IsRule (M.capJ j) (ψ1 j))
    (h2r : ∀ i, IsRule (M.capI i) (ψ2 i)) (η : I × J → Option Unit) (F : Finset (I × J))
    (hηF : ∀ e, (η e).isSome → e ∈ F) (w1 w2 : I × J → ℝ) :
    (∑ i, prodExp (fun j T => ψ1 j (colC η j) T) fun T =>
        prodExp (fun i' T' => ψ2 i' (univ.filter fun j => i' ∈ T j) T') fun T' =>
          ∑ j ∈ T' i, w1 (i, j)) +
      (∑ j, prodExp (fun j' T => ψ1 j' (colC η j') T) fun T =>
        prodExp (fun i' T' => ψ2 i' (univ.filter fun j' => i' ∈ T j') T') fun T' =>
          ∑ i ∈ univ.filter (fun i => j ∈ T' i), w2 (i, j)) ≤
      M.capsMarket.bestMatch F (fun e => w1 e + w2 e) := by
  set B := M.capsMarket.bestMatch F (fun e => w1 e + w2 e)
  have hd1 : ∀ j, ∑ T, ψ1 j (colC η j) T = 1 := fun j => ((h1r j) _).2.1
  have hd2 : ∀ (T : J → Finset I) i, ∑ T', ψ2 i (univ.filter fun j => i ∈ T j) T' = 1 :=
    fun T i => ((h2r i) _).2.1
  -- Combine both sums under the rule laws.
  rw [← prodExp_sum, ← prodExp_sum, ← prodExp_add]
  have hin : ∀ T : J → Finset I,
      (∑ i, prodExp (fun i' T' => ψ2 i' (univ.filter fun j => i' ∈ T j) T') fun T' =>
          ∑ j ∈ T' i, w1 (i, j)) +
        (∑ j, prodExp (fun i' T' => ψ2 i' (univ.filter fun j' => i' ∈ T j') T') fun T' =>
          ∑ i ∈ univ.filter (fun i => j ∈ T' i), w2 (i, j)) =
      prodExp (fun i' T' => ψ2 i' (univ.filter fun j => i' ∈ T j) T') fun T' =>
        (∑ i, ∑ j ∈ T' i, w1 (i, j)) + ∑ j, ∑ i ∈ univ.filter (fun i => j ∈ T' i), w2 (i, j) :=
    fun T => by rw [← prodExp_sum, ← prodExp_sum, ← prodExp_add]
  rw [prodExp_congr _ hin]
  calc _ ≤ prodExp (fun j T => ψ1 j (colC η j) T) fun T =>
        prodExp (fun i' T' => ψ2 i' (univ.filter fun j => i' ∈ T j) T') fun _ => B := by
        refine prodExp_le_of_support (fun j T => ((h1r j) _).1 T) fun T hT => ?_
        refine prodExp_le_of_support (fun i T' => ((h2r i) _).1 T') fun T' hT' => ?_
        have hs1 := fun j => ((h1r j) (colC η j)).2.2 (T j) (hT j)
        have hs2 := fun i => ((h2r i) (univ.filter fun j => i ∈ T j)).2.2 (T' i) (hT' i)
        -- The selected pairs.
        set S := univ.filter fun e : I × J => e.2 ∈ T' e.1 with hS
        have hmemS : ∀ i j, (i, j) ∈ S ↔ j ∈ T' i := fun i j => by simp [hS]
        have hsum : ∑ e ∈ S, (w1 e + w2 e) =
            (∑ i, ∑ j ∈ T' i, w1 (i, j)) + ∑ j, ∑ i ∈ univ.filter (fun i => j ∈ T' i), w2 (i, j) := by
          rw [sum_add_distrib, sum_filter, sum_filter, Fintype.sum_prod_type,
            Fintype.sum_prod_type]
          dsimp only
          rw [sum_comm (f := fun i j => if j ∈ T' i then w2 (i, j) else 0)]
          congr 1
          · exact sum_congr rfl fun i _ => by rw [sum_ite_mem, univ_inter]
          · exact sum_congr rfl fun j _ => (sum_filter _ _).symm
        have hSF : S ⊆ F := fun e he => by
          obtain ⟨i, j⟩ := e
          have hj : j ∈ T' i := (hmemS i j).mp he
          have hi : i ∈ T j := by simpa using (hs2 i).1 hj
          have hc : i ∈ colC η j := (hs1 j).1 hi
          exact hηF (i, j) (by simpa [colC] using hc)
        have hcap : M.capsMarket.CapOK S := by
          refine ⟨fun i => ?_, fun j => ?_⟩
          · have h := ScreenedMarket.card_filter_fst S i
            simp only [hmemS, sum_boole] at h
            have : ((S.filter fun e => e.1 = i).card : ℝ) ≤ M.capI i := by
              rw [h]
              have hc := (hs2 i).2
              have : (univ.filter fun j => j ∈ T' i) = T' i := by ext; simp
              rw [this]
              exact_mod_cast hc
            exact_mod_cast this
          · have h := ScreenedMarket.card_filter_snd S j
            simp only [hmemS] at h
            have hle : ((S.filter fun e => e.2 = j).card : ℝ) ≤ (T j).card := by
              rw [h]
              calc (∑ i, if j ∈ T' i then (1 : ℝ) else 0) ≤ ∑ i, if i ∈ T j then 1 else 0 :=
                    sum_le_sum fun i _ => by
                      by_cases hj : j ∈ T' i
                      · have hi : i ∈ T j := by simpa using (hs2 i).1 hj
                        simp [hj, hi]
                      · simp only [hj, ↓reduceIte]; split_ifs <;> norm_num
                _ = (T j).card := by rw [sum_boole, filter_mem_eq_inter, univ_inter]
            have hc : ((T j).card : ℝ) ≤ M.capJ j := by exact_mod_cast (hs1 j).2
            exact_mod_cast hle.trans hc
        rw [← hsum]
        exact M.capsMarket.sum_le_bestMatch _ hSF hcap
    _ = B := by
        rw [prodExp_congr _ fun T => prodExp_const (hd2 T) B, prodExp_const hd1 B]

/-- **Theorem Q(d) for priors with finite means.** SDH's own selection, the best capped set
of found pairs, run with a feasible query-aware plan, earns at least `c_K^2` times the plan's
value `∑_e ∫ (wI + wJ) y`, for `K` at most every cap. With SDH's plan (`τ e = 1` on the pairs
it uses, no budget) this is Theorem 3(b) of the truthful-swiping note for continuous priors. -/
theorem contSDH_welfare (hM : M.Regular) (hy : M.ContFeasible QI QJ y τ) (K : ℕ)
    (hKI : ∀ i, K ≤ M.capI i) (hKJ : ∀ j, K ≤ M.capJ j) :
    cK K ^ 2 * (∑ i, M.lpSurplusI y i + ∑ j, M.lpSurplusJ y j) ≤ M.contSDHValue τ := by
  have := hM.1
  obtain ⟨ψ1, ψ2, hr1, hr2, hI, hJ⟩ := M.contUtil_cK hM hy K hKI hKJ
  have hτ0 : ∀ e, 0 ≤ τ e := fun e => (hy.2.1 e 0).1.trans (hy.2.1 e 0).2
  have hf01 : ∀ e s, 0 ≤ M.foundP τ e s ∧ M.foundP τ e s ≤ 1 := fun e s => by
    unfold foundP
    split_ifs
    exacts [⟨hτ0 e, hy.2.2.1 e⟩, ⟨le_rfl, zero_le_one⟩]
  have hyf : ∀ e s, y e s ≤ M.foundP τ e s := fun e s => by
    unfold foundP
    split_ifs with h
    · exact (hy.2.1 e s).2
    · rw [hy.2.2.2.1 e s h]
  -- Three outcomes per pair: a candidate, found but not kept, or not found.
  set G : (I × J → ℝ × ℝ) → I × J → Option Bool → ℝ := fun ω e o =>
    o.elim (1 - M.foundP τ e (ω e))
      (fun b => if b then y e (ω e) else M.foundP τ e (ω e) - y e (ω e)) with hG
  have hG0 : ∀ ω e o, 0 ≤ G ω e o := fun ω e o => by
    cases o with
    | none => simp only [hG, Option.elim]; linarith [(hf01 e (ω e)).2]
    | some b =>
      cases b
      · simp only [hG, Option.elim, Bool.false_eq_true, ↓reduceIte]; linarith [hyf e (ω e)]
      · simp only [hG, Option.elim, ↓reduceIte]; exact (hy.2.1 e (ω e)).1
  set cand : Option Bool → Option Unit := fun o => if o = some true then some () else none
    with hcand
  have hpushF : ∀ ω, (fun e (b : Bool) => ∑ o ∈ univ.filter (fun o : Option Bool => o.isSome = b),
      G ω e o) = fun e b => if b then M.foundP τ e (ω e) else 1 - M.foundP τ e (ω e) := by
    intro ω
    funext e b
    rw [sum_filter, Fintype.sum_option, Fintype.sum_bool]
    cases b <;> simp [hG]
  have hpushC : ∀ ω, (fun e (o' : Option Unit) =>
      ∑ o ∈ univ.filter (fun o : Option Bool => cand o = o'), G ω e o) =
      fun e => bern (y e (ω e)) := by
    intro ω
    funext e o'
    rw [sum_filter, Fintype.sum_option, Fintype.sum_bool]
    cases o' <;> simp [hG, hcand, bern]
  -- The users' total utility given the values, and SDH's welfare given the values.
  set U : (I × J → ℝ × ℝ) → ℝ := fun ω =>
    (∑ i, prodExp (fun e => bern (y e (ω e))) (fun η =>
      prodExp (fun j T => ψ1 j (colC η j) T) fun T =>
        prodExp (fun i' T' => ψ2 i' (univ.filter fun j => i' ∈ T j) T') fun T' =>
          ∑ j ∈ T' i, M.wI (i, j) (ω (i, j)))) +
    ∑ j, prodExp (fun e => bern (y e (ω e))) (fun η =>
      prodExp (fun j' T => ψ1 j' (colC η j') T) fun T =>
        prodExp (fun i' T' => ψ2 i' (univ.filter fun j' => i' ∈ T j') T') fun T' =>
          ∑ i ∈ univ.filter (fun i => j ∈ T' i), M.wJ (i, j) (ω (i, j))) with hU
  set V : (I × J → ℝ × ℝ) → ℝ := fun ω =>
    prodExp (fun e b => if b then M.foundP τ e (ω e) else 1 - M.foundP τ e (ω e))
      (fun b => M.capsMarket.bestMatch (univ.filter fun e => b e = true)
        (fun e => M.wI e (ω e) + M.wJ e (ω e))) with hV
  have hUV : ∀ ω, U ω ≤ V ω := fun ω => by
    set Φ : (I × J → Option Unit) → ℝ := fun η =>
      (∑ i, prodExp (fun j T => ψ1 j (colC η j) T) fun T =>
        prodExp (fun i' T' => ψ2 i' (univ.filter fun j => i' ∈ T j) T') fun T' =>
          ∑ j ∈ T' i, M.wI (i, j) (ω (i, j))) +
      ∑ j, prodExp (fun j' T => ψ1 j' (colC η j') T) fun T =>
        prodExp (fun i' T' => ψ2 i' (univ.filter fun j' => i' ∈ T j') T') fun T' =>
          ∑ i ∈ univ.filter (fun i => j ∈ T' i), M.wJ (i, j) (ω (i, j)) with hΦ
    set Ψ : (I × J → Bool) → ℝ := fun b => M.capsMarket.bestMatch
      (univ.filter fun e => b e = true) (fun e => M.wI e (ω e) + M.wJ e (ω e)) with hΨ
    have hU' : U ω = prodExp (G ω) (fun o => Φ (fun e => cand (o e))) := by
      rw [prodExp_map (G ω) (fun _ => cand) Φ, hpushC ω, hΦ, prodExp_add, prodExp_sum,
        prodExp_sum]
    have hV' : V ω = prodExp (G ω) (fun o => Ψ (fun e => (o e).isSome)) := by
      rw [prodExp_map (G ω) (fun _ o => o.isSome) Ψ, hpushF ω]
    rw [hU', hV']
    refine prodExp_mono (hG0 ω) fun o => ?_
    refine rules_le_bestMatch hr1 hr2 (fun e => cand (o e)) _ (fun e he => ?_)
      (fun e => M.wI e (ω e)) (fun e => M.wJ e (ω e))
    simp only [mem_filter, mem_univ, true_and]
    by_cases h : o e = some true
    · simp [h]
    · simp [hcand, h] at he
  -- Integrability.
  have hW : ∀ e, Integrable (fun s => M.wI e s + M.wJ e s) (M.μ e) := fun e =>
    (integrable_wI hM e).add (integrable_wJ hM e)
  have hWm : ∀ e, Measurable (fun s : ℝ × ℝ => M.wI e s + M.wJ e s) := fun e => by
    unfold wI wJ
    fun_prop
  have hAccm : ∀ e, MeasurableSet {s : ℝ × ℝ | M.Acc e s} := fun e =>
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const measurable_snd)
  have hfm : ∀ e, Measurable (M.foundP τ e) := fun e =>
    Measurable.ite (hAccm e) measurable_const measurable_const
  have hVint : Integrable V (Measure.pi M.μ) := by
    have hbound : Integrable (fun ω : I × J → ℝ × ℝ => ∑ e, |M.wI e (ω e) + M.wJ e (ω e)|)
        (Measure.pi M.μ) :=
      integrable_finsetSum _ fun e _ =>
        ((measurePreserving_eval M.μ e).integrable_comp_of_integrable (hW e)).abs
    refine hbound.mono' ?_ (ae_of_all _ fun ω => ?_)
    · refine Measurable.aestronglyMeasurable ?_
      simp only [hV, prodExp]
      refine Finset.measurable_sum _ fun b _ => Measurable.mul ?_ ?_
      · refine Finset.measurable_prod _ fun e _ => ?_
        cases b e
        · exact (measurable_const.sub (hfm e)).comp (measurable_pi_apply e)
        · exact (hfm e).comp (measurable_pi_apply e)
      · exact measurable_bestMatch_caps _ fun e => (hWm e).comp (measurable_pi_apply e)
    · have hd : ∀ e, (∑ b : Bool, if b then M.foundP τ e (ω e) else 1 - M.foundP τ e (ω e)) = 1 :=
        fun e => by simp
      have hn : ∀ e (b : Bool), 0 ≤ (if b then M.foundP τ e (ω e) else 1 - M.foundP τ e (ω e)) :=
        fun e b => by cases b <;> simp <;> linarith [hf01 e (ω e)]
      have h0 : 0 ≤ V ω := prodExp_nonneg hn fun b => bestMatch_caps_nonneg _ _
      have h1 : V ω ≤ ∑ e, |M.wI e (ω e) + M.wJ e (ω e)| :=
        (prodExp_mono hn fun b => bestMatch_caps_le _ _).trans_eq (prodExp_const hd _)
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact h1
  have hUint : Integrable U (Measure.pi M.μ) :=
    (integrable_finsetSum _ fun i _ => integrable_contUtilI hM hy hr1 hr2 i).add
      (integrable_finsetSum _ fun j _ => integrable_contUtilJ hM hy hr1 hr2 j)
  calc cK K ^ 2 * (∑ i, M.lpSurplusI y i + ∑ j, M.lpSurplusJ y j)
      ≤ ∑ i, M.contUtilI y ψ1 ψ2 i + ∑ j, M.contUtilJ y ψ1 ψ2 j := by
        rw [mul_add, mul_sum, mul_sum]
        exact add_le_add (sum_le_sum fun i _ => hI i) (sum_le_sum fun j _ => hJ j)
    _ = ∫ ω, U ω ∂(Measure.pi M.μ) := by
        simp only [hU]
        rw [integral_add (integrable_finsetSum _ fun i _ => integrable_contUtilI hM hy hr1 hr2 i)
            (integrable_finsetSum _ fun j _ => integrable_contUtilJ hM hy hr1 hr2 j),
          integral_finsetSum _ fun i _ => integrable_contUtilI hM hy hr1 hr2 i,
          integral_finsetSum _ fun j _ => integrable_contUtilJ hM hy hr1 hr2 j]
        rfl
    _ ≤ ∫ ω, V ω ∂(Measure.pi M.μ) := integral_mono hUint hVint hUV
    _ = M.contSDHValue τ := rfl

end MaxWeight

/-! ### The benchmark -/

/-- **A budgeted screened policy**, described by `q e ω` and `m e ω`, the chances that it
queries and matches `e` given all values `ω`. It matches only queried acceptable pairs,
its expected matches given `ω` are within caps, its expected calls are within budget, and
it is non-anticipating: `q e` does not depend on `e`'s own values. Every randomized adaptive
policy has such `q` and `m`. -/
def IsContPolicy (QI : I → ℝ) (QJ : J → ℝ) (q m : I × J → (I × J → ℝ × ℝ) → ℝ) : Prop :=
  (∀ e, Measurable (q e)) ∧ (∀ e, Measurable (m e)) ∧
    (∀ e ω, 0 ≤ m e ω ∧ m e ω ≤ q e ω ∧ q e ω ≤ 1) ∧
    (∀ e ω, ¬ M.Acc e (ω e) → m e ω = 0) ∧
    (∀ ω i, ∑ j, m (i, j) ω ≤ M.capI i) ∧ (∀ ω j, ∑ i, m (i, j) ω ≤ M.capJ j) ∧
    (∀ e ω s, q e (Function.update ω e s) = q e ω) ∧
    (∀ i, ∫ ω, ∑ j, q (i, j) ω * M.chargeI (i, j) (ω (i, j)) ∂(Measure.pi M.μ) ≤ QI i) ∧
    ∀ j, ∫ ω, ∑ i, q (i, j) ω * M.chargeJ (i, j) (ω (i, j)) ∂(Measure.pi M.μ) ≤ QJ j

/-- `i`'s expected utility under the policy. -/
noncomputable def polUtilI (m : I × J → (I × J → ℝ × ℝ) → ℝ) (i : I) : ℝ :=
  ∫ ω, ∑ j, m (i, j) ω * M.wI (i, j) (ω (i, j)) ∂(Measure.pi M.μ)

/-- `j`'s expected utility under the policy. -/
noncomputable def polUtilJ (m : I × J → (I × J → ℝ × ℝ) → ℝ) (j : J) : ℝ :=
  ∫ ω, ∑ i, m (i, j) ω * M.wJ (i, j) (ω (i, j)) ∂(Measure.pi M.μ)

/-- **Theorem Q(e).** Every budgeted screened policy induces a feasible plan that gives
every user exactly its expected utility under the policy: `τ e = E[q e]` and
`y e s = E[m e (ω with ω e := s)]`. -/
theorem exists_contPlan_of_policy (hM : M.Regular) {QI : I → ℝ} {QJ : J → ℝ}
    {q m : I × J → (I × J → ℝ × ℝ) → ℝ} (hP : M.IsContPolicy QI QJ q m) :
    ∃ y τ, M.ContFeasible QI QJ y τ ∧ (∀ i, M.lpSurplusI y i = M.polUtilI m i) ∧
      ∀ j, M.lpSurplusJ y j = M.polUtilJ m j := by
  obtain ⟨hqm, hmm, hmq, hacc, hcapI, hcapJ, hna, hbI, hbJ⟩ := hP
  have := hM.1
  have hm01 : ∀ e ω, 0 ≤ m e ω ∧ m e ω ≤ 1 := fun e ω =>
    ⟨(hmq e ω).1, (hmq e ω).2.1.trans (hmq e ω).2.2⟩
  have hq01 : ∀ e ω, 0 ≤ q e ω ∧ q e ω ≤ 1 := fun e ω =>
    ⟨(hmq e ω).1.trans (hmq e ω).2.1, (hmq e ω).2.2⟩
  -- Bounded measurable functions of all values are integrable.
  have hbdd : ∀ {h : (I × J → ℝ × ℝ) → ℝ}, Measurable h → (∀ ω, 0 ≤ h ω ∧ h ω ≤ 1) →
      Integrable h (Measure.pi M.μ) := fun hh h01 =>
    (integrable_const (1 : ℝ)).mono' hh.aestronglyMeasurable (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h01 ω])
  have hupd : ∀ e (s : ℝ × ℝ), Measurable fun ω : I × J → ℝ × ℝ => Function.update ω e s :=
    fun e s => measurable_update'.comp (measurable_id.prodMk measurable_const)
  -- The plan: `τ e = E[q e]`, `y e s = E[m e (ω with ω e := s)]`.
  set τ : I × J → ℝ := fun e => ∫ ω, q e ω ∂(Measure.pi M.μ) with hτ
  set y : I × J → ℝ × ℝ → ℝ := fun e s => ∫ ω, m e (Function.update ω e s) ∂(Measure.pi M.μ)
    with hy
  have hym : ∀ e, Measurable (y e) := fun e => by
    have hs : StronglyMeasurable (Function.uncurry fun (s : ℝ × ℝ) (ω : I × J → ℝ × ℝ) =>
        m e (Function.update ω e s)) :=
      ((hmm e).comp (measurable_update'.comp measurable_swap)).stronglyMeasurable
    exact (hs.integral_prod_right (ν := Measure.pi M.μ)).measurable
  -- Resampling: `E[m e (ω) f (ω e)] = ∫ f · y e` and `E[q e (ω) f (ω e)] = τ e ∫ f`.
  have hres : ∀ e {f : ℝ × ℝ → ℝ}, Integrable f (M.μ e) →
      ∫ ω, m e ω * f (ω e) ∂(Measure.pi M.μ) = ∫ s, f s * y e s ∂(M.μ e) := fun e f hf =>
    integral_mul_coord_eq M.μ e (hmm e) (hm01 e) hf
  have hresq : ∀ e {f : ℝ × ℝ → ℝ}, Integrable f (M.μ e) →
      ∫ ω, q e ω * f (ω e) ∂(Measure.pi M.μ) = τ e * ∫ s, f s ∂(M.μ e) := fun e f hf => by
    rw [integral_mul_coord_eq M.μ e (hqm e) (hq01 e) hf]
    simp only [hna]
    rw [integral_mul_const, mul_comm]
  have hint_m : ∀ e {f : ℝ × ℝ → ℝ}, Integrable f (M.μ e) →
      Integrable (fun ω : I × J → ℝ × ℝ => m e ω * f (ω e)) (Measure.pi M.μ) := fun e f hf =>
    ((measurePreserving_eval M.μ e).integrable_comp_of_integrable hf).bdd_mul
      (hmm e).aestronglyMeasurable (c := 1)
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hm01 e ω])
  have hint_q : ∀ e {f : ℝ × ℝ → ℝ}, Integrable f (M.μ e) →
      Integrable (fun ω : I × J → ℝ × ℝ => q e ω * f (ω e)) (Measure.pi M.μ) := fun e f hf =>
    ((measurePreserving_eval M.μ e).integrable_comp_of_integrable hf).bdd_mul
      (hqm e).aestronglyMeasurable (c := 1)
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hq01 e ω])
  have hone : ∀ e, Integrable (fun _ : ℝ × ℝ => (1 : ℝ)) (M.μ e) := fun e => integrable_const 1
  -- Expected matches and calls.
  have hmatch : ∀ e, ∫ s, y e s ∂(M.μ e) = ∫ ω, m e ω ∂(Measure.pi M.μ) := fun e => by
    have := hres e (hone e)
    simp only [mul_one, one_mul] at this
    exact this.symm
  have hchI : ∀ e, Integrable (M.chargeI e) (M.μ e) := fun e =>
    (integrable_const (1 : ℝ)).mono' (M.measurable_chargeI e).aestronglyMeasurable
      (ae_of_all _ fun s => by
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [M.chargeI_mem e s])
  have hchJ : ∀ e, Integrable (M.chargeJ e) (M.μ e) := fun e =>
    (integrable_const (1 : ℝ)).mono' (M.measurable_chargeJ e).aestronglyMeasurable
      (ae_of_all _ fun s => by
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [M.chargeJ_mem e s])
  have hcI : ∀ e, M.callsI τ e = ∫ ω, q e ω * M.chargeI e (ω e) ∂(Measure.pi M.μ) := fun e => by
    rw [hresq e (hchI e), M.integral_chargeI hM]
    rfl
  have hcJ : ∀ e, M.callsJ τ e = ∫ ω, q e ω * M.chargeJ e (ω e) ∂(Measure.pi M.μ) := fun e => by
    rw [hresq e (hchJ e), M.integral_chargeJ hM]
    rfl
  have hmI : ∀ e, Integrable (m e) (Measure.pi M.μ) := fun e => hbdd (hmm e) (hm01 e)
  refine ⟨y, τ, ⟨hym, fun e s => ⟨?_, ?_⟩, fun e => ?_, fun e s hs => ?_, fun i => ?_,
    fun j => ?_, fun i => ?_, fun j => ?_⟩, fun i => ?_, fun j => ?_⟩
  · exact integral_nonneg fun ω => (hm01 e _).1
  · exact integral_mono (hbdd ((hmm e).comp (hupd e s)) fun ω => hm01 e _)
      (hbdd (hqm e) (hq01 e)) fun ω => ((hmq e _).2.1).trans_eq (hna e ω s)
  · calc τ e ≤ ∫ _, (1 : ℝ) ∂(Measure.pi M.μ) :=
          integral_mono (hbdd (hqm e) (hq01 e)) (integrable_const 1) fun ω => (hq01 e ω).2
      _ = 1 := by simp
  · exact integral_eq_zero_of_ae (ae_of_all _ fun ω =>
      hacc e _ (by rw [Function.update_self]; exact hs))
  · calc ∑ j, ∫ s, y (i, j) s ∂(M.μ (i, j)) = ∑ j, ∫ ω, m (i, j) ω ∂(Measure.pi M.μ) :=
          sum_congr rfl fun j _ => hmatch _
      _ = ∫ ω, ∑ j, m (i, j) ω ∂(Measure.pi M.μ) :=
          (integral_finsetSum _ fun j _ => hmI _).symm
      _ ≤ ∫ _, (M.capI i : ℝ) ∂(Measure.pi M.μ) :=
          integral_mono (integrable_finsetSum _ fun j _ => hmI _) (integrable_const _)
            fun ω => hcapI ω i
      _ = M.capI i := by simp
  · calc ∑ i, ∫ s, y (i, j) s ∂(M.μ (i, j)) = ∑ i, ∫ ω, m (i, j) ω ∂(Measure.pi M.μ) :=
          sum_congr rfl fun i _ => hmatch _
      _ = ∫ ω, ∑ i, m (i, j) ω ∂(Measure.pi M.μ) :=
          (integral_finsetSum _ fun i _ => hmI _).symm
      _ ≤ ∫ _, (M.capJ j : ℝ) ∂(Measure.pi M.μ) :=
          integral_mono (integrable_finsetSum _ fun i _ => hmI _) (integrable_const _)
            fun ω => hcapJ ω j
      _ = M.capJ j := by simp
  · calc ∑ j, M.callsI τ (i, j) =
          ∑ j, ∫ ω, q (i, j) ω * M.chargeI (i, j) (ω (i, j)) ∂(Measure.pi M.μ) :=
          sum_congr rfl fun j _ => hcI _
      _ = ∫ ω, ∑ j, q (i, j) ω * M.chargeI (i, j) (ω (i, j)) ∂(Measure.pi M.μ) :=
          (integral_finsetSum _ fun j _ => hint_q _ (hchI _)).symm
      _ ≤ QI i := hbI i
  · calc ∑ i, M.callsJ τ (i, j) =
          ∑ i, ∫ ω, q (i, j) ω * M.chargeJ (i, j) (ω (i, j)) ∂(Measure.pi M.μ) :=
          sum_congr rfl fun i _ => hcJ _
      _ = ∫ ω, ∑ i, q (i, j) ω * M.chargeJ (i, j) (ω (i, j)) ∂(Measure.pi M.μ) :=
          (integral_finsetSum _ fun i _ => hint_q _ (hchJ _)).symm
      _ ≤ QJ j := hbJ j
  · unfold lpSurplusI polUtilI
    rw [integral_finsetSum _ fun j _ => hint_m _ (integrable_wI hM _)]
    exact sum_congr rfl fun j _ => (hres _ (integrable_wI hM _)).symm
  · unfold lpSurplusJ polUtilJ
    rw [integral_finsetSum _ fun i _ => hint_m _ (integrable_wJ hM _)]
    exact sum_congr rfl fun i _ => (hres _ (integrable_wJ hM _)).symm

/-! ### Objectives -/

/-- A plan within `ε` of the best feasible plan for objective `W`. -/
def IsContOptimal (QI : I → ℝ) (QJ : J → ℝ) (W : (I ⊕ J → ℝ) → ℝ) (ε : ℝ)
    (y : I × J → ℝ × ℝ → ℝ) (τ : I × J → ℝ) : Prop :=
  M.ContFeasible QI QJ y τ ∧
    ∀ y' τ', M.ContFeasible QI QJ y' τ' → W (M.lpVec y') ≤ W (M.lpVec y) + ε

/-- **Theorem Q(f), core.** If the mechanism gives every user at least `γ` times its
planned surplus, then for a monotone, homogeneous objective it gets `γ (W(P) - ε)` against
every budgeted screened policy `P`, when run on an `ε`-optimal plan. -/
theorem cont_objective_of_perUser (hM : M.Regular) {W : (I ⊕ J → ℝ) → ℝ}
    (hW : ScreenedMarket.IsMonoHom W) {QI : I → ℝ} {QJ : J → ℝ} {ε : ℝ}
    {y : I × J → ℝ × ℝ → ℝ} {τ : I × J → ℝ} (hopt : M.IsContOptimal QI QJ W ε y τ)
    {γ : ℝ} (hγ : 0 ≤ γ) {u : I ⊕ J → ℝ} (hu : ∀ ℓ, γ * M.lpVec y ℓ ≤ u ℓ)
    {q m : I × J → (I × J → ℝ × ℝ) → ℝ} (hP : M.IsContPolicy QI QJ q m) :
    γ * (W (Sum.elim (M.polUtilI m) (M.polUtilJ m)) - ε) ≤ W u := by
  obtain ⟨y', τ', hq', hI, hJ⟩ := M.exists_contPlan_of_policy hM hP
  have hvec : Sum.elim (M.polUtilI m) (M.polUtilJ m) = M.lpVec y' := by
    funext ℓ
    cases ℓ with
    | inl i => exact (hI i).symm
    | inr j => exact (hJ j).symm
  have h1 : W (M.lpVec y') - ε ≤ W (M.lpVec y) := by linarith [hopt.2 y' τ' hq']
  have h2 : γ * W (M.lpVec y) ≤ W u := by
    rw [← hW.2 γ _ hγ]
    exact hW.1 _ _ fun ℓ => by simpa only [Pi.smul_apply, smul_eq_mul] using hu ℓ
  rw [hvec]
  exact (mul_le_mul_of_nonneg_left h1 hγ).trans h2

/-- **Theorem Q(f) with random order:** `W(Q-SDH) ≥ (W(P) - ε) / 4`. -/
theorem cont_objective_quarter (hM : M.Regular) {W : (I ⊕ J → ℝ) → ℝ}
    (hW : ScreenedMarket.IsMonoHom W) {QI : I → ℝ} {QJ : J → ℝ} {ε : ℝ}
    {y : I × J → ℝ × ℝ → ℝ} {τ : I × J → ℝ} (hopt : M.IsContOptimal QI QJ W ε y τ)
    {q m : I × J → (I × J → ℝ × ℝ) → ℝ} (hP : M.IsContPolicy QI QJ q m) :
    (W (Sum.elim (M.polUtilI m) (M.polUtilJ m)) - ε) / 4 ≤
      W (Sum.elim (M.contUtilI y (fun j => uniformRule (M.capJ j))
          (fun i => uniformRule (M.capI i)))
        (M.contUtilJ y (fun j => uniformRule (M.capJ j)) (fun i => uniformRule (M.capI i)))) := by
  obtain ⟨hI, hJ⟩ := M.contUtil_quarter hM hopt.1
  have := M.cont_objective_of_perUser hM hW hopt (γ := 1 / 4) (by norm_num)
    (u := Sum.elim (M.contUtilI y (fun j => uniformRule (M.capJ j))
      (fun i => uniformRule (M.capI i)))
      (M.contUtilJ y (fun j => uniformRule (M.capJ j)) (fun i => uniformRule (M.capI i))))
    (fun ℓ => by
      cases ℓ with
      | inl i => simp only [lpVec, Sum.elim_inl]; linarith [hI i]
      | inr j => simp only [lpVec, Sum.elim_inr]; linarith [hJ j]) hP
  linarith

/-- **Theorem Q(f) with balanced rules:** `W(Q-SDH) ≥ c_K^2 (W(P) - ε)`. -/
theorem cont_objective_cK (hM : M.Regular) {W : (I ⊕ J → ℝ) → ℝ}
    (hW : ScreenedMarket.IsMonoHom W) {QI : I → ℝ} {QJ : J → ℝ} {ε : ℝ}
    {y : I × J → ℝ × ℝ → ℝ} {τ : I × J → ℝ} (hopt : M.IsContOptimal QI QJ W ε y τ)
    (K : ℕ) (hKI : ∀ i, K ≤ M.capI i) (hKJ : ∀ j, K ≤ M.capJ j) :
    ∃ ψ1 : J → Finset I → Finset I → ℝ, ∃ ψ2 : I → Finset J → Finset J → ℝ,
      (∀ j, IsRule (M.capJ j) (ψ1 j)) ∧ (∀ i, IsRule (M.capI i) (ψ2 i)) ∧
      ∀ q m, M.IsContPolicy QI QJ q m →
        cK K ^ 2 * (W (Sum.elim (M.polUtilI m) (M.polUtilJ m)) - ε) ≤
          W (Sum.elim (M.contUtilI y ψ1 ψ2) (M.contUtilJ y ψ1 ψ2)) := by
  obtain ⟨ψ1, ψ2, h1, h2, hI, hJ⟩ := M.contUtil_cK hM hopt.1 K hKI hKJ
  refine ⟨ψ1, ψ2, h1, h2, fun q m hP =>
    M.cont_objective_of_perUser hM hW hopt (sq_nonneg _) (fun ℓ => ?_) hP⟩
  cases ℓ with
  | inl i => simpa only [lpVec, Sum.elim_inl] using hI i
  | inr j => simpa only [lpVec, Sum.elim_inr] using hJ j

end ContMarket

end DatingAlgo
