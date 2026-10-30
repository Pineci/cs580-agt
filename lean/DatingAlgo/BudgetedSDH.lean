import DatingAlgo.MaxMinSDH

/-!
# Query budgets in screened DH

Theorem Q of the vault note "Query Budgets in Screened DH", for finitely many value
combinations per pair (the market of `ScreenedDH.lean`). `ContinuousSDH.lean` proves the
algorithm's guarantees and the benchmark for priors with finite means, continuous ones
included.

**The plan.** SDH's query probability is `τ_e = max_c x_{e,c} / π_{e,c}`, fixed by the plan.
The query-aware plan (`QFeasible`) makes `τ` a variable: `x e c ≤ τ e · π e c`, and each
user's expected calls (`callsI`, `callsJ`: the side less likely to accept is asked first,
the other side only after a yes) are within its budget (`BudgetOK`).

**Results.**
* `qsdh_calls` (Q(b)): querying each pair with probability `τ e` charges each user an
  expected `∑ callsI τ`, which the budget bounds.
* `qsdh_welfare`, `qsdh_quarter`, `qsdh_cK` (Q(c), Q(d)): SDH's and MM-SDH's guarantees
  hold for every query-aware plan, because `lpValue_le_sdhValue`, `mmsdh_quarter` and
  `mmsdh_cK` only need `x ≤ τ π`.
* `IsBudgetedPolicy`: a policy given by the law of its (queried, matched) sets given all
  combinations. It matches only queried acceptable pairs within caps, stays within budget,
  and is *non-anticipating*: the chance it queries `e` does not depend on `e`'s own
  combination. `isBudgetedPolicy_of_trees`: every random mixture of adaptive query trees
  (`QTree`) is non-anticipating.
* `exists_qplan_of_policy` (Q(e)): every budgeted policy induces a feasible query-aware
  plan with the policy's expected surplus for every user.
* `qsdh_objective` (Q(f)): for every objective `W` of the users' expected utilities that
  is monotone and positively homogeneous (`IsMonoHom`), Q-SDH run on an `ε`-optimal plan
  gets `γ (W(policy) - ε)` against every budgeted policy, where `γ` is the per-user factor:
  `1/4` with random order (`qsdh_objective_quarter`), `c_K^2` with balanced rules
  (`qsdh_objective_cK`). `isMonoHom_inf'` covers max-min over any nonempty set of users,
  for example the users who can match at all; `isMonoHom_weightedInf` covers max-min of
  normalized utilities; `isMonoHom_weightedSum` covers weighted welfare.
* `qfeasible_scaled`: Theorem 3(d)'s scaled plan is feasible, so the query-aware plan is
  never worse than scaling.

**Truthfulness (Q(a)).** Q-SDH shows each user a capped set of acceptable partners chosen
from oracle answers and coins, so `sdh_dsic` (`TruthfulSwiping.lean`) applies unchanged.
-/

namespace DatingAlgo

open Finset

/-! ### Resampling one coordinate -/

section Resample

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
/-- **Resampling one coordinate.** Redrawing coordinate `e` from its own law, independently
of everything else, leaves every expectation unchanged. -/
theorem prodExp_update {μ : ι → Ω → ℝ} (hμ : ∀ k, ∑ o, μ k o = 1) (e : ι)
    (G : (ι → Ω) → ℝ) :
    prodExp μ G = ∑ o, μ e o * prodExp μ (fun ω => G (Function.update ω e o)) := by
  -- Split `ω` into its `e`-coordinate `a` and the rest `r`.
  set S := Equiv.funSplitAt e Ω
  have hsum : ∀ F : (ι → Ω) → ℝ, ∑ ω, F ω = ∑ a, ∑ r, F (S.symm (a, r)) := fun F => by
    rw [← Fintype.sum_prod_type' (f := fun a r => F (S.symm (a, r)))]
    exact (Equiv.sum_comp S.symm F).symm
  have hval : ∀ a r, S.symm (a, r) e = a := fun a r => by
    simp [S, Equiv.funSplitAt, Equiv.piSplitAt]
  have hval' : ∀ a r (k : {j // j ≠ e}), S.symm (a, r) k = r k := fun a r k => by
    simp [S, Equiv.funSplitAt, Equiv.piSplitAt, k.2]
  have hprod : ∀ a r, ∏ k, μ k (S.symm (a, r) k) =
      μ e a * ∏ k : {j // j ≠ e}, μ k (r k) := fun a r => by
    rw [← mul_prod_erase univ _ (mem_univ e), hval,
      prod_subtype (univ.erase e) (p := fun j => j ≠ e) (fun j => by simp)]
    exact congrArg _ (prod_congr rfl fun k _ => by rw [hval'])
  have hupd : ∀ a r o, Function.update (S.symm (a, r)) e o = S.symm (o, r) := fun a r o => by
    funext k
    by_cases hk : k = e
    · subst hk
      rw [Function.update_self, hval]
    · rw [Function.update_of_ne hk, hval' a r ⟨k, hk⟩, hval' o r ⟨k, hk⟩]
  unfold prodExp
  rw [hsum]
  refine sum_congr rfl fun o _ => ?_
  rw [hsum]
  simp only [hupd, hprod]
  have hrest : ∀ a, ∑ r : {j // j ≠ e} → Ω, μ e a * (∏ k : {j // j ≠ e}, μ k (r k)) *
      G (S.symm (o, r)) = μ e a * ∑ r : {j // j ≠ e} → Ω,
        (∏ k : {j // j ≠ e}, μ k (r k)) * G (S.symm (o, r)) := fun a => by
    rw [mul_sum]
    exact sum_congr rfl fun r _ => by ring
  rw [hrest o]
  simp only [hrest]
  rw [← sum_mul, hμ e, one_mul]

omit [DecidableEq Ω] in
/-- A factor that never looks at coordinate `e` separates from one that only does. -/
theorem prodExp_mul_coord_of_blind {μ : ι → Ω → ℝ} (hμ : ∀ k, ∑ o, μ k o = 1) (e : ι)
    {g : (ι → Ω) → ℝ} (hg : ∀ ω o, g (Function.update ω e o) = g ω) (f : Ω → ℝ) :
    prodExp μ (fun ω => g ω * f (ω e)) = prodExp μ g * ∑ o, μ e o * f o := by
  rw [prodExp_update hμ e]
  simp only [hg, Function.update_self]
  rw [mul_sum]
  refine sum_congr rfl fun o _ => ?_
  rw [prodExp_congr μ (fun ω => mul_comm (g ω) (f o)), prodExp_const_mul]
  ring

end Resample

namespace ScreenedMarket

variable {I J C : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype C] [DecidableEq C] (M : ScreenedMarket I J C)

/-! ### The query-aware plan -/

/-- Every user's expected calls are within its budget. -/
def BudgetOK (QI : I → ℝ) (QJ : J → ℝ) (τ : I × J → ℝ) : Prop :=
  (∀ i, ∑ j, M.callsI τ (i, j) ≤ QI i) ∧ ∀ j, ∑ i, M.callsJ τ (i, j) ≤ QJ j

/-- Feasible plans of the query-aware program: an SDH plan `x`, query probabilities `τ`
that find each combination at least as often as `x` uses it, and the budgets. -/
def QFeasible (QI : I → ℝ) (QJ : J → ℝ) (x : I × J → C → ℝ) (τ : I × J → ℝ) : Prop :=
  M.LPFeasible x ∧ (∀ e, 0 ≤ τ e ∧ τ e ≤ 1) ∧ (∀ e c, x e c ≤ τ e * M.π e c) ∧
    M.BudgetOK QI QJ τ

/-! ### Calls -/

/-- Calls charged to `i` when pair `e` is queried and has combination `c`: one if `i` is
asked first, otherwise one exactly when `j` said yes. -/
noncomputable def chargeI (e : I × J) (c : C) : ℝ :=
  if M.phiI e ≤ M.phiJ e then 1 else if M.costJ e.2 < M.valJ e c then 1 else 0

/-- Calls charged to `j` when pair `e` is queried and has combination `c`. -/
noncomputable def chargeJ (e : I × J) (c : C) : ℝ :=
  if M.phiI e ≤ M.phiJ e then (if M.costI e.1 < M.valI e c then 1 else 0) else 1

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [DecidableEq C] in
theorem sum_π_chargeI (hπ : IsDist M.π) (e : I × J) (t : ℝ) :
    t * ∑ c, M.π e c * M.chargeI e c = M.callsI (fun _ => t) e := by
  unfold chargeI callsI
  by_cases h : M.phiI e ≤ M.phiJ e
  · simp only [h, ↓reduceIte, mul_one, hπ.2 e]
  · simp only [h, ↓reduceIte, mul_ite, mul_one, mul_zero]
    rw [← sum_filter]
    rfl

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [DecidableEq C] in
theorem sum_π_chargeJ (hπ : IsDist M.π) (e : I × J) (t : ℝ) :
    t * ∑ c, M.π e c * M.chargeJ e c = M.callsJ (fun _ => t) e := by
  unfold chargeJ callsJ
  by_cases h : M.phiI e ≤ M.phiJ e
  · simp only [h, ↓reduceIte, mul_ite, mul_one, mul_zero]
    rw [← sum_filter]
    rfl
  · simp only [h, ↓reduceIte, mul_one, hπ.2 e]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [DecidableEq C] in
/-- The screening law is a probability law on (combination, queried?). -/
theorem sum_screenLaw (hπ : IsDist M.π) (τ : I × J → ℝ) (e : I × J) :
    ∑ o, M.screenLaw τ e o = 1 := by
  simp only [screenLaw, Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte,
    Bool.false_eq_true, ← mul_add, add_sub_cancel, mul_one, hπ.2 e]

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [DecidableEq C] in
/-- One pair's expected charge: `τ e` times the charge of a query. -/
theorem sum_screenLaw_chargeI (hπ : IsDist M.π) (τ : I × J → ℝ) (e : I × J) :
    ∑ o, M.screenLaw τ e o * (if o.2 then M.chargeI e o.1 else 0) = M.callsI τ e := by
  rw [show M.callsI τ e = M.callsI (fun _ => τ e) e from rfl, ← M.sum_π_chargeI hπ e (τ e),
    mul_sum]
  simp only [screenLaw, Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte,
    Bool.false_eq_true, mul_zero, add_zero]
  exact sum_congr rfl fun c _ => by ring

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] [DecidableEq C] in
theorem sum_screenLaw_chargeJ (hπ : IsDist M.π) (τ : I × J → ℝ) (e : I × J) :
    ∑ o, M.screenLaw τ e o * (if o.2 then M.chargeJ e o.1 else 0) = M.callsJ τ e := by
  rw [show M.callsJ τ e = M.callsJ (fun _ => τ e) e from rfl, ← M.sum_π_chargeJ hπ e (τ e),
    mul_sum]
  simp only [screenLaw, Fintype.sum_prod_type, Fintype.sum_bool, ↓reduceIte,
    Bool.false_eq_true, mul_zero, add_zero]
  exact sum_congr rfl fun c _ => by ring

/-- **Theorem Q(b) for `i`.** Querying each pair independently with probability `τ e`
charges `i` an expected `∑_j callsI τ (i, j)` calls. -/
theorem qsdh_callsI (hπ : IsDist M.π) (τ : I × J → ℝ) (i : I) :
    prodExp (M.screenLaw τ) (fun ω => ∑ j,
      if (ω (i, j)).2 then M.chargeI (i, j) (ω (i, j)).1 else 0) = ∑ j, M.callsI τ (i, j) := by
  rw [prodExp_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [prodExp_coord (M.sum_screenLaw hπ τ) (i, j)
    (fun o => if o.2 then M.chargeI (i, j) o.1 else 0)]
  exact M.sum_screenLaw_chargeI hπ τ (i, j)

/-- **Theorem Q(b) for `j`.** -/
theorem qsdh_callsJ (hπ : IsDist M.π) (τ : I × J → ℝ) (j : J) :
    prodExp (M.screenLaw τ) (fun ω => ∑ i,
      if (ω (i, j)).2 then M.chargeJ (i, j) (ω (i, j)).1 else 0) = ∑ i, M.callsJ τ (i, j) := by
  rw [prodExp_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [prodExp_coord (M.sum_screenLaw hπ τ) (i, j)
    (fun o => if o.2 then M.chargeJ (i, j) o.1 else 0)]
  exact M.sum_screenLaw_chargeJ hπ τ (i, j)

/-! ### The algorithm's guarantees -/

variable {QI : I → ℝ} {QJ : J → ℝ}

/-- **Theorem Q(d), discrete.** SDH's max-weight selection, run with a query-aware plan,
earns at least `c_K^2` times the plan's value. -/
theorem qsdh_welfare (hπ : IsDist M.π) {x : I × J → C → ℝ} {τ : I × J → ℝ}
    (hq : M.QFeasible QI QJ x τ) (K : ℕ) (hKI : ∀ i, K ≤ M.capI i) (hKJ : ∀ j, K ≤ M.capJ j) :
    cK K ^ 2 * M.lpValue x ≤ M.sdhValue τ :=
  M.lpValue_le_sdhValue hπ hq.1 hq.2.1 hq.2.2.1 K hKI hKJ

/-- **Theorem Q(c) with random order.** Every user gets at least a quarter of its planned
surplus. -/
theorem qsdh_quarter (hπ : IsDist M.π) {x : I × J → C → ℝ} {τ : I × J → ℝ}
    (hq : M.QFeasible QI QJ x τ) :
    (∀ i, M.lpSurplusI x i / 4 ≤ M.mmUtilI x τ (fun j => uniformRule (M.capJ j))
      (fun i => uniformRule (M.capI i)) i) ∧
    ∀ j, M.lpSurplusJ x j / 4 ≤ M.mmUtilJ x τ (fun j => uniformRule (M.capJ j))
      (fun i => uniformRule (M.capI i)) j :=
  M.mmsdh_quarter hπ hq.1 hq.2.1 hq.2.2.1

/-- **Theorem Q(c) with balanced rules.** Every user gets at least `c_K^2` times its
planned surplus, for `K` at most every cap. -/
theorem qsdh_cK (hπ : IsDist M.π) {x : I × J → C → ℝ} {τ : I × J → ℝ}
    (hq : M.QFeasible QI QJ x τ) (K : ℕ) (hKI : ∀ i, K ≤ M.capI i) (hKJ : ∀ j, K ≤ M.capJ j) :
    ∃ ψ1 : J → Finset I → Finset I → ℝ, ∃ ψ2 : I → Finset J → Finset J → ℝ,
      (∀ j, IsRule (M.capJ j) (ψ1 j)) ∧ (∀ i, IsRule (M.capI i) (ψ2 i)) ∧
      (∀ i, cK K ^ 2 * M.lpSurplusI x i ≤ M.mmUtilI x τ ψ1 ψ2 i) ∧
      ∀ j, cK K ^ 2 * M.lpSurplusJ x j ≤ M.mmUtilJ x τ ψ1 ψ2 j :=
  M.mmsdh_cK hπ hq.1 hq.2.1 hq.2.2.1 K hKI hKJ

omit [DecidableEq I] [DecidableEq J] [DecidableEq C] in
/-- Theorem 3(d)'s plan, `λ` times an SDH plan with SDH's query probabilities, is feasible
for the query-aware program whenever its calls fit the budgets. So the best query-aware
plan is never worse than scaling. -/
theorem qfeasible_scaled [Nonempty C] {x : I × J → C → ℝ} (hx : M.LPFeasible x) {lam : ℝ}
    (hlam : 0 ≤ lam ∧ lam ≤ 1) (hb : M.BudgetOK QI QJ (fun e => lam * M.sdhTau x e)) :
    M.QFeasible QI QJ (fun e c => lam * x e c) (fun e => lam * M.sdhTau x e) := by
  obtain ⟨hl0, hl1⟩ := hlam
  obtain ⟨h1, h2, h3, h4⟩ := hx
  have hspec := M.sdhTau_spec ⟨h1, h2, h3, h4⟩
  refine ⟨⟨fun e c => ⟨mul_nonneg hl0 (h1 e c).1, ?_⟩, fun e c hc => by simp [h2 e c hc],
    fun i => ?_, fun j => ?_⟩, fun e => ⟨mul_nonneg hl0 (hspec.1 e).1, ?_⟩,
    fun e c => ?_, hb⟩
  · calc lam * x e c ≤ 1 * x e c := mul_le_mul_of_nonneg_right hl1 (h1 e c).1
      _ ≤ M.π e c := by rw [one_mul]; exact (h1 e c).2
  · calc ∑ j, ∑ c, lam * x (i, j) c = lam * ∑ j, ∑ c, x (i, j) c := by simp only [mul_sum]
      _ ≤ 1 * M.capI i := mul_le_mul hl1 (h3 i)
          (sum_nonneg fun j _ => sum_nonneg fun c _ => (h1 _ c).1) zero_le_one
      _ = M.capI i := one_mul _
  · calc ∑ i, ∑ c, lam * x (i, j) c = lam * ∑ i, ∑ c, x (i, j) c := by simp only [mul_sum]
      _ ≤ 1 * M.capJ j := mul_le_mul hl1 (h4 j)
          (sum_nonneg fun i _ => sum_nonneg fun c _ => (h1 _ c).1) zero_le_one
      _ = M.capJ j := one_mul _
  · calc lam * M.sdhTau x e ≤ 1 * 1 := mul_le_mul hl1 (hspec.1 e).2 (hspec.1 e).1 zero_le_one
      _ = 1 := one_mul 1
  · calc lam * x e c ≤ lam * (M.sdhTau x e * M.π e c) :=
          mul_le_mul_of_nonneg_left (hspec.2 e c) hl0
      _ = lam * M.sdhTau x e * M.π e c := by ring

/-! ### Budgeted policies -/

/-- Probability that the policy queries `e`, given the combinations `ω`. `P ω (Q, S)` is
the probability that it queries the set `Q` and matches the set `S`. -/
noncomputable def queryProb (P : (I × J → C) → Finset (I × J) × Finset (I × J) → ℝ)
    (ω : I × J → C) (e : I × J) : ℝ :=
  ∑ QS, P ω QS * if e ∈ QS.1 then 1 else 0

/-- The law of the matched set alone. -/
noncomputable def matchLaw (P : (I × J → C) → Finset (I × J) × Finset (I × J) → ℝ)
    (ω : I × J → C) (S : Finset (I × J)) : ℝ :=
  ∑ Q, P ω (Q, S)

/-- `i`'s expected calls under the policy. -/
noncomputable def polCallsI (P : (I × J → C) → Finset (I × J) × Finset (I × J) → ℝ)
    (i : I) : ℝ :=
  prodExp M.π fun ω => ∑ QS, P ω QS * ∑ j,
    if (i, j) ∈ QS.1 then M.chargeI (i, j) (ω (i, j)) else 0

/-- `j`'s expected calls under the policy. -/
noncomputable def polCallsJ (P : (I × J → C) → Finset (I × J) × Finset (I × J) → ℝ)
    (j : J) : ℝ :=
  prodExp M.π fun ω => ∑ QS, P ω QS * ∑ i,
    if (i, j) ∈ QS.1 then M.chargeJ (i, j) (ω (i, j)) else 0

/-- **A budgeted screened policy.** Given all combinations `ω`, it queries `QS.1` and
matches `QS.2` with probability `P ω QS`, where:
* it matches only pairs it queried and found acceptable, within caps;
* it is *non-anticipating*: the chance that it queries `e` does not depend on `e`'s own
  combination, since a query of `e` is decided before `e`'s values are seen;
* each user's expected calls are within its budget.
Every adaptive policy has these properties (`isBudgetedPolicy_of_trees`). -/
def IsBudgetedPolicy (QI : I → ℝ) (QJ : J → ℝ)
    (P : (I × J → C) → Finset (I × J) × Finset (I × J) → ℝ) : Prop :=
  (∀ ω, (∀ QS, 0 ≤ P ω QS) ∧ ∑ QS, P ω QS = 1 ∧
    ∀ QS, P ω QS ≠ 0 → QS.2 ⊆ QS.1 ∧ M.CapOK QS.2 ∧ ∀ e ∈ QS.2, M.Acc e (ω e)) ∧
  (∀ e ω o, queryProb P (Function.update ω e o) e = queryProb P ω e) ∧
  (∀ i, M.polCallsI P i ≤ QI i) ∧ ∀ j, M.polCallsJ P j ≤ QJ j

/-- **Theorem Q(e).** Every budgeted policy induces a feasible query-aware plan that gives
every user exactly its expected surplus under the policy. -/
theorem exists_qplan_of_policy (hπ : IsDist M.π)
    {P : (I × J → C) → Finset (I × J) × Finset (I × J) → ℝ}
    (hP : M.IsBudgetedPolicy QI QJ P) :
    ∃ x τ, M.QFeasible QI QJ x τ ∧ (∀ i, M.lpSurplusI x i = M.polUtilI (matchLaw P) i) ∧
      ∀ j, M.lpSurplusJ x j = M.polUtilJ (matchLaw P) j := by
  obtain ⟨hdist, hna, hbI, hbJ⟩ := hP
  set P' := matchLaw P with hP'
  have hFI : M.IsFIPolicy P' := fun ω => by
    refine ⟨fun S => sum_nonneg fun Q _ => (hdist ω).1 _, ?_, fun S hS => ?_⟩
    · simp only [hP', matchLaw]
      rw [sum_comm, ← Fintype.sum_prod_type']
      exact (hdist ω).2.1
    · obtain ⟨Q, -, hQ⟩ := exists_ne_zero_of_sum_ne_zero hS
      obtain ⟨-, hcap, hacc⟩ := (hdist ω).2.2 (Q, S) hQ
      exact ⟨hcap, hacc⟩
  -- `m ω e`: the chance the policy matches `e`; `q ω e`: the chance it queries `e`.
  set m : (I × J → C) → I × J → ℝ := fun ω e => ∑ S, P' ω S * if e ∈ S then 1 else 0
    with hm
  set q : (I × J → C) → I × J → ℝ := fun ω e => queryProb P ω e with hqdef
  have hmQS : ∀ ω e, m ω e = ∑ QS, P ω QS * if e ∈ QS.2 then 1 else 0 := fun ω e => by
    simp only [hm, hP', matchLaw, sum_mul]
    rw [sum_comm, ← Fintype.sum_prod_type']
  have hm0 : ∀ ω e, 0 ≤ m ω e := fun ω e =>
    sum_nonneg fun S _ => mul_nonneg ((hFI ω).1 S) (by split_ifs <;> norm_num)
  have hmq : ∀ ω e, m ω e ≤ q ω e := fun ω e => by
    rw [hmQS]
    refine sum_le_sum fun QS _ => ?_
    by_cases hQS : P ω QS = 0
    · simp [hQS]
    · refine mul_le_mul_of_nonneg_left ?_ ((hdist ω).1 QS)
      by_cases h2 : e ∈ QS.2
      · simp [h2, ((hdist ω).2.2 QS hQS).1 h2]
      · simp only [h2, ↓reduceIte]
        split_ifs <;> norm_num
  have hq0 : ∀ ω e, 0 ≤ q ω e := fun ω e =>
    sum_nonneg fun QS _ => mul_nonneg ((hdist ω).1 QS) (by split_ifs <;> norm_num)
  have hq1 : ∀ ω e, q ω e ≤ 1 := fun ω e => by
    calc q ω e ≤ ∑ QS, P ω QS := sum_le_sum fun QS _ => by
          split_ifs <;> simp [(hdist ω).1 QS]
      _ = 1 := (hdist ω).2.1
  have hmacc : ∀ ω e, ¬ M.Acc e (ω e) → m ω e = 0 := fun ω e he => sum_eq_zero fun S _ => by
    by_cases heS : e ∈ S
    · have hS : P' ω S = 0 := by
        by_contra h
        exact he (((hFI ω).2.2 S h).2 e heS)
      rw [hS, zero_mul]
    · rw [ite_eq_right heS, mul_zero]
  have hrow : ∀ ω i, ∑ j, m ω (i, j) ≤ M.capI i := fun ω i => by
    calc ∑ j, m ω (i, j) = ∑ S, P' ω S * ((S.filter fun e => e.1 = i).card : ℝ) := by
          simp only [hm, card_filter_fst, mul_sum]
          exact sum_comm
      _ ≤ ∑ S, P' ω S * M.capI i := sum_le_sum fun S _ => by
          by_cases hS : P' ω S = 0
          · rw [hS, zero_mul, zero_mul]
          · exact mul_le_mul_of_nonneg_left (by exact_mod_cast ((hFI ω).2.2 S hS).1.1 i)
              ((hFI ω).1 S)
      _ = M.capI i := by rw [← sum_mul, (hFI ω).2.1, one_mul]
  have hcol : ∀ ω j, ∑ i, m ω (i, j) ≤ M.capJ j := fun ω j => by
    calc ∑ i, m ω (i, j) = ∑ S, P' ω S * ((S.filter fun e => e.2 = j).card : ℝ) := by
          simp only [hm, card_filter_snd, mul_sum]
          exact sum_comm
      _ ≤ ∑ S, P' ω S * M.capJ j := sum_le_sum fun S _ => by
          by_cases hS : P' ω S = 0
          · rw [hS, zero_mul, zero_mul]
          · exact mul_le_mul_of_nonneg_left (by exact_mod_cast ((hFI ω).2.2 S hS).1.2 j)
              ((hFI ω).1 S)
      _ = M.capJ j := by rw [← sum_mul, (hFI ω).2.1, one_mul]
  -- The plan: `x e c = Pr[e is matched and has combination c]`, `τ e = Pr[e is queried]`.
  set x : I × J → C → ℝ := fun e c => prodExp M.π fun ω => if ω e = c then m ω e else 0
    with hx
  set τ : I × J → ℝ := fun e => prodExp M.π fun ω => q ω e with hτ
  have hsum : ∀ e, ∑ c, x e c = prodExp M.π (fun ω => m ω e) := fun e => by
    simp only [hx]
    rw [← prodExp_sum]
    exact prodExp_congr _ fun ω => by simp
  have hval : ∀ e (v : C → ℝ), ∑ c, v c * x e c = prodExp M.π (fun ω => v (ω e) * m ω e) :=
    fun e v => by
      simp only [hx]
      simp_rw [← prodExp_const_mul]
      rw [← prodExp_sum]
      exact prodExp_congr _ fun ω => by simp [mul_ite]
  -- Non-anticipation: querying `e` is independent of `e`'s combination.
  have hindep : ∀ e (f : C → ℝ), prodExp M.π (fun ω => q ω e * f (ω e)) =
      τ e * ∑ c, M.π e c * f c := fun e f =>
    prodExp_mul_coord_of_blind hπ.2 e (g := fun ω => q ω e) (fun ω o => hna e ω o) f
  -- The policy's calls are the plan's calls.
  have hcallsI : ∀ i, M.polCallsI P i = ∑ j, M.callsI τ (i, j) := fun i => by
    have hpt : ∀ ω : I × J → C, (∑ QS, P ω QS * ∑ j,
        if (i, j) ∈ QS.1 then M.chargeI (i, j) (ω (i, j)) else 0) =
        ∑ j, q ω (i, j) * M.chargeI (i, j) (ω (i, j)) := fun ω => by
      simp only [hqdef, queryProb, mul_sum, sum_mul]
      rw [sum_comm]
      exact sum_congr rfl fun j _ => sum_congr rfl fun QS _ => by split_ifs <;> ring
    unfold polCallsI
    rw [prodExp_congr _ hpt, prodExp_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [hindep (i, j) (M.chargeI (i, j)), M.sum_π_chargeI hπ (i, j)]
    rfl
  have hcallsJ : ∀ j, M.polCallsJ P j = ∑ i, M.callsJ τ (i, j) := fun j => by
    have hpt : ∀ ω : I × J → C, (∑ QS, P ω QS * ∑ i,
        if (i, j) ∈ QS.1 then M.chargeJ (i, j) (ω (i, j)) else 0) =
        ∑ i, q ω (i, j) * M.chargeJ (i, j) (ω (i, j)) := fun ω => by
      simp only [hqdef, queryProb, mul_sum, sum_mul]
      rw [sum_comm]
      exact sum_congr rfl fun i _ => sum_congr rfl fun QS _ => by split_ifs <;> ring
    unfold polCallsJ
    rw [prodExp_congr _ hpt, prodExp_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [hindep (i, j) (M.chargeJ (i, j)), M.sum_π_chargeJ hπ (i, j)]
    rfl
  refine ⟨x, τ, ⟨⟨fun e c => ⟨?_, ?_⟩, fun e c hc => ?_, fun i => ?_, fun j => ?_⟩,
    fun e => ⟨prodExp_nonneg hπ.1 fun ω => hq0 ω e, ?_⟩, fun e c => ?_,
    fun i => (hcallsI i).symm ▸ hbI i, fun j => (hcallsJ j).symm ▸ hbJ j⟩,
    fun i => ?_, fun j => ?_⟩
  · exact prodExp_nonneg hπ.1 fun ω => by split_ifs; exacts [hm0 ω e, le_rfl]
  · calc x e c ≤ prodExp M.π (fun ω => (fun o => if o = c then (1 : ℝ) else 0) (ω e)) :=
          prodExp_mono hπ.1 fun ω => by
            simp only
            split_ifs
            exacts [(hmq ω e).trans (hq1 ω e), le_rfl]
      _ = M.π e c := by
          rw [prodExp_coord hπ.2 e (fun o => if o = c then (1 : ℝ) else 0)]
          simp
  · calc x e c = prodExp M.π (fun _ => 0) :=
          prodExp_congr _ fun ω => by
            split_ifs with h
            · exact hmacc ω e fun hacc => hc (h ▸ hacc)
            · rfl
      _ = 0 := prodExp_const hπ.2 0
  · calc ∑ j, ∑ c, x (i, j) c = prodExp M.π (fun ω => ∑ j, m ω (i, j)) := by
          simp only [hsum]
          exact (prodExp_sum _ _ _).symm
      _ ≤ prodExp M.π (fun _ => (M.capI i : ℝ)) := prodExp_mono hπ.1 fun ω => hrow ω i
      _ = M.capI i := prodExp_const hπ.2 _
  · calc ∑ i, ∑ c, x (i, j) c = prodExp M.π (fun ω => ∑ i, m ω (i, j)) := by
          simp only [hsum]
          exact (prodExp_sum _ _ _).symm
      _ ≤ prodExp M.π (fun _ => (M.capJ j : ℝ)) := prodExp_mono hπ.1 fun ω => hcol ω j
      _ = M.capJ j := prodExp_const hπ.2 _
  · calc τ e ≤ prodExp M.π (fun _ => 1) := prodExp_mono hπ.1 fun ω => hq1 ω e
      _ = 1 := prodExp_const hπ.2 1
  · calc x e c ≤ prodExp M.π (fun ω => q ω e * (fun o => if o = c then (1 : ℝ) else 0) (ω e)) :=
          prodExp_mono hπ.1 fun ω => by
            simp only
            split_ifs
            · rw [mul_one]; exact hmq ω e
            · rw [mul_zero]
      _ = τ e * M.π e c :=
          (hindep e (fun o => if o = c then (1 : ℝ) else 0)).trans (by simp)
  · unfold lpSurplusI polUtilI
    simp only [hval (_, _) fun c => M.valI _ c - M.costI i]
    rw [← prodExp_sum]
    refine prodExp_congr _ fun ω => ?_
    simp only [hm, mul_sum, sum_filter_fst]
    rw [sum_comm]
    refine sum_congr rfl fun S _ => sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  · unfold lpSurplusJ polUtilJ
    simp only [hval (_, _) fun c => M.valJ _ c - M.costJ j]
    rw [← prodExp_sum]
    refine prodExp_congr _ fun ω => ?_
    simp only [hm, mul_sum, sum_filter_snd]
    rw [sum_comm]
    refine sum_congr rfl fun S _ => sum_congr rfl fun i _ => ?_
    split_ifs <;> ring

/-! ### Adaptive query trees -/

/-- An adaptive query policy: `query e k` queries pair `e`, sees its combination `c` and
continues with `k c`; `stop S` matches `S`. -/
inductive QTree (E C : Type*) where
  | stop : Finset E → QTree E C
  | query : E → (C → QTree E C) → QTree E C

namespace QTree

variable {E : Type*} [DecidableEq E]

/-- The (queried, matched) sets of a tree when the combinations are `ω`. -/
def run : QTree E C → (E → C) → Finset E × Finset E
  | stop S, _ => (∅, S)
  | query e k, ω => (insert e ((k (ω e)).run ω).1, ((k (ω e)).run ω).2)

omit [Fintype C] [DecidableEq C] in
/-- **Non-anticipation.** Whether a tree queries `e` does not depend on `e`'s own
combination: the path to a query of `e` never looks at `e`. -/
theorem mem_run_update (T : QTree E C) (e : E) (ω : E → C) (o : C) :
    e ∈ (T.run (Function.update ω e o)).1 ↔ e ∈ (T.run ω).1 := by
  induction T with
  | stop S => simp [run]
  | query e' k ih =>
    simp only [run, mem_insert]
    by_cases h : e = e'
    · simp [h]
    · rw [Function.update_of_ne (Ne.symm h), ih]

end QTree

omit [DecidableEq C] in
/-- **Adaptive policies are budgeted policies.** A random mixture of query trees, each
matching only pairs it queried and found acceptable within caps, is non-anticipating;
with its calls within budget it is a budgeted policy. -/
theorem isBudgetedPolicy_of_trees {R : Type*} [Fintype R] {ρ : R → ℝ}
    (hρ : (∀ r, 0 ≤ ρ r) ∧ ∑ r, ρ r = 1) (T : R → QTree (I × J) C)
    (hT : ∀ r ω, ((T r).run ω).2 ⊆ ((T r).run ω).1 ∧ M.CapOK ((T r).run ω).2 ∧
      ∀ e ∈ ((T r).run ω).2, M.Acc e (ω e))
    (hbI : ∀ i, M.polCallsI (fun ω QS => ∑ r, ρ r * if (T r).run ω = QS then 1 else 0) i ≤ QI i)
    (hbJ : ∀ j, M.polCallsJ (fun ω QS => ∑ r, ρ r * if (T r).run ω = QS then 1 else 0) j ≤ QJ j) :
    M.IsBudgetedPolicy QI QJ (fun ω QS => ∑ r, ρ r * if (T r).run ω = QS then 1 else 0) := by
  -- The chance of querying `e` is the weight of the trees that query `e`.
  have hq : ∀ ω e, queryProb (fun ω QS => ∑ r, ρ r * if (T r).run ω = QS then 1 else 0) ω e =
      ∑ r, ρ r * if e ∈ ((T r).run ω).1 then 1 else 0 := fun ω e => by
    unfold queryProb
    simp only [sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun r _ => ?_
    rw [sum_eq_single ((T r).run ω) (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  refine ⟨fun ω => ⟨fun QS => sum_nonneg fun r _ => mul_nonneg (hρ.1 r) (by split_ifs <;> norm_num),
    ?_, fun QS hQS => ?_⟩, fun e ω o => ?_, hbI, hbJ⟩
  · rw [sum_comm]
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, ↓reduceIte]
    exact hρ.2
  · obtain ⟨r, -, hr⟩ := exists_ne_zero_of_sum_ne_zero hQS
    have hrun : (T r).run ω = QS := by
      by_contra h
      simp [h] at hr
    exact hrun ▸ hT r ω
  · simp only [hq, QTree.mem_run_update]

/-! ### Objectives -/

/-- The planned surpluses as one vector over all users. -/
def lpVec (x : I × J → C → ℝ) : I ⊕ J → ℝ :=
  Sum.elim (M.lpSurplusI x) (M.lpSurplusJ x)

/-- An objective of the users' expected utilities that is monotone and positively
homogeneous. -/
def IsMonoHom {U : Type*} (W : (U → ℝ) → ℝ) : Prop :=
  (∀ u v, u ≤ v → W u ≤ W v) ∧ ∀ (γ : ℝ) (u : U → ℝ), 0 ≤ γ → W (γ • u) = γ * W u

/-- A query-aware plan within `ε` of the best feasible plan for objective `W`. -/
def IsQOptimal (QI : I → ℝ) (QJ : J → ℝ) (W : (I ⊕ J → ℝ) → ℝ) (ε : ℝ)
    (x : I × J → C → ℝ) (τ : I × J → ℝ) : Prop :=
  M.QFeasible QI QJ x τ ∧
    ∀ x' τ', M.QFeasible QI QJ x' τ' → W (M.lpVec x') ≤ W (M.lpVec x) + ε

/-- **Theorem Q(f), core.** If the mechanism gives every user at least `γ` times its
planned surplus, then for a monotone, homogeneous objective it gets `γ (W(P) - ε)` against
every budgeted policy `P`, when run on an `ε`-optimal plan. -/
theorem objective_of_perUser (hπ : IsDist M.π) {W : (I ⊕ J → ℝ) → ℝ} (hW : IsMonoHom W)
    {ε : ℝ} {x : I × J → C → ℝ} {τ : I × J → ℝ} (hopt : M.IsQOptimal QI QJ W ε x τ)
    {γ : ℝ} (hγ : 0 ≤ γ) {u : I ⊕ J → ℝ} (hu : ∀ ℓ, γ * M.lpVec x ℓ ≤ u ℓ)
    {P : (I × J → C) → Finset (I × J) × Finset (I × J) → ℝ}
    (hP : M.IsBudgetedPolicy QI QJ P) :
    γ * (W (Sum.elim (M.polUtilI (matchLaw P)) (M.polUtilJ (matchLaw P))) - ε) ≤ W u := by
  obtain ⟨x', τ', hq', hI, hJ⟩ := M.exists_qplan_of_policy hπ hP
  have hvec : Sum.elim (M.polUtilI (matchLaw P)) (M.polUtilJ (matchLaw P)) = M.lpVec x' := by
    funext ℓ
    cases ℓ with
    | inl i => exact (hI i).symm
    | inr j => exact (hJ j).symm
  have h1 : W (M.lpVec x') - ε ≤ W (M.lpVec x) := by linarith [hopt.2 x' τ' hq']
  have h2 : γ * W (M.lpVec x) ≤ W u := by
    rw [← hW.2 γ _ hγ]
    exact hW.1 _ _ fun ℓ => by simpa only [Pi.smul_apply, smul_eq_mul] using hu ℓ
  rw [hvec]
  exact (mul_le_mul_of_nonneg_left h1 hγ).trans h2

/-- **Theorem Q(f) with random order:** `W(Q-SDH) ≥ (W(P) - ε) / 4`. -/
theorem qsdh_objective_quarter (hπ : IsDist M.π) {W : (I ⊕ J → ℝ) → ℝ} (hW : IsMonoHom W)
    {ε : ℝ} {x : I × J → C → ℝ} {τ : I × J → ℝ} (hopt : M.IsQOptimal QI QJ W ε x τ)
    {P : (I × J → C) → Finset (I × J) × Finset (I × J) → ℝ}
    (hP : M.IsBudgetedPolicy QI QJ P) :
    (W (Sum.elim (M.polUtilI (matchLaw P)) (M.polUtilJ (matchLaw P))) - ε) / 4 ≤
      W (Sum.elim (M.mmUtilI x τ (fun j => uniformRule (M.capJ j))
          (fun i => uniformRule (M.capI i)))
        (M.mmUtilJ x τ (fun j => uniformRule (M.capJ j)) (fun i => uniformRule (M.capI i)))) := by
  obtain ⟨hI, hJ⟩ := M.qsdh_quarter hπ hopt.1
  have := M.objective_of_perUser hπ hW hopt (γ := 1 / 4) (by norm_num)
    (u := Sum.elim (M.mmUtilI x τ (fun j => uniformRule (M.capJ j))
      (fun i => uniformRule (M.capI i)))
      (M.mmUtilJ x τ (fun j => uniformRule (M.capJ j)) (fun i => uniformRule (M.capI i))))
    (fun ℓ => by
    cases ℓ with
    | inl i => simp only [lpVec, Sum.elim_inl]; linarith [hI i]
    | inr j => simp only [lpVec, Sum.elim_inr]; linarith [hJ j]) hP
  linarith

/-- **Theorem Q(f) with balanced rules:** `W(Q-SDH) ≥ c_K^2 (W(P) - ε)`. -/
theorem qsdh_objective_cK (hπ : IsDist M.π) {W : (I ⊕ J → ℝ) → ℝ} (hW : IsMonoHom W)
    {ε : ℝ} {x : I × J → C → ℝ} {τ : I × J → ℝ} (hopt : M.IsQOptimal QI QJ W ε x τ)
    (K : ℕ) (hKI : ∀ i, K ≤ M.capI i) (hKJ : ∀ j, K ≤ M.capJ j) :
    ∃ ψ1 : J → Finset I → Finset I → ℝ, ∃ ψ2 : I → Finset J → Finset J → ℝ,
      (∀ j, IsRule (M.capJ j) (ψ1 j)) ∧ (∀ i, IsRule (M.capI i) (ψ2 i)) ∧
      ∀ P, M.IsBudgetedPolicy QI QJ P →
        cK K ^ 2 * (W (Sum.elim (M.polUtilI (matchLaw P)) (M.polUtilJ (matchLaw P))) - ε) ≤
          W (Sum.elim (M.mmUtilI x τ ψ1 ψ2) (M.mmUtilJ x τ ψ1 ψ2)) := by
  obtain ⟨ψ1, ψ2, h1, h2, hI, hJ⟩ := M.qsdh_cK hπ hopt.1 K hKI hKJ
  refine ⟨ψ1, ψ2, h1, h2, fun P hP =>
    M.objective_of_perUser hπ hW hopt (sq_nonneg _) (fun ℓ => ?_) hP⟩
  cases ℓ with
  | inl i => simpa only [lpVec, Sum.elim_inl] using hI i
  | inr j => simpa only [lpVec, Sum.elim_inr] using hJ j

end ScreenedMarket

/-! ### Which objectives -/

section Objectives

variable {U : Type*}

/-- **Max-min over a set of users** is monotone and homogeneous: the worst-off user, or the
worst-off among the users who can match at all. -/
theorem isMonoHom_inf' (s : Finset U) (hs : s.Nonempty) :
    ScreenedMarket.IsMonoHom (fun u : U → ℝ => s.inf' hs u) := by
  refine ⟨fun u v huv => le_inf' hs _ fun ℓ hℓ => (inf'_le u hℓ).trans (huv ℓ),
    fun γ u hγ => le_antisymm ?_ ?_⟩
  · obtain ⟨ℓ, hℓ, heq⟩ := exists_mem_eq_inf' hs u
    calc s.inf' hs (γ • u) ≤ (γ • u) ℓ := inf'_le _ hℓ
      _ = γ * s.inf' hs u := by rw [heq, Pi.smul_apply, smul_eq_mul]
  · exact le_inf' hs _ fun ℓ hℓ => by
      rw [Pi.smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (inf'_le u hℓ) hγ

/-- **Max-min of weighted utilities**, such as utilities normalized by each user's best
case, is monotone and homogeneous. -/
theorem isMonoHom_weightedInf (s : Finset U) (hs : s.Nonempty) {a : U → ℝ}
    (ha : ∀ ℓ, 0 ≤ a ℓ) :
    ScreenedMarket.IsMonoHom (fun u : U → ℝ => s.inf' hs fun ℓ => a ℓ * u ℓ) := by
  refine ⟨fun u v huv => (isMonoHom_inf' s hs).1 _ _ fun ℓ =>
    mul_le_mul_of_nonneg_left (huv ℓ) (ha ℓ), fun γ u hγ => ?_⟩
  have hfun : (fun ℓ => a ℓ * (γ • u) ℓ) = γ • fun ℓ => a ℓ * u ℓ := by
    funext ℓ
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  simp only [hfun]
  exact (isMonoHom_inf' s hs).2 γ _ hγ

/-- **Weighted welfare** is monotone and homogeneous. -/
theorem isMonoHom_weightedSum [Fintype U] {a : U → ℝ} (ha : ∀ ℓ, 0 ≤ a ℓ) :
    ScreenedMarket.IsMonoHom (fun u : U → ℝ => ∑ ℓ, a ℓ * u ℓ) := by
  refine ⟨fun u v huv => sum_le_sum fun ℓ _ => mul_le_mul_of_nonneg_left (huv ℓ) (ha ℓ),
    fun γ u _ => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, mul_sum]
  exact sum_congr rfl fun ℓ _ => by ring

end Objectives

end DatingAlgo
