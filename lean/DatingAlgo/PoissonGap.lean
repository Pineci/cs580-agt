import DatingAlgo.TwoPeriod

/-!
# The `c_K` cardinality gap and R1

For independent coin flips with mean `μ = ∑ p`,
`E[min(|S|, K)] ≥ c_K · min(μ, K)` with `c_K = 1 - e^{-K} K^K / K!`
(`poissonBinomial_min_ge`). With `dhInt_approx_of_card_gap` this gives R1:
DH-int is a `c_K`-approximation (`dhInt_approx_cK`).

The textbook proof compares `|S|` with a Poisson variable of the same mean in convex
order. We keep everything finite. `E[min(Poi(μ), j)]` is a finite sum, so we never need
the Poisson distribution itself, only two real functions of `μ`:
* `poiCdf j μ = e^{-μ} ∑_{i<j} μ^i / i!`, the probability that `Poi(μ) < j`;
* `poiMin j μ = ∑_{m<j} (1 - poiCdf (m+1) μ)`, the expectation of `min(Poi(μ), j)`.

The proof has three steps:
- *calculus:* `poiMin j` has derivative `poiCdf j`, which is antitone for `μ ≥ 0`. So
  `poiMin j` is concave there and lies below its tangents (`poiMin_sub_le`);
- *comparison:* by induction on `U`, `E[min(|S|, j)] ≥ poiMin j (∑ p)` for every `j`
  (`poiMin_le_indepExp`). A new coin with probability `p` turns `E[min(|S|, j)]` into
  `(1-p) E[min(|S|, j)] + p (1 + E[min(|S|, j-1)])`, and the tangent bound for
  `poiMin j` is exactly this step;
- *the Poisson case:* `poiMin K K = K c_K` (`poiMin_self`). Concavity and
  `poiMin K 0 = 0` give `poiMin K μ ≥ c_K min(μ, K)` (`cK_mul_min_le_poiMin`).
-/

namespace DatingAlgo

open Finset

/-- `P(Poi(μ) < j) = e^{-μ} ∑_{i<j} μ^i / i!`. -/
noncomputable def poiCdf (j : ℕ) (μ : ℝ) : ℝ :=
  Real.exp (-μ) * ∑ i ∈ range j, μ ^ i / (i.factorial : ℝ)

/-- `E[min(Poi(μ), j)] = ∑_{m<j} P(Poi(μ) > m)`. -/
noncomputable def poiMin (j : ℕ) (μ : ℝ) : ℝ :=
  ∑ m ∈ range j, (1 - poiCdf (m + 1) μ)

theorem poiCdf_succ (j : ℕ) (μ : ℝ) :
    poiCdf (j + 1) μ = poiCdf j μ + Real.exp (-μ) * (μ ^ j / (j.factorial : ℝ)) := by
  unfold poiCdf
  rw [sum_range_succ, mul_add]

theorem poiCdf_nonneg (j : ℕ) {μ : ℝ} (hμ : 0 ≤ μ) : 0 ≤ poiCdf j μ := by
  unfold poiCdf
  exact mul_nonneg (Real.exp_pos _).le (sum_nonneg fun i _ => by positivity)

theorem poiMin_succ (j : ℕ) (μ : ℝ) :
    poiMin (j + 1) μ = poiMin j μ + 1 - poiCdf (j + 1) μ := by
  unfold poiMin
  rw [sum_range_succ]
  ring

/-- `E[min(Poi(0), j)] = 0`. -/
theorem poiMin_zero_right (j : ℕ) : poiMin j 0 = 0 := by
  unfold poiMin poiCdf
  refine sum_eq_zero fun m _ => ?_
  rw [sum_range_succ']
  simp

/-- Closed form: `poiMin j μ = j - e^{-μ} ∑_{i<j} (j - i) μ^i / i!`. -/
theorem poiMin_eq (j : ℕ) (μ : ℝ) :
    poiMin j μ = j - Real.exp (-μ) * ∑ i ∈ range j, ((j : ℝ) - i) * (μ ^ i / (i.factorial : ℝ)) := by
  induction j with
  | zero => simp [poiMin]
  | succ j ih =>
    rw [poiMin_succ, ih, poiCdf, sum_range_succ (n := j), sum_range_succ (n := j)]
    have h : ∑ i ∈ range j, (((j + 1 : ℕ) : ℝ) - i) * (μ ^ i / (i.factorial : ℝ)) =
        ∑ i ∈ range j, ((j : ℝ) - i) * (μ ^ i / (i.factorial : ℝ)) +
          ∑ i ∈ range j, μ ^ i / (i.factorial : ℝ) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl fun i _ => by push_cast; ring
    rw [h]
    push_cast
    ring

/-- `∑_{i ≤ n} (x - i) x^i / i! = x^{n+1} / n!` (the sum telescopes). -/
theorem sum_sub_mul_pow_div (n : ℕ) (x : ℝ) :
    ∑ i ∈ range (n + 1), (x - i) * (x ^ i / (i.factorial : ℝ)) =
      x ^ (n + 1) / (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- The Poisson case at `μ = K`: `E[min(Poi(K), K)] = K c_K`. -/
theorem poiMin_self (K : ℕ) : poiMin K K = K * cK K := by
  rcases K with _ | n
  · simp [poiMin]
  · rw [poiMin_eq, sum_sub_mul_pow_div, cK, Nat.factorial_succ]
    push_cast
    field_simp

/-! ### Calculus: `poiMin j` is concave on `μ ≥ 0` -/

/-- `d/dμ P(Poi(μ) ≤ j) = -e^{-μ} μ^j / j!`. -/
theorem hasDerivAt_poiCdf_succ (j : ℕ) (μ : ℝ) :
    HasDerivAt (poiCdf (j + 1)) (-(Real.exp (-μ) * (μ ^ j / (j.factorial : ℝ)))) μ := by
  have he : HasDerivAt (fun μ : ℝ => Real.exp (-μ)) (-Real.exp (-μ)) μ := by
    simpa using (hasDerivAt_neg' (x := μ)).exp
  induction j with
  | zero =>
    have hf : poiCdf (0 + 1) = fun μ => Real.exp (-μ) := by
      funext μ
      simp [poiCdf]
    rw [hf]
    simpa using he
  | succ j ih =>
    have hf : poiCdf (j + 1 + 1) = fun μ =>
        poiCdf (j + 1) μ + Real.exp (-μ) * (μ ^ (j + 1) / ((j + 1).factorial : ℝ)) := by
      funext μ
      exact poiCdf_succ (j + 1) μ
    rw [hf]
    have hp : HasDerivAt (fun μ : ℝ => μ ^ (j + 1) / ((j + 1).factorial : ℝ))
        (((j + 1 : ℕ) : ℝ) * μ ^ j / ((j + 1).factorial : ℝ)) μ := by
      simpa using (hasDerivAt_pow (j + 1) μ).div_const ((j + 1).factorial : ℝ)
    convert ih.add (he.mul hp) using 1
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- `d/dμ E[min(Poi(μ), j)] = P(Poi(μ) < j)`. -/
theorem hasDerivAt_poiMin (j : ℕ) (μ : ℝ) : HasDerivAt (poiMin j) (poiCdf j μ) μ := by
  induction j with
  | zero =>
    have hf : poiMin 0 = fun _ => 0 := by
      funext μ
      simp [poiMin]
    rw [hf]
    simpa [poiCdf] using hasDerivAt_const μ (0 : ℝ)
  | succ j ih =>
    have hf : poiMin (j + 1) = fun μ => poiMin j μ + 1 - poiCdf (j + 1) μ := by
      funext μ
      exact poiMin_succ j μ
    rw [hf]
    convert (ih.add_const 1).sub (hasDerivAt_poiCdf_succ j μ) using 1
    rw [poiCdf_succ]
    ring

/-- `P(Poi(μ) < j)` is antitone in `μ ≥ 0`. -/
theorem poiCdf_antitoneOn (j : ℕ) : AntitoneOn (poiCdf j) (Set.Ici 0) := by
  rcases j with _ | j
  · intro a _ b _ _
    simp [poiCdf]
  · have hd := hasDerivAt_poiCdf_succ j
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [interior_Ici] at hx
    rw [(hd x).deriv]
    have hx0 : 0 ≤ x := le_of_lt hx
    have : 0 ≤ Real.exp (-x) * (x ^ j / (j.factorial : ℝ)) := by positivity
    linarith

/-- Upper tangent bound: for `0 ≤ a ≤ b`, `poiMin j b - poiMin j a ≤ (b - a) poiCdf j a`. -/
theorem poiMin_sub_le (j : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    poiMin j b - poiMin j a ≤ poiCdf j a * (b - a) := by
  have hd := hasDerivAt_poiMin j
  refine (convex_Icc a b).image_sub_le_mul_sub_of_deriv_le
    (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => (hd x).differentiableAt.differentiableWithinAt) ?_
    a (Set.left_mem_Icc.mpr hab) b (Set.right_mem_Icc.mpr hab) hab
  intro x hx
  rw [interior_Icc] at hx
  rw [(hd x).deriv]
  exact poiCdf_antitoneOn j (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr (ha.trans hx.1.le)) hx.1.le

/-- Lower tangent bound: for `0 ≤ a ≤ b`, `(b - a) poiCdf j b ≤ poiMin j b - poiMin j a`. -/
theorem le_poiMin_sub (j : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    poiCdf j b * (b - a) ≤ poiMin j b - poiMin j a := by
  have hd := hasDerivAt_poiMin j
  refine (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
    (fun x _ => (hd x).continuousAt.continuousWithinAt)
    (fun x _ => (hd x).differentiableAt.differentiableWithinAt) ?_
    a (Set.left_mem_Icc.mpr hab) b (Set.right_mem_Icc.mpr hab) hab
  intro x hx
  rw [interior_Icc] at hx
  rw [(hd x).deriv]
  exact poiCdf_antitoneOn j (Set.mem_Ici.mpr (ha.trans hx.1.le))
    (Set.mem_Ici.mpr (ha.trans hab)) hx.2.le

/-! ### The Poisson case -/

/-- `E[min(Poi(μ), K)] ≥ c_K min(μ, K)`: concavity and `poiMin K K = K c_K`. -/
theorem cK_mul_min_le_poiMin (K : ℕ) {μ : ℝ} (hμ : 0 ≤ μ) : cK K * min μ K ≤ poiMin K μ := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp [cK_zero, poiMin]
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hself := poiMin_self K
  rcases le_total μ K with h | h
  · -- `μ ≤ K`: the chord from `0` to `K` lies below `poiMin K`.
    rw [min_eq_left h]
    have hup := poiMin_sub_le K hμ h
    have hlow := le_poiMin_sub K le_rfl hμ
    rw [poiMin_zero_right, sub_zero, sub_zero] at hlow
    have h1 : μ * (K * cK K) ≤ μ * poiMin K μ + μ * (poiCdf K μ * (K - μ)) := by
      rw [← hself, ← mul_add]
      exact mul_le_mul_of_nonneg_left (by linarith) hμ
    have h2 : μ * (poiCdf K μ * (K - μ)) ≤ (K - μ) * poiMin K μ := by
      rw [show μ * (poiCdf K μ * (K - μ)) = (K - μ) * (poiCdf K μ * μ) by ring]
      exact mul_le_mul_of_nonneg_left hlow (sub_nonneg.mpr h)
    have h3 : K * (cK K * μ) ≤ K * poiMin K μ := by nlinarith
    exact le_of_mul_le_mul_left h3 hKpos
  · -- `μ ≥ K`: `poiMin K` is monotone.
    rw [min_eq_right h]
    have hlow := le_poiMin_sub K hKpos.le h
    have := mul_nonneg (poiCdf_nonneg K hμ) (sub_nonneg.mpr h)
    linarith

/-! ### Comparison with the Poisson case -/

variable {α : Type*} [DecidableEq α]

/-- Coin flips beat the Poisson case: `E[min(|S|, j)] ≥ E[min(Poi(∑ p), j)]` for every
cap `j`. -/
theorem poiMin_le_indepExp (U : Finset α) (p : α → ℝ) (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1)
    (j : ℕ) : poiMin j (∑ i ∈ U, p i) ≤ indepExp U p (fun S => min (S.card : ℝ) j) := by
  induction U using Finset.induction_on generalizing j with
  | empty =>
    rw [sum_empty, poiMin_zero_right]
    simp [indepExp]
  | insert a U ha ih =>
    have hpa := hp a (mem_insert_self a U)
    have hpU : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1 := fun i hi => hp i (mem_insert_of_mem hi)
    have hμ : 0 ≤ ∑ i ∈ U, p i := sum_nonneg fun i hi => (hpU i hi).1
    rw [indepExp_insert ha, sum_insert ha]
    rcases j with _ | j
    · have hz : ∀ S : Finset α, min (S.card : ℝ) ((0 : ℕ) : ℝ) = 0 := fun S => by simp
      simp only [hz, indepExp_const]
      simp [poiMin]
    · -- `min(|S| + 1, j + 1) = 1 + min(|S|, j)`.
      have hshift : indepExp U p
          (fun S => min ((insert a S).card : ℝ) ((j + 1 : ℕ) : ℝ)) =
          1 + indepExp U p (fun S => min (S.card : ℝ) j) := by
        rw [indepExp_congr (h := fun S => 1 + min (S.card : ℝ) j), indepExp_add, indepExp_const]
        intro S hS
        rw [card_insert_of_notMem (fun h => ha (hS h))]
        push_cast
        rw [min_add_add_right]
        ring
      rw [hshift]
      have h1 := ih hpU (j + 1)
      have h0 := ih hpU j
      have htan := poiMin_sub_le (j + 1) hμ (le_add_of_nonneg_left hpa.1)
      have hstep : poiCdf (j + 1) (∑ i ∈ U, p i) =
          1 + poiMin j (∑ i ∈ U, p i) - poiMin (j + 1) (∑ i ∈ U, p i) := by
        rw [poiMin_succ]
        ring
      rw [hstep, add_sub_cancel_right] at htan
      have e1 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hpa.2)
      have e2 := mul_le_mul_of_nonneg_left (add_le_add_left h0 1) hpa.1
      push_cast at e1 e2 ⊢
      nlinarith

/-- **R1, key lemma: Poisson-binomial bound.**
For a sum `X` of independent coin flips with mean `μ`,
`E[min(X, K)] ≥ c_K · min(μ, K)`.
Proved by comparing with the Poisson case through the finite formula
`poiMin K μ = E[min(Poi(μ), K)]` (`poiMin_le_indepExp`, `cK_mul_min_le_poiMin`). The
constant `1 - 1/e` version is `cardinality_gap`. -/
theorem poissonBinomial_min_ge (U : Finset α) (p : α → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (K : ℕ) :
    cK K * min (∑ i ∈ U, p i) K ≤ indepExp U p (fun S => min (S.card : ℝ) K) :=
  (cK_mul_min_le_poiMin K (sum_nonneg fun i hi => (hp i hi).1)).trans
    (poiMin_le_indepExp U p hp K)

/-- **R1 (vault note).** With a common display cap `K`, DH-int is a
`c_K`-approximation (`c_3 ≈ 0.776`), improving the paper's `1 - 1/e`. -/
theorem dhInt_approx_cK {U D : Type*} [Fintype U] [DecidableEq U]
    (M : TwoPeriodModel U D) (K : ℕ) (hK : ∀ ℓ, M.K ℓ = K) {feasible : D → Prop}
    {d : D} {y : U → U → ℝ} (hdh : M.IsDHIntSolution feasible d y)
    {d' : D} (hd' : feasible d') :
    cK K * M.value d' ≤ M.value d := by
  refine M.dhInt_approx_of_card_gap (cK_nonneg K) (cK_le_one K) ?_ hdh hd'
  intro ℓ V
  rw [hK ℓ]
  exact poissonBinomial_min_ge V _ (fun i _ => ⟨M.φ1_nonneg i ℓ, M.φ1_le_one i ℓ⟩) K

end DatingAlgo
