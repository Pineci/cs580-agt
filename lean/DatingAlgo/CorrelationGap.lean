import DatingAlgo.IndepExp
import DatingAlgo.TopK

/-!
# Correlation gap for weighted top-K

The probabilistic step in the paper's proof of Theorem 4.3 (Appendix C.1). The
paper cites the general correlation gap of Agrawal, Ding, Saberi & Ye (2010) for
monotone submodular functions. Here we only need it for weighted top-K, the
period-2 value of a responder, and we prove it from scratch.

**Unweighted (`cardinality_gap`).** For independent coin flips with mean
`μ = ∑ p`: `E[min(|S|, K)] ≥ (1 - 1/e) · min(μ, K)`. The proof has three steps:
- *pointwise:* `min(s, K) ≥ K (1 - (1 - 1/K)^s)`, which is Bernoulli's inequality;
- *in expectation:* by the generating function,
  `E[(1 - 1/K)^|S|] = ∏ (1 - p i / K) ≤ e^{-μ/K}`;
- *finally:* `1 - e^{-x} ≥ (1 - 1/e) min(x, 1)` by convexity of `exp`.

**Weighted (`weighted_gap_of_card_gap`).** Any constant `c` that works for the
unweighted bound also works for weighted top-K and every fractional plan.

1. Strip the smallest weight `w_a` off every weight.
2. `topK` gains at least `w_a · min(|S|, K)`, by `topK_add_const_ge`.
3. Element `a` now has weight zero and can be dropped.
4. Induct on `U`.

With `c = 1 - 1/e` this gives the step in Theorem 4.3. With `c = c_K`
(`poissonBinomial_min_ge` in `PoissonGap.lean`) it gives the sharper result R1 in the vault note.
-/

namespace DatingAlgo

open Finset

/-- Pointwise bound behind the cardinality gap: `min(s, K) ≥ K (1 - (1 - 1/K)^s)`. -/
theorem card_pow_bound {K : ℕ} (hK : 1 ≤ K) (s : ℕ) :
    (K : ℝ) * (1 - (1 - 1 / (K : ℝ)) ^ s) ≤ min (s : ℝ) K := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hinv0 : 0 ≤ 1 / (K : ℝ) := one_div_nonneg.mpr hKpos.le
  have hinv1 : 1 / (K : ℝ) ≤ 1 := by rw [div_le_one hKpos]; exact hK1
  have ht0 : 0 ≤ 1 - 1 / (K : ℝ) := by linarith
  apply le_min
  · have hb := one_add_mul_le_pow (a := -(1 / (K : ℝ))) (by linarith) s
    have he : (1 : ℝ) + -(1 / K) = 1 - 1 / K := by ring
    rw [he] at hb
    calc (K : ℝ) * (1 - (1 - 1 / (K : ℝ)) ^ s)
        ≤ K * (1 - (1 + s * (-(1 / (K : ℝ))))) := by
          apply mul_le_mul_of_nonneg_left _ hKpos.le
          linarith
      _ = s := by field_simp; ring
  · have := pow_nonneg ht0 s
    nlinarith

/-- `1 - e^{-x} ≥ (1 - 1/e) min(x, 1)` for `x ≥ 0`. -/
theorem one_sub_exp_neg_ge {x : ℝ} (hx : 0 ≤ x) :
    (1 - Real.exp (-1)) * min x 1 ≤ 1 - Real.exp (-x) := by
  rcases le_total x 1 with h | h
  · rw [min_eq_left h]
    have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-1 : ℝ))
      (sub_nonneg.mpr h) hx (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one, mul_neg] at hc
    linarith
  · rw [min_eq_right h]
    have := Real.exp_le_exp.mpr (neg_le_neg h)
    linarith

variable {α : Type*} [DecidableEq α]

/-- **Cardinality gap.** For independent coin flips,
`E[min(|S|, K)] ≥ (1 - 1/e) · min(∑ p, K)`. -/
theorem cardinality_gap (U : Finset α) (p : α → ℝ) (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1)
    (K : ℕ) :
    (1 - Real.exp (-1)) * min (∑ i ∈ U, p i) K ≤
      indepExp U p (fun S => min (S.card : ℝ) K) := by
  have hμ0 : 0 ≤ ∑ i ∈ U, p i := Finset.sum_nonneg fun i hi => (hp i hi).1
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · have h0 : indepExp U p (fun S => min (S.card : ℝ) ((0 : ℕ) : ℝ)) = 0 := by
      have hf : (fun S : Finset α => min (S.card : ℝ) ((0 : ℕ) : ℝ)) = fun _ => 0 := by
        funext S; simp
      rw [hf, indepExp_const]
    rw [h0]
    simp [min_eq_right hμ0]
  · have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    -- Step 1 and 2: pointwise bound, then the generating function.
    have hE : (K : ℝ) - K * ∏ i ∈ U, (1 - p i / K) ≤
        indepExp U p (fun S => min (S.card : ℝ) K) := by
      have h1 : indepExp U p (fun S => (K : ℝ) + (-(K : ℝ)) * (1 - 1 / (K : ℝ)) ^ S.card) ≤
          indepExp U p (fun S => min (S.card : ℝ) K) := by
        apply indepExp_mono hp
        intro S _
        have := card_pow_bound hK S.card
        linarith
      have e1 : indepExp U p (fun S => (K : ℝ) + (-(K : ℝ)) * (1 - 1 / (K : ℝ)) ^ S.card) =
          (K : ℝ) - K * ∏ i ∈ U, (1 - p i / K) := by
        rw [indepExp_add U p (fun _ => (K : ℝ)) (fun S => (-(K : ℝ)) * (1 - 1 / (K : ℝ)) ^ S.card),
          indepExp_const,
          indepExp_const_mul U p (-(K : ℝ)) (fun S => (1 - 1 / (K : ℝ)) ^ S.card),
          indepExp_pow_card]
        have hfac : ∀ i ∈ U, 1 - p i + p i * (1 - 1 / (K : ℝ)) = 1 - p i / K := by
          intro i _; ring
        rw [Finset.prod_congr rfl hfac]
        ring
      rw [e1] at h1
      exact h1
    -- Step 3: `∏ (1 - p i / K) ≤ exp(-μ/K)`.
    have hprod : ∏ i ∈ U, (1 - p i / K) ≤ Real.exp (-((∑ i ∈ U, p i) / K)) := by
      calc ∏ i ∈ U, (1 - p i / K) ≤ ∏ i ∈ U, Real.exp (-(p i / K)) := by
            apply Finset.prod_le_prod₀
            · intro i hi
              have hpi : p i / K ≤ 1 := by
                rw [div_le_one hKpos]; linarith [(hp i hi).2]
              linarith
            · intro i _
              have := Real.add_one_le_exp (-(p i / K))
              linarith
        _ = Real.exp (-((∑ i ∈ U, p i) / K)) := by
            rw [← Real.exp_sum, Finset.sum_div, ← Finset.sum_neg_distrib]
    -- Step 4: convexity bound.
    have hx := one_sub_exp_neg_ge (div_nonneg hμ0 hKpos.le : 0 ≤ (∑ i ∈ U, p i) / K)
    have hmin : (K : ℝ) * min ((∑ i ∈ U, p i) / K) 1 = min (∑ i ∈ U, p i) K := by
      rw [mul_min_of_nonneg _ _ hKpos.le, mul_div_cancel₀ _ hKpos.ne', mul_one]
    have hKprod := mul_le_mul_of_nonneg_left hprod hKpos.le
    calc (1 - Real.exp (-1)) * min (∑ i ∈ U, p i) K
        = K * ((1 - Real.exp (-1)) * min ((∑ i ∈ U, p i) / K) 1) := by rw [← hmin]; ring
      _ ≤ K * (1 - Real.exp (-((∑ i ∈ U, p i) / K))) := mul_le_mul_of_nonneg_left hx hKpos.le
      _ ≤ K - K * ∏ i ∈ U, (1 - p i / K) := by linarith
      _ ≤ _ := hE

/-- **From unweighted to weighted.** If `E[min(|S|, K)] ≥ c · min(∑ p, K)` holds on
every subset of `U`, then for non-negative weights and every fractional plan `y`
(with `0 ≤ y ≤ p` and `∑ y ≤ K`), `E[topK w K S] ≥ c · ∑ w y`. -/
theorem weighted_gap_of_card_gap {c : ℝ} (hc : 0 ≤ c) {K : ℕ} {U : Finset α}
    {p : α → ℝ} (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1)
    (hcard : ∀ V ⊆ U, c * min (∑ i ∈ V, p i) K ≤
      indepExp V p (fun S => min (S.card : ℝ) K))
    {w y : α → ℝ} (hw : ∀ i ∈ U, 0 ≤ w i) (hy : ∀ i ∈ U, 0 ≤ y i ∧ y i ≤ p i)
    (hyK : ∑ i ∈ U, y i ≤ K) :
    c * ∑ i ∈ U, w i * y i ≤ indepExp U p (topK w K) := by
  induction U using Finset.strongInduction generalizing w y with
  | H U ih =>
  rcases U.eq_empty_or_nonempty with rfl | hne
  · have h0 := indepExp_mono (g := fun _ => (0 : ℝ)) (h := topK w K) hp
      (fun S _ => topK_nonneg)
    rw [indepExp_const] at h0
    simpa using h0
  obtain ⟨a, ha, hamin⟩ := Finset.exists_min_image U w hne
  set m := w a with hm_def
  have hm : 0 ≤ m := hw a ha
  set w' : α → ℝ := fun i => w i - m with hw'_def
  have hw'U : ∀ i ∈ U, 0 ≤ w' i := fun i hi => by
    simp only [hw'_def]; linarith [hamin i hi]
  have hww' : (fun i => m + w' i) = w := by funext i; simp [hw'_def]
  -- Pointwise: `topK w K S ≥ m * min |S| K + topK w' K (S.erase a)`.
  have hpt : ∀ S ⊆ U, m * min (S.card : ℝ) K + topK w' K (S.erase a) ≤ topK w K S := by
    intro S hS
    have h1 := topK_add_const_ge (w := w') (K := K) (S := S) hm (fun i hi => hw'U i (hS hi))
    rw [hww'] at h1
    have h2 : topK w' K (S.erase a) ≤ topK w' K S := topK_mono (Finset.erase_subset a S)
    linarith
  have hE := indepExp_mono hp hpt
  rw [indepExp_add U p (fun S => m * min (S.card : ℝ) K) (fun S => topK w' K (S.erase a)),
    indepExp_const_mul U p m (fun S => min (S.card : ℝ) K)] at hE
  have herase : indepExp U p (fun S => topK w' K (S.erase a)) = indepExp (U.erase a) p (topK w' K) := by
    have := indepExp_insert_erase (U := U.erase a) (a := a) (Finset.notMem_erase a U) p (topK w' K)
    rwa [Finset.insert_erase ha] at this
  rw [herase] at hE
  -- Induction hypothesis on `U.erase a` with weights `w'`.
  have hsub : U.erase a ⊆ U := Finset.erase_subset a U
  have hIH := ih (U.erase a) (Finset.erase_ssubset ha)
    (fun i hi => hp i (hsub hi))
    (fun V hV => hcard V (hV.trans hsub))
    (w := w') (y := y)
    (fun i hi => hw'U i (hsub hi))
    (fun i hi => hy i (hsub hi))
    (le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun i hi _ => (hy i hi).1) hyK)
  -- Cardinality bound on `U`.
  have hcU := hcard U (Finset.Subset.refl U)
  have hyle : ∑ i ∈ U, y i ≤ min (∑ i ∈ U, p i) K :=
    le_min (Finset.sum_le_sum fun i hi => (hy i hi).2) hyK
  have hcy : c * ∑ i ∈ U, y i ≤ indepExp U p (fun S => min (S.card : ℝ) K) :=
    (mul_le_mul_of_nonneg_left hyle hc).trans hcU
  have hmcy := mul_le_mul_of_nonneg_left hcy hm
  -- Split `∑ w y`.
  have hsplit : ∑ i ∈ U, w i * y i = m * ∑ i ∈ U, y i + ∑ i ∈ U.erase a, w' i * y i := by
    rw [Finset.sum_erase U (f := fun i => w' i * y i) (by simp [hw'_def, hm_def]), Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [hw'_def]; ring
  rw [hsplit, mul_add]
  have : c * (m * ∑ i ∈ U, y i) = m * (c * ∑ i ∈ U, y i) := by ring
  linarith

/-- **Correlation gap for weighted top-K, constant `1 - 1/e`.** This is the step in
the paper's proof of Theorem 4.3 that uses Agrawal et al. (2010). -/
theorem topK_correlation_gap (U : Finset α) (p w y : α → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (hw : ∀ i ∈ U, 0 ≤ w i) (K : ℕ)
    (hy : ∀ i ∈ U, 0 ≤ y i ∧ y i ≤ p i) (hyK : ∑ i ∈ U, y i ≤ K) :
    (1 - Real.exp (-1)) * ∑ i ∈ U, w i * y i ≤ indepExp U p (topK w K) := by
  exact weighted_gap_of_card_gap one_sub_exp_neg_one_nonneg hp
    (fun V hV => cardinality_gap V p (fun i hi => hp i (hV hi)) K) hw hy hyK

/-- `(n + 1)^n ≤ e · n^n`, i.e. `(1 + 1/n)^n ≤ e`. -/
theorem succ_pow_le_exp_one_mul_pow (n : ℕ) :
    ((n : ℝ) + 1) ^ n ≤ Real.exp 1 * (n : ℝ) ^ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : (n : ℝ) + 1 ≤ n * Real.exp (1 / n) := by
      have := Real.add_one_le_exp (1 / (n : ℝ))
      calc (n : ℝ) + 1 = n * (1 / n + 1) := by field_simp; ring
        _ ≤ n * Real.exp (1 / n) := by gcongr
    calc ((n : ℝ) + 1) ^ n ≤ (n * Real.exp (1 / n)) ^ n := by gcongr
      _ = Real.exp 1 * (n : ℝ) ^ n := by
        rw [mul_pow, ← Real.exp_nat_mul, mul_one_div_cancel hn'.ne', mul_comm]

/-- `c_n ≤ c_{n+1}`. Since `(n+1)^{n+1} / (n+1)! = (n+1)^n / n!`, this is
`(n + 1)^n ≤ e · n^n`. -/
theorem cK_le_succ (n : ℕ) : cK n ≤ cK (n + 1) := by
  unfold cK
  have hf : ((n + 1).factorial : ℝ) = (n + 1) * n.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hfpos : (0 : ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  have key := succ_pow_le_exp_one_mul_pow n
  have hexp : Real.exp (-((n : ℝ) + 1)) * Real.exp 1 = Real.exp (-(n : ℝ)) := by
    rw [← Real.exp_add]; ring_nf
  have : Real.exp (-((n + 1 : ℕ) : ℝ)) * ((n + 1 : ℕ) : ℝ) ^ (n + 1) /
      ((n + 1).factorial : ℝ) ≤ Real.exp (-(n : ℝ)) * (n : ℝ) ^ n / (n.factorial : ℝ) := by
    rw [hf, div_le_div_iff₀ (by positivity) hfpos]
    push_cast
    have hpos : 0 ≤ Real.exp (-((n : ℝ) + 1)) := (Real.exp_pos _).le
    calc Real.exp (-((n : ℝ) + 1)) * ((n : ℝ) + 1) ^ (n + 1) * (n.factorial : ℝ)
        = (Real.exp (-((n : ℝ) + 1)) * ((n : ℝ) + 1) ^ n) * (((n : ℝ) + 1) * n.factorial) := by
          ring
      _ ≤ (Real.exp (-((n : ℝ) + 1)) * (Real.exp 1 * (n : ℝ) ^ n)) *
            (((n : ℝ) + 1) * n.factorial) := by gcongr
      _ = Real.exp (-(n : ℝ)) * (n : ℝ) ^ n * (((n : ℝ) + 1) * n.factorial) := by
          rw [← hexp]; ring
  linarith

/-- `c_K` increases with `K`. -/
theorem cK_mono : Monotone cK := monotone_nat_of_le_succ cK_le_succ

/-- `c_K ≥ 1 - 1/e` for every `K ≥ 1`, so R1 strengthens the paper's constant:
`c_1 = 1 - 1/e` and `c_K` increases. -/
theorem one_sub_exp_neg_one_le_cK {K : ℕ} (hK : 1 ≤ K) : 1 - Real.exp (-1) ≤ cK K := by
  have := cK_mono hK
  rwa [cK_one] at this

/-- `c_K ≥ 0`: `e^{-K} K^K / K!` is a Poisson probability, so it is at most 1. -/
theorem cK_nonneg (K : ℕ) : 0 ≤ cK K := by
  unfold cK
  have h := Real.pow_div_factorial_le_exp (x := (K : ℝ)) (Nat.cast_nonneg K) K
  have key : Real.exp (-(K : ℝ)) * (K : ℝ) ^ K / (K.factorial : ℝ) ≤ 1 := by
    rw [mul_div_assoc]
    calc _ ≤ Real.exp (-(K : ℝ)) * Real.exp K :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  linarith

/-- `c_K ≤ 1`. -/
theorem cK_le_one (K : ℕ) : cK K ≤ 1 := by
  unfold cK
  have : 0 ≤ Real.exp (-(K : ℝ)) * (K : ℝ) ^ K / (K.factorial : ℝ) := by positivity
  linarith

end DatingAlgo
