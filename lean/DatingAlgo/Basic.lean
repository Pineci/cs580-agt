import Mathlib

/-!
# Basic definitions

Shared definitions for the match-quality analysis of the Rios & Torrico dating
heuristic (vault note "Match Quality in the Dating Heuristic Framework").

* `cK k = 1 - e^{-k} k^k / k!`: the correlation-gap constant for `k`-uniform matroids.
* `indepExp U p g`: the expectation of `g S` when each `i ∈ U` is put in `S`
  independently with probability `p i`.

Every random set in the paper's two-period model has the second form: who liked whom
in period 1 is a set of independent coin flips. So expectations are finite sums over
subsets, and no measure theory is needed.
-/

namespace DatingAlgo

open Finset

/-- The correlation-gap constant `c_k = 1 - e^{-k} k^k / k!`. -/
noncomputable def cK (k : ℕ) : ℝ :=
  1 - Real.exp (-(k : ℝ)) * (k : ℝ) ^ k / (k.factorial : ℝ)

theorem cK_zero : cK 0 = 0 := by simp [cK]

theorem cK_one : cK 1 = 1 - Real.exp (-1) := by simp [cK]

theorem one_sub_exp_neg_one_nonneg : 0 ≤ 1 - Real.exp (-1) := by
  have := Real.exp_le_one_iff.mpr (by norm_num : (-1 : ℝ) ≤ 0)
  linarith

theorem one_sub_exp_neg_one_le_one : 1 - Real.exp (-1) ≤ 1 := by
  linarith [Real.exp_pos (-1)]

/-- The numeric check behind both counterexamples: `1 - 1/e > 3/5`, so `(1 - 1/e) c > 1`
once `c ≥ 5/3`. -/
theorem one_lt_one_sub_exp_neg_one_mul {c : ℝ} (hc : 5 / 3 ≤ c) :
    1 < (1 - Real.exp (-1)) * c := by
  have he := Real.exp_one_gt_d9
  have hinv : (Real.exp 1)⁻¹ < 2 / 5 := by
    rw [inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
    norm_num
    linarith
  rw [Real.exp_neg]
  nlinarith

variable {α : Type*} [DecidableEq α]

/-- Expectation of `g` over a random subset of `U` that contains each `i ∈ U`
independently with probability `p i`. -/
noncomputable def indepExp (U : Finset α) (p : α → ℝ) (g : Finset α → ℝ) : ℝ :=
  ∑ S ∈ U.powerset, ((∏ i ∈ S, p i) * ∏ i ∈ U \ S, (1 - p i)) * g S

/-- The probabilities in `indepExp` sum to one. -/
theorem indepExp_one (U : Finset α) (p : α → ℝ) : indepExp U p (fun _ => 1) = 1 := by
  unfold indepExp
  simp only [mul_one]
  rw [← Finset.prod_add]
  simp

/-- Each outcome's probability is non-negative when every `p i` is in `[0, 1]`. -/
theorem indepExp_weight_nonneg {U S : Finset α} {p : α → ℝ}
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (hS : S ∈ U.powerset) :
    0 ≤ (∏ i ∈ S, p i) * ∏ i ∈ U \ S, (1 - p i) := by
  rw [Finset.mem_powerset] at hS
  apply mul_nonneg
  · exact Finset.prod_nonneg fun i hi => (hp i (hS hi)).1
  · exact Finset.prod_nonneg fun i hi =>
      sub_nonneg.mpr (hp i (Finset.mem_sdiff.mp hi).1).2

/-- Expectation is monotone. -/
theorem indepExp_mono {U : Finset α} {p : α → ℝ} {g h : Finset α → ℝ}
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (hgh : ∀ S ⊆ U, g S ≤ h S) :
    indepExp U p g ≤ indepExp U p h := by
  unfold indepExp
  apply Finset.sum_le_sum
  intro S hS
  exact mul_le_mul_of_nonneg_left (hgh S (Finset.mem_powerset.mp hS))
    (indepExp_weight_nonneg hp hS)

end DatingAlgo
