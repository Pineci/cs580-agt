import DatingAlgo.Basic

/-!
# R3: DH-int as written, judged on match quality

Abstract forms of result R3 in the vault note "Match Quality in the Dating Heuristic
Framework". They are stated in terms of the numbers involved: expected count `C`,
expected quality `Q`, and the optimum `OPT` of each. A full formalization would
derive the hypotheses from a model of policies.
-/

namespace DatingAlgo

/-- **R3 (bounded quality range).** Suppose every match has quality in
`[qmin, qmax]` and an algorithm is a `c`-approximation for the expected number of
matches. Then it is a `c * qmin / qmax`-approximation for expected quality.

* `hAlgQ`: each of the algorithm's matches is worth at least `qmin`.
* `hOptQ`: the quality-optimal policy gets at most `qmax` per match, and it has
  at most `optC` matches in expectation.
* `hAlgC`: the count guarantee. -/
theorem quality_ratio_of_count_ratio {c qmin qmax algC algQ optC optQ : ℝ}
    (hc : 0 ≤ c) (hqmin : 0 < qmin) (hqmax : 0 < qmax)
    (hAlgQ : qmin * algC ≤ algQ) (hOptQ : optQ ≤ qmax * optC)
    (hAlgC : c * optC ≤ algC) :
    c * (qmin / qmax) * optQ ≤ algQ := by
  have hk : 0 ≤ c * (qmin / qmax) := mul_nonneg hc (div_nonneg hqmin.le hqmax.le)
  have hq : qmax ≠ 0 := hqmax.ne'
  calc c * (qmin / qmax) * optQ
      ≤ c * (qmin / qmax) * (qmax * optC) := mul_le_mul_of_nonneg_left hOptQ hk
    _ = qmin * (c * optC) := by field_simp
    _ ≤ qmin * algC := mul_le_mul_of_nonneg_left hAlgC hqmin.le
    _ ≤ algQ := hAlgQ

/-- **R3 (count and quality conflict): the impossibility instance.**
One slot and two options. Option A is a sure match of quality 0. Option B is a match
with probability `ε` and quality 1. The best count is 1 (choose A); the best quality
is `ε` (choose B).

A policy that picks A with probability `θ` gets count `θ + (1 - θ) ε` and quality
`(1 - θ) ε`. Its two approximation ratios `α` and `β` therefore satisfy
`α + β ≤ 1 + ε`. -/
theorem count_quality_tradeoff {θ ε : ℝ} (hθ0 : 0 ≤ θ) (_hθ1 : θ ≤ 1) (hε : 0 < ε) :
    (θ * 1 + (1 - θ) * ε) / 1 + (θ * 0 + (1 - θ) * (ε * 1)) / ε ≤ 1 + ε := by
  have hε' : ε ≠ 0 := hε.ne'
  have h : (θ * 0 + (1 - θ) * (ε * 1)) / ε = 1 - θ := by
    rw [mul_zero, zero_add, mul_one, mul_div_assoc, div_self hε', mul_one]
  rw [h, div_one]
  nlinarith

/-- **R3 (count and quality conflict): mixing achieves the trade-off.**
Run a count-approximation (count at least `c * optC`) with probability `θ`, and a
quality-approximation (quality at least `c * optQ`) otherwise. In expectation the
mixture gets at least `θ c` of the best count and `(1 - θ) c` of the best quality. -/
theorem mixture_guarantee {θ c optC optQ countA countB qualA qualB : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hA : c * optC ≤ countA) (hB : c * optQ ≤ qualB)
    (hcountB : 0 ≤ countB) (hqualA : 0 ≤ qualA) :
    θ * c * optC ≤ θ * countA + (1 - θ) * countB ∧
      (1 - θ) * c * optQ ≤ θ * qualA + (1 - θ) * qualB := by
  have h1θ : 0 ≤ 1 - θ := sub_nonneg.mpr hθ1
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hA hθ0, mul_nonneg h1θ hcountB]
  · nlinarith [mul_le_mul_of_nonneg_left hB h1θ, mul_nonneg hθ0 hqualA]

end DatingAlgo
