import DatingAlgo.Basic
import DatingAlgo.TopK

/-!
# Open proof targets

Statements we want to prove but haven't yet. Each is closed with `sorry`, so the
project still builds and the statement is type-checked. `lean/check.sh` lists every
remaining `sorry`; move a theorem out of this file once it is proved.

Keep each statement faithful to the math in the vault note "Match Quality in the
Dating Heuristic Framework". A wrong statement proved is worse than an open one.
-/

namespace DatingAlgo

open Finset

variable {α : Type*} [DecidableEq α]

/-- **Target (R1, key lemma): Poisson-binomial bound.**
For a sum `X` of independent coin flips with mean `μ`,
`E[min(X, K)] ≥ c_K · min(μ, K)`. This gives DH-int's sharper constant `c_K`.
Expected route: a sum of Bernoullis is dominated by a Poisson with the same mean in
convex order, and the Poisson case gives exactly `c_K`. -/
theorem poissonBinomial_min_ge (U : Finset α) (p : α → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (K : ℕ) :
    cK K * min (∑ i ∈ U, p i) K ≤ indepExp U p (fun S => min (S.card : ℝ) K) := by
  sorry

/-- **Target (R1/R2): weighted correlation gap for top-K.**
For non-negative weights and any fractional plan `y` that respects the like
probabilities (`y ≤ p`) and the display cap (`∑ y ≤ K`), the realized value
`E[topK]` is at least `c_K` times the planned value. This is the step that replaces
`1 - 1/e` in the paper's proof of Theorem 4.3. It follows from
`poissonBinomial_min_ge` by the layer-cake argument in the vault note. -/
theorem topK_correlation_gap (U : Finset α) (p w y : α → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (hw : ∀ i, 0 ≤ w i) (K : ℕ)
    (hy : ∀ i ∈ U, 0 ≤ y i ∧ y i ≤ p i) (hyK : ∑ i ∈ U, y i ≤ K) :
    cK K * ∑ i ∈ U, w i * y i ≤ indepExp U p (topK w K) := by
  sorry

/-- **Target (paper, Lemma 4.1): top-K is submodular.**
Adding a profile to a smaller backlog helps at least as much as adding it to a
larger one. -/
theorem topK_submodular {w : α → ℝ} (hw : ∀ i, 0 ≤ w i) (K : ℕ) {B B' : Finset α}
    (hBB' : B ⊆ B') (a : α) :
    topK w K (insert a B') - topK w K B' ≤ topK w K (insert a B) - topK w K B := by
  sorry

end DatingAlgo
