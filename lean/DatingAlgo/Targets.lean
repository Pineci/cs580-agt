import DatingAlgo.TwoPeriod

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
`E[min(X, K)] ≥ c_K · min(μ, K)`.
Expected route: a sum of Bernoullis is dominated by a Poisson with the same mean in
convex order, and the Poisson case gives exactly `c_K`. The constant `1 - 1/e`
version is proved (`cardinality_gap`). -/
theorem poissonBinomial_min_ge (U : Finset α) (p : α → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (K : ℕ) :
    cK K * min (∑ i ∈ U, p i) K ≤ indepExp U p (fun S => min (S.card : ℝ) K) := by
  sorry

/-- **R1 (vault note).** With a common display cap `K`, DH-int is a
`c_K`-approximation (`c_3 ≈ 0.776`), improving the paper's `1 - 1/e`. This follows
from `dhInt_approx_of_card_gap` once `poissonBinomial_min_ge` is proved. -/
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
