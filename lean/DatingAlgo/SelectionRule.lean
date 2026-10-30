import DatingAlgo.ProdExp

/-!
# Selection rules

A user who can keep at most `K` partners receives a random set `A` of candidates and
keeps a random subset of it. A *rule* `ψ` gives the law of the kept set: `ψ A T` is the
probability of keeping `T` when the candidates are `A`. The rule sees only `A` and its own
coins, never the candidates' values, so a policy built from rules stays swipe-local
(vault note "Truthful Swiping with an LLM Oracle", T1).

* `IsRule K ψ`: `ψ A` is a probability law on subsets of `A` with at most `K` elements.
* `ruleKeep ψ A e`: the probability that the rule keeps `e` when the candidates are `A`.
* `IsBalanced y γ ψ`: when each `e` is a candidate independently with probability
  `y e`, the rule keeps `e` with probability at least `γ · y e`. This is a `γ`-balanced
  contention-resolution scheme (Chekuri, Vondrák and Zenklusen). Max-min SDH needs
  balance, a guarantee for every element, because a guarantee on total weight says
  nothing about any one user (vault note "Max-Min Match Quality and Egalitarian
  Matching").
* `uniformRule K`: keep a uniformly random `min K |A|` of the candidates, which is what
  showing candidates in random order and keeping the first `K` does.

`UniformRule.lean` shows that `uniformRule K` is `1/2`-balanced whenever the expected
number of candidates is at most `K`. `BalancedCRS.lean` shows that some rule is
`c_K`-balanced, by Sion's minimax theorem and the `c_K` correlation gap.
-/

namespace DatingAlgo

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `ψ` is a selection rule for a user with cap `K`: for every candidate set `A`, `ψ A`
is a probability law on the subsets of `A` with at most `K` elements. -/
def IsRule (K : ℕ) (ψ : Finset α → Finset α → ℝ) : Prop :=
  ∀ A, (∀ T, 0 ≤ ψ A T) ∧ ∑ T, ψ A T = 1 ∧ ∀ T, ψ A T ≠ 0 → T ⊆ A ∧ T.card ≤ K

/-- The probability that rule `ψ` keeps `e` when the candidates are `A`. -/
noncomputable def ruleKeep (ψ : Finset α → Finset α → ℝ) (A : Finset α) (e : α) : ℝ :=
  ∑ T, ψ A T * if e ∈ T then 1 else 0

/-- `ψ` is `γ`-balanced for candidate probabilities `y`: when each `e` is a candidate
independently with probability `y e`, the rule keeps `e` with probability at least
`γ · y e`. -/
def IsBalanced (y : α → ℝ) (γ : ℝ) (ψ : Finset α → Finset α → ℝ) : Prop :=
  ∀ e, γ * y e ≤ indepExp univ y (fun A => ruleKeep ψ A e)

/-- Keep a uniformly random `min K |A|` of the candidates `A`. -/
noncomputable def uniformRule (K : ℕ) (A T : Finset α) : ℝ :=
  if T ⊆ A ∧ T.card = min K A.card then ((A.card.choose (min K A.card) : ℕ) : ℝ)⁻¹ else 0

end DatingAlgo
