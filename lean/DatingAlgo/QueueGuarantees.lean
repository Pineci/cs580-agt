import DatingAlgo.MaxMinSDH
import DatingAlgo.BalancedCRS
import DatingAlgo.UniformRule
import DatingAlgo.LiveSet

/-!
# Guarantees for the responder queue and its queried versions

Conversation guarantees of the vault notes "Welfare of Truthful Feeds in the Two-Cost
Model" (Theorem C) and "Queries and the Live-Set Theorem" (Theorems F and G).

**Model.** Initiators `I` browse and responders `J` see the initiators who liked them.
A pair `(i, j)` is a *mutual like* if `i` is shown `j` and both like each other. Each
responder `j` converses with at most `kJ j` of its mutual likes, so with `A` its set of
mutual likes it has `min(|A|, kJ j)` conversations. In all three mechanisms the feeds of
different initiators are drawn independently and values are independent across pairs, so
for each responder the initiators bring mutual likes independently. `queueConv kJ θ` is
the expected number of conversations when initiator `i` brings responder `j` a mutual
like with probability `θ i j`, and `fluidConv kJ m = ∑_j min(∑_i m i j, kJ j)` is the
objective of the linear programs.

* `conv_le_fluidConv` (the upper bound in Theorems C, F, G): for *any* joint law of the
  mutual likes with marginals at most `m`, expected conversations are at most
  `fluidConv kJ m`.
* `queueConv_ge`, `queue_plan_ge`, `queue_approx` (Theorem C(c)): the responder queue
  gets at least `c_K` times the LP objective, hence `c_K` times any benchmark whose
  marginals the plan dominates. With unlimited queries this is also the conversation
  guarantee of the queried queue (Theorem F with the whole queue as window).
* `screenedQueue_ge`, `screenedQueue_uniform_ge`, `screenedQueue_exists_ge`
  (Theorem G(b)): the screened queue with a `γ`-balanced selection rule gets at least
  `γ c_K` times `LP_Q`; `γ = 1/2` for the uniform rule and `γ = c_K` for the balanced
  rules of `BalancedCRS.lean`. `ScreenPlan.Feasible` is the feasible set of `LP_Q`.
* `queue_initiator_truthful`: an initiator shown at most `k` profiles has sincere
  swiping as a best strategy (Theorem A, "if" direction). For responders under the
  keep-best rule see `keepBest_sincere_best` in `LiveSet.lean`, with the query window as
  the live set.

Not formalized: the two-cap lemma (Theorem C′ and the factor `c_k c_B` of Theorem F for a
finite query window), responder surplus (Theorem C(d); its core is
`prodExp_randomWeight_gap`), Theorem D and Proposition T. That the marginals of a
mechanism in the benchmark class are bounded by a feasible plan is the modeling step of
the notes and is a hypothesis here.
-/

namespace DatingAlgo

open Finset

/-- A product of a number at most one and a number in `[0, 1]` is at most one. -/
private theorem mul_le_one_aux {a b : ℝ} (ha : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    a * b ≤ 1 := by nlinarith

section OneResponder

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- **One responder, lower bound.** If initiators bring mutual likes independently with
probabilities `θ i ≥ γ m i`, the responder's expected conversations are at least
`γ c_k min(∑ m, k)`. -/
theorem scaled_conv_ge {θ m : α → ℝ} {γ : ℝ} (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ 1) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (hm : ∀ i, 0 ≤ m i) (hθm : ∀ i, γ * m i ≤ θ i) (k : ℕ) :
    γ * (cK k * min (∑ i, m i) k) ≤ indepExp univ θ (fun A => min (A.card : ℝ) k) := by
  have h1 := poissonBinomial_min_ge univ θ (fun i _ => hθ i) k
  have h2 : γ * ∑ i, m i ≤ ∑ i, θ i := by
    rw [mul_sum]; exact sum_le_sum fun i _ => hθm i
  have hM : 0 ≤ ∑ i, m i := sum_nonneg fun i _ => hm i
  have hmin : 0 ≤ min (∑ i, m i) (k : ℝ) := le_min hM (Nat.cast_nonneg k)
  have h3 : γ * min (∑ i, m i) k ≤ min (∑ i, θ i) k := by
    apply le_min
    · exact (mul_le_mul_of_nonneg_left (min_le_left _ _) hγ0).trans h2
    · calc γ * min (∑ i, m i) k ≤ 1 * min (∑ i, m i) k :=
            mul_le_mul_of_nonneg_right hγ1 hmin
        _ ≤ k := by rw [one_mul]; exact min_le_right _ _
  calc γ * (cK k * min (∑ i, m i) k) = cK k * (γ * min (∑ i, m i) k) := by ring
    _ ≤ cK k * min (∑ i, θ i) k := mul_le_mul_of_nonneg_left h3 (cK_nonneg k)
    _ ≤ _ := h1

/-- **One responder, upper bound.** For any joint law `w` on outcomes `ω` and any random
set `A ω` of mutual likes, expected conversations are at most `min(∑_i Pr[i ∈ A], k)`. -/
theorem conv_le_min {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hw1 : ∑ ω, w ω = 1) (A : Ω → Finset α) (k : ℕ) :
    ∑ ω, w ω * min ((A ω).card : ℝ) k ≤
      min (∑ i, ∑ ω, w ω * (if i ∈ A ω then 1 else 0)) k := by
  apply le_min
  · have hc : ∑ i, ∑ ω, w ω * (if i ∈ A ω then (1 : ℝ) else 0) = ∑ ω, w ω * (A ω).card := by
      rw [sum_comm]
      refine sum_congr rfl fun ω _ => ?_
      rw [← mul_sum]
      congr 1
      simp
    rw [hc]
    exact sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (min_le_left _ _) (hw ω)
  · calc ∑ ω, w ω * min ((A ω).card : ℝ) k ≤ ∑ ω, w ω * k :=
          sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (min_le_right _ _) (hw ω)
      _ = k := by rw [← sum_mul, hw1, one_mul]

end OneResponder

section Queue

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The LP objective: `∑_j min(∑_i m i j, kJ j)`, the fluid number of conversations when
`m i j` is the probability that `(i, j)` is a mutual like. -/
noncomputable def fluidConv (kJ : J → ℕ) (m : I → J → ℝ) : ℝ :=
  ∑ j, min (∑ i, m i j) (kJ j)

/-- Expected conversations when, for each responder `j`, the initiators bring mutual likes
independently with probabilities `θ i j`, and `j` converses with at most `kJ j` of them. -/
noncomputable def queueConv (kJ : J → ℕ) (θ : I → J → ℝ) : ℝ :=
  ∑ j, indepExp univ (fun i => θ i j) (fun A => min (A.card : ℝ) (kJ j))

omit [DecidableEq J] in
/-- Lower bound with a loss factor `γ` on the initiator side. -/
theorem queueConv_ge_scaled {kJ : J → ℕ} {θ m : I → J → ℝ} {γ : ℝ} {K : ℕ}
    (hK : ∀ j, K ≤ kJ j) (hθ : ∀ i j, 0 ≤ θ i j ∧ θ i j ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hm : ∀ i j, 0 ≤ m i j) (hθm : ∀ i j, γ * m i j ≤ θ i j) :
    γ * (cK K * fluidConv kJ m) ≤ queueConv kJ θ := by
  unfold fluidConv queueConv
  rw [mul_sum, mul_sum]
  refine sum_le_sum fun j _ => ?_
  have h := scaled_conv_ge (θ := fun i => θ i j) (m := fun i => m i j) (fun i => hθ i j) hγ0
    hγ1 (fun i => hm i j) (fun i => hθm i j) (kJ j)
  have hmin : 0 ≤ min (∑ i, m i j) (kJ j : ℝ) :=
    le_min (sum_nonneg fun i _ => hm i j) (Nat.cast_nonneg _)
  have hc : cK K * min (∑ i, m i j) (kJ j) ≤ cK (kJ j) * min (∑ i, m i j) (kJ j) :=
    mul_le_mul_of_nonneg_right (cK_mono (hK j)) hmin
  calc γ * (cK K * min (∑ i, m i j) (kJ j))
      ≤ γ * (cK (kJ j) * min (∑ i, m i j) (kJ j)) := mul_le_mul_of_nonneg_left hc hγ0
    _ ≤ _ := h

omit [DecidableEq J] in
/-- **Theorem C(c), lower bound.** The responder queue gets at least `c_K` times the LP
objective, where `K` is at most every responder's limit. -/
theorem queueConv_ge {kJ : J → ℕ} {θ : I → J → ℝ} {K : ℕ} (hK : ∀ j, K ≤ kJ j)
    (hθ : ∀ i j, 0 ≤ θ i j ∧ θ i j ≤ 1) : cK K * fluidConv kJ θ ≤ queueConv kJ θ := by
  have h := queueConv_ge_scaled (γ := 1) hK hθ zero_le_one le_rfl (fun i j => (hθ i j).1)
    (fun i j => by rw [one_mul])
  rwa [one_mul] at h

omit [DecidableEq J] in
/-- **Theorem C(c) for a plan.** If initiator `i` is shown `j` with probability `x i j`,
likes `j` with probability `pIJ i j` and is accepted with probability `pJI j i`, the queue
gets at least `c_K` times `LP_1`'s objective at `x`. -/
theorem queue_plan_ge {kJ : J → ℕ} {x pIJ : I → J → ℝ} {pJI : J → I → ℝ} {K : ℕ}
    (hK : ∀ j, K ≤ kJ j) (hx : ∀ i j, 0 ≤ x i j ∧ x i j ≤ 1)
    (hpIJ : ∀ i j, 0 ≤ pIJ i j ∧ pIJ i j ≤ 1) (hpJI : ∀ j i, 0 ≤ pJI j i ∧ pJI j i ≤ 1) :
    cK K * fluidConv kJ (fun i j => x i j * pIJ i j * pJI j i) ≤
      queueConv kJ (fun i j => x i j * pIJ i j * pJI j i) := by
  refine queueConv_ge hK fun i j => ⟨?_, ?_⟩
  · exact mul_nonneg (mul_nonneg (hx i j).1 (hpIJ i j).1) (hpJI j i).1
  · have h1 : x i j * pIJ i j ≤ 1 := mul_le_one_aux (hx i j).2 (hpIJ i j).1 (hpIJ i j).2
    exact mul_le_one_aux h1 (hpJI j i).1 (hpJI j i).2

omit [DecidableEq J] in
/-- **The upper bound in Theorems C, F and G.** Take any mechanism: a joint law `w` on
outcomes `ω` and, for each responder `j`, the random set `A ω j` of initiators that are
mutual likes of `j`. If the marginals are at most `m`, expected conversations are at most
the LP objective `fluidConv kJ m`. -/
theorem conv_le_fluidConv {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hw1 : ∑ ω, w ω = 1) (A : Ω → J → Finset I) (kJ : J → ℕ) {m : I → J → ℝ}
    (hmarg : ∀ i j, ∑ ω, w ω * (if i ∈ A ω j then 1 else 0) ≤ m i j) :
    ∑ j, ∑ ω, w ω * min ((A ω j).card : ℝ) (kJ j) ≤ fluidConv kJ m := by
  unfold fluidConv
  refine sum_le_sum fun j _ => ?_
  refine (conv_le_min w hw hw1 (fun ω => A ω j) (kJ j)).trans ?_
  exact min_le_min (sum_le_sum fun i _ => hmarg i j) le_rfl

omit [DecidableEq J] in
/-- **Theorem C(c), approximation.** If the plan's LP objective is at least that of a
benchmark mechanism's marginals `m'`, the queue gets at least `c_K` times the benchmark's
expected conversations. -/
theorem queue_approx {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (hw1 : ∑ ω, w ω = 1) (A : Ω → J → Finset I) {kJ : J → ℕ} {θ m' : I → J → ℝ} {K : ℕ}
    (hK : ∀ j, K ≤ kJ j) (hθ : ∀ i j, 0 ≤ θ i j ∧ θ i j ≤ 1)
    (hmarg : ∀ i j, ∑ ω, w ω * (if i ∈ A ω j then 1 else 0) ≤ m' i j)
    (hopt : fluidConv kJ m' ≤ fluidConv kJ θ) :
    cK K * ∑ j, ∑ ω, w ω * min ((A ω j).card : ℝ) (kJ j) ≤ queueConv kJ θ :=
  (mul_le_mul_of_nonneg_left ((conv_le_fluidConv w hw hw1 A kJ hmarg).trans hopt)
    (cK_nonneg K)).trans (queueConv_ge hK hθ)

end Queue

/-! ### The screened queue (Theorem G) -/

/-- A plan for the screened queue: the variables of `LP_Q`. For the pair `(i, j)`,
`u` is the probability of proposing `j` to `i` unscreened, `τ` of asking `j`'s oracle,
`s1` of proposing after a yes from `j`'s oracle, `g` of then asking `i`'s oracle, and
`s2` of proposing after a second yes. -/
structure ScreenPlan (I J : Type*) where
  u : I → J → ℝ
  τ : I → J → ℝ
  s1 : I → J → ℝ
  g : I → J → ℝ
  s2 : I → J → ℝ

namespace ScreenPlan

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The probability that `j` is proposed to `i`. -/
def proposal (P : ScreenPlan I J) (i : I) (j : J) : ℝ := P.u i j + P.s1 i j + P.s2 i j

/-- The probability that `j` is proposed to `i` and the two like each other: an unscreened
proposal is a mutual like with probability `pIJ pJI`, a screened one with probability
`pIJ`, a double-screened one for sure. -/
def mutualProb (P : ScreenPlan I J) (pIJ : I → J → ℝ) (pJI : J → I → ℝ) (i : I) (j : J) : ℝ :=
  P.u i j * pIJ i j * pJI j i + P.s1 i j * pIJ i j + P.s2 i j

/-- The constraints of `LP_Q`: probabilities, one kind per pair, answers independent of
the decision to ask, at most `kI i` proposals in expectation, and the call budgets. -/
structure Feasible (P : ScreenPlan I J) (kI : I → ℕ) (pIJ : I → J → ℝ) (pJI : J → I → ℝ)
    (BI : I → ℝ) (BJ : J → ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ P.u i j ∧ 0 ≤ P.τ i j ∧ 0 ≤ P.s1 i j ∧ 0 ≤ P.g i j ∧ 0 ≤ P.s2 i j
  kind : ∀ i j, P.u i j + P.τ i j ≤ 1
  screen : ∀ i j, P.s1 i j + P.g i j ≤ P.τ i j * pJI j i
  double : ∀ i j, P.s2 i j ≤ P.g i j * pIJ i j
  cap : ∀ i, ∑ j, P.proposal i j ≤ kI i
  budgetJ : ∀ j, ∑ i, P.τ i j ≤ BJ j
  budgetI : ∀ i, ∑ j, P.g i j ≤ BI i

omit [DecidableEq I] [DecidableEq J] in
/-- Proposal probabilities of a feasible plan are probabilities. -/
theorem Feasible.proposal_mem {P : ScreenPlan I J} {kI : I → ℕ} {pIJ : I → J → ℝ}
    {pJI : J → I → ℝ} {BI : I → ℝ} {BJ : J → ℝ} (hP : P.Feasible kI pIJ pJI BI BJ)
    (hpIJ : ∀ i j, 0 ≤ pIJ i j ∧ pIJ i j ≤ 1) (hpJI : ∀ j i, 0 ≤ pJI j i ∧ pJI j i ≤ 1)
    (i : I) (j : J) : 0 ≤ P.proposal i j ∧ P.proposal i j ≤ 1 := by
  obtain ⟨hu, hτ, hs1, hg, hs2⟩ := hP.nonneg i j
  have h1 : P.g i j * pIJ i j ≤ P.g i j := mul_le_of_le_one_right hg (hpIJ i j).2
  have h2 : P.τ i j * pJI j i ≤ P.τ i j := mul_le_of_le_one_right hτ (hpJI j i).2
  have h3 := hP.kind i j
  have h4 := hP.screen i j
  have h5 := hP.double i j
  unfold proposal
  constructor <;> linarith

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
/-- A mutual like needs a proposal. -/
theorem mutualProb_mem {P : ScreenPlan I J} {pIJ : I → J → ℝ} {pJI : J → I → ℝ}
    (hn : ∀ i j, 0 ≤ P.u i j ∧ 0 ≤ P.s1 i j ∧ 0 ≤ P.s2 i j)
    (hpIJ : ∀ i j, 0 ≤ pIJ i j ∧ pIJ i j ≤ 1) (hpJI : ∀ j i, 0 ≤ pJI j i ∧ pJI j i ≤ 1)
    (i : I) (j : J) : 0 ≤ P.mutualProb pIJ pJI i j ∧ P.mutualProb pIJ pJI i j ≤ P.proposal i j := by
  obtain ⟨hu, hs1, hs2⟩ := hn i j
  have h1 : 0 ≤ P.u i j * pIJ i j := mul_nonneg hu (hpIJ i j).1
  have h2 : P.u i j * pIJ i j ≤ P.u i j := mul_le_of_le_one_right hu (hpIJ i j).2
  have h3 : 0 ≤ P.u i j * pIJ i j * pJI j i := mul_nonneg h1 (hpJI j i).1
  have h4 : P.u i j * pIJ i j * pJI j i ≤ P.u i j * pIJ i j :=
    mul_le_of_le_one_right h1 (hpJI j i).2
  have h5 : 0 ≤ P.s1 i j * pIJ i j := mul_nonneg hs1 (hpIJ i j).1
  have h6 : P.s1 i j * pIJ i j ≤ P.s1 i j := mul_le_of_le_one_right hs1 (hpIJ i j).2
  unfold mutualProb proposal
  constructor <;> linarith

end ScreenPlan

section Screened

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The probability that initiator `i` is shown `j`: the profiles proposed to `i` are
independent with probabilities `π i`, and the selection rule `ψ i` keeps some of them. -/
noncomputable def shownProb (π : I → J → ℝ) (ψ : I → Finset J → Finset J → ℝ) (i : I)
    (j : J) : ℝ :=
  indepExp univ (π i) (fun A => ruleKeep (ψ i) A j)

/-- The probability that `i` brings `j` a mutual like in the screened queue. The rule sees
only which profiles are proposed, so given that `j` is shown, the pair is a mutual like
with probability `m i j / π i j`. -/
noncomputable def screenedTheta (π m : I → J → ℝ) (ψ : I → Finset J → Finset J → ℝ) (i : I)
    (j : J) : ℝ :=
  shownProb π ψ i j * (m i j / π i j)

omit [Fintype I] [DecidableEq I] in
theorem screenedTheta_mem {π m : I → J → ℝ} {ψ : I → Finset J → Finset J → ℝ} {kI : I → ℕ}
    (hπ : ∀ i j, 0 ≤ π i j ∧ π i j ≤ 1) (hm : ∀ i j, 0 ≤ m i j ∧ m i j ≤ π i j)
    (hψ : ∀ i, IsRule (kI i) (ψ i)) (i : I) (j : J) :
    0 ≤ screenedTheta π m ψ i j ∧ screenedTheta π m ψ i j ≤ 1 := by
  have hs : 0 ≤ shownProb π ψ i j ∧ shownProb π ψ i j ≤ 1 :=
    indepExp_mem_Icc (fun k _ => hπ i k) fun A => ruleKeep_mem (hψ i) A j
  have hr0 : 0 ≤ m i j / π i j := div_nonneg (hm i j).1 (hπ i j).1
  have hr1 : m i j / π i j ≤ 1 := div_le_one_of_le₀ (hm i j).2 (hπ i j).1
  exact ⟨mul_nonneg hs.1 hr0, mul_le_one_aux hs.2 hr0 hr1⟩

omit [Fintype I] [DecidableEq I] in
/-- With a `γ`-balanced rule, `i` brings `j` a mutual like with probability at least
`γ m i j`. -/
theorem screenedTheta_ge {π m : I → J → ℝ} {ψ : I → Finset J → Finset J → ℝ} {kI : I → ℕ}
    {γ : ℝ} (hπ : ∀ i j, 0 ≤ π i j ∧ π i j ≤ 1) (hm : ∀ i j, 0 ≤ m i j ∧ m i j ≤ π i j)
    (hψ : ∀ i, IsRule (kI i) (ψ i)) (hbal : ∀ i, IsBalanced (π i) γ (ψ i)) (i : I) (j : J) :
    γ * m i j ≤ screenedTheta π m ψ i j := by
  have hb : γ * π i j ≤ shownProb π ψ i j := hbal i j
  have hr0 : 0 ≤ m i j / π i j := div_nonneg (hm i j).1 (hπ i j).1
  rcases (hπ i j).1.eq_or_lt with h0 | hpos
  · have hm0 : m i j = 0 := le_antisymm (by rw [h0]; exact (hm i j).2) (hm i j).1
    rw [hm0, mul_zero]
    exact (screenedTheta_mem hπ hm hψ i j).1
  · calc γ * m i j = γ * π i j * (m i j / π i j) := by field_simp
      _ ≤ shownProb π ψ i j * (m i j / π i j) := mul_le_mul_of_nonneg_right hb hr0

/-- **Theorem G(b).** With `γ`-balanced selection rules, the screened queue gets at least
`γ c_K` times `LP_Q`'s objective at the plan. -/
theorem screenedQueue_ge {P : ScreenPlan I J} {kI : I → ℕ} {kJ : J → ℕ}
    {pIJ : I → J → ℝ} {pJI : J → I → ℝ} {BI : I → ℝ} {BJ : J → ℝ} {K : ℕ} {γ : ℝ}
    (hP : P.Feasible kI pIJ pJI BI BJ) (hpIJ : ∀ i j, 0 ≤ pIJ i j ∧ pIJ i j ≤ 1)
    (hpJI : ∀ j i, 0 ≤ pJI j i ∧ pJI j i ≤ 1) (hK : ∀ j, K ≤ kJ j)
    {ψ : I → Finset J → Finset J → ℝ} (hψ : ∀ i, IsRule (kI i) (ψ i)) (hγ0 : 0 ≤ γ)
    (hγ1 : γ ≤ 1) (hbal : ∀ i, IsBalanced (P.proposal i) γ (ψ i)) :
    γ * (cK K * fluidConv kJ (P.mutualProb pIJ pJI)) ≤
      queueConv kJ (screenedTheta P.proposal (P.mutualProb pIJ pJI) ψ) := by
  have hπ := hP.proposal_mem hpIJ hpJI
  have hm := ScreenPlan.mutualProb_mem (P := P)
    (fun i j => ⟨(hP.nonneg i j).1, (hP.nonneg i j).2.2.1, (hP.nonneg i j).2.2.2.2⟩) hpIJ hpJI
  exact queueConv_ge_scaled hK (screenedTheta_mem hπ hm hψ) hγ0 hγ1 (fun i j => (hm i j).1)
    (screenedTheta_ge hπ hm hψ hbal)

/-- **Theorem G(b), random rule.** Showing each initiator a uniformly random `kI i` of the
proposed profiles gets at least `c_K / 2` times `LP_Q`'s objective. -/
theorem screenedQueue_uniform_ge {P : ScreenPlan I J} {kI : I → ℕ} {kJ : J → ℕ}
    {pIJ : I → J → ℝ} {pJI : J → I → ℝ} {BI : I → ℝ} {BJ : J → ℝ} {K : ℕ}
    (hP : P.Feasible kI pIJ pJI BI BJ) (hpIJ : ∀ i j, 0 ≤ pIJ i j ∧ pIJ i j ≤ 1)
    (hpJI : ∀ j i, 0 ≤ pJI j i ∧ pJI j i ≤ 1) (hK : ∀ j, K ≤ kJ j) :
    1 / 2 * (cK K * fluidConv kJ (P.mutualProb pIJ pJI)) ≤
      queueConv kJ (screenedTheta P.proposal (P.mutualProb pIJ pJI) fun i => uniformRule (kI i)) :=
  screenedQueue_ge hP hpIJ hpJI hK (fun i => isRule_uniformRule (kI i)) (by norm_num)
    (by norm_num)
    (fun i => uniformRule_balanced (fun j => hP.proposal_mem hpIJ hpJI i j) (hP.cap i))

/-- **Theorem G(b), balanced rules.** Some selection rules get at least `c_{K'} c_K` times
`LP_Q`'s objective, where `K'` is at most every initiator's limit and `K` at most every
responder's. -/
theorem screenedQueue_exists_ge {P : ScreenPlan I J} {kI : I → ℕ} {kJ : J → ℕ}
    {pIJ : I → J → ℝ} {pJI : J → I → ℝ} {BI : I → ℝ} {BJ : J → ℝ} {K K' : ℕ}
    (hP : P.Feasible kI pIJ pJI BI BJ) (hpIJ : ∀ i j, 0 ≤ pIJ i j ∧ pIJ i j ≤ 1)
    (hpJI : ∀ j i, 0 ≤ pJI j i ∧ pJI j i ≤ 1) (hK : ∀ j, K ≤ kJ j) (hK' : ∀ i, K' ≤ kI i) :
    ∃ ψ : I → Finset J → Finset J → ℝ, (∀ i, IsRule (kI i) (ψ i)) ∧
      cK K' * (cK K * fluidConv kJ (P.mutualProb pIJ pJI)) ≤
        queueConv kJ (screenedTheta P.proposal (P.mutualProb pIJ pJI) ψ) := by
  have hπ := hP.proposal_mem hpIJ hpJI
  choose ψ hψ hbal using fun i => exists_balanced_rule (kI i) (fun j => hπ i j) (hP.cap i)
  refine ⟨ψ, hψ, screenedQueue_ge hP hpIJ hpJI hK hψ (cK_nonneg K') (cK_le_one K') fun i => ?_⟩
  exact (hbal i).mono (cK_mono (hK' i)) fun j => (hπ i j).1

end Screened

/-! ### Truthfulness of initiators -/

/-- **Initiators in the queue are exactly truthful (Theorems C, F, G (a)).** An initiator
is shown a set `D` of at most `k` profiles, and `R` is the set of profiles that would
accept and keep it, which its swipes do not change. Whatever it likes, it does no better
than by swiping sincerely. -/
theorem queue_initiator_truthful {β : Type*} [DecidableEq β] {q : β → ℝ}
    (hq : ∀ x, 0 ≤ q x) {k : ℕ} {c d : ℝ} (hd : 0 ≤ d) {D : Finset β} (hD : D.card ≤ k)
    (R N : Finset β) {L : Finset β} (hL : L ⊆ N) :
    twoCostUtil (topK q k) c d (L ∩ (D ∩ R)) ≤
      twoCostUtil (topK q k) c d (sincereSet q c N ∩ (D ∩ R)) :=
  twoCost_sincere_best_topK hq hd ((card_le_card inter_subset_left).trans hD) N hL

end DatingAlgo
