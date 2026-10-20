import DatingAlgo.Designs

/-!
# Proposition D.1: the local greedy policy can be `O(1/n)`-bad

Rios & Torrico, Appendix D. In *local greedy*, each user picks the display that maximizes
their own expected matches. With an empty initial backlog that is
`∑_{ℓ' ∈ S} φ¹_{ℓℓ'} φ¹_{ℓ'ℓ}`.

**The instance.**
- `n` users on each side; every display cap is 1.
- Every `I`-user likes every `J`-user for sure.
- `j₀` likes everyone for sure; every other `J`-user likes with probability `1 - ε`.
- So `β_{i j₀} = 1` and `β_{i j} = 1 - ε` otherwise. Period-2 rewards are zero.

**Why greedy fails.** Every `I`-user's greedy choice is `j₀`, and `j₀` can see only
one of them. Greedy therefore gets exactly one match, while showing each `iₖ` and
`jₖ` to each other gets `1 + (n - 1)(1 - ε)`.
-/

namespace DatingAlgo

open Finset

namespace Market

variable {U : Type*} [Fintype U] [DecidableEq U] (mk : Market U)

/-- Local greedy displays for period 1 (empty backlog): each user's display maximizes
their own expected number of matches, `∑ φ¹_{ℓℓ'} φ¹_{ℓ'ℓ}`, among feasible displays. -/
def IsLocalGreedy (S : U → Finset U) : Prop :=
  mk.Feasible S ∧ ∀ ℓ (T : Finset U), T ⊆ mk.pot ℓ → T.card ≤ mk.K ℓ →
    ∑ ℓ' ∈ T, mk.φ1 ℓ ℓ' * mk.φ1 ℓ' ℓ ≤ ∑ ℓ' ∈ S ℓ, mk.φ1 ℓ ℓ' * mk.φ1 ℓ' ℓ

end Market

/-- The Proposition D.1 instance: `inl k` is `iₖ` (side `I`), `inr k` is `jₖ`
(side `J`), and `j₀ = inr 0`. -/
noncomputable def greedyInstance (n : ℕ) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Market (Fin n ⊕ Fin n) where
  side := fun u => u.isLeft
  pot := fun u => match u with
    | .inl _ => univ.filter (fun v => v.isRight)
    | .inr _ => univ.filter (fun v => v.isLeft)
  K := fun _ => 1
  φ1 := fun a b => match a, b with
    | .inl _, .inr _ => 1
    | .inr j, .inl _ => if j.val = 0 then 1 else 1 - ε
    | _, _ => 0
  φ2 := fun _ _ => 0
  q := fun _ _ => 1
  pot_other_side := by
    intro a b hb
    cases a <;> cases b <;> simp_all
  φ1_nonneg := by
    intro a b
    cases a <;> cases b <;> dsimp only <;> (try split_ifs) <;> linarith
  φ1_le_one := by
    intro a b
    cases a <;> cases b <;> dsimp only <;> (try split_ifs) <;> linarith
  φ2_nonneg := fun _ _ => le_refl 0
  q_nonneg := fun _ _ => zero_le_one

section GreedyInstance

variable {n : ℕ} {ε : ℝ} {hε0 : 0 ≤ ε} {hε1 : ε ≤ 1}

/-- A finset with at most one element is empty or a singleton. -/
theorem eq_empty_or_singleton_of_card_le_one {α : Type*} {s : Finset α} (h : s.card ≤ 1) :
    s = ∅ ∨ ∃ x, s = {x} := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h | h
  · exact Or.inl (Finset.card_eq_zero.mp h)
  · exact Or.inr (Finset.card_eq_one.mp h)

/-- Every backlog of the greedy instance is worth zero, since period-2 rewards vanish. -/
theorem greedyInstance_backlogValue (S : Fin n ⊕ Fin n → Finset (Fin n ⊕ Fin n))
    (ℓ : Fin n ⊕ Fin n) :
    (greedyInstance n ε hε0 hε1).toModel.backlogValue S ℓ = 0 := by
  unfold TwoPeriodModel.backlogValue
  refine (indepExp_congr (h := fun _ => (0 : ℝ)) fun B _ => ?_).trans (indepExp_const _ _ 0)
  obtain ⟨T, _, _, hT⟩ := exists_topK_eq ((greedyInstance n ε hε0 hε1).toModel.r2 ℓ) 1 B
  rw [show (greedyInstance n ε hε0 hε1).toModel.K ℓ = 1 from rfl, hT]
  simp [Market.toModel, greedyInstance]

/-- In the greedy instance the objective is the period-1 reward `immOf`. -/
theorem greedyInstance_value (S : Fin n ⊕ Fin n → Finset (Fin n ⊕ Fin n)) :
    (greedyInstance n ε hε0 hε1).toModel.value S = (greedyInstance n ε hε0 hε1).immOf S := by
  unfold TwoPeriodModel.value
  simp only [greedyInstance_backlogValue, Finset.sum_const_zero, add_zero]
  rfl

/-- `immOf` of the greedy instance sums the mutual views seen from the `I` side. -/
theorem greedyInstance_immOf (S : Fin n ⊕ Fin n → Finset (Fin n ⊕ Fin n)) :
    (greedyInstance n ε hε0 hε1).immOf S =
      ∑ k : Fin n, ∑ ℓ' ∈ S (.inl k), if Sum.inl k ∈ S ℓ' then
        (greedyInstance n ε hε0 hε1).φ1 (.inl k) ℓ' *
          (greedyInstance n ε hε0 hε1).φ1 ℓ' (.inl k) else 0 := by
  unfold Market.immOf
  rw [Fintype.sum_sum_type]
  have hl : ∀ k, (greedyInstance n ε hε0 hε1).side (.inl k) = true := fun _ => rfl
  have hr : ∀ k, (greedyInstance n ε hε0 hε1).side (.inr k) = false := fun _ => rfl
  have hq : ∀ a b, (greedyInstance n ε hε0 hε1).q a b = 1 := fun _ _ => rfl
  simp only [hl, hr, hq, and_true, mul_one, Bool.false_eq_true, and_false, ↓reduceIte,
    Finset.sum_const_zero, add_zero]

/-- The diagonal reward: the pair of `j₀` earns `1`, every other pair `1 - ε`. -/
theorem sum_fin_ite_val_eq_zero (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) :
    ∑ k : Fin n, (if k.val = 0 then (1 : ℝ) else 1 - ε) = 1 + (n - 1) * (1 - ε) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Fin.sum_univ_succ]
  simp [Fin.val_succ]
  ring

end GreedyInstance

/-- **Proposition D.1 (greedy side).** Every local-greedy display earns exactly one
expected match. -/
theorem greedyInstance_localGreedy_value (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) (S : Fin n ⊕ Fin n → Finset (Fin n ⊕ Fin n))
    (hS : (greedyInstance n ε hε0.le hε1.le).IsLocalGreedy S) :
    (greedyInstance n ε hε0.le hε1.le).toModel.value S = 1 := by
  obtain ⟨hfeas, hgr⟩ := hS
  obtain ⟨j0, hj0⟩ : ∃ j0 : Fin n, j0.val = 0 := ⟨⟨0, hn⟩, rfl⟩
  -- Every `I`-user shows `j₀`.
  have hI : ∀ k, S (.inl k) = {.inr j0} := by
    intro k
    have hge := hgr (.inl k) {.inr j0} (by simp [greedyInstance]) (by simp [greedyInstance])
    obtain ⟨hsub, hcard⟩ := hfeas (.inl k)
    rcases eq_empty_or_singleton_of_card_le_one hcard with h | ⟨x, h⟩
    · rw [h] at hge
      norm_num [greedyInstance, hj0] at hge
    · rw [h] at hge hsub ⊢
      have hx := hsub (Finset.mem_singleton_self x)
      rcases x with i | j
      · simp [greedyInstance] at hx
      · simp only [Finset.sum_singleton] at hge
        change (1 : ℝ) * (if j0.val = 0 then 1 else 1 - ε) ≤
          1 * (if j.val = 0 then 1 else 1 - ε) at hge
        simp only [hj0, ↓reduceIte] at hge
        split_ifs at hge with hj
        · rw [show j = j0 from Fin.ext (hj.trans hj0.symm)]
        · linarith
  -- `j₀` shows exactly one `I`-user.
  obtain ⟨istar, hJ⟩ : ∃ i, S (.inr j0) = {.inl i} := by
    have hge := hgr (.inr j0) {.inl j0} (by simp [greedyInstance]) (by simp [greedyInstance])
    obtain ⟨hsub, hcard⟩ := hfeas (.inr j0)
    rcases eq_empty_or_singleton_of_card_le_one hcard with h | ⟨x, h⟩
    · rw [h] at hge
      norm_num [greedyInstance, hj0] at hge
    · rw [h] at hsub
      have hx := hsub (Finset.mem_singleton_self x)
      rcases x with i | j
      · exact ⟨i, h⟩
      · simp [greedyInstance] at hx
  rw [greedyInstance_value, greedyInstance_immOf]
  simp only [hI, Finset.sum_singleton, hJ, Finset.mem_singleton, Sum.inl.injEq]
  simp [greedyInstance, hj0]

/-- **Proposition D.1 (optimal side).** Showing each `iₖ` and `jₖ` to each other is
feasible and earns `1 + (n - 1)(1 - ε)` expected matches. -/
theorem greedyInstance_diagonal_value (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) :
    ∃ S, (greedyInstance n ε hε0.le hε1.le).TwoDirectional S ∧
      (greedyInstance n ε hε0.le hε1.le).toModel.value S = 1 + (n - 1) * (1 - ε) := by
  refine ⟨fun u => {u.swap}, ?_, ?_⟩
  · intro u
    cases u <;> simp [greedyInstance]
  · rw [greedyInstance_value, greedyInstance_immOf, ← sum_fin_ite_val_eq_zero n hn ε]
    simp only [Sum.swap_inl, Sum.swap_inr, Finset.sum_singleton, Finset.mem_singleton,
      ↓reduceIte]
    exact Finset.sum_congr rfl fun k _ => one_mul _

end DatingAlgo
