import DatingAlgo.SelectionRule

/-!
# The uniform rule is `1/2`-balanced

`uniformRule K` keeps a uniformly random `min K |A|` of the candidates `A`: show them in
random order and keep the first `K`. Each candidate is kept with probability
`min 1 (K / |A|)`. When each `e` is a candidate independently with probability `y e`
and `∑ y ≤ K`, the number `D` of other candidates has mean at most `K`, and the bound
`min 1 (K / (1 + d)) ≥ 1 - d / (2K)` for natural `d` gives keep probability at least
`1 - E[D] / (2K) ≥ 1/2` (vault note "Max-Min Match Quality and Egalitarian Matching",
Correction).

* `isRule_uniformRule`: it is a rule for cap `K`.
* `ruleKeep_uniformRule`: a candidate is kept with probability `min 1 (K / |A|)`.
* `min_one_div_ge`: `1 - d / (2K) ≤ min 1 (K / (1 + d))` for natural `d` and `K ≥ 1`.
* `uniformRule_balanced`: it is `1/2`-balanced when `∑ y ≤ K`.
-/

namespace DatingAlgo

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Sums against `uniformRule K A` are averages over the `min K |A|`-subsets of `A`. -/
theorem sum_uniformRule_mul (K : ℕ) (A : Finset α) (g : Finset α → ℝ) :
    ∑ T, uniformRule K A T * g T =
      ((A.card.choose (min K A.card) : ℕ) : ℝ)⁻¹ *
        ∑ T ∈ A.powersetCard (min K A.card), g T := by
  rw [Finset.mul_sum]
  have hP : A.powersetCard (min K A.card) =
      univ.filter (fun T => T ⊆ A ∧ T.card = min K A.card) := by
    ext T
    simp [mem_powersetCard]
  rw [hP, Finset.sum_filter]
  refine Finset.sum_congr rfl fun T _ => ?_
  unfold uniformRule
  split_ifs <;> simp

/-- `uniformRule K` is a selection rule for cap `K`. -/
theorem isRule_uniformRule (K : ℕ) : IsRule K (uniformRule (α := α) K) := by
  intro A
  refine ⟨fun T => ?_, ?_, fun T hT => ?_⟩
  · unfold uniformRule
    split_ifs <;> positivity
  · have h := sum_uniformRule_mul K A (fun _ => 1)
    simp only [mul_one] at h
    rw [h, Finset.sum_const, card_powersetCard, nsmul_eq_mul, mul_one]
    have hpos : (0 : ℝ) < ((A.card.choose (min K A.card) : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_pos (min_le_right K A.card)
    exact inv_mul_cancel₀ hpos.ne'
  · unfold uniformRule at hT
    split_ifs at hT with h
    · exact ⟨h.1, h.2 ▸ min_le_left K A.card⟩
    · exact (hT rfl).elim

omit [Fintype α] in
/-- The `(m + 1)`-subsets of `A` that contain `e ∈ A` number `choose (|A| - 1) m`. -/
theorem card_filter_mem_powersetCard {A : Finset α} {e : α} (he : e ∈ A) (m : ℕ) :
    ((A.powersetCard (m + 1)).filter (fun T => e ∈ T)).card = (A.card - 1).choose m := by
  have hc : (A.powersetCard (m + 1)).filter (fun T => e ∈ T) =
      ((A.erase e).powersetCard m).image (insert e) := by
    ext T
    simp only [mem_filter, mem_powersetCard, mem_image]
    constructor
    · rintro ⟨⟨hTA, hTc⟩, heT⟩
      refine ⟨T.erase e, ⟨erase_subset_erase e hTA, ?_⟩, insert_erase heT⟩
      rw [card_erase_of_mem heT, hTc]
      rfl
    · rintro ⟨S, ⟨hSA, hSc⟩, rfl⟩
      have heS : e ∉ S := fun h => notMem_erase e A (hSA h)
      exact ⟨⟨insert_subset he (hSA.trans (erase_subset e A)),
        by rw [card_insert_of_notMem heS, hSc]⟩, mem_insert_self e S⟩
  rw [hc, card_image_of_injOn, card_powersetCard, card_erase_of_mem he]
  intro S₁ hS₁ S₂ hS₂ h
  have h₁ : e ∉ S₁ := fun h' => notMem_erase e A ((mem_powersetCard.mp hS₁).1 h')
  have h₂ : e ∉ S₂ := fun h' => notMem_erase e A ((mem_powersetCard.mp hS₂).1 h')
  rw [← erase_insert h₁, ← erase_insert h₂]
  exact congrArg (fun T => T.erase e) h

/-- A candidate is kept with probability `min 1 (K / |A|)`. -/
theorem ruleKeep_uniformRule (K : ℕ) {A : Finset α} {e : α} (he : e ∈ A) :
    ruleKeep (uniformRule K) A e = min 1 ((K : ℝ) / A.card) := by
  unfold ruleKeep
  rw [sum_uniformRule_mul, Finset.sum_boole]
  have hn : 0 < A.card := card_pos.mpr ⟨e, he⟩
  have hnR : (0 : ℝ) < A.card := by exact_mod_cast hn
  -- `min K |A| / |A| = min 1 (K / |A|)`
  have hmin : ((min K A.card : ℕ) : ℝ) / A.card = min 1 ((K : ℝ) / A.card) := by
    rcases le_total K A.card with h | h
    · rw [min_eq_left h, min_eq_right ((div_le_one hnR).mpr (by exact_mod_cast h))]
    · rw [min_eq_right h, div_self hnR.ne',
        min_eq_left ((one_le_div hnR).mpr (by exact_mod_cast h))]
  rw [← hmin]
  obtain ⟨n, hn'⟩ : ∃ n, A.card = n + 1 := ⟨A.card - 1, by omega⟩
  rcases Nat.eq_zero_or_eq_succ_pred (min K A.card) with hm | hm
  · rw [hm]
    simp
  · set m := (min K A.card).pred
    rw [hm, card_filter_mem_powersetCard he m]
    have key := Nat.add_one_mul_choose_eq n m
    rw [hn', Nat.succ_eq_add_one]
    simp only [Nat.add_sub_cancel]
    have hcpos : (0 : ℝ) < (((n + 1).choose (m + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_pos (by have := min_le_right K A.card; omega)
    have keyR : ((n : ℝ) + 1) * (n.choose m : ℝ) =
        ((n + 1).choose (m + 1) : ℝ) * ((m : ℝ) + 1) := by
      exact_mod_cast key
    rw [eq_div_iff (by positivity), inv_mul_eq_div, div_mul_eq_mul_div, div_eq_iff hcpos.ne']
    push_cast
    linarith [keyR]

/-- The linear lower bound behind the `1/2`. -/
theorem min_one_div_ge {K : ℕ} (hK : 1 ≤ K) (d : ℕ) :
    1 - (d : ℝ) / (2 * K) ≤ min 1 ((K : ℝ) / (1 + d)) := by
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hd : (0 : ℝ) ≤ d := d.cast_nonneg
  have h2K : (0 : ℝ) < 2 * K := by linarith
  have h1d : (0 : ℝ) < 1 + d := by linarith
  apply le_min
  · have : 0 ≤ (d : ℝ) / (2 * K) := div_nonneg hd h2K.le
    linarith
  · rcases le_or_gt K d with h | h
    · have hdK : (K : ℝ) ≤ d := by exact_mod_cast h
      rw [show 1 - (d : ℝ) / (2 * K) = (2 * K - d) / (2 * K) by field_simp,
        div_le_div_iff₀ h2K h1d]
      nlinarith [sq_nonneg ((d : ℝ) - K),
        mul_nonneg (sub_nonneg.mpr hKR) (by linarith : (0 : ℝ) ≤ K)]
    · have hdK : (d : ℝ) + 1 ≤ K := by exact_mod_cast h
      have : 1 ≤ (K : ℝ) / (1 + d) := (one_le_div h1d).mpr (by linarith)
      have : 0 ≤ (d : ℝ) / (2 * K) := div_nonneg hd h2K.le
      linarith

/-- The uniform rule keeps every candidate with non-negative probability. -/
theorem ruleKeep_uniformRule_nonneg (K : ℕ) (A : Finset α) (e : α) :
    0 ≤ ruleKeep (uniformRule K) A e := by
  unfold ruleKeep
  refine Finset.sum_nonneg fun T _ => mul_nonneg ((isRule_uniformRule K A).1 T) ?_
  split_ifs <;> norm_num

/-- **The uniform rule is `1/2`-balanced** whenever the expected number of candidates is
at most `K`. -/
theorem uniformRule_balanced {K : ℕ} {y : α → ℝ} (hy : ∀ e, 0 ≤ y e ∧ y e ≤ 1)
    (hK : ∑ e, y e ≤ K) : IsBalanced y (1 / 2) (uniformRule K) := by
  intro e
  set f : Finset α → ℝ := fun A => ruleKeep (uniformRule K) A e with hf
  set U := (univ : Finset α).erase e
  have hyU : ∀ i ∈ U, 0 ≤ y i ∧ y i ≤ 1 := fun i _ => hy i
  have hins : (univ : Finset α) = insert e U := (insert_erase (mem_univ e)).symm
  rw [hins, indepExp_insert (notMem_erase e univ)]
  have hX : 0 ≤ indepExp U y f := by
    have := indepExp_mono hyU (g := fun _ => 0) (h := f)
      (fun S _ => ruleKeep_uniformRule_nonneg K S e)
    rwa [indepExp_const] at this
  have hye := hy e
  have hX' : 0 ≤ (1 - y e) * indepExp U y f := mul_nonneg (by linarith) hX
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · -- `K = 0` forces `y e = 0`.
    have : y e ≤ 0 := by
      have := single_le_sum (fun i _ => (hy i).1) (mem_univ e)
      rw [hK0] at hK
      push_cast at hK
      linarith
    have hye0 : y e = 0 := le_antisymm this hye.1
    rw [hye0]
    linarith
  · have hK1 : 1 ≤ K := hKpos
    have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
    -- the pointwise bound `f (insert e S) ≥ 1 - |S| / (2K)`
    have hpt : ∀ S ⊆ U, 1 - (S.card : ℝ) / (2 * K) ≤ f (insert e S) := by
      intro S hS
      have heS : e ∉ S := fun h => notMem_erase e univ (hS h)
      simp only [hf]
      rw [ruleKeep_uniformRule K (mem_insert_self e S), card_insert_of_notMem heS]
      push_cast
      rw [add_comm]
      exact min_one_div_ge hK1 S.card
    have hlin : indepExp U y (fun S => 1 - (S.card : ℝ) / (2 * K)) =
        1 - (∑ i ∈ U, y i) / (2 * K) := by
      have h := indepExp_add U y (fun _ => 1) (fun S => (-(1 / (2 * K))) * (S.card : ℝ))
      rw [indepExp_const, indepExp_const_mul, indepExp_card] at h
      rw [show (fun S : Finset α => 1 - (S.card : ℝ) / (2 * K)) =
          fun S => 1 + (-(1 / (2 * K))) * (S.card : ℝ) from funext fun S => by ring, h]
      ring
    have hsumU : ∑ i ∈ U, y i ≤ K :=
      (sum_le_univ_sum_of_nonneg fun i => (hy i).1).trans hK
    have hY : 1 / 2 ≤ indepExp U y (fun S => f (insert e S)) := by
      have h := indepExp_mono hyU hpt
      rw [hlin] at h
      have : (∑ i ∈ U, y i) / (2 * K) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by positivity)]
        linarith
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hY hye.1]

end DatingAlgo
