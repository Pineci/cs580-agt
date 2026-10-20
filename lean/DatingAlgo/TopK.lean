import DatingAlgo.Basic

/-!
# Weighted top-K

`topK w K B` is the best total weight of at most `K` elements of `B`.

In the two-period model of Rios & Torrico, a responder `ℓ` with backlog `B` and
display cap `K_ℓ` gets expected value `topK w K_ℓ B` in period 2, where
`w ℓ' = φ²_{ℓℓ'}` (or `φ²_{ℓℓ'} q_{ℓℓ'}` for the quality-weighted variant).
These lemmas are the deterministic facts the paper's proof uses about this function.
-/

namespace DatingAlgo

open Finset

variable {α : Type*}

/-- Best total weight of at most `K` elements of `B`. -/
noncomputable def topK (w : α → ℝ) (K : ℕ) (B : Finset α) : ℝ :=
  (B.powerset.filter (fun S => S.card ≤ K)).sup'
    ⟨∅, by simp⟩ (fun S => ∑ i ∈ S, w i)

/-- Any subset of `B` with at most `K` elements is a lower bound. -/
theorem sum_le_topK {w : α → ℝ} {K : ℕ} {B S : Finset α} (hSB : S ⊆ B)
    (hSK : S.card ≤ K) : ∑ i ∈ S, w i ≤ topK w K B := by
  unfold topK
  exact Finset.le_sup' (fun S => ∑ i ∈ S, w i)
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSB, hSK⟩)

/-- `topK` is attained by some subset of `B` with at most `K` elements. -/
theorem exists_topK_eq (w : α → ℝ) (K : ℕ) (B : Finset α) :
    ∃ S ⊆ B, S.card ≤ K ∧ topK w K B = ∑ i ∈ S, w i := by
  unfold topK
  obtain ⟨S, hS, hEq⟩ := Finset.exists_mem_eq_sup'
    (⟨∅, by simp⟩ : (B.powerset.filter (fun S => S.card ≤ K)).Nonempty)
    (fun S => ∑ i ∈ S, w i)
  obtain ⟨hSB, hSK⟩ := Finset.mem_filter.mp hS
  exact ⟨S, Finset.mem_powerset.mp hSB, hSK, hEq⟩

/-- A larger backlog never hurts. -/
theorem topK_mono {w : α → ℝ} {K : ℕ} {B B' : Finset α} (h : B ⊆ B') :
    topK w K B ≤ topK w K B' := by
  obtain ⟨S, hSB, hSK, hEq⟩ := exists_topK_eq w K B
  rw [hEq]
  exact sum_le_topK (hSB.trans h) hSK

/-- The value is never negative, because showing nobody is always allowed. -/
theorem topK_nonneg {w : α → ℝ} {K : ℕ} {B : Finset α} :
    0 ≤ topK w K B := by
  have := sum_le_topK (w := w) (K := K) (Finset.empty_subset B) (by simp)
  simpa using this

/-- When the backlog fits in the display cap, show all of it. The paper's Lemma C.4
uses this. -/
theorem topK_eq_sum_of_card_le {w : α → ℝ} {K : ℕ} {B : Finset α}
    (hw : ∀ i, 0 ≤ w i) (hB : B.card ≤ K) : topK w K B = ∑ i ∈ B, w i := by
  apply le_antisymm
  · obtain ⟨S, hSB, _, hEq⟩ := exists_topK_eq w K B
    rw [hEq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hSB fun i _ _ => hw i
  · exact sum_le_topK (Finset.Subset.refl B) hB

end DatingAlgo
