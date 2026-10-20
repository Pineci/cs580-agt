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

/-- With a display cap of zero, nothing can be shown. -/
theorem topK_zero_cap (w : α → ℝ) (B : Finset α) : topK w 0 B = 0 := by
  obtain ⟨S, _, hSK, hEq⟩ := exists_topK_eq w 0 B
  have hS : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hSK)
  rw [hEq, hS, Finset.sum_empty]

/-- Recursion: the best selection from `insert a B` either skips `a`, or takes `a`
plus the best `K` from `B`. -/
theorem topK_insert [DecidableEq α] {w : α → ℝ} {K : ℕ} {B : Finset α} {a : α}
    (ha : a ∉ B) :
    topK w (K + 1) (insert a B) = max (topK w (K + 1) B) (w a + topK w K B) := by
  apply le_antisymm
  · obtain ⟨T, hTB, hTK, hEq⟩ := exists_topK_eq w (K + 1) (insert a B)
    rw [hEq]
    by_cases haT : a ∈ T
    · rw [← Finset.add_sum_erase T w haT]
      have hsub : T.erase a ⊆ B := Finset.subset_insert_iff.mp hTB
      have hcard : (T.erase a).card ≤ K := by
        rw [Finset.card_erase_of_mem haT]; omega
      exact le_max_of_le_right (add_le_add le_rfl (sum_le_topK hsub hcard))
    · have hsub : T ⊆ B := (Finset.subset_insert_iff_of_notMem haT).mp hTB
      exact le_max_of_le_left (sum_le_topK hsub hTK)
  · refine max_le (topK_mono (Finset.subset_insert a B)) ?_
    obtain ⟨T, hTB, hTK, hEq⟩ := exists_topK_eq w K B
    have haT : a ∉ T := fun h => ha (hTB h)
    rw [hEq, ← Finset.sum_insert haT]
    exact sum_le_topK (Finset.insert_subset_insert a hTB)
      ((Finset.card_insert_le a T).trans (by omega))

/-- Adding a constant `c ≥ 0` to every weight adds at least `c · min(|S|, K)`. The
weighted correlation gap reduces to the unweighted one with this. -/
theorem topK_add_const_ge {w : α → ℝ} {K : ℕ} {S : Finset α} {c : ℝ} (_hc : 0 ≤ c)
    (hw : ∀ i ∈ S, 0 ≤ w i) :
    c * min (S.card : ℝ) K + topK w K S ≤ topK (fun i => c + w i) K S := by
  obtain ⟨T, hTS, hTK, hEq⟩ := exists_topK_eq w K S
  have hmin : T.card ≤ min S.card K := le_min (Finset.card_le_card hTS) hTK
  obtain ⟨T', hTT', hT'S, hcard⟩ :=
    Finset.exists_subsuperset_card_eq hTS hmin (min_le_left _ _)
  calc c * min (S.card : ℝ) K + topK w K S
      = c * (T'.card : ℝ) + ∑ i ∈ T, w i := by rw [hcard, Nat.cast_min, hEq]
    _ ≤ c * (T'.card : ℝ) + ∑ i ∈ T', w i :=
        add_le_add le_rfl (Finset.sum_le_sum_of_subset_of_nonneg hTT'
          (fun i hi _ => hw i (hT'S hi)))
    _ = ∑ i ∈ T', (c + w i) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ topK (fun i => c + w i) K S :=
        sum_le_topK hT'S (hcard ▸ min_le_right _ _)

/-- The empty backlog has value zero. -/
theorem topK_empty (w : α → ℝ) (K : ℕ) : topK w K ∅ = 0 := by
  obtain ⟨S, hSB, _, hEq⟩ := exists_topK_eq w K (∅ : Finset α)
  rw [hEq, Finset.subset_empty.mp hSB, Finset.sum_empty]

/-- `topK` is concave in the cap: increments in `K` are non-increasing. -/
theorem topK_concave [DecidableEq α] (w : α → ℝ) (X : Finset α) (j : ℕ) :
    topK w (j + 2) X + topK w j X ≤ 2 * topK w (j + 1) X := by
  induction X using Finset.induction_on generalizing j with
  | empty => simp [topK_empty]
  | insert x X hx ih =>
    cases j with
    | zero =>
      rw [topK_insert hx, topK_insert hx, topK_zero_cap, topK_zero_cap]
      have h0 := ih 0
      rw [topK_zero_cap] at h0
      have h1 := le_max_left (topK w (0 + 1) X) (w x + topK w 0 X)
      have h2 := le_max_right (topK w (0 + 1) X) (w x + topK w 0 X)
      rw [topK_zero_cap] at h1 h2
      rcases max_cases (topK w (0 + 1 + 1) X) (w x + topK w (0 + 1) X) with h | h <;>
        · rw [h.1]; linarith
    | succ i =>
      have hA := ih i
      have hB := ih (i + 1)
      rw [show i + 1 + 2 = (i + 2) + 1 by ring, topK_insert hx,
        show i + 1 + 1 = (i + 1) + 1 by ring, topK_insert hx,
        topK_insert hx]
      have h1 := le_max_left (topK w (i + 1 + 1) X) (w x + topK w (i + 1) X)
      have h2 := le_max_right (topK w (i + 1 + 1) X) (w x + topK w (i + 1) X)
      rcases max_cases (topK w (i + 2 + 1) X) (w x + topK w (i + 2) X) with h | h <;>
      rcases max_cases (topK w (i + 1) X) (w x + topK w i X) with h' | h' <;>
        · rw [h.1, h'.1]
          ring_nf at *
          linarith

/-- The marginal value of the `(k+1)`-th slot grows when one element is added. -/
theorem topK_gap_insert [DecidableEq α] (w : α → ℝ) (k : ℕ) {X : Finset α} {y : α}
    (hy : y ∉ X) :
    topK w (k + 1) X - topK w k X ≤ topK w (k + 1) (insert y X) - topK w k (insert y X) := by
  cases k with
  | zero =>
    rw [topK_zero_cap, topK_zero_cap]
    linarith [topK_mono (w := w) (K := 0 + 1) (Finset.subset_insert y X)]
  | succ m =>
    rw [topK_insert hy, topK_insert hy]
    have hc := topK_concave w X m
    have h1 := le_max_left (topK w (m + 1 + 1) X) (w y + topK w (m + 1) X)
    have h2 := le_max_right (topK w (m + 1 + 1) X) (w y + topK w (m + 1) X)
    rcases max_cases (topK w (m + 1) X) (w y + topK w m X) with h | h
    · rw [h.1]; linarith
    · rw [h.1]; ring_nf at *; linarith

/-- The marginal value of the `(k+1)`-th slot is monotone in the backlog. -/
theorem topK_gap_mono [DecidableEq α] (w : α → ℝ) (k : ℕ) {X X' : Finset α}
    (h : X ⊆ X') :
    topK w (k + 1) X - topK w k X ≤ topK w (k + 1) X' - topK w k X' := by
  have key : ∀ D : Finset α,
      topK w (k + 1) X - topK w k X ≤ topK w (k + 1) (X ∪ D) - topK w k (X ∪ D) := by
    intro D
    induction D using Finset.induction_on with
    | empty => simp
    | insert y D _ ih =>
      rw [Finset.union_insert]
      by_cases hy : y ∈ X ∪ D
      · rw [Finset.insert_eq_of_mem hy]; exact ih
      · exact ih.trans (topK_gap_insert w k hy)
  simpa [Finset.union_sdiff_of_subset h] using key (X' \ X)

/-- **Paper, Lemma 4.1 (core): top-K is submodular.** Adding a profile to a
smaller backlog helps at least as much as adding it to a larger one. -/
theorem topK_submodular [DecidableEq α] {w : α → ℝ} (_hw : ∀ i, 0 ≤ w i) (K : ℕ)
    {B B' : Finset α} (hBB' : B ⊆ B') (a : α) :
    topK w K (insert a B') - topK w K B' ≤ topK w K (insert a B) - topK w K B := by
  by_cases haB' : a ∈ B'
  · rw [Finset.insert_eq_of_mem haB', sub_self]
    exact sub_nonneg.mpr (topK_mono (Finset.subset_insert a B))
  · have haB : a ∉ B := fun h => haB' (hBB' h)
    cases K with
    | zero => simp [topK_zero_cap]
    | succ k =>
      rw [topK_insert haB', topK_insert haB]
      have hg := topK_gap_mono w k hBB'
      have h1 := le_max_left (topK w (k + 1) B) (w a + topK w k B)
      have h2 := le_max_right (topK w (k + 1) B) (w a + topK w k B)
      rcases max_cases (topK w (k + 1) B') (w a + topK w k B') with h | h
      · rw [h.1]; linarith
      · rw [h.1]; linarith

end DatingAlgo
