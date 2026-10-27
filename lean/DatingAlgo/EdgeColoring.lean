import DatingAlgo.Basic

/-!
# König's edge-coloring theorem, and degree-capped subgraphs

Tools for Theorems 2 and 4 of the vault note "Truthful Swiping with an LLM Oracle". A
bipartite graph is a set `S ⊆ I × J` of pairs.

* `exists_matching_cover_max`: if every degree is at most `b ≥ 1`, some matching covers
  every vertex of degree exactly `b`. The proof embeds `S` in a `b`-regular bipartite
  multigraph (two mirrored copies of `S`, joined by `b - deg` parallel edges at each
  vertex) and applies Hall's theorem to it.
* `exists_edgeColoring` (König): a bipartite graph with all degrees at most `b` can be
  properly edge-colored with `b` colors. Induct on `b`, removing such a matching.
* `exists_degCap_subset`: if every degree is at most `b` and `k ≤ b`, some subgraph with
  every degree at most `k` keeps at least a `k/b` share of any weight. Take `k`
  consecutive colors out of `b`, cyclically: each edge lies in exactly `k` of the `b`
  windows.
-/

namespace DatingAlgo

open Finset

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- `i`'s degree in `S`. -/
def degI (S : Finset (I × J)) (i : I) : ℕ := (S.filter fun e => e.1 = i).card

/-- `j`'s degree in `S`. -/
def degJ (S : Finset (I × J)) (j : J) : ℕ := (S.filter fun e => e.2 = j).card

omit [Fintype I] [Fintype J] [DecidableEq J] in
/-- Degrees can only drop in a subgraph. -/
theorem degI_mono {S T : Finset (I × J)} (h : T ⊆ S) (i : I) : degI T i ≤ degI S i :=
  card_le_card (filter_subset_filter _ h)

omit [Fintype I] [DecidableEq I] [Fintype J] in
/-- Degrees can only drop in a subgraph. -/
theorem degJ_mono {S T : Finset (I × J)} (h : T ⊆ S) (j : J) : degJ T j ≤ degJ S j :=
  card_le_card (filter_subset_filter _ h)

omit [Fintype I] in
/-- `i`'s degree counts the `j` with `(i, j) ∈ S`. -/
theorem degI_eq_sum (S : Finset (I × J)) (i : I) :
    degI S i = ∑ j, if (i, j) ∈ S then 1 else 0 := by
  rw [← card_filter, degI]
  refine card_bij (fun e _ => e.2) ?_ ?_ ?_
  · rintro ⟨i', j⟩ he
    simp only [mem_filter] at he
    obtain ⟨he, rfl⟩ := he
    simpa using he
  · rintro ⟨i1, j1⟩ h1 ⟨i2, j2⟩ h2 h
    simp only [mem_filter] at h1 h2
    simp_all
  · intro j hj
    exact ⟨(i, j), by simpa using hj, rfl⟩

omit [Fintype J] in
/-- `j`'s degree counts the `i` with `(i, j) ∈ S`. -/
theorem degJ_eq_sum (S : Finset (I × J)) (j : J) :
    degJ S j = ∑ i, if (i, j) ∈ S then 1 else 0 := by
  rw [← card_filter, degJ]
  refine card_bij (fun e _ => e.1) ?_ ?_ ?_
  · rintro ⟨i, j'⟩ he
    simp only [mem_filter] at he
    obtain ⟨he, rfl⟩ := he
    simpa using he
  · rintro ⟨i1, j1⟩ h1 ⟨i2, j2⟩ h2 h
    simp only [mem_filter] at h1 h2
    simp_all
  · intro i hi
    exact ⟨(i, j), by simpa using hi, rfl⟩

omit [Fintype I] [Fintype J] in
/-- Removing a subgraph `N ⊆ S` lowers each degree by its degree in `N`. -/
theorem degI_sdiff_add {S N : Finset (I × J)} (h : N ⊆ S) (i : I) :
    degI (S \ N) i + degI N i = degI S i := by
  unfold degI
  rw [show (S \ N).filter (fun e => e.1 = i) = S.filter (fun e => e.1 = i) \
    N.filter (fun e => e.1 = i) by ext; simp only [mem_filter, mem_sdiff]; tauto]
  exact card_sdiff_add_card_eq_card (filter_subset_filter _ h)

omit [Fintype I] [Fintype J] in
/-- Removing a subgraph `N ⊆ S` lowers each degree by its degree in `N`. -/
theorem degJ_sdiff_add {S N : Finset (I × J)} (h : N ⊆ S) (j : J) :
    degJ (S \ N) j + degJ N j = degJ S j := by
  unfold degJ
  rw [show (S \ N).filter (fun e => e.2 = j) = S.filter (fun e => e.2 = j) \
    N.filter (fun e => e.2 = j) by ext; simp only [mem_filter, mem_sdiff]; tauto]
  exact card_sdiff_add_card_eq_card (filter_subset_filter _ h)

omit [Fintype I] [Fintype J] in
/-- Two edges of a matching that share an endpoint are equal. -/
theorem eq_of_matching {N : Finset (I × J)} (hNI : ∀ i, degI N i ≤ 1)
    (hNJ : ∀ j, degJ N j ≤ 1) {e e' : I × J} (he : e ∈ N) (he' : e' ∈ N)
    (h : e.1 = e'.1 ∨ e.2 = e'.2) : e = e' := by
  rcases h with h | h
  · exact card_le_one.mp (hNI e.1) e (by simp [he]) e' (by simp [he', h])
  · exact card_le_one.mp (hNJ e.2) e (by simp [he]) e' (by simp [he', h])

/-- **Hall's theorem for regular multigraphs.** If every row of a matrix `m` of
multiplicities sums to at least `b ≥ 1` and every column to at most `b`, some injection
picks a positive entry in every row. -/
theorem exists_injective_of_mult {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (m : α → β → ℕ) {b : ℕ} (hb : 1 ≤ b) (hrow : ∀ a, b ≤ ∑ y, m a y)
    (hcol : ∀ y, ∑ a, m a y ≤ b) :
    ∃ f : α → β, Function.Injective f ∧ ∀ a, 0 < m a (f a) := by
  refine (Fintype.all_card_le_filter_rel_iff_exists_injective (fun a y => 0 < m a y)).mp ?_
  intro A
  set N : Finset β := {y | ∃ a ∈ A, 0 < m a y}
  refine Nat.le_of_mul_le_mul_left ?_ hb
  calc b * #A = ∑ a ∈ A, b := by rw [sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ a ∈ A, ∑ y, m a y := sum_le_sum fun a _ => hrow a
    _ = ∑ a ∈ A, ∑ y ∈ N, m a y := by
        refine sum_congr rfl fun a ha => (sum_subset (subset_univ N) fun y _ hy => ?_).symm
        simp only [N, mem_filter, mem_univ, true_and, not_exists, not_and, not_lt] at hy
        exact Nat.le_zero.mp (hy a ha)
    _ = ∑ y ∈ N, ∑ a ∈ A, m a y := sum_comm
    _ ≤ ∑ y ∈ N, ∑ a, m a y := sum_le_sum fun y _ => sum_le_sum_of_subset (subset_univ A)
    _ ≤ ∑ y ∈ N, b := sum_le_sum fun y _ => hcol y
    _ = b * #N := by rw [sum_const, smul_eq_mul, mul_comm]

/-- The `b`-regular bipartite multigraph of `exists_matching_cover_max`. Left side
`I ⊕ J`, right side `J ⊕ I`: two mirrored copies of `S`, plus `b - deg` parallel edges
joining the two copies of each vertex. -/
def hallMult (S : Finset (I × J)) (b : ℕ) : I ⊕ J → J ⊕ I → ℕ
  | .inl i, .inl j => if (i, j) ∈ S then 1 else 0
  | .inl i, .inr i' => if i = i' then b - degI S i else 0
  | .inr j, .inr i => if (i, j) ∈ S then 1 else 0
  | .inr j, .inl j' => if j = j' then b - degJ S j else 0

/-- Every row of `hallMult` sums to `b`. -/
theorem hallMult_row (S : Finset (I × J)) {b : ℕ} (hI : ∀ i, degI S i ≤ b)
    (hJ : ∀ j, degJ S j ≤ b) (a : I ⊕ J) : ∑ y, hallMult S b a y = b := by
  rw [Fintype.sum_sum_type]
  cases a with
  | inl i =>
    simp only [hallMult]
    rw [← degI_eq_sum, sum_ite_eq]
    simp only [mem_univ, ↓reduceIte]
    have := hI i
    omega
  | inr j =>
    simp only [hallMult]
    rw [← degJ_eq_sum, sum_ite_eq]
    simp only [mem_univ, ↓reduceIte]
    have := hJ j
    omega

/-- Every column of `hallMult` sums to `b`. -/
theorem hallMult_col (S : Finset (I × J)) {b : ℕ} (hI : ∀ i, degI S i ≤ b)
    (hJ : ∀ j, degJ S j ≤ b) (y : J ⊕ I) : ∑ a, hallMult S b a y = b := by
  rw [Fintype.sum_sum_type]
  cases y with
  | inl j =>
    simp only [hallMult]
    rw [← degJ_eq_sum, sum_ite_eq']
    simp only [mem_univ, ↓reduceIte]
    have := hJ j
    omega
  | inr i =>
    simp only [hallMult]
    rw [← degI_eq_sum, sum_ite_eq']
    simp only [mem_univ, ↓reduceIte]
    have := hI i
    omega

/-- **Hall step.** If every degree in `S` is at most `b ≥ 1`, some matching `N ⊆ S`
covers every vertex of degree exactly `b`. -/
theorem exists_matching_cover_max (S : Finset (I × J)) {b : ℕ} (hb : 1 ≤ b)
    (hI : ∀ i, degI S i ≤ b) (hJ : ∀ j, degJ S j ≤ b) :
    ∃ N ⊆ S, (∀ i, degI N i ≤ 1) ∧ (∀ j, degJ N j ≤ 1) ∧
      (∀ i, degI S i = b → degI N i = 1) ∧ ∀ j, degJ S j = b → degJ N j = 1 := by
  obtain ⟨f, hf, hpos⟩ := exists_injective_of_mult (hallMult S b) hb
    (fun a => (hallMult_row S hI hJ a).ge) (fun y => (hallMult_col S hI hJ y).le)
  have hsurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hf, by simp only [Fintype.card_sum, add_comm]⟩).2
  set N : Finset (I × J) := {e | f (.inl e.1) = .inl e.2}
  have hmem : ∀ i j, (i, j) ∈ N ↔ f (.inl i) = .inl j := by simp [N]
  have hNI : ∀ i, degI N i ≤ 1 := by
    intro i
    rw [degI, card_le_one]
    rintro ⟨i1, j1⟩ h1 ⟨i2, j2⟩ h2
    simp only [mem_filter, hmem] at h1 h2
    obtain ⟨h1, rfl⟩ := h1
    obtain ⟨h2, rfl⟩ := h2
    obtain rfl := Sum.inl_injective (h1.symm.trans h2)
    rfl
  have hNJ : ∀ j, degJ N j ≤ 1 := by
    intro j
    rw [degJ, card_le_one]
    rintro ⟨i1, j1⟩ h1 ⟨i2, j2⟩ h2
    simp only [mem_filter, hmem] at h1 h2
    obtain ⟨h1, rfl⟩ := h1
    obtain ⟨h2, rfl⟩ := h2
    obtain rfl := Sum.inl_injective (hf (h1.trans h2.symm))
    rfl
  refine ⟨N, ?_, hNI, hNJ, ?_, ?_⟩
  · rintro ⟨i, j⟩ he
    have h := hpos (.inl i)
    rw [(hmem i j).mp he] at h
    simp only [hallMult] at h
    split_ifs at h with hij
    · exact hij
    · exact absurd h (lt_irrefl 0)
  · intro i hi
    have h := hpos (.inl i)
    rcases hfi : f (.inl i) with j | i'
    · exact le_antisymm (hNI i) (card_pos.mpr ⟨(i, j), by simp [hmem, hfi]⟩)
    · rw [hfi] at h
      simp only [hallMult] at h
      split_ifs at h <;> omega
  · intro j hj
    obtain ⟨a, ha⟩ := hsurj (.inl j)
    cases a with
    | inl i => exact le_antisymm (hNJ j) (card_pos.mpr ⟨(i, j), by simp [hmem, ha]⟩)
    | inr j' =>
      have h := hpos (.inr j')
      rw [ha] at h
      simp only [hallMult] at h
      split_ifs at h with hjj
      · subst hjj
        omega
      · omega

/-- **König's edge-coloring theorem.** A bipartite graph with all degrees at most `b`
has a proper edge coloring with colors `0, …, b - 1`: edges that share an endpoint get
different colors. -/
theorem exists_edgeColoring (S : Finset (I × J)) (b : ℕ) (hI : ∀ i, degI S i ≤ b)
    (hJ : ∀ j, degJ S j ≤ b) :
    ∃ col : I × J → ℕ, (∀ e ∈ S, col e < b) ∧
      ∀ e ∈ S, ∀ e' ∈ S, e ≠ e' → (e.1 = e'.1 ∨ e.2 = e'.2) → col e ≠ col e' := by
  induction b generalizing S with
  | zero =>
    have hS : S = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun e he => ?_
      have h := hI e.1
      rw [degI, Nat.le_zero, card_eq_zero, eq_empty_iff_forall_notMem] at h
      exact h e (by simp [he])
    subst hS
    exact ⟨fun _ => 0, by simp, by simp⟩
  | succ b ih =>
    obtain ⟨N, hNS, hNI, hNJ, hcI, hcJ⟩ := exists_matching_cover_max S (Nat.succ_pos b) hI hJ
    have hI' : ∀ i, degI (S \ N) i ≤ b := by
      intro i
      have h := degI_sdiff_add hNS i
      by_cases hi : degI S i = b + 1
      · have := hcI i hi
        omega
      · have := hI i
        omega
    have hJ' : ∀ j, degJ (S \ N) j ≤ b := by
      intro j
      have h := degJ_sdiff_add hNS j
      by_cases hj : degJ S j = b + 1
      · have := hcJ j hj
        omega
      · have := hJ j
        omega
    obtain ⟨col, hlt, hprop⟩ := ih (S \ N) hI' hJ'
    refine ⟨fun e => if e ∈ N then b else col e, fun e he => ?_, ?_⟩
    · dsimp only
      split_ifs with h
      · exact Nat.lt_succ_self b
      · exact Nat.lt_succ_of_lt (hlt e (mem_sdiff.mpr ⟨he, h⟩))
    · intro e he e' he' hne hshare
      simp only
      split_ifs with h1 h2 h2
      · exact absurd (eq_of_matching hNI hNJ h1 h2 hshare) hne
      · exact (hlt e' (mem_sdiff.mpr ⟨he', h2⟩)).ne'
      · exact (hlt e (mem_sdiff.mpr ⟨he, h1⟩)).ne
      · exact hprop e (mem_sdiff.mpr ⟨he, h1⟩) e' (mem_sdiff.mpr ⟨he', h2⟩) hne hshare

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
/-- A window of `k ≤ b` consecutive residues mod `b`, shifted by `y`, holds exactly `k`
of `0, …, b - 1`. -/
theorem card_filter_add_mod_lt {b k : ℕ} (hkb : k ≤ b) (y : ℕ) :
    #{x ∈ range b | (x + y) % b < k} = k := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp only [range_zero, filter_empty, card_empty]
    omega
  have hinj : Set.InjOn (fun x => (x + y) % b) (range b) := by
    intro x hx x' hx' h
    simp only [coe_range, Set.mem_Iio] at hx hx'
    have : x ≡ x' [MOD b] := Nat.ModEq.add_right_cancel' y h
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hx'] at this
  have himage : (range b).image (fun x => (x + y) % b) = range b := by
    refine eq_of_subset_of_card_le (fun z hz => ?_) (by rw [card_image_of_injOn hinj])
    obtain ⟨x, -, rfl⟩ := mem_image.mp hz
    exact mem_range.mpr (Nat.mod_lt _ hb)
  calc #{x ∈ range b | (x + y) % b < k}
      = #(({x ∈ range b | (x + y) % b < k}).image fun x => (x + y) % b) :=
        (card_image_of_injOn (hinj.mono (coe_subset.mpr (filter_subset _ _)))).symm
    _ = #{z ∈ range b | z < k} := by conv_rhs => rw [← himage, filter_image]
    _ = k := by
        rw [show ({z ∈ range b | z < k} : Finset ℕ) = range k by
          ext z
          simp only [mem_filter, mem_range]
          omega]
        exact card_range k

/-- **Degree-capped subgraphs.** If every degree in `S` is at most `b` and `k ≤ b`, then
for any weights some `T ⊆ S` with every degree at most `k` has `k ∑_S w ≤ b ∑_T w`. -/
theorem exists_degCap_subset (S : Finset (I × J)) {b k : ℕ} (hkb : k ≤ b)
    (hI : ∀ i, degI S i ≤ b) (hJ : ∀ j, degJ S j ≤ b) (w : I × J → ℝ) :
    ∃ T ⊆ S, (∀ i, degI T i ≤ k) ∧ (∀ j, degJ T j ≤ k) ∧
      (k : ℝ) * ∑ e ∈ S, w e ≤ b * ∑ e ∈ T, w e := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨∅, empty_subset _, fun i => by simp [degI], fun j => by simp [degJ], by simp⟩
  have hb : 0 < b := lt_of_lt_of_le hk hkb
  obtain ⟨col, hlt, hprop⟩ := exists_edgeColoring S b hI hJ
  obtain ⟨T, hT⟩ : ∃ T : ℕ → Finset (I × J), T = fun s => {e ∈ S | (col e + s) % b < k} :=
    ⟨_, rfl⟩
  have hsum : ∑ s ∈ range b, ∑ e ∈ T s, w e = k * ∑ e ∈ S, w e := by
    simp only [hT, sum_filter]
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun e _ => ?_
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    congr 1
    simp_rw [add_comm (col e)]
    exact_mod_cast card_filter_add_mod_lt hkb (col e)
  obtain ⟨s, -, hs⟩ := exists_le_of_sum_le (s := range b)
    (f := fun _ => (k : ℝ) * ∑ e ∈ S, w e) (g := fun s => (b : ℝ) * ∑ e ∈ T s, w e)
    (nonempty_range_iff.mpr hb.ne') (by
      rw [sum_const, card_range, nsmul_eq_mul, ← mul_sum, hsum])
  refine ⟨T s, hT ▸ filter_subset _ _, fun i => ?_, fun j => ?_, hs⟩
  · rw [degI, ← card_filter_add_mod_lt hkb s]
    refine card_le_card_of_injOn col (fun e he => ?_) (fun e he e' he' h => ?_)
    · simp only [hT, mem_coe, mem_filter] at he
      simp [hlt e he.1.1, he.1.2]
    · simp only [hT, mem_coe, mem_filter] at he he'
      by_contra hne
      exact hprop e he.1.1 e' he'.1.1 hne (Or.inl (he.2.trans he'.2.symm)) h
  · rw [degJ, ← card_filter_add_mod_lt hkb s]
    refine card_le_card_of_injOn col (fun e he => ?_) (fun e he e' he' h => ?_)
    · simp only [hT, mem_coe, mem_filter] at he
      simp [hlt e he.1.1, he.1.2]
    · simp only [hT, mem_coe, mem_filter] at he he'
      by_contra hne
      exact hprop e he.1.1 e' he'.1.1 hne (Or.inr (he.2.trans he'.2.symm)) h

end DatingAlgo
