import DatingAlgo.PoissonGap

/-!
# Expectations over independent finite random variables

`prodExp μ g` is the expectation of `g ω` when the coordinates `ω e` (for `e` in a
finite type `ι`) are independent and `ω e = o` with probability `μ e o`. It extends
`indepExp`, where every coordinate is a coin, to coordinates with finitely many
outcomes, such as the value combination of a pair in screened DH (vault note
"Truthful Swiping with an LLM Oracle").

Expectations are finite sums, so no measure theory is needed. The tools:
- linearity, monotonicity and constants;
- `prodExp_coord`: the law of one coordinate;
- `prodExp_map`: applying a function to each coordinate pushes the law forward;
- `prodExp_filter`: a function of the set of coordinates that satisfy a predicate is an
  `indepExp` over coins;
- `prodExp_curry`: coordinates indexed by `I × J`, regrouped into independent blocks
  indexed by `J`;
- `prodExp_randomWeight_gap`: the `c_K` gap for independent random weights, from the
  layer cake and R1's lemma `poissonBinomial_min_ge`.
-/

namespace DatingAlgo

open Finset

section ProdExp

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

/-- Expectation of `g ω` when the coordinates `ω e` are independent and `ω e = o` with
probability `μ e o`. -/
noncomputable def prodExp (μ : ι → Ω → ℝ) (g : (ι → Ω) → ℝ) : ℝ :=
  ∑ ω : ι → Ω, (∏ e, μ e (ω e)) * g ω

/-- `μ e` is a probability distribution on `Ω` for every coordinate `e`. -/
def IsDist (μ : ι → Ω → ℝ) : Prop :=
  (∀ e o, 0 ≤ μ e o) ∧ ∀ e, ∑ o, μ e o = 1

theorem prodExp_congr (μ : ι → Ω → ℝ) {g h : (ι → Ω) → ℝ} (hgh : ∀ ω, g ω = h ω) :
    prodExp μ g = prodExp μ h := by
  unfold prodExp
  exact sum_congr rfl fun ω _ => by rw [hgh ω]

theorem prodExp_add (μ : ι → Ω → ℝ) (g h : (ι → Ω) → ℝ) :
    prodExp μ (fun ω => g ω + h ω) = prodExp μ g + prodExp μ h := by
  unfold prodExp
  rw [← sum_add_distrib]
  exact sum_congr rfl fun ω _ => by ring

theorem prodExp_const_mul (μ : ι → Ω → ℝ) (c : ℝ) (g : (ι → Ω) → ℝ) :
    prodExp μ (fun ω => c * g ω) = c * prodExp μ g := by
  unfold prodExp
  rw [mul_sum]
  exact sum_congr rfl fun ω _ => by ring

theorem prodExp_sum {κ : Type*} (s : Finset κ) (μ : ι → Ω → ℝ) (g : κ → (ι → Ω) → ℝ) :
    prodExp μ (fun ω => ∑ k ∈ s, g k ω) = ∑ k ∈ s, prodExp μ (g k) := by
  unfold prodExp
  simp_rw [mul_sum]
  exact sum_comm

/-- The outcome probabilities multiply out: `∑_ω ∏_e μ e (ω e) = ∏_e ∑_o μ e o`. -/
theorem sum_prod_weight (μ : ι → Ω → ℝ) :
    ∑ ω : ι → Ω, ∏ e, μ e (ω e) = ∏ e, ∑ o, μ e o :=
  (Fintype.prod_sum (fun e o => μ e o)).symm

theorem prodExp_const {μ : ι → Ω → ℝ} (hμ : ∀ e, ∑ o, μ e o = 1) (c : ℝ) :
    prodExp μ (fun _ => c) = c := by
  unfold prodExp
  rw [← sum_mul, sum_prod_weight]
  simp [hμ]

theorem prodExp_mono {μ : ι → Ω → ℝ} (hμ : ∀ e o, 0 ≤ μ e o) {g h : (ι → Ω) → ℝ}
    (hgh : ∀ ω, g ω ≤ h ω) : prodExp μ g ≤ prodExp μ h := by
  unfold prodExp
  exact sum_le_sum fun ω _ =>
    mul_le_mul_of_nonneg_left (hgh ω) (prod_nonneg fun e _ => hμ e _)

theorem prodExp_nonneg {μ : ι → Ω → ℝ} (hμ : ∀ e o, 0 ≤ μ e o) {g : (ι → Ω) → ℝ}
    (hg : ∀ ω, 0 ≤ g ω) : 0 ≤ prodExp μ g := by
  unfold prodExp
  exact sum_nonneg fun ω _ => mul_nonneg (prod_nonneg fun e _ => hμ e _) (hg ω)

/-- The law of one coordinate: `E[g (ω e)] = ∑_o μ e o · g o`. -/
theorem prodExp_coord [DecidableEq Ω] {μ : ι → Ω → ℝ} (hμ : ∀ e, ∑ o, μ e o = 1) (e : ι)
    (g : Ω → ℝ) : prodExp μ (fun ω => g (ω e)) = ∑ o, μ e o * g o := by
  unfold prodExp
  rw [← sum_fiberwise univ (fun ω : ι → Ω => ω e)]
  refine sum_congr rfl fun o _ => ?_
  rw [sum_congr rfl (g := fun ω => (∏ e, μ e (ω e)) * g o) (fun ω hω => by
    simp only [(mem_filter.mp hω).2]), ← sum_mul]
  congr 1
  have hset : univ.filter (fun ω : ι → Ω => ω e = o) =
      Fintype.piFinset (fun e' => if e' = e then ({o} : Finset Ω) else univ) := by
    ext ω
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h e'
      split_ifs with h'
      · subst h'; simp [h]
      · exact mem_univ _
    · intro h
      simpa using h e
  rw [hset, ← prod_univ_sum, ← mul_prod_erase univ _ (mem_univ e)]
  rw [prod_congr rfl (g := fun _ => (1 : ℝ)) (fun e' he' => by
    simp [ne_of_mem_erase he', hμ e'])]
  simp

/-- Pushing the law forward along a map applied to each coordinate. -/
theorem prodExp_map {Ω' : Type*} [Fintype Ω'] [DecidableEq Ω'] (μ : ι → Ω → ℝ)
    (f : ι → Ω → Ω') (g : (ι → Ω') → ℝ) :
    prodExp μ (fun ω => g (fun e => f e (ω e))) =
      prodExp (fun e o' => ∑ o ∈ univ.filter (fun o => f e o = o'), μ e o) g := by
  unfold prodExp
  have key : ∀ ω' : ι → Ω', (∏ e, ∑ o ∈ univ.filter (fun o => f e o = ω' e), μ e o) =
      ∑ ω ∈ univ.filter (fun ω : ι → Ω => (fun e => f e (ω e)) = ω'), ∏ e, μ e (ω e) := by
    intro ω'
    rw [prod_univ_sum]
    refine sum_congr ?_ fun _ _ => rfl
    ext ω
    simp [Fintype.mem_piFinset, funext_iff]
  simp_rw [key, sum_mul]
  rw [← sum_fiberwise univ (fun ω : ι → Ω => fun e => f e (ω e))]
  refine sum_congr rfl fun ω' _ => sum_congr rfl fun ω hω => ?_
  rw [(mem_filter.mp hω).2]

omit [Fintype ι] [DecidableEq ι] in
/-- The pushed-forward laws are again distributions. -/
theorem isDist_map {Ω' : Type*} [Fintype Ω'] [DecidableEq Ω'] {μ : ι → Ω → ℝ}
    (hμ : IsDist μ) (f : ι → Ω → Ω') :
    IsDist (fun e o' => ∑ o ∈ univ.filter (fun o => f e o = o'), μ e o) := by
  refine ⟨fun e o' => sum_nonneg fun o _ => hμ.1 e o, fun e => ?_⟩
  rw [sum_fiberwise univ (f e) (μ e), hμ.2 e]

/-- A function of the set of coordinates satisfying `P` is an expectation over
independent coins: coordinate `e` is in the set with probability
`∑_{o, P e o} μ e o`. -/
theorem prodExp_filter {μ : ι → Ω → ℝ} (hμ : ∀ e, ∑ o, μ e o = 1) (P : ι → Ω → Prop)
    [∀ e, DecidablePred (P e)] (h : Finset ι → ℝ) :
    prodExp μ (fun ω => h (univ.filter fun e => P e (ω e))) =
      indepExp univ (fun e => ∑ o ∈ univ.filter (P e), μ e o) h := by
  unfold prodExp indepExp
  rw [powerset_univ, ← sum_fiberwise univ (fun ω : ι → Ω => univ.filter fun e => P e (ω e))]
  refine sum_congr rfl fun S _ => ?_
  rw [sum_congr rfl (g := fun ω => (∏ e, μ e (ω e)) * h S) (fun ω hω => by
    simp only [(mem_filter.mp hω).2]), ← sum_mul]
  congr 1
  have hset : univ.filter (fun ω : ι → Ω => (univ.filter fun e => P e (ω e)) = S) =
      Fintype.piFinset (fun e => univ.filter (fun o => (P e o ↔ e ∈ S))) := by
    ext ω
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, Finset.ext_iff]
  rw [hset, ← prod_univ_sum]
  have hcase : ∀ e, ∑ o ∈ univ.filter (fun o => (P e o ↔ e ∈ S)), μ e o =
      if e ∈ S then ∑ o ∈ univ.filter (P e), μ e o
      else 1 - ∑ o ∈ univ.filter (P e), μ e o := by
    intro e
    by_cases he : e ∈ S
    · simp [he]
    · simp only [he, iff_false, ↓reduceIte]
      rw [← hμ e, ← sum_filter_add_sum_filter_not univ (P e)]
      ring
  rw [prod_congr rfl (fun e _ => hcase e), prod_ite, filter_mem_eq_inter, univ_inter, ← sdiff_eq_filter]

/-- Regrouping: coordinates indexed by `I × J` are independent blocks `b j = ω (·, j)`,
each with the product law over `I`. -/
theorem prodExp_curry {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (μ : I × J → Ω → ℝ) (g : (I × J → Ω) → ℝ) :
    prodExp μ g =
      prodExp (fun (j : J) (b : I → Ω) => ∏ i, μ (i, j) (b i))
        (fun β => g (fun e => β e.2 e.1)) := by
  unfold prodExp
  let E : (I × J → Ω) ≃ (J → I → Ω) :=
    { toFun := fun ω j i => ω (i, j)
      invFun := fun β e => β e.2 e.1
      left_inv := fun ω => rfl
      right_inv := fun β => rfl }
  refine Fintype.sum_equiv E _ _ fun ω => ?_
  simp only [E, Equiv.coe_fn_mk]
  rw [Fintype.prod_prod_type, prod_comm]

/-- The block laws of `prodExp_curry` are distributions. -/
theorem isDist_curry {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] {μ : I × J → Ω → ℝ}
    (hμ : IsDist μ) : IsDist (fun (j : J) (b : I → Ω) => ∏ i, μ (i, j) (b i)) := by
  refine ⟨fun j b => prod_nonneg fun i _ => hμ.1 _ _, fun j => ?_⟩
  rw [sum_prod_weight (fun i o => μ (i, j) o)]
  simp [hμ.2]

end ProdExp

/-! ### The `c_K` gap for random weights -/

section RandomWeight

variable {J O : Type*} [Fintype J] [DecidableEq J] [Fintype O] [DecidableEq O]

/-- `topK` only sees the weights on the ground set. -/
theorem topK_congr {α : Type*} {w w' : α → ℝ} {K : ℕ} {B : Finset α}
    (h : ∀ i ∈ B, w i = w' i) : topK w K B = topK w' K B := by
  unfold topK
  refine sup'_congr _ rfl fun S hS => sum_congr rfl fun i hi => h i ?_
  exact (mem_powerset.mp (mem_filter.mp hS).1) hi

/-- Items of weight zero don't change `topK`. -/
theorem topK_le_topK_filter_pos {α : Type*} [DecidableEq α] {w : α → ℝ} {K : ℕ}
    {B : Finset α} (hw : ∀ i ∈ B, 0 ≤ w i) :
    topK w K B ≤ topK w K (B.filter fun i => 0 < w i) := by
  obtain ⟨S, hSB, hSK, hEq⟩ := exists_topK_eq w K B
  rw [hEq, ← sum_filter_of_ne (p := fun i => 0 < w i) (fun i hi hne =>
    lt_of_le_of_ne (hw i (hSB hi)) (Ne.symm hne))]
  exact sum_le_topK (fun i hi => mem_filter.mpr
      ⟨hSB (mem_filter.mp hi).1, (mem_filter.mp hi).2⟩)
    ((card_filter_le _ _).trans hSK)

/-- The positive values a weight family takes. -/
noncomputable def posVals (W : J → O → ℝ) : Finset ℝ :=
  ((univ : Finset (J × O)).image fun p => W p.1 p.2).filter fun v => 0 < v

omit [DecidableEq O] in
/-- **The `c_K` gap for random weights.** Item `j` has an independent random outcome
`ω j` with law `ρ j` and weight `W j (ω j) ≥ 0`. If the expected number of items with
positive weight is at most `K`, the best `K` items are worth, in expectation, at least
`c_K` times the expected total weight.

This is R1's lemma (`poissonBinomial_min_ge`) integrated over thresholds (the layer
cake), done as an induction that peels off the smallest positive weight. It is the
step of Theorem 3(b) in the vault note that both stages of the selection use. -/
theorem prodExp_randomWeight_gap {ρ : J → O → ℝ} (hρ : IsDist ρ) (K : ℕ)
    (W : J → O → ℝ) (hW : ∀ j o, 0 ≤ W j o)
    (hK : ∑ j, ∑ o ∈ univ.filter (fun o => 0 < W j o), ρ j o ≤ K) :
    cK K * prodExp ρ (fun ω => ∑ j, W j (ω j)) ≤
      prodExp ρ (fun ω => topK (fun j => W j (ω j)) K univ) := by
  suffices H : ∀ n : ℕ, ∀ W : J → O → ℝ, (posVals W).card ≤ n → (∀ j o, 0 ≤ W j o) →
      ∑ j, ∑ o ∈ univ.filter (fun o => 0 < W j o), ρ j o ≤ K →
      cK K * prodExp ρ (fun ω => ∑ j, W j (ω j)) ≤
        prodExp ρ (fun ω => topK (fun j => W j (ω j)) K univ) from
    H _ W le_rfl hW hK
  have hrhs : ∀ W : J → O → ℝ,
      0 ≤ prodExp ρ (fun ω => topK (fun j => W j (ω j)) K univ) := fun W =>
    prodExp_nonneg hρ.1 fun ω => topK_nonneg
  -- With no positive values every weight is zero.
  have hzero : ∀ W : J → O → ℝ, (∀ j o, 0 ≤ W j o) → posVals W = ∅ →
      cK K * prodExp ρ (fun ω => ∑ j, W j (ω j)) ≤
        prodExp ρ (fun ω => topK (fun j => W j (ω j)) K univ) := by
    intro W hW h0
    have hW0 : ∀ j o, W j o = 0 := by
      intro j o
      refine le_antisymm (not_lt.mp fun hpos => ?_) (hW j o)
      have : W j o ∈ posVals W :=
        mem_filter.mpr ⟨mem_image.mpr ⟨(j, o), mem_univ _, rfl⟩, hpos⟩
      simp [h0] at this
    have hsum0 : prodExp ρ (fun ω => ∑ j, W j (ω j)) = 0 := by
      rw [prodExp_congr ρ (h := fun _ => 0) (fun ω => by simp [hW0]), prodExp_const hρ.2]
    rw [hsum0, mul_zero]
    exact hrhs W
  intro n
  induction n with
  | zero =>
    intro W hcard hW _
    exact hzero W hW (card_eq_zero.mp (Nat.le_zero.mp hcard))
  | succ n ih =>
    intro W hcard hW hK
    rcases (posVals W).eq_empty_or_nonempty with h0 | hne
    · exact hzero W hW h0
    set m := (posVals W).min' hne with hm_def
    have hm_mem : m ∈ posVals W := min'_mem _ hne
    have hm_pos : 0 < m := (mem_filter.mp hm_mem).2
    have hm_le : ∀ j o, 0 < W j o → m ≤ W j o := fun j o h =>
      min'_le _ _ (mem_filter.mpr ⟨mem_image.mpr ⟨(j, o), mem_univ _, rfl⟩, h⟩)
    -- Peel off `m` from every positive weight.
    set W' : J → O → ℝ := fun j o => if 0 < W j o then W j o - m else 0 with hW'_def
    have hW' : ∀ j o, 0 ≤ W' j o := fun j o => by
      simp only [hW'_def]
      split_ifs with h
      · linarith [hm_le j o h]
      · exact le_rfl
    have hW'pos : ∀ j o, 0 < W' j o → 0 < W j o := fun j o h => by
      simp only [hW'_def] at h
      split_ifs at h with h'
      · exact h'
      · exact absurd h (lt_irrefl 0)
    have hsplit : ∀ j o, W j o = m * (if 0 < W j o then 1 else 0) + W' j o := fun j o => by
      simp only [hW'_def]
      split_ifs with h
      · ring
      · simp only [mul_zero, zero_add]
        exact le_antisymm (not_lt.mp h) (hW j o)
    -- `W'` has fewer positive values.
    have hcard' : (posVals W').card ≤ n := by
      have hsub : posVals W' ⊆ ((posVals W).filter fun v => m < v).image fun v => v - m := by
        intro v hv
        obtain ⟨hv1, hvpos⟩ := mem_filter.mp hv
        obtain ⟨⟨j, o⟩, _, rfl⟩ := mem_image.mp hv1
        have hpos := hW'pos j o hvpos
        simp only [hW'_def, hpos, ↓reduceIte] at hvpos ⊢
        refine mem_image.mpr ⟨W j o, mem_filter.mpr ⟨mem_filter.mpr
          ⟨mem_image.mpr ⟨(j, o), mem_univ _, rfl⟩, hpos⟩, by linarith⟩, rfl⟩
      have hlt : ((posVals W).filter fun v => m < v).card < (posVals W).card :=
        card_lt_card (filter_ssubset.mpr ⟨m, hm_mem, lt_irrefl m⟩)
      have := (card_le_card hsub).trans card_image_le
      omega
    have hK' : ∑ j, ∑ o ∈ univ.filter (fun o => 0 < W' j o), ρ j o ≤ K := by
      refine le_trans (sum_le_sum fun j _ => ?_) hK
      exact sum_le_sum_of_subset_of_nonneg
        (fun o ho => mem_filter.mpr ⟨mem_univ _, hW'pos j o (mem_filter.mp ho).2⟩)
        (fun o _ _ => hρ.1 j o)
    have hIH := ih W' hcard' hW' hK'
    -- The coins "item `j` has positive weight".
    set p : J → ℝ := fun j => ∑ o ∈ univ.filter (fun o => 0 < W j o), ρ j o with hp_def
    have hp01 : ∀ j ∈ (univ : Finset J), 0 ≤ p j ∧ p j ≤ 1 := fun j _ => by
      refine ⟨sum_nonneg fun o _ => hρ.1 j o, ?_⟩
      rw [← hρ.2 j]
      exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun o _ _ => hρ.1 j o
    have hcount : prodExp ρ (fun ω => ((univ.filter fun j => 0 < W j (ω j)).card : ℝ)) =
        ∑ j, p j := by
      rw [prodExp_filter hρ.2 (fun j o => 0 < W j o) (fun S => (S.card : ℝ)), indepExp_card]
    have hmin : cK K * ∑ j, p j ≤
        prodExp ρ (fun ω => min ((univ.filter fun j => 0 < W j (ω j)).card : ℝ) K) := by
      rw [prodExp_filter hρ.2 (fun j o => 0 < W j o) (fun S => min (S.card : ℝ) K)]
      have := poissonBinomial_min_ge univ p hp01 K
      rwa [min_eq_left hK] at this
    -- Pointwise: the best `K` items earn `m` per positive item, plus the best under `W'`.
    have hpt : ∀ ω : J → O,
        m * min ((univ.filter fun j => 0 < W j (ω j)).card : ℝ) K +
          topK (fun j => W' j (ω j)) K univ ≤ topK (fun j => W j (ω j)) K univ := by
      intro ω
      set P := univ.filter fun j => 0 < W j (ω j)
      have h1 : topK (fun j => W' j (ω j)) K univ ≤ topK (fun j => W' j (ω j)) K P := by
        refine (topK_le_topK_filter_pos fun j _ => hW' j (ω j)).trans
          (topK_mono fun j hj => ?_)
        exact mem_filter.mpr ⟨mem_univ _, hW'pos j (ω j) (mem_filter.mp hj).2⟩
      have h2 := topK_add_const_ge (w := fun j => W' j (ω j)) (K := K) (S := P) hm_pos.le
        fun j _ => hW' j (ω j)
      have h3 : topK (fun j => m + W' j (ω j)) K P = topK (fun j => W j (ω j)) K P :=
        topK_congr fun j hj => by
          have := hsplit j (ω j)
          simp only [(mem_filter.mp hj).2, ↓reduceIte, mul_one] at this
          exact this.symm
      have h4 : topK (fun j => W j (ω j)) K P ≤ topK (fun j => W j (ω j)) K univ :=
        topK_mono (subset_univ _)
      linarith
    have hE := prodExp_mono hρ.1 hpt
    rw [prodExp_add, prodExp_const_mul] at hE
    -- Expected total weight splits the same way.
    have htot : prodExp ρ (fun ω => ∑ j, W j (ω j)) =
        m * ∑ j, p j + prodExp ρ (fun ω => ∑ j, W' j (ω j)) := by
      rw [← hcount, ← prodExp_const_mul, ← prodExp_add]
      refine prodExp_congr ρ fun ω => ?_
      rw [show ((univ.filter fun j => 0 < W j (ω j)).card : ℝ) =
          ∑ j, (if 0 < W j (ω j) then 1 else 0) by rw [sum_boole], mul_sum,
        ← sum_add_distrib]
      exact sum_congr rfl fun j _ => hsplit j (ω j)
    rw [htot, mul_add]
    have : cK K * (m * ∑ j, p j) = m * (cK K * ∑ j, p j) := by ring
    nlinarith [mul_le_mul_of_nonneg_left hmin hm_pos.le]

/-- A function of one column `ω (·, j)` only sees that column's law. -/
theorem prodExp_column {I J Ω : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype Ω] [DecidableEq Ω] {μ : I × J → Ω → ℝ} (hμ : ∀ e, ∑ o, μ e o = 1) (j : J)
    (h : (I → Ω) → ℝ) :
    prodExp μ (fun ω => h (fun i => ω (i, j))) = prodExp (fun i o => μ (i, j) o) h := by
  rw [prodExp_curry]
  have hblock : ∀ j' : J, ∑ b : I → Ω, ∏ i, μ (i, j') (b i) = 1 := fun j' => by
    rw [sum_prod_weight (fun i o => μ (i, j') o)]
    simp [hμ]
  exact prodExp_coord (μ := fun (j : J) (b : I → Ω) => ∏ i, μ (i, j) (b i)) hblock j h

/-- **The `c_K` gap for functions of independent columns.** Each item `j` has outcome
`F j (ω (·, j))`, a function of column `j` only, and weight `W j` of that outcome. The
columns are independent, so `prodExp_randomWeight_gap` applies. The hypothesis bounds
the expected number of items with positive weight. -/
theorem prodExp_columns_gap {I J Ω O : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] [Fintype Ω] [DecidableEq Ω] [Fintype O] [DecidableEq O]
    {μ : I × J → Ω → ℝ} (hμ : IsDist μ) (F : J → (I → Ω) → O) (W : J → O → ℝ)
    (hW : ∀ j o, 0 ≤ W j o) (K : ℕ)
    (hK : ∑ j, prodExp μ (fun ω => if 0 < W j (F j (fun i => ω (i, j))) then 1 else 0) ≤ K) :
    cK K * prodExp μ (fun ω => ∑ j, W j (F j (fun i => ω (i, j)))) ≤
      prodExp μ (fun ω => topK (fun j => W j (F j (fun i => ω (i, j)))) K univ) := by
  have hβ := isDist_curry (J := J) hμ
  have hρ := isDist_map hβ F
  have hconv : ∀ g : (J → O) → ℝ,
      prodExp μ (fun ω => g (fun j => F j (fun i => ω (i, j)))) =
        prodExp (fun j o => ∑ b ∈ univ.filter (fun b => F j b = o),
          ∏ i, μ (i, j) (b i)) g := by
    intro g
    rw [prodExp_curry]
    exact prodExp_map (fun (j : J) (b : I → Ω) => ∏ i, μ (i, j) (b i)) F g
  rw [hconv (fun y => ∑ j, W j (y j)), hconv (fun y => topK (fun j => W j (y j)) K univ)]
  refine prodExp_randomWeight_gap hρ K W hW (le_trans (le_of_eq ?_) hK)
  refine sum_congr rfl fun j _ => ?_
  rw [hconv (fun y => if 0 < W j (y j) then 1 else 0),
    prodExp_coord hρ.2 j (fun o => if 0 < W j o then 1 else 0), sum_filter]
  simp

end RandomWeight

end DatingAlgo
