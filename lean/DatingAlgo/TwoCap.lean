import DatingAlgo.QueueGuarantees

/-!
# The two-cap lemma

The lemma behind Theorem C′ of the vault note "Welfare of Truthful Feeds in the Two-Cost
Model" and the factor `c_k c_B` of Theorem F in "Queries and the Live-Set Theorem".

**Model.** A responder's queue is a list of admirers `(y, p)` in queue order: the admirer
is *present* (liked the responder and is in the backlog) with probability `y`, and if
present is *accepted* with probability `p`, all independently. The responder looks at the
first `m` present admirers and keeps at most `k` accepted ones. `twoCapValue q m k` is the
expected number kept, defined by running the queue from the front.

**Result.** `twoCap_ge`: if the queue is ordered by decreasing acceptance probability,
then for every fluid prefix (the admirers `pre`, plus a fraction `e ≤ y` of the next one)
that uses at most `m` looks and at most `k` keeps in expectation,
`twoCapValue q m k ≥ c_k c_m (expected accepted admirers in the prefix)`.
The longest such prefix has `min(k, V_m)` expected accepted admirers, the bound of the
notes. `twoCap_ge_full` is the case where the whole queue is the prefix.

**Proof.** Write the value as a sum over admirers (`twoCapValue_eq`): admirer `i` is kept
iff it is present and accepted, fewer than `m` earlier admirers are present and fewer
than `k` earlier ones are accepted. `twoCapSum` stores the queue reversed, so that "the
admirers before `i`" is a tail of the list.
1. The two events are positively correlated (`capG_mul_le_twoCapG`), by induction on the
   queue: adding an admirer changes the gap by
   `(1 - y) y p (α_m - α_{m-1}) (β_k - β_{k-1}) ≥ 0`.
2. With one cap, every prefix keeps at least `c_j` of its mean (`capSum_ge`), by the
   comparison with the Poisson case in `PoissonGap.lean`.
3. Two summations by parts, one with the look probability as the decreasing multiplier
   (`sumAB_ge`) and one with the acceptance probability (`sumA_ge`), combine 1 and 2.

The notes' sharper factor `c_m` for `m ≤ k` is not formalized; `c_k c_m` holds for all
`m` and `k`.
-/

namespace DatingAlgo

/-! ### One cap -/

/-- The probability that fewer than `j` of independent events with probabilities `θs`
occur. -/
noncomputable def capG : List ℝ → ℕ → ℝ
  | [], j => if 0 < j then 1 else 0
  | θ :: t, j => (1 - θ) * capG t j + θ * capG t (j - 1)

theorem capG_zero (l : List ℝ) : capG l 0 = 0 := by
  induction l with
  | nil => simp [capG]
  | cons θ t ih => simp [capG, ih]

theorem capG_mem {l : List ℝ} (hl : ∀ θ ∈ l, 0 ≤ θ ∧ θ ≤ 1) (j : ℕ) :
    0 ≤ capG l j ∧ capG l j ≤ 1 := by
  induction l generalizing j with
  | nil => simp only [capG]; split_ifs <;> norm_num
  | cons θ t ih =>
    have hθ := hl θ (by simp)
    have ht : ∀ θ' ∈ t, 0 ≤ θ' ∧ θ' ≤ 1 := fun θ' h => hl θ' (List.mem_cons_of_mem _ h)
    have h1 := ih ht j
    have h2 := ih ht (j - 1)
    have hθ' : 0 ≤ 1 - θ := sub_nonneg.mpr hθ.2
    simp only [capG]
    constructor
    · exact add_nonneg (mul_nonneg hθ' h1.1) (mul_nonneg hθ.1 h2.1)
    · nlinarith [mul_le_mul_of_nonneg_left h1.2 hθ', mul_le_mul_of_nonneg_left h2.2 hθ.1]

theorem capG_le_succ {l : List ℝ} (hl : ∀ θ ∈ l, 0 ≤ θ ∧ θ ≤ 1) (j : ℕ) :
    capG l j ≤ capG l (j + 1) := by
  induction l generalizing j with
  | nil => simp only [capG]; split_ifs <;> simp_all
  | cons θ t ih =>
    have hθ := hl θ (by simp)
    have ht : ∀ θ' ∈ t, 0 ≤ θ' ∧ θ' ≤ 1 := fun θ' h => hl θ' (List.mem_cons_of_mem _ h)
    have hθ' : 0 ≤ 1 - θ := sub_nonneg.mpr hθ.2
    have h1 := mul_le_mul_of_nonneg_left (ih ht j) hθ'
    have h2 : capG t (j - 1) ≤ capG t j := by
      rcases j with _ | j
      · exact le_rfl
      · simpa using ih ht j
    have h3 := mul_le_mul_of_nonneg_left h2 hθ.1
    simp only [capG, Nat.add_sub_cancel]
    linarith

theorem capG_pred_le {l : List ℝ} (hl : ∀ θ ∈ l, 0 ≤ θ ∧ θ ≤ 1) (j : ℕ) :
    capG l (j - 1) ≤ capG l j := by
  rcases j with _ | j
  · exact le_rfl
  · simpa using capG_le_succ hl j

/-- One more event makes "fewer than `j`" less likely. -/
theorem capG_cons_le {θ : ℝ} {t : List ℝ} (hθ : 0 ≤ θ ∧ θ ≤ 1)
    (ht : ∀ θ' ∈ t, 0 ≤ θ' ∧ θ' ≤ 1) (j : ℕ) : capG (θ :: t) j ≤ capG t j := by
  have h := mul_le_mul_of_nonneg_left (capG_pred_le ht j) hθ.1
  simp only [capG]
  linarith

/-- `E[min(N, j)]` for the number `N` of events that occur, written as a sum over events:
event `i` counts iff it occurs and fewer than `j` of the events after it in the list do. -/
noncomputable def capSum : List ℝ → ℕ → ℝ
  | [], _ => 0
  | θ :: t, j => θ * capG t j + capSum t j

theorem capSum_zero (l : List ℝ) : capSum l 0 = 0 := by
  induction l with
  | nil => rfl
  | cons θ t ih => simp [capSum, capG_zero, ih]

/-- `E[min(N, j + 1)] - E[min(N, j)] = P(N ≥ j + 1)`. -/
theorem capSum_succ_sub (l : List ℝ) (j : ℕ) :
    capSum l (j + 1) - capSum l j = 1 - capG l (j + 1) := by
  induction l with
  | nil => simp [capSum, capG]
  | cons θ t ih =>
    simp only [capSum, capG, Nat.add_sub_cancel]
    linear_combination ih

/-- Conditioning on the first event of the list. -/
theorem capSum_cons_succ (θ : ℝ) (t : List ℝ) (j : ℕ) :
    capSum (θ :: t) (j + 1) = (1 - θ) * capSum t (j + 1) + θ * (1 + capSum t j) := by
  have h := capSum_succ_sub t j
  simp only [capSum]
  linear_combination θ * h

/-- Independent events beat the Poisson case, as in `poiMin_le_indepExp`. -/
theorem poiMin_le_capSum {l : List ℝ} (hl : ∀ θ ∈ l, 0 ≤ θ ∧ θ ≤ 1) (j : ℕ) :
    poiMin j l.sum ≤ capSum l j := by
  induction l generalizing j with
  | nil => simp [capSum, poiMin_zero_right]
  | cons θ t ih =>
    have hθ := hl θ (by simp)
    have ht : ∀ θ' ∈ t, 0 ≤ θ' ∧ θ' ≤ 1 := fun θ' h => hl θ' (List.mem_cons_of_mem _ h)
    have hμ : 0 ≤ t.sum := List.sum_nonneg fun x hx => (ht x hx).1
    rw [List.sum_cons]
    rcases j with _ | j
    · simp [capSum_zero, poiMin]
    · rw [capSum_cons_succ]
      have h1 := ih ht (j + 1)
      have h0 := ih ht j
      have htan := poiMin_sub_le (j + 1) hμ (le_add_of_nonneg_left hθ.1)
      have hstep : poiCdf (j + 1) t.sum = 1 + poiMin j t.sum - poiMin (j + 1) t.sum := by
        rw [poiMin_succ]
        ring
      rw [hstep, add_sub_cancel_right] at htan
      have e1 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hθ.2)
      have e2 := mul_le_mul_of_nonneg_left (add_le_add_left h0 1) hθ.1
      nlinarith

/-- **One cap.** `E[min(N, j)] ≥ c_j min(E N, j)`, for events listed in any order. -/
theorem capSum_ge {l : List ℝ} (hl : ∀ θ ∈ l, 0 ≤ θ ∧ θ ≤ 1) (j : ℕ) :
    cK j * min l.sum j ≤ capSum l j :=
  (cK_mul_min_le_poiMin j (List.sum_nonneg fun x hx => (hl x hx).1)).trans
    (poiMin_le_capSum hl j)

/-! ### Two caps -/

/-- The probability that an admirer `(y, p)` is present and accepted. -/
def likeProb (x : ℝ × ℝ) : ℝ := x.1 * x.2

/-- Every presence and acceptance probability is in `[0, 1]`. -/
def QueueValid (l : List (ℝ × ℝ)) : Prop :=
  ∀ x ∈ l, (0 ≤ x.1 ∧ x.1 ≤ 1) ∧ (0 ≤ x.2 ∧ x.2 ≤ 1)

theorem QueueValid.tail {x : ℝ × ℝ} {t : List (ℝ × ℝ)} (h : QueueValid (x :: t)) :
    QueueValid t := fun z hz => h z (List.mem_cons_of_mem _ hz)

theorem QueueValid.fst {l : List (ℝ × ℝ)} (h : QueueValid l) :
    ∀ θ ∈ l.map Prod.fst, 0 ≤ θ ∧ θ ≤ 1 := by
  intro θ hθ
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hθ
  exact (h x hx).1

theorem QueueValid.like {l : List (ℝ × ℝ)} (h : QueueValid l) :
    ∀ θ ∈ l.map likeProb, 0 ≤ θ ∧ θ ≤ 1 := by
  intro θ hθ
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hθ
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h x hx
  exact ⟨mul_nonneg h1 h3, by unfold likeProb; nlinarith⟩

/-- The probability that fewer than `m` of the admirers in `l` are present and fewer than
`k` are present and accepted. -/
noncomputable def twoCapG : List (ℝ × ℝ) → ℕ → ℕ → ℝ
  | [], m, k => if 0 < m ∧ 0 < k then 1 else 0
  | x :: t, m, k =>
      (1 - x.1) * twoCapG t m k + x.1 * (1 - x.2) * twoCapG t (m - 1) k +
        x.1 * x.2 * twoCapG t (m - 1) (k - 1)

theorem twoCapG_zero_left (l : List (ℝ × ℝ)) (k : ℕ) : twoCapG l 0 k = 0 := by
  induction l generalizing k with
  | nil => simp [twoCapG]
  | cons x t ih => simp [twoCapG, ih]

theorem twoCapG_zero_right (l : List (ℝ × ℝ)) (m : ℕ) : twoCapG l m 0 = 0 := by
  induction l generalizing m with
  | nil => simp [twoCapG]
  | cons x t ih => simp [twoCapG, ih]

theorem twoCapG_nonneg {l : List (ℝ × ℝ)} (hv : QueueValid l) (m k : ℕ) :
    0 ≤ twoCapG l m k := by
  induction l generalizing m k with
  | nil => simp only [twoCapG]; split_ifs <;> norm_num
  | cons x t ih =>
    obtain ⟨⟨hy0, hy1⟩, hp0, hp1⟩ := hv x (by simp)
    have ht := hv.tail
    simp only [twoCapG]
    exact add_nonneg (add_nonneg (mul_nonneg (sub_nonneg.mpr hy1) (ih ht m k))
      (mul_nonneg (mul_nonneg hy0 (sub_nonneg.mpr hp1)) (ih ht (m - 1) k)))
      (mul_nonneg (mul_nonneg hy0 hp0) (ih ht (m - 1) (k - 1)))

/-- **Step 1: the two caps are positively correlated.** "Fewer than `m` present" and
"fewer than `k` accepted" are at least as likely together as the product. -/
theorem capG_mul_le_twoCapG {l : List (ℝ × ℝ)} (hv : QueueValid l) (m k : ℕ) :
    capG (l.map Prod.fst) m * capG (l.map likeProb) k ≤ twoCapG l m k := by
  induction l generalizing m k with
  | nil => simp only [List.map_nil, capG, twoCapG]; split_ifs <;> simp_all
  | cons x t ih =>
    obtain ⟨⟨hy0, hy1⟩, hp0, hp1⟩ := hv x (by simp)
    have ht := hv.tail
    have i1 := ih ht m k
    have i2 := ih ht (m - 1) k
    have i3 := ih ht (m - 1) (k - 1)
    have ha := capG_pred_le ht.fst m
    have hb := capG_pred_le ht.like k
    have hprod : 0 ≤ (1 - x.1) * x.1 * x.2 *
        ((capG (t.map Prod.fst) m - capG (t.map Prod.fst) (m - 1)) *
          (capG (t.map likeProb) k - capG (t.map likeProb) (k - 1))) :=
      mul_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr hy1) hy0) hp0)
        (mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb))
    have e1 := mul_le_mul_of_nonneg_left i1 (sub_nonneg.mpr hy1)
    have e2 := mul_le_mul_of_nonneg_left i2 (mul_nonneg hy0 (sub_nonneg.mpr hp1))
    have e3 := mul_le_mul_of_nonneg_left i3 (mul_nonneg hy0 hp0)
    simp only [List.map_cons, capG, twoCapG, likeProb]
    nlinarith

/-- Expected number kept, as a sum over admirers. The list is the queue *reversed*: for
`x :: t`, the admirers before `x` in the queue are `t`. Admirer `x` is kept iff it is
present and accepted, fewer than `m` of `t` are present and fewer than `k` accepted. -/
noncomputable def twoCapSum : List (ℝ × ℝ) → ℕ → ℕ → ℝ
  | [], _, _ => 0
  | x :: t, m, k => x.1 * x.2 * twoCapG t m k + twoCapSum t m k

theorem twoCapSum_zero_left (l : List (ℝ × ℝ)) (k : ℕ) : twoCapSum l 0 k = 0 := by
  induction l with
  | nil => rfl
  | cons x t ih => simp [twoCapSum, twoCapG_zero_left, ih]

theorem twoCapSum_zero_right (l : List (ℝ × ℝ)) (m : ℕ) : twoCapSum l m 0 = 0 := by
  induction l with
  | nil => rfl
  | cons x t ih => simp [twoCapSum, twoCapG_zero_right, ih]

/-- `∑_i y_i p_i a_i b_i`, with `a_i`, `b_i` the two cap probabilities for the admirers
before `i`. -/
noncomputable def sumAB : List (ℝ × ℝ) → ℕ → ℕ → ℝ
  | [], _, _ => 0
  | x :: t, m, k =>
      likeProb x * (capG (t.map Prod.fst) m * capG (t.map likeProb) k) + sumAB t m k

/-- `∑_i y_i p_i a_i`. -/
noncomputable def sumA : List (ℝ × ℝ) → ℕ → ℝ
  | [], _ => 0
  | x :: t, m => likeProb x * capG (t.map Prod.fst) m + sumA t m

theorem sumAB_le_twoCapSum {r : List (ℝ × ℝ)} (hv : QueueValid r) (m k : ℕ) :
    sumAB r m k ≤ twoCapSum r m k := by
  induction r with
  | nil => exact le_rfl
  | cons x t ih =>
    obtain ⟨⟨hy0, _⟩, hp0, _⟩ := hv x (by simp)
    have h := mul_le_mul_of_nonneg_left (capG_mul_le_twoCapG hv.tail m k) (mul_nonneg hy0 hp0)
    have h' := ih hv.tail
    simp only [sumAB, twoCapSum, likeProb]
    linarith

/-- **Step 3a: summation by parts with the look probability.** -/
theorem sumAB_ge {r : List (ℝ × ℝ)} (hv : QueueValid r) (m k : ℕ)
    (hk : (r.map likeProb).sum ≤ k) :
    capG (r.map Prod.fst) m * (capSum (r.map likeProb) k - cK k * (r.map likeProb).sum) ≤
      sumAB r m k - cK k * sumA r m := by
  induction r with
  | nil => simp [capSum, sumAB, sumA]
  | cons x t ih =>
    obtain ⟨hx1, hx2⟩ := hv x (by simp)
    have ht := hv.tail
    have hlx : 0 ≤ likeProb x := mul_nonneg hx1.1 hx2.1
    have hk' : (t.map likeProb).sum ≤ k := by
      simp only [List.map_cons, List.sum_cons] at hk
      linarith
    have ih' := ih ht hk'
    have hE : 0 ≤ capSum ((x :: t).map likeProb) k - cK k * ((x :: t).map likeProb).sum := by
      have h := capSum_ge hv.like k
      rw [min_eq_left hk] at h
      linarith
    have hA : capG ((x :: t).map Prod.fst) m ≤ capG (t.map Prod.fst) m :=
      capG_cons_le hx1 ht.fst m
    have hmul := mul_le_mul_of_nonneg_right hA hE
    simp only [List.map_cons, List.sum_cons, capSum, sumAB, sumA] at hmul ⊢
    nlinarith

/-- **Step 3b: summation by parts with the acceptance probability.** `P` is a lower bound
on the acceptance probabilities in the list. -/
theorem sumA_ge {r : List (ℝ × ℝ)} (hv : QueueValid r)
    (hs : r.Pairwise fun a b => a.2 ≤ b.2) (m : ℕ) (hm : (r.map Prod.fst).sum ≤ m) :
    ∀ P : ℝ, 0 ≤ P → (∀ z ∈ r, P ≤ z.2) →
      P * (capSum (r.map Prod.fst) m - cK m * (r.map Prod.fst).sum) ≤
        sumA r m - cK m * (r.map likeProb).sum := by
  induction r with
  | nil => intro P _ _; simp [capSum, sumA]
  | cons x t ih =>
    intro P hP0 hP
    obtain ⟨hx1, hx2⟩ := hv x (by simp)
    have ht := hv.tail
    obtain ⟨hxt, hst⟩ := List.pairwise_cons.mp hs
    have hm' : (t.map Prod.fst).sum ≤ m := by
      simp only [List.map_cons, List.sum_cons] at hm
      linarith
    have ih' := ih ht hst hm' x.2 hx2.1 hxt
    have hD : 0 ≤ capSum ((x :: t).map Prod.fst) m - cK m * ((x :: t).map Prod.fst).sum := by
      have h := capSum_ge hv.fst m
      rw [min_eq_left hm] at h
      linarith
    have hmul := mul_le_mul_of_nonneg_right (hP x (by simp)) hD
    simp only [List.map_cons, List.sum_cons, capSum, sumA, likeProb] at hmul ⊢
    nlinarith

/-- **The two-cap lemma, for the reversed queue.** If the acceptance probabilities do not
decrease along the list (so they do not increase along the queue) and the admirers use at
most `m` looks and `k` keeps in expectation, the responder keeps at least `c_k c_m` times
the expected number of accepted admirers. -/
theorem twoCapSum_ge {r : List (ℝ × ℝ)} (hv : QueueValid r)
    (hs : r.Pairwise fun a b => a.2 ≤ b.2) {m k : ℕ} (hm : (r.map Prod.fst).sum ≤ m)
    (hk : (r.map likeProb).sum ≤ k) :
    cK k * (cK m * (r.map likeProb).sum) ≤ twoCapSum r m k := by
  have h1 := sumAB_le_twoCapSum hv m k
  have h2 := sumAB_ge hv m k hk
  have h3 := sumA_ge hv hs m hm 0 le_rfl
  have hE : 0 ≤ capSum (r.map likeProb) k - cK k * (r.map likeProb).sum := by
    have h := capSum_ge hv.like k
    rw [min_eq_left hk] at h
    linarith
  have hA := (capG_mem hv.fst m).1
  have h4 := mul_nonneg hA hE
  have h5 : 0 ≤ sumA r m - cK m * (r.map likeProb).sum := by
    have h := h3 (fun z hz => ((hv z hz).2).1)
    linarith
  have h6 := mul_nonneg (cK_nonneg k) h5
  nlinarith

/-! ### The queue run from the front -/

/-- Expected number of admirers kept when the responder runs the queue `q` from the
front, looking at the first `m` present admirers and keeping at most `k` accepted ones. -/
noncomputable def twoCapValue : List (ℝ × ℝ) → ℕ → ℕ → ℝ
  | [], _, _ => 0
  | x :: l, m, k =>
      if m = 0 ∨ k = 0 then 0
      else (1 - x.1) * twoCapValue l m k +
        x.1 * (x.2 * (1 + twoCapValue l (m - 1) (k - 1)) + (1 - x.2) * twoCapValue l (m - 1) k)

theorem twoCapG_swap (a b : ℝ × ℝ) (t : List (ℝ × ℝ)) (m k : ℕ) :
    twoCapG (a :: b :: t) m k = twoCapG (b :: a :: t) m k := by
  simp only [twoCapG]
  ring

/-- The cap probabilities do not depend on the order of the admirers. -/
theorem twoCapG_perm {l₁ l₂ : List (ℝ × ℝ)} (h : l₁.Perm l₂) (m k : ℕ) :
    twoCapG l₁ m k = twoCapG l₂ m k := by
  induction h generalizing m k with
  | nil => rfl
  | cons x _ ih => simp only [twoCapG, ih]
  | swap x y l => exact twoCapG_swap y x l m k
  | trans _ _ ih₁ ih₂ => rw [ih₁, ih₂]

theorem twoCapSum_snoc (t : List (ℝ × ℝ)) (x : ℝ × ℝ) (m k : ℕ) :
    twoCapSum (t ++ [x]) m k = x.1 * x.2 * twoCapG [] m k +
      ((1 - x.1) * twoCapSum t m k + x.1 * (1 - x.2) * twoCapSum t (m - 1) k +
        x.1 * x.2 * twoCapSum t (m - 1) (k - 1)) := by
  induction t with
  | nil => simp [twoCapSum]
  | cons z t ih =>
    have hperm : twoCapG (t ++ [x]) m k = twoCapG (x :: t) m k :=
      twoCapG_perm (List.perm_append_singleton x t) m k
    simp only [List.cons_append, twoCapSum, hperm, ih]
    simp only [twoCapG]
    ring

/-- **The sum over admirers is the value of the queue run from the front.** -/
theorem twoCapValue_eq (q : List (ℝ × ℝ)) (m k : ℕ) :
    twoCapValue q m k = twoCapSum q.reverse m k := by
  induction q generalizing m k with
  | nil => rfl
  | cons x q ih =>
    rw [List.reverse_cons, twoCapSum_snoc]
    simp only [twoCapValue]
    split_ifs with h
    · rcases h with rfl | rfl
      · simp [twoCapSum_zero_left, twoCapG]
      · simp [twoCapSum_zero_right, twoCapG]
    · push Not at h
      have hG : twoCapG [] m k = 1 := by
        simp [twoCapG, Nat.pos_of_ne_zero h.1, Nat.pos_of_ne_zero h.2]
      rw [ih, ih, ih, hG]
      ring

theorem twoCapSum_nonneg {l : List (ℝ × ℝ)} (hv : QueueValid l) (m k : ℕ) :
    0 ≤ twoCapSum l m k := by
  induction l with
  | nil => exact le_rfl
  | cons x t ih =>
    obtain ⟨⟨hy0, _⟩, hp0, _⟩ := hv x (by simp)
    simp only [twoCapSum]
    exact add_nonneg (mul_nonneg (mul_nonneg hy0 hp0) (twoCapG_nonneg hv.tail m k)) (ih hv.tail)

/-- Admirers further down the queue only add to the value. -/
theorem twoCapSum_le_append {s l : List (ℝ × ℝ)} (hv : QueueValid (s ++ l)) (m k : ℕ) :
    twoCapSum l m k ≤ twoCapSum (s ++ l) m k := by
  induction s with
  | nil => exact le_rfl
  | cons z s ih =>
    have hv' : QueueValid (s ++ l) := QueueValid.tail (x := z) hv
    obtain ⟨⟨hy0, _⟩, hp0, _⟩ := hv z (by simp)
    have h := mul_nonneg (mul_nonneg hy0 hp0) (twoCapG_nonneg hv' m k)
    have h' := ih hv'
    simp only [List.cons_append, twoCapSum]
    linarith

/-- **The two-cap lemma, whole queue.** If the queue is ordered by decreasing acceptance
probability and uses at most `m` looks and `k` keeps in expectation, the responder keeps
at least `c_k c_m` times the expected number of accepted admirers. -/
theorem twoCap_ge_full {q : List (ℝ × ℝ)} (hv : QueueValid q)
    (hs : q.Pairwise fun a b => b.2 ≤ a.2) {m k : ℕ} (hm : (q.map Prod.fst).sum ≤ m)
    (hk : (q.map likeProb).sum ≤ k) :
    cK k * (cK m * (q.map likeProb).sum) ≤ twoCapValue q m k := by
  rw [twoCapValue_eq]
  have hv' : QueueValid q.reverse := fun z hz => hv z (List.mem_reverse.mp hz)
  have hs' : q.reverse.Pairwise fun a b => a.2 ≤ b.2 := List.pairwise_reverse.mpr hs
  have h := twoCapSum_ge hv' hs' (m := m) (k := k)
    (by rw [List.map_reverse, List.sum_reverse]; exact hm)
    (by rw [List.map_reverse, List.sum_reverse]; exact hk)
  rwa [List.map_reverse, List.sum_reverse] at h

/-- **The two-cap lemma (Theorem C′; the factor `c_k c_B` of Theorem F).** The queue is
`pre ++ x :: rest`, ordered by decreasing acceptance probability. Take the admirers `pre`
and a fraction `e ≤ y` of the next admirer `x = (y, p)`, using at most `m` looks and at
most `k` keeps in expectation. Then the responder keeps at least `c_k c_m` times the
expected number of accepted admirers in this fluid prefix. -/
theorem twoCap_ge {pre rest : List (ℝ × ℝ)} {x : ℝ × ℝ} {e : ℝ} {m k : ℕ}
    (hv : QueueValid (pre ++ x :: rest))
    (hs : (pre ++ x :: rest).Pairwise fun a b => b.2 ≤ a.2) (he0 : 0 ≤ e) (he : e ≤ x.1)
    (hm : (pre.map Prod.fst).sum + e ≤ m) (hk : (pre.map likeProb).sum + e * x.2 ≤ k) :
    cK k * (cK m * ((pre.map likeProb).sum + e * x.2)) ≤
      twoCapValue (pre ++ x :: rest) m k := by
  rw [twoCapValue_eq]
  have hrev : (pre ++ x :: rest).reverse = rest.reverse ++ x :: pre.reverse := by simp
  rw [hrev]
  obtain ⟨⟨hy0, hy1⟩, hp0, hp1⟩ := hv x (by simp)
  have hvpre : QueueValid pre.reverse := fun z hz =>
    hv z (List.mem_append_left _ (List.mem_reverse.mp hz))
  have hvx : QueueValid (x :: pre.reverse) := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hv z (by simp)
    · exact hvpre z hz
  have hvall : QueueValid (rest.reverse ++ x :: pre.reverse) := by
    intro z hz
    refine hv z ?_
    have : z ∈ (pre ++ x :: rest).reverse := hrev ▸ hz
    exact List.mem_reverse.mp this
  -- Drop the admirers after `x`.
  have h1 := twoCapSum_le_append hvall m k
  -- Lower `x`'s presence probability to `e`.
  have hG := twoCapG_nonneg hvpre m k
  have h2 : twoCapSum ((e, x.2) :: pre.reverse) m k ≤ twoCapSum (x :: pre.reverse) m k := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hp0) hG
    simp only [twoCapSum]
    linarith
  -- Apply the lemma to the fluid prefix.
  have hvr : QueueValid ((e, x.2) :: pre.reverse) := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact ⟨⟨he0, he.trans hy1⟩, hp0, hp1⟩
    · exact hvpre z hz
  obtain ⟨hspre, -, hcross⟩ := List.pairwise_append.mp hs
  have hsr : ((e, x.2) :: pre.reverse).Pairwise fun a b => a.2 ≤ b.2 := by
    refine List.pairwise_cons.mpr ⟨fun z hz => ?_, List.pairwise_reverse.mpr hspre⟩
    exact hcross z (List.mem_reverse.mp hz) x (by simp)
  have h3 := twoCapSum_ge hvr hsr (m := m) (k := k)
    (by simp only [List.map_cons, List.sum_cons, List.map_reverse, List.sum_reverse]; linarith)
    (by
      simp only [List.map_cons, List.sum_cons, List.map_reverse, List.sum_reverse, likeProb]
      linarith)
  simp only [List.map_cons, List.sum_cons, List.map_reverse, List.sum_reverse] at h3
  have hsum : likeProb (e, x.2) + (pre.map likeProb).sum = (pre.map likeProb).sum + e * x.2 := by
    simp only [likeProb]; ring
  rw [hsum] at h3
  linarith

end DatingAlgo
