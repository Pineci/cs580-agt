import DatingAlgo.TopK

/-!
# R4: optimizing additive quality can lose a factor `(K + 1) / 2` in best-match quality

Result R4 of the vault note "Match Quality in the Dating Heuristic Framework", for
`k = 1` (each user values only their best match).

**The instance.** One round of mutual views with certain likes.
- `K` block users on each side (`a i` and `b j`) all like each other, with quality 1.
- Each block user also has `K - 1` private admirers (`oa i t` for `a i`, `ob j t` for
  `b j`), each with quality `qo < 1/2`.
- Everyone has display cap `K`, so a set of matches is a subgraph with degrees at most
  `K`.

**The results.**
- Maximizing total (additive) quality picks exactly the full `K × K` block, where each
  user's best match is 1. Best-match quality summed over users is `2K`.
- Keeping a perfect matching inside the block plus all the admirers gives
  `2K + 2K(K - 1) qo`.
- As `qo → 1/2` the ratio tends to `2 / (K + 1)`, which is `1/2` at `K = 3`.

Since DH-int_q maximizes expected additive quality, it inherits this loss.
-/

namespace DatingAlgo

open Finset

namespace R4

/-- Users of the instance. `a i` (side `I`) and `b j` (side `J`) form the block.
`oa i t` (side `J`) admires `a i`; `ob j t` (side `I`) admires `b j`. -/
inductive User (K : ℕ)
  | a (i : Fin K)
  | b (j : Fin K)
  | oa (i : Fin K) (t : Fin (K - 1))
  | ob (j : Fin K) (t : Fin (K - 1))
  deriving DecidableEq, Fintype

variable (K : ℕ)

/-- Whether a pair is a candidate match, written `(side-I user, side-J user)`. -/
def isCandidate : User K × User K → Bool
  | (.a _, .b _) => true
  | (.a i, .oa i' _) => decide (i = i')
  | (.ob j _, .b j') => decide (j = j')
  | _ => false

/-- Candidate pairs. -/
def candidates : Finset (User K × User K) :=
  univ.filter fun e => isCandidate K e = true

/-- Quality of a pair: 1 inside the block, `qo` with an admirer, 0 otherwise. -/
def quality (qo : ℝ) : User K × User K → ℝ
  | (.a _, .b _) => 1
  | (.a _, .oa _ _) => qo
  | (.ob _ _, .b _) => qo
  | _ => 0

/-- The pairs involving user `v`. -/
def incident (M : Finset (User K × User K)) (v : User K) : Finset (User K × User K) :=
  M.filter (fun e => e.1 = v ∨ e.2 = v)

/-- A feasible set of matches: candidate pairs only, and every user in at most `K`. -/
def Feasible (M : Finset (User K × User K)) : Prop :=
  M ⊆ candidates K ∧ ∀ v, (incident K M v).card ≤ K

/-- Additive quality: the sum over matches. -/
noncomputable def additive (qo : ℝ) (M : Finset (User K × User K)) : ℝ :=
  ∑ e ∈ M, quality K qo e

/-- Best-match quality: each user's best match (0 if none), summed over users. -/
noncomputable def bestMatch (qo : ℝ) (M : Finset (User K × User K)) : ℝ :=
  ∑ v, topK (quality K qo) 1 (incident K M v)

/-- The full block: every `a i` matched with every `b j`. -/
def block : Finset (User K × User K) :=
  (univ : Finset (Fin K × Fin K)).image fun p => (User.a p.1, User.b p.2)

/-- Sorting users by constructor. -/
def userEquiv : User K ≃ (Fin K ⊕ Fin K) ⊕ ((Fin K × Fin (K - 1)) ⊕ (Fin K × Fin (K - 1))) where
  toFun
    | .a i => .inl (.inl i)
    | .b j => .inl (.inr j)
    | .oa i t => .inr (.inl (i, t))
    | .ob j t => .inr (.inr (j, t))
  invFun
    | .inl (.inl i) => .a i
    | .inl (.inr j) => .b j
    | .inr (.inl p) => .oa p.1 p.2
    | .inr (.inr p) => .ob p.1 p.2
  left_inv v := by cases v <;> rfl
  right_inv x := by rcases x with (i | j) | (⟨i, t⟩ | ⟨j, t⟩) <;> rfl

/-- A sum over users splits by constructor. -/
lemma sum_user (f : User K → ℝ) :
    ∑ v, f v = ∑ i, f (.a i) + ∑ j, f (.b j) + ∑ i, ∑ t, f (.oa i t)
      + ∑ j, ∑ t, f (.ob j t) := by
  rw [← (userEquiv K).symm.sum_comp]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type]
  rw [← add_assoc]
  rfl

/-- Membership in `candidates`. -/
lemma mem_candidates {e : User K × User K} : e ∈ candidates K ↔ isCandidate K e = true := by
  unfold candidates
  rw [Finset.mem_filter]
  simp

/-- Membership in `incident`. -/
lemma mem_incident {M : Finset (User K × User K)} {v : User K} {e : User K × User K} :
    e ∈ incident K M v ↔ e ∈ M ∧ (e.1 = v ∨ e.2 = v) :=
  Finset.mem_filter

/-- Every candidate pair is a block pair or an admirer pair. -/
lemma candidate_cases {e : User K × User K} (he : e ∈ candidates K) :
    (∃ i j, e = (.a i, .b j)) ∨ (∃ i t, e = (.a i, .oa i t)) ∨
      (∃ j t, e = (.ob j t, .b j)) := by
  obtain ⟨x, y⟩ := e
  rw [mem_candidates] at he
  cases x <;> cases y <;> simp [isCandidate] at he ⊢
  all_goals exact he.symm

/-- Membership in the block. -/
lemma mem_block {x y : User K} : (x, y) ∈ block K ↔ ∃ i j, x = .a i ∧ y = .b j := by
  simp [block, eq_comm]

/-- The block has `K * K` pairs. -/
lemma card_block : (block K).card = K * K := by
  unfold block
  rw [Finset.card_image_of_injective]
  · simp
  · intro p q h
    simp only [Prod.mk.injEq, User.a.injEq, User.b.injEq] at h
    exact Prod.ext h.1 h.2

/-- The block uses only candidate pairs. -/
lemma block_subset_candidates : block K ⊆ candidates K := by
  intro e he
  obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 he
  rw [mem_candidates]
  rfl

/-- Weight 1 on block users and 0 on admirers. -/
noncomputable def blockUser : User K → ℝ
  | .a _ => 1
  | .b _ => 1
  | _ => 0

/-- Indicator of the block pairs. -/
noncomputable def inBlock (e : User K × User K) : ℝ := if e ∈ block K then 1 else 0

/-- `blockUser` is nonnegative. -/
lemma blockUser_nonneg (v : User K) : 0 ≤ blockUser K v := by
  cases v <;> simp [blockUser]

/-- There are `2K` block users. -/
lemma sum_blockUser : ∑ v, blockUser K v = 2 * K := by
  rw [sum_user]
  simp [blockUser]
  ring

/-- A candidate pair is not a loop. -/
lemma fst_ne_snd {e : User K × User K} (he : e ∈ candidates K) : e.1 ≠ e.2 := by
  rcases candidate_cases K he with ⟨i, j, rfl⟩ | ⟨i, t, rfl⟩ | ⟨j, t, rfl⟩ <;> simp

/-- On a candidate pair, the quality is 1 in the block and `qo` outside it. -/
lemma quality_eq (qo : ℝ) {e : User K × User K} (he : e ∈ candidates K) :
    quality K qo e = inBlock K e + qo * (1 - inBlock K e) := by
  rcases candidate_cases K he with ⟨i, j, rfl⟩ | ⟨i, t, rfl⟩ | ⟨j, t, rfl⟩ <;>
    simp [quality, inBlock, mem_block]

/-- A candidate pair has two block endpoints in the block and one outside it. -/
lemma blockUser_add {e : User K × User K} (he : e ∈ candidates K) :
    blockUser K e.1 + blockUser K e.2 = 1 + inBlock K e := by
  rcases candidate_cases K he with ⟨i, j, rfl⟩ | ⟨i, t, rfl⟩ | ⟨j, t, rfl⟩ <;>
    simp [blockUser, inBlock, mem_block]

/-- A candidate pair has quality at most 1. -/
lemma quality_le_one {qo : ℝ} (hqo1 : qo ≤ 1) {e : User K × User K} (he : e ∈ candidates K) :
    quality K qo e ≤ 1 := by
  rcases candidate_cases K he with ⟨i, j, rfl⟩ | ⟨i, t, rfl⟩ | ⟨j, t, rfl⟩ <;>
    simp [quality, hqo1]

/-- A candidate pair at an admirer has quality `qo`. -/
lemma quality_admirer (qo : ℝ) {e : User K × User K} (he : e ∈ candidates K) {v : User K}
    (hv : blockUser K v = 0) (hev : e.1 = v ∨ e.2 = v) : quality K qo e = qo := by
  rcases candidate_cases K he with ⟨i, j, rfl⟩ | ⟨i, t, rfl⟩ | ⟨j, t, rfl⟩ <;>
    rcases hev with rfl | rfl <;> simp_all [quality, blockUser]

/-- Double counting: weighting each user's degree by `f` sums `f` over match endpoints. -/
lemma sum_mul_card_incident (f : User K → ℝ) (M : Finset (User K × User K))
    (hM : ∀ e ∈ M, e.1 ≠ e.2) :
    ∑ v, f v * ((incident K M v).card : ℝ) = ∑ e ∈ M, (f e.1 + f e.2) := by
  have h1 : ∀ v, ((incident K M v).card : ℝ) =
      ∑ e ∈ M, (if e.1 = v ∨ e.2 = v then (1 : ℝ) else 0) := by
    intro v
    rw [incident, Finset.natCast_card_filter]
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e he => ?_
  have hne := hM e he
  have h2 : ∀ v, f v * (if e.1 = v ∨ e.2 = v then (1 : ℝ) else 0) =
      (if e.1 = v then f v else 0) + (if e.2 = v then f v else 0) := by
    intro v
    by_cases h1 : e.1 = v <;> by_cases h2 : e.2 = v
    · exact absurd (h1.trans h2.symm) hne
    all_goals simp [h1, h2]
  simp_rw [h2, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The three counting facts behind `additive_le`, where `∑ e ∈ M, inBlock K e` counts the
block pairs in `M`. -/
lemma key_bounds (qo : ℝ) {M : Finset (User K × User K)} (hM : Feasible K M) :
    additive K qo M =
        (∑ e ∈ M, inBlock K e) + qo * ((M.card : ℝ) - ∑ e ∈ M, inBlock K e) ∧
      (M.card : ℝ) + ∑ e ∈ M, inBlock K e ≤ 2 * (K : ℝ) ^ 2 ∧
      ∑ e ∈ M, inBlock K e ≤ (K : ℝ) ^ 2 := by
  obtain ⟨hsub, hdeg⟩ := hM
  refine ⟨?_, ?_, ?_⟩
  · unfold additive
    rw [Finset.sum_congr rfl fun e he => quality_eq K qo (hsub he), Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_sub_distrib]
    simp
  · have hdc := sum_mul_card_incident K (blockUser K) M (fun e he => fst_ne_snd K (hsub he))
    rw [Finset.sum_congr rfl fun e he => blockUser_add K (hsub he), Finset.sum_add_distrib]
      at hdc
    have hle : ∑ v, blockUser K v * ((incident K M v).card : ℝ) ≤ ∑ v, blockUser K v * K :=
      Finset.sum_le_sum fun v _ =>
        mul_le_mul_of_nonneg_left (by exact_mod_cast hdeg v) (blockUser_nonneg K v)
    rw [← Finset.sum_mul, sum_blockUser] at hle
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hdc
    linarith
  · have h1 : ∑ e ∈ M, inBlock K e = ((M.filter (· ∈ block K)).card : ℝ) := by
      rw [Finset.natCast_card_filter]
      rfl
    have h2 : (M.filter (· ∈ block K)).card ≤ (block K).card :=
      Finset.card_le_card fun e he => (Finset.mem_filter.1 he).2
    rw [card_block] at h2
    rw [h1, sq]
    exact_mod_cast h2


/-- With cap 1, `topK` is the largest weight `c ≥ 0` when some element attains it. -/
lemma topK_one_eq {α : Type*} {w : α → ℝ} {S : Finset α} {c : ℝ} {x : α} (hc : 0 ≤ c)
    (hx : x ∈ S) (hwx : w x = c) (hle : ∀ y ∈ S, w y ≤ c) : topK w 1 S = c := by
  apply le_antisymm
  · obtain ⟨T, hTS, hT1, hEq⟩ := exists_topK_eq w 1 S
    rw [hEq]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hT1 with h | h
    · rw [Finset.card_eq_zero.1 h, Finset.sum_empty]
      exact hc
    · obtain ⟨y, rfl⟩ := Finset.card_eq_one.1 h
      rw [Finset.sum_singleton]
      exact hle y (hTS (Finset.mem_singleton_self y))
  · have := sum_le_topK (w := w) (K := 1) (Finset.singleton_subset_iff.2 hx)
      (by rw [Finset.card_singleton])
    rwa [Finset.sum_singleton, hwx] at this

/-- No feasible set beats the full block on additive quality. -/
theorem additive_le (qo : ℝ) (hqo0 : 0 ≤ qo) (hqo : qo < 1 / 2)
    {M : Finset (User K × User K)} (hM : Feasible K M) :
    additive K qo M ≤ (K : ℝ) ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := key_bounds K qo hM
  rw [h1]
  nlinarith [mul_nonneg hqo0 (by linarith : (0 : ℝ) ≤ 2 * (K : ℝ) ^ 2 - (M.card : ℝ)
      - ∑ e ∈ M, inBlock K e),
    mul_nonneg (sub_nonneg.2 h3) (by linarith : (0 : ℝ) ≤ 1 - 2 * qo)]

/-- The full block is feasible and achieves additive quality `K²`. -/
theorem block_feasible_additive (qo : ℝ) :
    Feasible K (block K) ∧ additive K qo (block K) = (K : ℝ) ^ 2 := by
  refine ⟨⟨block_subset_candidates K, ?_⟩, ?_⟩
  · intro v
    cases v with
    | a i =>
      have hsub : incident K (block K) (.a i) ⊆ univ.image fun j => (User.a i, User.b j) := by
        intro e he
        obtain ⟨he, hv⟩ := (mem_incident K).1 he
        obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 he
        simp only [User.a.injEq, reduceCtorEq, or_false] at hv
        exact Finset.mem_image.2 ⟨p.2, Finset.mem_univ _, by rw [hv]⟩
      exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
    | b j =>
      have hsub : incident K (block K) (.b j) ⊆ univ.image fun i => (User.a i, User.b j) := by
        intro e he
        obtain ⟨he, hv⟩ := (mem_incident K).1 he
        obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 he
        simp only [User.b.injEq, reduceCtorEq, false_or] at hv
        exact Finset.mem_image.2 ⟨p.1, Finset.mem_univ _, by rw [hv]⟩
      exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by simp))
    | oa i t =>
      have : incident K (block K) (.oa i t) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun e he => ?_
        obtain ⟨he, hv⟩ := (mem_incident K).1 he
        obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 he
        simp at hv
      simp [this]
    | ob j t =>
      have : incident K (block K) (.ob j t) = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun e he => ?_
        obtain ⟨he, hv⟩ := (mem_incident K).1 he
        obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 he
        simp at hv
      simp [this]
  · unfold additive
    have : ∀ e ∈ block K, quality K qo e = 1 := by
      intro e he
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 he
      rfl
    rw [Finset.sum_congr rfl this, Finset.sum_const, card_block, nsmul_eq_mul, mul_one]
    push_cast
    ring

/-- The full block is the *only* additive optimum. -/
theorem eq_block_of_additive_eq (qo : ℝ) (hqo0 : 0 ≤ qo) (hqo : qo < 1 / 2)
    {M : Finset (User K × User K)} (hM : Feasible K M)
    (hval : additive K qo M = (K : ℝ) ^ 2) : M = block K := by
  obtain ⟨h1, h2, h3⟩ := key_bounds K qo hM
  set Ec := ∑ e ∈ M, inBlock K e with hEc
  have hEcK : Ec = (K : ℝ) ^ 2 := by
    refine le_antisymm h3 ?_
    by_contra hlt
    replace hlt := not_le.1 hlt
    nlinarith [mul_nonneg hqo0 (by linarith : (0 : ℝ) ≤ 2 * (K : ℝ) ^ 2 - (M.card : ℝ) - Ec),
      mul_pos (sub_pos.2 hlt) (by linarith : (0 : ℝ) < 1 - 2 * qo)]
  have hle1 : ∀ e ∈ M, inBlock K e ≤ 1 := fun e _ => by
    unfold inBlock; split_ifs <;> norm_num
  have hEcC : Ec ≤ M.card := by
    rw [hEc, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    exact Finset.sum_le_sum hle1
  have hzero : ∑ e ∈ M, (1 - inBlock K e) = 0 := by
    rw [Finset.sum_sub_distrib, ← hEc]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    linarith
  have hMsub : M ⊆ block K := by
    intro e he
    have := (Finset.sum_eq_zero_iff_of_nonneg fun e he => sub_nonneg.2 (hle1 e he)).1 hzero e he
    by_contra hn
    simp [inBlock, hn] at this
  refine Finset.eq_of_subset_of_card_le hMsub ?_
  rw [card_block]
  have : ((K * K : ℕ) : ℝ) ≤ (M.card : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast this

/-- The full block's best-match quality is `2K`. -/
theorem bestMatch_block (qo : ℝ) (hqo0 : 0 ≤ qo) (hqo1 : qo ≤ 1) :
    bestMatch K qo (block K) = 2 * K := by
  have h01 : (0 : ℝ) ≤ 1 := hqo0.trans hqo1
  unfold bestMatch
  rw [sum_user]
  have hsub := block_subset_candidates K
  have hb1 : ∀ v, ∀ e ∈ incident K (block K) v, quality K qo e ≤ 1 := fun v e he =>
    quality_le_one K hqo1 (hsub ((mem_incident K).1 he).1)
  have ha : ∀ i, topK (quality K qo) 1 (incident K (block K) (.a i)) = 1 := fun i =>
    topK_one_eq h01 (x := (.a i, .b i))
      ((mem_incident K).2 ⟨Finset.mem_image.2 ⟨(i, i), Finset.mem_univ _, rfl⟩, Or.inl rfl⟩)
      rfl (hb1 (.a i))
  have hb : ∀ j, topK (quality K qo) 1 (incident K (block K) (.b j)) = 1 := fun j =>
    topK_one_eq h01 (x := (.a j, .b j))
      ((mem_incident K).2 ⟨Finset.mem_image.2 ⟨(j, j), Finset.mem_univ _, rfl⟩, Or.inr rfl⟩)
      rfl (hb1 (.b j))
  have hoa : ∀ i t, incident K (block K) (.oa i t) = ∅ := by
    intro i t
    refine Finset.eq_empty_of_forall_notMem fun e he => ?_
    obtain ⟨he, hv⟩ := (mem_incident K).1 he
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 he
    simp at hv
  have hob : ∀ j t, incident K (block K) (.ob j t) = ∅ := by
    intro j t
    refine Finset.eq_empty_of_forall_notMem fun e he => ?_
    obtain ⟨he, hv⟩ := (mem_incident K).1 he
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 he
    simp at hv
  simp only [ha, hb, hoa, hob, topK_empty, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, mul_zero, add_zero]
  ring


/-- Pairs of the spread solution: the block's diagonal plus every admirer pair. -/
def isSpread : User K × User K → Bool
  | (.a i, .b j) => decide (i = j)
  | (.a i, .oa i' _) => decide (i = i')
  | (.ob j _, .b j') => decide (j = j')
  | _ => false

/-- The spread solution: a perfect matching inside the block plus all admirers. -/
def spread : Finset (User K × User K) :=
  univ.filter fun e => isSpread K e = true

/-- Membership in `spread`. -/
lemma mem_spread {e : User K × User K} : e ∈ spread K ↔ isSpread K e = true := by
  unfold spread
  rw [Finset.mem_filter]
  simp

/-- The spread solution uses only candidate pairs. -/
lemma spread_subset_candidates : spread K ⊆ candidates K := by
  rintro ⟨x, y⟩ he
  rw [mem_spread] at he
  rw [mem_candidates]
  cases x <;> cases y <;> simp_all [isSpread, isCandidate]

/-- A perfect matching inside the block plus all admirers is feasible, with best-match
quality `2K + 2K(K - 1) qo`. -/
theorem exists_spread (qo : ℝ) (hqo0 : 0 ≤ qo) (hqo1 : qo ≤ 1) (hK : 1 ≤ K) :
    ∃ M, Feasible K M ∧ bestMatch K qo M = 2 * K + 2 * K * (K - 1) * qo := by
  have hsub := spread_subset_candidates K
  refine ⟨spread K, ⟨hsub, ?_⟩, ?_⟩
  · intro v
    cases v with
    | a i =>
      have h : incident K (spread K) (.a i) ⊆
          insert (User.a i, User.b i) (univ.image fun t => (User.a i, User.oa i t)) := by
        rintro ⟨x, y⟩ he
        obtain ⟨he, hv⟩ := (mem_incident K).1 he
        rw [mem_spread] at he
        cases x <;> cases y <;> simp_all [isSpread]
      calc (incident K (spread K) (.a i)).card
          ≤ (univ.image fun t => (User.a i, User.oa i t)).card + 1 :=
            (Finset.card_le_card h).trans (Finset.card_insert_le _ _)
        _ ≤ (K - 1) + 1 := by
            gcongr
            exact Finset.card_image_le.trans (by simp)
        _ = K := by omega
    | b j =>
      have h : incident K (spread K) (.b j) ⊆
          insert (User.a j, User.b j) (univ.image fun t => (User.ob j t, User.b j)) := by
        rintro ⟨x, y⟩ he
        obtain ⟨he, hv⟩ := (mem_incident K).1 he
        rw [mem_spread] at he
        cases x <;> cases y <;> simp_all [isSpread]
      calc (incident K (spread K) (.b j)).card
          ≤ (univ.image fun t => (User.ob j t, User.b j)).card + 1 :=
            (Finset.card_le_card h).trans (Finset.card_insert_le _ _)
        _ ≤ (K - 1) + 1 := by
            gcongr
            exact Finset.card_image_le.trans (by simp)
        _ = K := by omega
    | oa i t =>
      have h : incident K (spread K) (.oa i t) ⊆ {(User.a i, User.oa i t)} := by
        rintro ⟨x, y⟩ he
        obtain ⟨he, hv⟩ := (mem_incident K).1 he
        rw [mem_spread] at he
        cases x <;> cases y <;> simp_all [isSpread]
      exact (Finset.card_le_card h).trans (by simpa using hK)
    | ob j t =>
      have h : incident K (spread K) (.ob j t) ⊆ {(User.ob j t, User.b j)} := by
        rintro ⟨x, y⟩ he
        obtain ⟨he, hv⟩ := (mem_incident K).1 he
        rw [mem_spread] at he
        cases x <;> cases y <;> simp_all [isSpread]
      exact (Finset.card_le_card h).trans (by simpa using hK)
  · unfold bestMatch
    rw [sum_user]
    have hb1 : ∀ v, ∀ e ∈ incident K (spread K) v, quality K qo e ≤ 1 := fun v e he =>
      quality_le_one K hqo1 (hsub ((mem_incident K).1 he).1)
    have hadm : ∀ v, blockUser K v = 0 → ∀ e ∈ incident K (spread K) v, quality K qo e ≤ qo :=
      fun v hv e he => (quality_admirer K qo (hsub ((mem_incident K).1 he).1) hv
        ((mem_incident K).1 he).2).le
    have ha : ∀ i, topK (quality K qo) 1 (incident K (spread K) (.a i)) = 1 := fun i =>
      topK_one_eq zero_le_one (x := (.a i, .b i))
        ((mem_incident K).2 ⟨(mem_spread K).2 (by simp [isSpread]), Or.inl rfl⟩)
        rfl (hb1 (.a i))
    have hb : ∀ j, topK (quality K qo) 1 (incident K (spread K) (.b j)) = 1 := fun j =>
      topK_one_eq zero_le_one (x := (.a j, .b j))
        ((mem_incident K).2 ⟨(mem_spread K).2 (by simp [isSpread]), Or.inr rfl⟩)
        rfl (hb1 (.b j))
    have hoa : ∀ i t, topK (quality K qo) 1 (incident K (spread K) (.oa i t)) = qo :=
      fun i t => topK_one_eq hqo0 (x := (.a i, .oa i t))
        ((mem_incident K).2 ⟨(mem_spread K).2 (by simp [isSpread]), Or.inr rfl⟩)
        rfl (hadm (.oa i t) rfl)
    have hob : ∀ j t, topK (quality K qo) 1 (incident K (spread K) (.ob j t)) = qo :=
      fun j t => topK_one_eq hqo0 (x := (.ob j t, .b j))
        ((mem_incident K).2 ⟨(mem_spread K).2 (by simp [isSpread]), Or.inl rfl⟩)
        rfl (hadm (.ob j t) rfl)
    simp only [ha, hb, hoa, hob, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    rw [Nat.cast_sub hK, Nat.cast_one]
    ring

/-- **R4 (k = 1).** Every additive-quality optimum has best-match quality `2K`, while
some feasible set achieves `2K + 2K(K - 1) qo`. -/
theorem additive_optimum_loses (qo : ℝ) (hqo0 : 0 ≤ qo) (hqo : qo < 1 / 2) (hK : 1 ≤ K)
    {M : Finset (User K × User K)} (hM : Feasible K M)
    (hopt : ∀ M', Feasible K M' → additive K qo M' ≤ additive K qo M) :
    bestMatch K qo M = 2 * K ∧
      ∃ M', Feasible K M' ∧ bestMatch K qo M' = 2 * K + 2 * K * (K - 1) * qo := by
  have hqo1 : qo ≤ 1 := by linarith
  have hblock := block_feasible_additive K qo
  have hle := additive_le K qo hqo0 hqo hM
  have hge := hopt (block K) hblock.1
  rw [hblock.2] at hge
  have hMeq := eq_block_of_additive_eq K qo hqo0 hqo hM (le_antisymm hle hge)
  exact ⟨hMeq ▸ bestMatch_block K qo hqo0 hqo1, exists_spread K qo hqo0 hqo1 hK⟩

end R4

end DatingAlgo
