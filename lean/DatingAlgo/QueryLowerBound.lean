import DatingAlgo.IndepExp
import DatingAlgo.EdgeColoring

/-!
# Theorem 4 (queries are unavoidable) and Proposition 6(b) (DSIC without queries)

Theorem 4 and Proposition 6(b) of the vault note "Truthful Swiping with an LLM Oracle".

**The market.** Two sides `I`, `J` with `n` users each. Each pair is acceptable
independently with probability `p`, and an acceptable pair is worth `w = 2`.
* Theorem 4: each `I`-user values each `J`-user at 2 with probability `p` (else 0), all
  `J`-users value everyone at 2, all costs are 1, utilities are additive.
* Proposition 6(b): every value is 2 with probability `√p` (else 0), costs are 1, users
  are top-1.

In both, the acceptable graph `G` is `G(n, n, p)`: a random subset of `I × J` containing
each pair independently with probability `p` (`indepExp univ (fun _ => p)`), and a
matched acceptable pair adds 2 to welfare. Unacceptable pairs add at most 0, and sincere
users never match them.

**Policies (Theorem 4).** Users swipe sincerely, as in `OPT_FI`'s definition; the policy
is arbitrary and adaptive. Only an `I`-side query or a display reveals whether a pair is
acceptable (`J`-users accept everyone, so `J`-side queries reveal nothing). A policy is
therefore described by a `RevealTree`: it reveals one pair at a time, choosing the next
pair from what it has seen, and each reveal is a query or a display (displays of pairs
already revealed need no node). The policy's matches are acceptable pairs it revealed
(`mset S ⊆ revealed ∩ S`). This class contains every real policy, so an upper bound for
it is an upper bound for all. A randomized policy is a mixture of trees, and the bound
is linear, so it covers those too.

**Results.**
* `RevealTree.indepExp_revealed_true` (the revealing lemma): the expected number of
  acceptable pairs revealed is `E ∑_{revealed} p`, because each revealed pair is fresh.
* `thm4_policy`: `E W ≤ 2p (E[queries] + D_max)`, where every path makes at most `D_max`
  displays (`2nb`: each user sees at most `b` profiles).
* `maxBMatch_ge` (the benchmark): `E[best b-matching of G] ≥ (b/D) n² p κ` for every
  threshold `D ≥ b` above the mean degree, with `κ = 1 - 2σ²/(D - μ)²`. The proof keeps
  edges whose ends have degree at most `D`, bounds their number with Chebyshev's
  inequality, and splits them by König's theorem (`exists_degCap_subset`).
* `thm4` and `thm4_asymp` (Theorem 4): `E W ≤ p (2q̄/b + 2)(1 + o(1)) OPT_FI` as
  `np → ∞` with `b ≤ np`. The note assumed `np ≥ C(K + log n)`; `np → ∞` suffices.
* `prop6b_policy` and `prop6b_asymp` (Proposition 6(b)): if the pairs that can match are
  fixed before values are drawn and number at most `2n`, `E W ≤ 2p (1 + o(1)) OPT_IR`.
-/

namespace DatingAlgo

open Finset

/-- An adaptive process that reveals coins one at a time: at a node it reveals coin `e`
(by a query if `isQuery`, else by a display) and continues with `t1` if the coin is true,
`t0` if false. -/
inductive RevealTree (α : Type*) where
  | leaf : RevealTree α
  | node (e : α) (isQuery : Bool) (t0 t1 : RevealTree α) : RevealTree α

namespace RevealTree

variable {α : Type*} [DecidableEq α]

/-- Every coin the tree may reveal. -/
def coins : RevealTree α → Finset α
  | leaf => ∅
  | node e _ t0 t1 => insert e (t0.coins ∪ t1.coins)

/-- No coin is revealed twice along a path. -/
def WF : RevealTree α → Prop
  | leaf => True
  | node e _ t0 t1 => e ∉ t0.coins ∧ e ∉ t1.coins ∧ t0.WF ∧ t1.WF

/-- The coins revealed along the path followed when `S` is the set of true coins. -/
def revealed : RevealTree α → Finset α → Finset α
  | leaf, _ => ∅
  | node e _ t0 t1, S => insert e (if e ∈ S then t1.revealed S else t0.revealed S)

/-- The number of queries along the path. -/
def queries : RevealTree α → Finset α → ℕ
  | leaf, _ => 0
  | node e b t0 t1, S => (if b then 1 else 0) + if e ∈ S then t1.queries S else t0.queries S

/-- The number of revealing displays along the path. -/
def displays : RevealTree α → Finset α → ℕ
  | leaf, _ => 0
  | node e b t0 t1, S => (if b then 0 else 1) + if e ∈ S then t1.displays S else t0.displays S

theorem revealed_subset_coins (T : RevealTree α) (S : Finset α) : T.revealed S ⊆ T.coins := by
  induction T with
  | leaf => simp [revealed]
  | node e _ t0 t1 ih0 ih1 =>
    simp only [revealed, coins]
    apply insert_subset_insert
    split_ifs
    · exact ih1.trans subset_union_right
    · exact ih0.trans subset_union_left

/-- The path only depends on the coins the tree may reveal. -/
theorem revealed_congr (T : RevealTree α) {S S' : Finset α}
    (h : ∀ x ∈ T.coins, x ∈ S ↔ x ∈ S') : T.revealed S = T.revealed S' := by
  induction T with
  | leaf => rfl
  | node e _ t0 t1 ih0 ih1 =>
    simp only [coins, mem_insert, mem_union] at h
    simp only [revealed]
    rw [ih0 fun x hx => h x (Or.inr (Or.inl hx)), ih1 fun x hx => h x (Or.inr (Or.inr hx)),
      if_congr (h e (Or.inl rfl)) rfl rfl]

/-- A coin the tree never reveals does not affect its path. -/
theorem revealed_insert {T : RevealTree α} {e : α} (he : e ∉ T.coins) (S : Finset α) :
    T.revealed (insert e S) = T.revealed S :=
  T.revealed_congr fun x hx => by
    rw [mem_insert, or_iff_right]
    rintro rfl
    exact he hx

/-- Every reveal is a query or a display. -/
theorem card_revealed {T : RevealTree α} (hT : T.WF) (S : Finset α) :
    (T.revealed S).card = T.queries S + T.displays S := by
  induction T with
  | leaf => simp [revealed, queries, displays]
  | node e b t0 t1 ih0 ih1 =>
    obtain ⟨h0, h1, hw0, hw1⟩ := hT
    simp only [revealed, queries, displays]
    by_cases he : e ∈ S
    · simp only [he, ↓reduceIte]
      rw [card_insert_of_notMem fun h => h1 (revealed_subset_coins t1 S h), ih1 hw1]
      cases b <;> simp <;> ring
    · simp only [he, ↓reduceIte]
      rw [card_insert_of_notMem fun h => h0 (revealed_subset_coins t0 S h), ih0 hw0]
      cases b <;> simp <;> ring

/-- **The revealing lemma.** For independent coins, the expected number of true coins an
adaptive process reveals equals the expected sum of the probabilities of the coins it
reveals: each revealed coin is fresh when it is revealed. -/
theorem indepExp_revealed_true {T : RevealTree α} (hT : T.WF) {U : Finset α}
    (hU : T.coins ⊆ U) (p : α → ℝ) :
    indepExp U p (fun S => (((T.revealed S).filter (· ∈ S)).card : ℝ)) =
      indepExp U p (fun S => ∑ e ∈ T.revealed S, p e) := by
  induction T generalizing U with
  | leaf => simp [revealed]
  | node e b t0 t1 ih0 ih1 =>
    obtain ⟨h0, h1, hw0, hw1⟩ := hT
    simp only [coins, insert_subset_iff, union_subset_iff] at hU
    obtain ⟨heU, hU0, hU1⟩ := hU
    have hsub : ∀ {t : RevealTree α}, e ∉ t.coins → t.coins ⊆ U →
        t.coins ⊆ U.erase e :=
      fun he ht x hx => mem_erase.mpr ⟨fun h => he (h ▸ hx), ht hx⟩
    have hnot := notMem_erase e U
    have hS : ∀ S ⊆ U.erase e, e ∉ S := fun S hS h => hnot (hS h)
    have hr0 : ∀ S, e ∉ t0.revealed S := fun S h => h0 (revealed_subset_coins t0 S h)
    have hr1 : ∀ S, e ∉ t1.revealed S := fun S h => h1 (revealed_subset_coins t1 S h)
    rw [← insert_erase heU, indepExp_insert hnot, indepExp_insert hnot]
    have l0 : indepExp (U.erase e) p
        (fun S => ((((node e b t0 t1).revealed S).filter (· ∈ S)).card : ℝ)) =
        indepExp (U.erase e) p (fun S => (((t0.revealed S).filter (· ∈ S)).card : ℝ)) := by
      refine indepExp_congr fun S hSU => ?_
      simp only [revealed, hS S hSU, ↓reduceIte, filter_insert]
    have l1 : indepExp (U.erase e) p
        (fun S => ((((node e b t0 t1).revealed (insert e S)).filter
          (· ∈ insert e S)).card : ℝ)) =
        indepExp (U.erase e) p (fun S => 1 + (((t1.revealed S).filter (· ∈ S)).card : ℝ)) := by
      refine indepExp_congr fun S _ => ?_
      have hf : (t1.revealed S).filter (· ∈ insert e S) = (t1.revealed S).filter (· ∈ S) :=
        filter_congr fun x hx => by
          rw [mem_insert, or_iff_right]
          rintro rfl
          exact hr1 S hx
      simp only [revealed, mem_insert_self, ↓reduceIte, filter_insert, revealed_insert h1, hf]
      rw [card_insert_of_notMem fun h => hr1 S (mem_filter.mp h).1]
      push_cast
      ring
    have r0 : indepExp (U.erase e) p (fun S => ∑ x ∈ (node e b t0 t1).revealed S, p x) =
        indepExp (U.erase e) p (fun S => p e + ∑ x ∈ t0.revealed S, p x) := by
      refine indepExp_congr fun S hSU => ?_
      simp only [revealed, hS S hSU, ↓reduceIte]
      rw [sum_insert (hr0 S)]
    have r1 : indepExp (U.erase e) p
        (fun S => ∑ x ∈ (node e b t0 t1).revealed (insert e S), p x) =
        indepExp (U.erase e) p (fun S => p e + ∑ x ∈ t1.revealed S, p x) := by
      refine indepExp_congr fun S _ => ?_
      simp only [revealed, mem_insert_self, ↓reduceIte, revealed_insert h1]
      rw [sum_insert (hr1 S)]
    rw [l0, l1, r0, r1, indepExp_add, indepExp_add, indepExp_add, indepExp_const,
      indepExp_const, ih0 hw0 (hsub h0 hU0), ih1 hw1 (hsub h1 hU1)]
    ring

end RevealTree

/-- The second moment of a binomial count about any point `c`:
`E[(|S| - c)²] = |V| p (1 - p) + (|V| p - c)²`. -/
theorem indepExp_card_sub_sq {α : Type*} [DecidableEq α] (V : Finset α) (p c : ℝ) :
    indepExp V (fun _ => p) (fun S => ((S.card : ℝ) - c) ^ 2) =
      V.card * p * (1 - p) + (V.card * p - c) ^ 2 := by
  induction V using Finset.induction_on generalizing c with
  | empty => simp [indepExp]
  | insert a V ha ih =>
    have h : indepExp V (fun _ => p) (fun S => (((insert a S).card : ℝ) - c) ^ 2) =
        indepExp V (fun _ => p) (fun S => ((S.card : ℝ) - (c - 1)) ^ 2) :=
      indepExp_congr fun S hS => by
        rw [card_insert_of_notMem fun h => ha (hS h)]
        push_cast
        ring
    rw [indepExp_insert ha, h, ih, ih, card_insert_of_notMem ha]
    push_cast
    ring

/-- The second moment of the number of true coins in `W`. -/
theorem indepExp_card_inter_sub_sq {α : Type*} [DecidableEq α] [Fintype α] (W : Finset α)
    (p c : ℝ) :
    indepExp univ (fun _ => p) (fun S => (((S ∩ W).card : ℝ) - c) ^ 2) =
      W.card * p * (1 - p) + (W.card * p - c) ^ 2 := by
  rw [indepExp_inter univ W (fun _ => p) (fun S => ((S.card : ℝ) - c) ^ 2), univ_inter,
    indepExp_card_sub_sq]

section Market

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The size of the largest `b`-matching inside `G`: the largest `T ⊆ G` with every
degree at most `b`. -/
noncomputable def maxBMatch (b : ℕ) (G : Finset (I × J)) : ℕ :=
  (G.powerset.filter fun T => (∀ i, degI T i ≤ b) ∧ ∀ j, degJ T j ≤ b).sup card

/-- Any `b`-matching inside `G` is a lower bound. -/
theorem card_le_maxBMatch {b : ℕ} {G T : Finset (I × J)} (hTG : T ⊆ G)
    (hI : ∀ i, degI T i ≤ b) (hJ : ∀ j, degJ T j ≤ b) : T.card ≤ maxBMatch b G := by
  unfold maxBMatch
  exact le_sup (f := card) (mem_filter.mpr ⟨mem_powerset.mpr hTG, hI, hJ⟩)

/-- **Theorem 4, the policy side.** A policy whose matches are acceptable pairs it
revealed, with at most `Dmax` displays along every path, earns
`E W ≤ 2p (E[queries] + Dmax)`, since each match is worth 2. -/
theorem thm4_policy {T : RevealTree (I × J)} (hT : T.WF) {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1)
    (mset : Finset (I × J) → Finset (I × J))
    (hm : ∀ S, mset S ⊆ (T.revealed S).filter (· ∈ S)) {Dmax : ℕ}
    (hdisp : ∀ S, T.displays S ≤ Dmax) :
    indepExp univ (fun _ => p) (fun S => 2 * ((mset S).card : ℝ)) ≤
      2 * p * (indepExp univ (fun _ => p) (fun S => (T.queries S : ℝ)) + Dmax) := by
  have hp' : ∀ i ∈ (univ : Finset (I × J)), 0 ≤ p ∧ p ≤ 1 := fun _ _ => hp
  calc indepExp univ (fun _ => p) (fun S => 2 * ((mset S).card : ℝ))
      ≤ indepExp univ (fun _ => p)
          (fun S => 2 * (((T.revealed S).filter (· ∈ S)).card : ℝ)) :=
        indepExp_mono hp' fun S _ => by
          have := card_le_card (hm S)
          gcongr
    _ = 2 * p * indepExp univ (fun _ => p) (fun S => (T.queries S : ℝ) + T.displays S) := by
        have h1 : indepExp univ (fun _ => p)
            (fun S => 2 * (((T.revealed S).filter (· ∈ S)).card : ℝ)) =
            2 * indepExp univ (fun _ => p) (fun S => ∑ _ ∈ T.revealed S, p) := by
          rw [indepExp_const_mul, RevealTree.indepExp_revealed_true hT (subset_univ _)]
        have h2 : indepExp univ (fun _ => p) (fun S => ∑ _ ∈ T.revealed S, p) =
            p * indepExp univ (fun _ => p) (fun S => (T.queries S : ℝ) + T.displays S) := by
          rw [← indepExp_const_mul]
          apply indepExp_congr
          intro S _
          rw [sum_const, RevealTree.card_revealed hT, nsmul_eq_mul]
          push_cast
          ring
        rw [h1, h2, mul_assoc]
    _ ≤ 2 * p * (indepExp univ (fun _ => p) (fun S => (T.queries S : ℝ)) + Dmax) := by
        rw [indepExp_add]
        have : indepExp univ (fun _ => p) (fun S => (T.displays S : ℝ)) ≤ Dmax := by
          calc indepExp univ (fun _ => p) (fun S => (T.displays S : ℝ))
              ≤ indepExp univ (fun _ => p) (fun _ => (Dmax : ℝ)) :=
                indepExp_mono hp' fun S _ => by exact_mod_cast hdisp S
            _ = Dmax := indepExp_const _ _ _
        have : 0 ≤ 2 * p := by linarith [hp.1]
        gcongr

/-- The other pairs in `e`'s row number `|J| - 1`. -/
theorem card_row_erase (e : I × J) :
    (((univ.filter fun x : I × J => x.1 = e.1).erase e).card : ℝ) = Fintype.card J - 1 := by
  have h : (univ.filter fun x : I × J => x.1 = e.1) = {e.1} ×ˢ univ := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton, and_true]
  have he : e ∈ ({e.1} : Finset I) ×ˢ (univ : Finset J) := by simp
  rw [h, card_erase_of_mem he, card_product, card_singleton, one_mul, card_univ,
    Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨e.2⟩), Nat.cast_one]

/-- The other pairs in `e`'s column number `|I| - 1`. -/
theorem card_col_erase (e : I × J) :
    (((univ.filter fun x : I × J => x.2 = e.2).erase e).card : ℝ) = Fintype.card I - 1 := by
  have h : (univ.filter fun x : I × J => x.2 = e.2) = univ ×ˢ {e.2} := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton]
  have he : e ∈ (univ : Finset I) ×ˢ ({e.2} : Finset J) := by simp
  rw [h, card_erase_of_mem he, card_product, card_singleton, mul_one, card_univ,
    Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨e.1⟩), Nat.cast_one]

/-- `e.1`'s degree is at most one more than the number of other pairs of `S` in `e`'s row. -/
theorem degI_le_card_row (S : Finset (I × J)) (e : I × J) :
    degI S e.1 ≤ (S ∩ (univ.filter fun x : I × J => x.1 = e.1).erase e).card + 1 := by
  unfold degI
  refine (card_le_card fun x hx => ?_).trans (card_insert_le e _)
  obtain ⟨hxS, hx1⟩ := mem_filter.mp hx
  rw [mem_insert, mem_inter, mem_erase, mem_filter]
  by_cases hxe : x = e
  · exact Or.inl hxe
  · exact Or.inr ⟨hxS, hxe, mem_univ x, hx1⟩

/-- `e.2`'s degree is at most one more than the number of other pairs of `S` in `e`'s
column. -/
theorem degJ_le_card_col (S : Finset (I × J)) (e : I × J) :
    degJ S e.2 ≤ (S ∩ (univ.filter fun x : I × J => x.2 = e.2).erase e).card + 1 := by
  unfold degJ
  refine (card_le_card fun x hx => ?_).trans (card_insert_le e _)
  obtain ⟨hxS, hx2⟩ := mem_filter.mp hx
  rw [mem_insert, mem_inter, mem_erase, mem_filter]
  by_cases hxe : x = e
  · exact Or.inl hxe
  · exact Or.inr ⟨hxS, hxe, mem_univ x, hx2⟩

/-- **Theorem 4, the benchmark.** In `G(n, n, p)`, for every `D ≥ b` above the mean degree
`μ = (n - 1) p` of the other `n - 1` pairs at a user,
`E[best b-matching] ≥ (b / D) · n² p · (1 - 2 (n - 1) p (1 - p) / (D - (n - 1) p)²)`. -/
theorem maxBMatch_ge {n : ℕ} (hI : Fintype.card I = n) (hJ : Fintype.card J = n) {p : ℝ}
    (hp : 0 ≤ p ∧ p ≤ 1) {b D : ℕ} (hbD : b ≤ D) (hD : ((n : ℝ) - 1) * p < D) :
    (b : ℝ) / D * ((n : ℝ) ^ 2 * p *
        (1 - 2 * (((n : ℝ) - 1) * p * (1 - p)) / ((D : ℝ) - ((n : ℝ) - 1) * p) ^ 2)) ≤
      indepExp (univ : Finset (I × J)) (fun _ => p) (fun S => (maxBMatch b S : ℝ)) := by
  have hp' : ∀ i ∈ (univ : Finset (I × J)), 0 ≤ p ∧ p ≤ 1 := fun _ _ => hp
  set μ : ℝ := ((n : ℝ) - 1) * p with hμ
  set d : ℝ := (D : ℝ) - μ with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  set R : I × J → Finset (I × J) := fun e => (univ.filter fun x : I × J => x.1 = e.1).erase e
  set C : I × J → Finset (I × J) := fun e => (univ.filter fun x : I × J => x.2 = e.2).erase e
  set G : Finset (I × J) → Finset (I × J) :=
    fun S => S.filter fun e => degI S e.1 ≤ D ∧ degJ S e.2 ≤ D
  set φ : I × J → Finset (I × J) → ℝ := fun e S =>
    1 - (((S ∩ R e).card : ℝ) - μ) ^ 2 / d ^ 2 - (((S ∩ C e).card : ℝ) - μ) ^ 2 / d ^ 2
    with hφ
  -- König: the edges with both degrees at most `D` hold a `b`-matching of `b/D` their size
  have hA : ∀ S, (b : ℝ) / D * (G S).card ≤ maxBMatch b S := by
    intro S
    rcases Nat.eq_zero_or_pos D with hD0 | hD0
    · simp [hD0]
    have hGI : ∀ i, degI (G S) i ≤ D := by
      intro i
      rcases ((G S).filter fun e => e.1 = i).eq_empty_or_nonempty with h0 | ⟨e, he⟩
      · simp [degI, h0]
      · obtain ⟨heG, rfl⟩ := mem_filter.mp he
        exact (degI_mono (filter_subset _ S) e.1).trans (mem_filter.mp heG).2.1
    have hGJ : ∀ j, degJ (G S) j ≤ D := by
      intro j
      rcases ((G S).filter fun e => e.2 = j).eq_empty_or_nonempty with h0 | ⟨e, he⟩
      · simp [degJ, h0]
      · obtain ⟨heG, rfl⟩ := mem_filter.mp he
        exact (degJ_mono (filter_subset _ S) e.2).trans (mem_filter.mp heG).2.2
    obtain ⟨T, hTG, hTI, hTJ, hw⟩ := exists_degCap_subset (G S) hbD hGI hGJ (fun _ => 1)
    simp only [sum_const, nsmul_eq_mul, mul_one] at hw
    have hT : (T.card : ℝ) ≤ maxBMatch b S := by
      exact_mod_cast card_le_maxBMatch (hTG.trans (filter_subset _ S)) hTI hTJ
    rw [div_mul_eq_mul_div, div_le_iff₀ (by exact_mod_cast hD0)]
    calc (b : ℝ) * (G S).card ≤ D * T.card := hw
      _ ≤ D * maxBMatch b S := by gcongr
      _ = maxBMatch b S * D := mul_comm _ _
  -- Chebyshev, pointwise: a pair of `S` outside `G S` has `D` other pairs in its row or column
  have hC1 : ∀ S, ∑ e, φ e S * (if e ∈ S then 1 else 0) ≤ ((G S).card : ℝ) := by
    intro S
    have hcard : (∑ e, if e ∈ G S then (1 : ℝ) else 0) = ((G S).card : ℝ) := by
      rw [sum_boole, filter_mem_eq_inter, univ_inter]
    rw [← hcard]
    refine sum_le_sum fun e _ => ?_
    have hX : 0 ≤ (((S ∩ R e).card : ℝ) - μ) ^ 2 / d ^ 2 := by positivity
    have hY : 0 ≤ (((S ∩ C e).card : ℝ) - μ) ^ 2 / d ^ 2 := by positivity
    by_cases heS : e ∈ S
    · by_cases heG : e ∈ G S
      · simp only [heS, heG, ↓reduceIte, mul_one, hφ]
        linarith
      · have hne : ¬(degI S e.1 ≤ D ∧ degJ S e.2 ≤ D) :=
          fun h => heG (mem_filter.mpr ⟨heS, h⟩)
        simp only [heS, heG, ↓reduceIte, mul_one, hφ]
        rcases not_and_or.mp hne with h | h
        · have h1 : degI S e.1 ≤ (S ∩ R e).card + 1 := degI_le_card_row S e
          have h2 : (D : ℝ) ≤ (S ∩ R e).card := by
            exact_mod_cast (by omega : D ≤ (S ∩ R e).card)
          have h3 : 1 ≤ (((S ∩ R e).card : ℝ) - μ) ^ 2 / d ^ 2 := by
            rw [le_div_iff₀ (by positivity), one_mul]
            exact pow_le_pow_left₀ hd0.le (by linarith) 2
          linarith
        · have h1 : degJ S e.2 ≤ (S ∩ C e).card + 1 := degJ_le_card_col S e
          have h2 : (D : ℝ) ≤ (S ∩ C e).card := by
            exact_mod_cast (by omega : D ≤ (S ∩ C e).card)
          have h3 : 1 ≤ (((S ∩ C e).card : ℝ) - μ) ^ 2 / d ^ 2 := by
            rw [le_div_iff₀ (by positivity), one_mul]
            exact pow_le_pow_left₀ hd0.le (by linarith) 2
          linarith
    · simp only [heS, ↓reduceIte, mul_zero]
      split_ifs <;> norm_num
  -- each row and column count has mean `μ` and variance `(n - 1) p (1 - p)`
  have hC2 : ∀ e, indepExp univ (fun _ => p) (φ e) = 1 - 2 * (μ * (1 - p)) / d ^ 2 := by
    intro e
    have hRc : ((R e).card : ℝ) = n - 1 := (card_row_erase e).trans (by rw [hJ])
    have hCc : ((C e).card : ℝ) = n - 1 := (card_col_erase e).trans (by rw [hI])
    have hvR : indepExp univ (fun _ => p) (fun S => (((S ∩ R e).card : ℝ) - μ) ^ 2) =
        μ * (1 - p) := by
      rw [indepExp_card_inter_sub_sq, hRc, hμ]
      ring
    have hvC : indepExp univ (fun _ => p) (fun S => (((S ∩ C e).card : ℝ) - μ) ^ 2) =
        μ * (1 - p) := by
      rw [indepExp_card_inter_sub_sq, hCc, hμ]
      ring
    have hφe : φ e = fun S => 1 + (-(1 / d ^ 2)) * ((((S ∩ R e).card : ℝ) - μ) ^ 2) +
        (-(1 / d ^ 2)) * ((((S ∩ C e).card : ℝ) - μ) ^ 2) := by
      funext S
      simp only [hφ]
      ring
    rw [hφe, indepExp_add, indepExp_add, indepExp_const, indepExp_const_mul, indepExp_const_mul,
      hvR, hvC]
    ring
  have hb0 : (0 : ℝ) ≤ b / D := by positivity
  calc (b : ℝ) / D * ((n : ℝ) ^ 2 * p * (1 - 2 * (μ * (1 - p)) / d ^ 2))
      = b / D * ∑ e : I × J, p * indepExp univ (fun _ => p) (φ e) := by
        simp only [hC2, sum_const, card_univ, Fintype.card_prod, hI, hJ, nsmul_eq_mul]
        push_cast
        ring
    _ = b / D * indepExp univ (fun _ => p) (fun S => ∑ e, φ e S * if e ∈ S then 1 else 0) := by
        rw [indepExp_sum]
        congr 1
        refine sum_congr rfl fun e _ =>
          (indepExp_mul_mem_of_blind (mem_univ e) (fun _ => p) (φ e) ?_).symm
        intro S
        have key : ∀ W : Finset (I × J), e ∉ W → insert e S ∩ W = S.erase e ∩ W := by
          intro W hW
          rw [insert_inter_of_notMem hW, erase_inter,
            erase_eq_of_notMem fun h => hW (mem_inter.mp h).2]
        simp only [hφ, key (R e) (notMem_erase e _), key (C e) (notMem_erase e _)]
    _ ≤ b / D * indepExp univ (fun _ => p) (fun S => ((G S).card : ℝ)) :=
        mul_le_mul_of_nonneg_left (indepExp_mono hp' fun S _ => hC1 S) hb0
    _ = indepExp univ (fun _ => p) (fun S => b / D * ((G S).card : ℝ)) :=
        (indepExp_const_mul _ _ _ _).symm
    _ ≤ _ := indepExp_mono hp' fun S _ => hA S

/-- **Theorem 4, explicit form.** With `n` users per side, display capacity `b` (so at
most `2nb` displays), threshold `D` and `κ = 1 - 2 (n-1) p (1-p) / (D - (n-1) p)² > 0`,
every policy as above earns `E W ≤ p (2q̄/b + 2) · D / (n p κ) · OPT_FI`, where `q̄` is
the expected number of queries per user and `OPT_FI = 2 E[best b-matching of G]`. -/
theorem thm4 {n : ℕ} (hI : Fintype.card I = n) (hJ : Fintype.card J = n) (hn : 1 ≤ n)
    {p : ℝ} (hp : 0 < p ∧ p ≤ 1) {b D : ℕ} (hb : 1 ≤ b) (hbD : b ≤ D)
    (hD : ((n : ℝ) - 1) * p < D)
    (hκ : 0 < 1 - 2 * (((n : ℝ) - 1) * p * (1 - p)) / ((D : ℝ) - ((n : ℝ) - 1) * p) ^ 2)
    {T : RevealTree (I × J)} (hT : T.WF) (mset : Finset (I × J) → Finset (I × J))
    (hm : ∀ S, mset S ⊆ (T.revealed S).filter (· ∈ S))
    (hdisp : ∀ S, T.displays S ≤ 2 * n * b) :
    indepExp univ (fun _ => p) (fun S => 2 * ((mset S).card : ℝ)) ≤
      p * (2 * (indepExp univ (fun _ => p) (fun S => (T.queries S : ℝ)) / (2 * n)) / b + 2) *
        (D / (n * p *
          (1 - 2 * (((n : ℝ) - 1) * p * (1 - p)) / ((D : ℝ) - ((n : ℝ) - 1) * p) ^ 2))) *
        indepExp (univ : Finset (I × J)) (fun _ => p) (fun S => 2 * (maxBMatch b S : ℝ)) := by
  have hp' : 0 ≤ p ∧ p ≤ 1 := ⟨hp.1.le, hp.2⟩
  have hu : ∀ i ∈ (univ : Finset (I × J)), 0 ≤ p ∧ p ≤ 1 := fun _ _ => hp'
  set κ := 1 - 2 * (((n : ℝ) - 1) * p * (1 - p)) / ((D : ℝ) - ((n : ℝ) - 1) * p) ^ 2
  set Q := indepExp univ (fun _ => p) (fun S => (T.queries S : ℝ))
  set M := indepExp (univ : Finset (I × J)) (fun _ => p) (fun S => (maxBMatch b S : ℝ))
  have hM : (b : ℝ) / D * ((n : ℝ) ^ 2 * p * κ) ≤ M := maxBMatch_ge hI hJ hp' hbD hD
  have h2M : indepExp (univ : Finset (I × J)) (fun _ => p) (fun S => 2 * (maxBMatch b S : ℝ)) =
      2 * M := indepExp_const_mul _ _ _ _
  have hW : indepExp univ (fun _ => p) (fun S => 2 * ((mset S).card : ℝ)) ≤
      2 * p * (Q + 2 * n * b) := by
    have := thm4_policy hT hp' mset hm hdisp
    push_cast at this
    exact this
  have hQ : 0 ≤ Q := by
    calc (0 : ℝ) = indepExp univ (fun _ => p) (fun _ => (0 : ℝ)) := (indepExp_const _ _ _).symm
      _ ≤ Q := indepExp_mono hu fun S _ => Nat.cast_nonneg _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hD0 : (0 : ℝ) < D := by
    have : (b : ℝ) ≤ D := by exact_mod_cast hbD
    linarith
  have hp0 := hp.1
  have hfac : 0 ≤ p * (2 * (Q / (2 * n)) / b + 2) * (D / (n * p * κ)) := by positivity
  rw [h2M]
  calc indepExp univ (fun _ => p) (fun S => 2 * ((mset S).card : ℝ))
      ≤ 2 * p * (Q + 2 * n * b) := hW
    _ = p * (2 * (Q / (2 * n)) / b + 2) * (D / (n * p * κ)) *
          (2 * ((b : ℝ) / D * ((n : ℝ) ^ 2 * p * κ))) := by
        field_simp
    _ ≤ p * (2 * (Q / (2 * n)) / b + 2) * (D / (n * p * κ)) * (2 * M) :=
        mul_le_mul_of_nonneg_left (by linarith) hfac

/-- The threshold behind `thm4_asymp` and `prop6b_asymp`: once `np` is large,
`D = ⌈(1 + ε/4) np⌉` lies above the mean degree, has `κ > 0`, and `D ≤ (1 + ε) n p κ`. -/
theorem exists_threshold {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℝ, 0 < m₀ ∧ ∀ (n : ℕ) (p : ℝ), 0 < p → p ≤ 1 → m₀ ≤ n * p →
      ∃ D : ℕ, (n : ℝ) * p ≤ D ∧ ((n : ℝ) - 1) * p < D ∧
        0 < 1 - 2 * (((n : ℝ) - 1) * p * (1 - p)) / ((D : ℝ) - ((n : ℝ) - 1) * p) ^ 2 ∧
        (D : ℝ) ≤ (1 + ε) * (n * p *
          (1 - 2 * (((n : ℝ) - 1) * p * (1 - p)) / ((D : ℝ) - ((n : ℝ) - 1) * p) ^ 2)) := by
  refine ⟨64 * (1 + ε) / ε ^ 3 + 4 / ε, by positivity, fun n p hp0 hp1 hm => ?_⟩
  have hA : 64 * (1 + ε) ≤ ε ^ 3 * (n * p) := by
    have : 64 * (1 + ε) / ε ^ 3 ≤ n * p := by
      have : 0 < 4 / ε := by positivity
      linarith
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have hB : 4 ≤ ε * (n * p) := by
    have : 4 / ε ≤ n * p := by
      have : 0 < 64 * (1 + ε) / ε ^ 3 := by positivity
      linarith
    rw [div_le_iff₀ hε] at this
    linarith
  have hx0 : 0 < (n : ℝ) * p := by
    by_contra h
    push Not at h
    nlinarith
  have hn : (1 : ℝ) ≤ n := by
    have : (n : ℝ) ≠ 0 := by
      rintro h
      rw [h, zero_mul] at hx0
      exact lt_irrefl _ hx0
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast this)
  refine ⟨⌈(1 + ε / 4) * ((n : ℝ) * p)⌉₊, ?_⟩
  set x : ℝ := (n : ℝ) * p with hx
  set D : ℕ := ⌈(1 + ε / 4) * x⌉₊
  have hD1 : (1 + ε / 4) * x ≤ D := Nat.le_ceil _
  have hD2 : (D : ℝ) < (1 + ε / 4) * x + 1 := Nat.ceil_lt_add_one (by positivity)
  have hμ : ((n : ℝ) - 1) * p = x - p := by rw [hx]; ring
  have hv0 : 0 ≤ ((n : ℝ) - 1) * p * (1 - p) :=
    mul_nonneg (mul_nonneg (by linarith) hp0.le) (by linarith)
  have hvx : ((n : ℝ) - 1) * p * (1 - p) ≤ x := by
    rw [hμ]
    nlinarith
  have hd : ε / 4 * x + p ≤ (D : ℝ) - ((n : ℝ) - 1) * p := by
    rw [hμ]
    linarith
  set d := (D : ℝ) - ((n : ℝ) - 1) * p
  set v := ((n : ℝ) - 1) * p * (1 - p)
  have hd0 : 0 < d := by
    have : 0 < ε / 4 * x := by positivity
    linarith
  have hdx : (ε / 4 * x) ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hkey : (1 + ε) * (2 * v / d ^ 2) ≤ ε / 2 := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    have s1 : (1 + ε) * (2 * v) ≤ 2 * (1 + ε) * x := by nlinarith
    have s2 : 64 * (1 + ε) * x ≤ ε ^ 3 * x * x := by nlinarith
    have s3 : ε / 2 * (ε / 4 * x) ^ 2 ≤ ε / 2 * d ^ 2 :=
      mul_le_mul_of_nonneg_left hdx (by positivity)
    nlinarith
  refine ⟨by nlinarith, by linarith, by nlinarith, ?_⟩
  have h1 : (D : ℝ) ≤ (1 + ε / 2) * x := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hkey hx0.le]

/-- **Theorem 4.** For every `ε > 0` there is `m₀` such that, whenever `np ≥ m₀` and
`b ≤ np`, every policy as above earns at most `(1 + ε) p (2q̄/b + 2) OPT_FI`. So a
constant fraction of `OPT_FI` needs `Ω(b/p)` queries per user, and zero queries get at
most about `2p`. -/
theorem thm4_asymp {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℝ, ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
      (n : ℕ), Fintype.card I = n → Fintype.card J = n → ∀ p : ℝ, 0 < p → p ≤ 1 →
      m₀ ≤ n * p → ∀ b : ℕ, 1 ≤ b → (b : ℝ) ≤ n * p →
      ∀ T : RevealTree (I × J), T.WF → ∀ mset : Finset (I × J) → Finset (I × J),
      (∀ S, mset S ⊆ (T.revealed S).filter (· ∈ S)) → (∀ S, T.displays S ≤ 2 * n * b) →
      indepExp univ (fun _ => p) (fun S => 2 * ((mset S).card : ℝ)) ≤
        (1 + ε) * p *
          (2 * (indepExp univ (fun _ => p) (fun S => (T.queries S : ℝ)) / (2 * n)) / b + 2) *
          indepExp (univ : Finset (I × J)) (fun _ => p) (fun S => 2 * (maxBMatch b S : ℝ)) := by
  obtain ⟨m₀, hm₀, hth⟩ := exists_threshold hε
  refine ⟨m₀, ?_⟩
  intro I J _ _ _ _ n hI hJ p hp0 hp1 hm b hb hbnp T hT mset hmset hdisp
  obtain ⟨D, hnpD, hμD, hκ, hDle⟩ := hth n p hp0 hp1 hm
  have hx : 0 < (n : ℝ) * p := by linarith
  have hn : 1 ≤ n := by
    have : (n : ℝ) ≠ 0 := by
      rintro h
      rw [h, zero_mul] at hx
      exact lt_irrefl _ hx
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast this)
  have hbD : b ≤ D := by exact_mod_cast hbnp.trans hnpD
  have hu : ∀ i ∈ (univ : Finset (I × J)), 0 ≤ p ∧ p ≤ 1 := fun _ _ => ⟨hp0.le, hp1⟩
  refine (thm4 hI hJ hn ⟨hp0, hp1⟩ hb hbD hμD hκ hT mset hmset hdisp).trans ?_
  set κ := 1 - 2 * (((n : ℝ) - 1) * p * (1 - p)) / ((D : ℝ) - ((n : ℝ) - 1) * p) ^ 2
  set Q := indepExp univ (fun _ => p) (fun S => (T.queries S : ℝ))
  set M := indepExp (univ : Finset (I × J)) (fun _ => p) (fun S => 2 * (maxBMatch b S : ℝ))
  have hQ : 0 ≤ Q := by
    calc (0 : ℝ) = indepExp univ (fun _ => p) (fun _ => (0 : ℝ)) := (indepExp_const _ _ _).symm
      _ ≤ Q := indepExp_mono hu fun S _ => Nat.cast_nonneg _
  have hM : 0 ≤ M := by
    calc (0 : ℝ) = indepExp univ (fun _ => p) (fun _ => (0 : ℝ)) := (indepExp_const _ _ _).symm
      _ ≤ M := indepExp_mono hu fun S _ => by positivity
  have hF : (D : ℝ) / (n * p * κ) ≤ 1 + ε := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hA : 0 ≤ p * (2 * (Q / (2 * n)) / b + 2) := by positivity
  calc p * (2 * (Q / (2 * n)) / b + 2) * (D / (n * p * κ)) * M
      ≤ p * (2 * (Q / (2 * n)) / b + 2) * (1 + ε) * M :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF hA) hM
    _ = (1 + ε) * p * (2 * (Q / (2 * n)) / b + 2) * M := by ring

/-- **Proposition 6(b), the policy side.** Without queries, every match starts as a
period-1 initiation or mutual view, chosen before any value is known. Under DSIC each
user sees at most one profile that can match it (Proposition 6(a)), so the period-1
pairs `P` that can match number at most `2n`. If the matches are acceptable pairs in
`P`, then `E W ≤ 2 · 2np`. -/
theorem prop6b_policy {p : ℝ} (hp : 0 ≤ p ∧ p ≤ 1) (P : Finset (I × J)) {n : ℕ}
    (hP : P.card ≤ 2 * n) (mset : Finset (I × J) → Finset (I × J))
    (hm : ∀ S, mset S ⊆ P ∩ S) :
    indepExp univ (fun _ => p) (fun S => 2 * ((mset S).card : ℝ)) ≤ 2 * (2 * n * p) := by
  have hp' : ∀ i ∈ (univ : Finset (I × J)), 0 ≤ p ∧ p ≤ 1 := fun _ _ => hp
  have hPS : indepExp univ (fun _ => p) (fun S => ((S ∩ P).card : ℝ)) = P.card * p := by
    rw [indepExp_inter univ P (fun _ => p) (fun S => (S.card : ℝ)), univ_inter, indepExp_card,
      sum_const, nsmul_eq_mul]
  calc indepExp univ (fun _ => p) (fun S => 2 * ((mset S).card : ℝ))
      ≤ indepExp univ (fun _ => p) (fun S => 2 * ((S ∩ P).card : ℝ)) :=
        indepExp_mono hp' fun S _ => by
          have := card_le_card ((hm S).trans (inter_comm P S).le)
          gcongr
    _ = 2 * (P.card * p) := by rw [indepExp_const_mul, hPS]
    _ ≤ 2 * (2 * n * p) := by
        have : (P.card : ℝ) ≤ 2 * n := by exact_mod_cast hP
        have := hp.1
        gcongr

/-- **Proposition 6(b).** For every `ε > 0` there is `m₀` such that, whenever `np ≥ m₀`,
every zero-query DSIC policy as in `prop6b_policy` earns at most `(1 + ε) 2p OPT_IR`,
where `OPT_IR = 2 E[best matching of G]` for top-1 users. SDH earns at least
`c_1² OPT_IR ≈ 0.40 OPT_IR` (Theorem 3(b)). -/
theorem prop6b_asymp {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℝ, ∀ (I J : Type) [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
      (n : ℕ), Fintype.card I = n → Fintype.card J = n → ∀ p : ℝ, 0 < p → p ≤ 1 →
      m₀ ≤ n * p → ∀ P : Finset (I × J), P.card ≤ 2 * n →
      ∀ mset : Finset (I × J) → Finset (I × J), (∀ S, mset S ⊆ P ∩ S) →
      indepExp univ (fun _ => p) (fun S => 2 * ((mset S).card : ℝ)) ≤
        (1 + ε) * (2 * p) * indepExp (univ : Finset (I × J)) (fun _ => p) (fun S => 2 * (maxBMatch 1 S : ℝ)) := by
  obtain ⟨m₀, hm₀, hth⟩ := exists_threshold hε
  refine ⟨m₀, ?_⟩
  intro I J _ _ _ _ n hI hJ p hp0 hp1 hm P hP mset hmset
  obtain ⟨D, hnpD, hμD, hκ, hDle⟩ := hth n p hp0 hp1 hm
  have hx : 0 < (n : ℝ) * p := by linarith
  have hD0 : (0 : ℝ) < D := by linarith
  have hD1 : 1 ≤ D := by
    have : 0 < D := by exact_mod_cast hD0
    omega
  set κ := 1 - 2 * (((n : ℝ) - 1) * p * (1 - p)) / ((D : ℝ) - ((n : ℝ) - 1) * p) ^ 2
  set M := indepExp (univ : Finset (I × J)) (fun _ => p) (fun S => (maxBMatch 1 S : ℝ))
  have hM : ((1 : ℕ) : ℝ) / D * ((n : ℝ) ^ 2 * p * κ) ≤ M :=
    maxBMatch_ge hI hJ ⟨hp0.le, hp1⟩ hD1 hμD
  have h2M : indepExp (univ : Finset (I × J)) (fun _ => p) (fun S => 2 * (maxBMatch 1 S : ℝ)) =
      2 * M := indepExp_const_mul _ _ _ _
  have h1 : 1 ≤ (1 + ε) * (n * p * κ) / D := (one_le_div hD0).mpr hDle
  have key : 2 * (2 * n * p) ≤
      (1 + ε) * (2 * p) * (2 * (((1 : ℕ) : ℝ) / D * ((n : ℝ) ^ 2 * p * κ))) := by
    have e : (1 + ε) * (2 * p) * (2 * (((1 : ℕ) : ℝ) / D * ((n : ℝ) ^ 2 * p * κ))) =
        4 * (n * p) * ((1 + ε) * (n * p * κ) / D) := by
      push_cast
      field_simp
      ring
    rw [e]
    nlinarith
  rw [h2M]
  calc indepExp univ (fun _ => p) (fun S => 2 * ((mset S).card : ℝ))
      ≤ 2 * (2 * n * p) := prop6b_policy ⟨hp0.le, hp1⟩ P hP mset hmset
    _ ≤ (1 + ε) * (2 * p) * (2 * (((1 : ℕ) : ℝ) / D * ((n : ℝ) ^ 2 * p * κ))) := key
    _ ≤ (1 + ε) * (2 * p) * (2 * M) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end Market

end DatingAlgo
