import DatingAlgo.CorrelationGap

/-!
# Greedy backlog responses over `T` periods

The single-responder part of the repaired Theorem 5.3: the per-period relaxation Rel_τ in
the vault note "Counterexamples to the Multi-Period Dating Heuristic Guarantees", section
"Repairing the relaxation".

## Setting
One responder, periods `0, …, T-1`.
- Period `n` has `c n` free display slots.
- `A n` is the set of profiles that initiated toward the responder before period `n`. It
  grows with `n`.
- `L` is the random set of profiles that liked the responder: each `a` independently with
  probability `q a`. So the backlog can hold `L ∩ A n` in period `n`.
- Answering `a` earns `w a ≥ 0`, the probability that the responder likes `a` back.

**Greedy** (`greedyPick`) answers, in each period, a best set of at most `c n` profiles
still waiting in the backlog ("best available profiles first", any tie-breaking).

## Results
1. **Greedy is optimal on every sample path** (`greedy_optimal`), even against a clairvoyant
   plan. Every backlog profile stays answerable until period `T-1`, so an exchange argument
   works. Here it is a counting invariant: for every threshold `θ > 0`, greedy has answered
   at least as many profiles of weight `≥ θ` as any plan, at the end of every period.
2. **Correlation gap** (`greedy_correlation_gap`). Let `y n a ≥ 0` be a fractional response
   plan: `y n a = 0` unless `a ∈ A n`, `∑_n y n a ≤ q a`, and `∑_a y n a ≤ c n`. This is
   Rel_τ's response part for one user. Then `E[greedy] ≥ (1 - 1/e) ∑ w y`.

## Proof of the correlation gap
The vault note's sketch goes through a laminar matroid, its concave closure, and the
correlation gap for matroid rank functions. This proof avoids matroid theory.
- *Splitting* (`indepExp_split_le`): assign each profile in `L`, independently, to period
  `n` with probability `y n a / q a`. The profiles assigned to `n` form an independent random
  set with marginals `y n`. Answering the best `c n` of them in period `n`, for every `n`, is
  a feasible plan. So `E[greedy] ≥ ∑_n E[topK (c n) (profiles assigned to n)]`.
- *Per period*: the weighted top-K correlation gap (`topK_correlation_gap`) bounds each term
  by `(1 - 1/e) ∑_a w a y n a`.

The splitting lemma is proved by induction on the ground set, without constructing the
assignment explicitly.
-/

namespace DatingAlgo

open Finset

variable {α : Type*} [DecidableEq α]

/-! ### Expectations: relabelling, restriction, independence from one coin -/

/-- Relabelling coins: if `g` only looks at the coins `e '' V`, through an injective `e`, its
expectation is an expectation over `V`. -/
theorem indepExp_comap {β : Type*} [DecidableEq β] {e : β → α} (he : Function.Injective e)
    (p : α → ℝ) :
    ∀ (U : Finset α) (V : Finset β) (g : Finset β → ℝ), (∀ b ∈ V, e b ∈ U) →
      indepExp U p (fun S => g (V.filter fun b => e b ∈ S)) =
        indepExp V (fun b => p (e b)) g := by
  intro U
  induction U using Finset.induction_on with
  | empty =>
    intro V g hV
    have hV0 : V = ∅ := Finset.eq_empty_of_forall_notMem fun b hb => by simpa using hV b hb
    subst hV0
    simp [indepExp]
  | insert a U ha ih =>
    intro V g hV
    rw [indepExp_insert ha]
    by_cases hb : ∃ b ∈ V, e b = a
    · obtain ⟨b, hbV, hba⟩ := hb
      have hV' : ∀ b' ∈ V.erase b, e b' ∈ U := by
        intro b' hb'
        obtain ⟨hne, hb'V⟩ := Finset.mem_erase.mp hb'
        rcases Finset.mem_insert.mp (hV b' hb'V) with h | h
        · exact absurd (he (h.trans hba.symm)) hne
        · exact h
      have h1 : indepExp U p (fun S => g (V.filter fun b => e b ∈ S)) =
          indepExp U p (fun S => g ((V.erase b).filter fun b => e b ∈ S)) := by
        apply indepExp_congr
        intro S hS
        congr 1
        ext b'
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨⟨fun h => ?_, h1⟩, h2⟩
          subst h
          exact ha (hba ▸ hS h2)
        · rintro ⟨⟨_, h1⟩, h2⟩
          exact ⟨h1, h2⟩
      have h2 : indepExp U p (fun S => g (V.filter fun b => e b ∈ insert a S)) =
          indepExp U p (fun S => g (insert b ((V.erase b).filter fun b => e b ∈ S))) := by
        apply indepExp_congr
        intro S _
        congr 1
        ext b'
        simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨h1, h2 | h2⟩
          · exact Or.inl (he (h2.trans hba.symm))
          · by_cases hbb : b' = b
            · exact Or.inl hbb
            · exact Or.inr ⟨⟨hbb, h1⟩, h2⟩
        · rintro (h | ⟨⟨_, h1⟩, h2⟩)
          · subst h
            exact ⟨hbV, Or.inl hba⟩
          · exact ⟨h1, Or.inr h2⟩
      rw [h1, h2, ih (V.erase b) g hV', ih (V.erase b) (fun X => g (insert b X)) hV', ← hba]
      conv_rhs => rw [← Finset.insert_erase hbV, indepExp_insert (Finset.notMem_erase b V)]
    · simp only [not_exists, not_and] at hb
      have hV' : ∀ b ∈ V, e b ∈ U := by
        intro b hbV
        rcases Finset.mem_insert.mp (hV b hbV) with h | h
        · exact absurd h (hb b hbV)
        · exact h
      have h2 : indepExp U p (fun S => g (V.filter fun b => e b ∈ insert a S)) =
          indepExp U p (fun S => g (V.filter fun b => e b ∈ S)) := by
        apply indepExp_congr
        intro S _
        congr 1
        ext b'
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2 | h2⟩
          · exact absurd h2 (hb b' h1)
          · exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, Or.inr h2⟩
      rw [h2, ih V g hV']
      ring

/-- Restriction: a function of `S ∩ W` only needs the coins in `U ∩ W`. -/
theorem indepExp_inter (U W : Finset α) (p : α → ℝ) (g : Finset α → ℝ) :
    indepExp U p (fun S => g (S ∩ W)) = indepExp (U ∩ W) p g := by
  have h := indepExp_comap (e := id) Function.injective_id p U (U ∩ W) g
    (fun b hb => (Finset.mem_inter.mp hb).1)
  rw [show indepExp (U ∩ W) p g = indepExp (U ∩ W) (fun b => p (id b)) g from rfl, ← h]
  apply indepExp_congr
  intro S hS
  congr 1
  ext a
  simp only [Finset.mem_inter, Finset.mem_filter, id]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨hS h1, h2⟩, h1⟩
  · rintro ⟨⟨_, h2⟩, h1⟩
    exact ⟨h1, h2⟩

/-- If `h` does not depend on coin `a`, then `a` is independent of it:
`E[h · 1{a ∈ S}] = p a · E[h]`. -/
theorem indepExp_mul_mem_of_blind {U : Finset α} {a : α} (ha : a ∈ U) (p : α → ℝ)
    (h : Finset α → ℝ) (hblind : ∀ S, h (insert a S) = h (S.erase a)) :
    indepExp U p (fun S => h S * if a ∈ S then 1 else 0) = p a * indepExp U p h := by
  have hU := Finset.insert_erase ha
  have hnot := Finset.notMem_erase a U
  rw [← hU, indepExp_insert hnot, indepExp_insert hnot]
  have h1 : indepExp (U.erase a) p (fun S => h S * if a ∈ S then 1 else 0) = 0 := by
    rw [indepExp_congr (h := fun _ => 0), indepExp_const]
    intro S hS
    have : a ∉ S := fun h' => hnot (hS h')
    simp [this]
  have h2 : indepExp (U.erase a) p
      (fun S => h (insert a S) * if a ∈ insert a S then 1 else 0) =
      indepExp (U.erase a) p (fun S => h (insert a S)) := by
    apply indepExp_congr
    intro S _
    simp
  have h3 : indepExp (U.erase a) p h = indepExp (U.erase a) p (fun S => h (insert a S)) := by
    apply indepExp_congr
    intro S hS
    have : a ∉ S := fun h' => hnot (hS h')
    rw [hblind, Finset.erase_eq_of_notMem this]
  rw [h1, h2, h3]
  ring

/-! ### Splitting a random set across periods -/

/-- **Splitting lemma.** Let each `a ∈ U` be in the random set `L` with probability `q a`,
and let `y i a ≥ 0` with `∑_i y i a ≤ q a`. Suppose `f` is monotone and
`f X ≥ ∑_i g i (L i)` whenever the `L i` are disjoint subsets of `X`. Then
`E_q[f] ≥ ∑_i E_{y i}[g i]`.

Think of assigning each `a ∈ L` to part `i` with probability `y i a / q a`: part `i` is then
an independent random set with marginals `y i`. The proof inducts on `U` instead of building
this assignment. -/
theorem indepExp_split_le {ι : Type*} [DecidableEq ι] (P : Finset ι) (q : α → ℝ)
    (y : ι → α → ℝ) :
    ∀ (U : Finset α), (∀ a ∈ U, 0 ≤ q a ∧ q a ≤ 1) → (∀ i ∈ P, ∀ a ∈ U, 0 ≤ y i a) →
      (∀ a ∈ U, ∑ i ∈ P, y i a ≤ q a) →
      ∀ (f : Finset α → ℝ) (g : ι → Finset α → ℝ),
        (∀ X Y, X ⊆ Y → Y ⊆ U → f X ≤ f Y) →
        (∀ (L : ι → Finset α) (X : Finset α), X ⊆ U → (∀ i ∈ P, L i ⊆ X) →
          (∀ i ∈ P, ∀ j ∈ P, i ≠ j → Disjoint (L i) (L j)) → ∑ i ∈ P, g i (L i) ≤ f X) →
        ∑ i ∈ P, indepExp U (y i) (g i) ≤ indepExp U q f := by
  intro U
  induction U using Finset.induction_on with
  | empty =>
    intro _ _ _ f g _ hfg
    simp only [indepExp, Finset.powerset_empty, Finset.sum_singleton, Finset.prod_empty,
      Finset.sdiff_self, one_mul]
    exact hfg (fun _ => ∅) ∅ (subset_refl _) (fun _ _ => subset_refl _)
      (fun _ _ _ _ _ => Finset.disjoint_empty_left _)
  | insert a U ha ih =>
    intro hq hy0 hyq f g hf hfg
    have hqU : ∀ b ∈ U, 0 ≤ q b ∧ q b ≤ 1 := fun b hb => hq b (Finset.mem_insert_of_mem hb)
    have hy0U : ∀ i ∈ P, ∀ b ∈ U, 0 ≤ y i b :=
      fun i hi b hb => hy0 i hi b (Finset.mem_insert_of_mem hb)
    have hyqU : ∀ b ∈ U, ∑ i ∈ P, y i b ≤ q b := fun b hb => hyq b (Finset.mem_insert_of_mem hb)
    have hya : ∀ i ∈ P, 0 ≤ y i a := fun i hi => hy0 i hi a (Finset.mem_insert_self a U)
    have hqa := hq a (Finset.mem_insert_self a U)
    have hYa := hyq a (Finset.mem_insert_self a U)
    -- The two conditional expectations of `f`.
    set A0 := indepExp U q f with hA0
    set B0 := indepExp U q (fun S => f (insert a S)) with hB0
    have hAB : A0 ≤ B0 := indepExp_mono hqU fun S hS =>
      hf S (insert a S) (Finset.subset_insert a S) (Finset.insert_subset
        (Finset.mem_insert_self a U) (hS.trans (Finset.subset_insert a U)))
    -- Induction hypothesis: `a` absent.
    have hIH1 : ∑ i ∈ P, indepExp U (y i) (g i) ≤ A0 :=
      ih hqU hy0U hyqU f g (fun X Y hXY hY => hf X Y hXY (hY.trans (Finset.subset_insert a U)))
        (fun L X hX hLX hdisj => hfg L X (hX.trans (Finset.subset_insert a U)) hLX hdisj)
    -- Induction hypothesis: `a` present and assigned to part `u`.
    have hIH2 : ∀ u ∈ P, ∑ i ∈ P, indepExp U (y i) (g i) - indepExp U (y u) (g u) +
        indepExp U (y u) (fun S => g u (insert a S)) ≤ B0 := by
      intro u hu
      have key := ih hqU hy0U hyqU (fun S => f (insert a S))
        (Function.update g u (fun S => g u (insert a S)))
        (fun X Y hXY hY => hf _ _ (Finset.insert_subset_insert a hXY)
          (Finset.insert_subset_insert a hY))
        (by
          intro L X hX hLX hdisj
          have hsum : ∑ i ∈ P, Function.update g u (fun S => g u (insert a S)) i (L i) =
              ∑ i ∈ P, g i (Function.update L u (insert a (L u)) i) := by
            apply Finset.sum_congr rfl
            intro i _
            by_cases hiu : i = u
            · subst hiu; simp
            · simp [Function.update_of_ne hiu]
          rw [hsum]
          have haL : ∀ i ∈ P, a ∉ L i := fun i hi h => ha (hX (hLX i hi h))
          apply hfg _ (insert a X) (Finset.insert_subset_insert a hX)
          · intro i hi
            by_cases hiu : i = u
            · subst hiu
              simp only [Function.update_self]
              exact Finset.insert_subset_insert a (hLX i hi)
            · simp only [Function.update_of_ne hiu]
              exact (hLX i hi).trans (Finset.subset_insert a X)
          · intro i hi j hj hij
            by_cases hiu : i = u
            · subst hiu
              have hju : j ≠ i := fun h => hij h.symm
              simp only [Function.update_self, Function.update_of_ne hju]
              exact Finset.disjoint_insert_left.mpr ⟨haL j hj, hdisj i hi j hj hij⟩
            · by_cases hju : j = u
              · subst hju
                simp only [Function.update_self, Function.update_of_ne hiu]
                exact Finset.disjoint_insert_right.mpr ⟨haL i hi, hdisj i hi j hj hij⟩
              · simp only [Function.update_of_ne hiu, Function.update_of_ne hju]
                exact hdisj i hi j hj hij)
      have hupd : ∑ i ∈ P, indepExp U (y i) (Function.update g u (fun S => g u (insert a S)) i) =
          ∑ i ∈ P, indepExp U (y i) (g i) - indepExp U (y u) (g u) +
            indepExp U (y u) (fun S => g u (insert a S)) := by
        rw [← Finset.add_sum_erase P _ hu, ← Finset.add_sum_erase P _ hu]
        simp only [Function.update_self]
        have : ∑ x ∈ P.erase u, indepExp U (y x) (Function.update g u
            (fun S => g u (insert a S)) x) = ∑ x ∈ P.erase u, indepExp U (y x) (g x) :=
          Finset.sum_congr rfl fun x hx => by
            rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
        rw [this]
        ring
      rw [← hupd]
      exact key
    -- Combine.
    rw [indepExp_insert ha]
    have hrhs : ∑ i ∈ P, indepExp (insert a U) (y i) (g i) =
        ∑ i ∈ P, indepExp U (y i) (g i) + ∑ i ∈ P, y i a *
          (indepExp U (y i) (fun S => g i (insert a S)) - indepExp U (y i) (g i)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [indepExp_insert ha]
      ring
    rw [hrhs]
    set Sg := ∑ i ∈ P, indepExp U (y i) (g i)
    have hsum2 : ∑ i ∈ P, y i a * (Sg - indepExp U (y i) (g i) +
        indepExp U (y i) (fun S => g i (insert a S))) ≤ ∑ i ∈ P, y i a * B0 :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hIH2 i hi) (hya i hi)
    have hexp : ∑ i ∈ P, y i a * (Sg - indepExp U (y i) (g i) +
        indepExp U (y i) (fun S => g i (insert a S))) =
        (∑ i ∈ P, y i a) * Sg + ∑ i ∈ P, y i a *
          (indepExp U (y i) (fun S => g i (insert a S)) - indepExp U (y i) (g i)) := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hexp, ← Finset.sum_mul] at hsum2
    set Ya := ∑ i ∈ P, y i a
    have h1 : (1 - Ya) * Sg ≤ (1 - Ya) * A0 :=
      mul_le_mul_of_nonneg_left hIH1 (by linarith [hqa.2])
    have h2 : 0 ≤ (q a - Ya) * (B0 - A0) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

/-! ### Best selections and a counting criterion -/

/-- `sel k B` is a best set of at most `k` profiles from `B` for the weights `w`: the
responder's "best available profiles first", with any tie-breaking. -/
def IsTopSel (w : α → ℝ) (sel : ℕ → Finset α → Finset α) : Prop :=
  ∀ k B, sel k B ⊆ B ∧ (sel k B).card ≤ k ∧ ∑ a ∈ sel k B, w a = topK w k B

omit [DecidableEq α] in
/-- Best selections exist. -/
theorem exists_topSel (w : α → ℝ) : ∃ sel, IsTopSel w sel := by
  choose sel h1 h2 h3 using fun (k : ℕ) (B : Finset α) => exists_topK_eq w k B
  exact ⟨sel, fun k B => ⟨h1 k B, h2 k B, (h3 k B).symm⟩⟩

/-- A best set `S` of at most `k` profiles from `B` contains as many profiles of weight at
least `θ > 0` as possible: `min(k, #{b ∈ B : w b ≥ θ})`. Otherwise adding or swapping in a
missing one would beat it. -/
theorem topSel_count {w : α → ℝ} {k : ℕ} {B S : Finset α} (hSB : S ⊆ B) (hSk : S.card ≤ k)
    (hS : ∑ a ∈ S, w a = topK w k B) {θ : ℝ} (hθ : 0 < θ) :
    min k (B.filter fun b => θ ≤ w b).card ≤ (S.filter fun b => θ ≤ w b).card := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 : (S.filter fun b => θ ≤ w b).card < (B.filter fun b => θ ≤ w b).card :=
    lt_of_lt_of_le hlt (min_le_right _ _)
  obtain ⟨b, hbB, hbS⟩ := Finset.exists_mem_notMem_of_card_lt_card h1
  rw [Finset.mem_filter] at hbB
  have hbS' : b ∉ S := fun h => hbS (Finset.mem_filter.mpr ⟨h, hbB.2⟩)
  rcases Nat.lt_or_ge S.card k with hlt' | hge
  · -- A free slot: add `b`.
    have hle := sum_le_topK (w := w) (K := k) (Finset.insert_subset hbB.1 hSB)
      ((Finset.card_insert_le b S).trans (by omega))
    rw [Finset.sum_insert hbS', hS] at hle
    linarith
  · -- No free slot: some shown profile has weight below `θ`; swap it for `b`.
    have h2 : (S.filter fun b => θ ≤ w b).card < S.card :=
      lt_of_lt_of_le (lt_of_lt_of_le hlt (min_le_left _ _)) hge
    obtain ⟨a, haS, haW⟩ := Finset.exists_mem_notMem_of_card_lt_card h2
    have hwa : w a < θ := by
      by_contra h
      exact haW (Finset.mem_filter.mpr ⟨haS, not_lt.mp h⟩)
    have hbE : b ∉ S.erase a := fun h => hbS' (Finset.mem_of_mem_erase h)
    have hle := sum_le_topK (w := w) (K := k) (B := B) (S := insert b (S.erase a))
      (Finset.insert_subset hbB.1 ((Finset.erase_subset a S).trans hSB))
      (by rw [Finset.card_insert_of_notMem hbE, Finset.card_erase_of_mem haS]; omega)
    rw [Finset.sum_insert hbE, ← hS, ← Finset.add_sum_erase S w haS] at hle
    linarith [hbB.2]

/-- **Counting criterion.** With non-negative weights, if `A` has at least as many elements of
weight `≥ θ` as `B` for every `θ > 0`, then `A` has at least the total weight of `B`. -/
theorem sum_le_sum_of_count_le {w : α → ℝ} (hw : ∀ a, 0 ≤ w a) (B : Finset α) :
    ∀ A : Finset α, (∀ θ : ℝ, 0 < θ →
      (B.filter fun b => θ ≤ w b).card ≤ (A.filter fun a => θ ≤ w a).card) →
      ∑ b ∈ B, w b ≤ ∑ a ∈ A, w a := by
  induction B using Finset.strongInduction with
  | H B ih =>
  intro A hcount
  rcases B.eq_empty_or_nonempty with rfl | hne
  · simpa using Finset.sum_nonneg fun a _ => hw a
  obtain ⟨b, hbB, hbmax⟩ := Finset.exists_max_image B w hne
  rcases (hw b).lt_or_eq with hpos | hzero
  · -- `A` has an element `a` at least as heavy as `b`; match the two and recurse.
    have hB1 : 0 < (B.filter fun x => w b ≤ w x).card :=
      Finset.card_pos.mpr ⟨b, Finset.mem_filter.mpr ⟨hbB, le_rfl⟩⟩
    have hA1 := lt_of_lt_of_le hB1 (hcount (w b) hpos)
    obtain ⟨a', ha'⟩ := Finset.card_pos.mp hA1
    rw [Finset.mem_filter] at ha'
    obtain ⟨a, haA, hamax⟩ := Finset.exists_max_image A w ⟨a', ha'.1⟩
    have hab : w b ≤ w a := ha'.2.trans (hamax a' ha'.1)
    have hrec := ih (B.erase b) (Finset.erase_ssubset hbB) (A.erase a) (by
      intro θ hθ
      rw [Finset.filter_erase, Finset.filter_erase]
      by_cases hθb : θ ≤ w b
      · have hbF : b ∈ B.filter fun x => θ ≤ w x := Finset.mem_filter.mpr ⟨hbB, hθb⟩
        have haF : a ∈ A.filter fun x => θ ≤ w x := Finset.mem_filter.mpr ⟨haA, hθb.trans hab⟩
        rw [Finset.card_erase_of_mem hbF, Finset.card_erase_of_mem haF]
        have := hcount θ hθ
        omega
      · have : (B.filter fun x => θ ≤ w x) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro x hx h
          exact hθb (h.trans (hbmax x hx))
        rw [this]
        simp)
    rw [← Finset.add_sum_erase B w hbB, ← Finset.add_sum_erase A w haA]
    linarith
  · -- Every weight in `B` is zero.
    have : ∑ x ∈ B, w x ≤ ∑ x ∈ B, (0 : ℝ) :=
      Finset.sum_le_sum fun x hx => (hbmax x hx).trans hzero.symm.le
    simp only [Finset.sum_const_zero] at this
    linarith [Finset.sum_nonneg fun a (_ : a ∈ A) => hw a]

/-! ### Greedy responses and their optimality -/

/-- Profiles greedy has answered before period `n`. In period `n` it answers
`sel (c n) B`, where `B` holds the profiles waiting in the backlog: they liked the responder
(`L`), arrived before period `n` (`A n`), and are not yet answered. -/
def greedyAns (sel : ℕ → Finset α → Finset α) (c : ℕ → ℕ) (A : ℕ → Finset α)
    (L : Finset α) : ℕ → Finset α
  | 0 => ∅
  | n + 1 => greedyAns sel c A L n ∪ sel (c n) ((L ∩ A n) \ greedyAns sel c A L n)

/-- Profiles greedy answers in period `n`. -/
def greedyPick (sel : ℕ → Finset α → Finset α) (c : ℕ → ℕ) (A : ℕ → Finset α)
    (L : Finset α) (n : ℕ) : Finset α :=
  sel (c n) ((L ∩ A n) \ greedyAns sel c A L n)

/-- Greedy's total response value over periods `0, …, T-1`. -/
noncomputable def greedyValue (w : α → ℝ) (sel : ℕ → Finset α → Finset α) (c : ℕ → ℕ)
    (A : ℕ → Finset α) (T : ℕ) (L : Finset α) : ℝ :=
  ∑ n ∈ range T, ∑ a ∈ greedyPick sel c A L n, w a

/-- A response plan for one responder, possibly clairvoyant: in period `n < T` it answers
`P n`, at most `c n` profiles from the backlog, each profile at most once. -/
def IsRespPlan (c : ℕ → ℕ) (A : ℕ → Finset α) (T : ℕ) (L : Finset α) (P : ℕ → Finset α) :
    Prop :=
  (∀ n < T, P n ⊆ L ∩ A n) ∧ (∀ n < T, (P n).card ≤ c n) ∧
    ∀ m < T, ∀ n < T, m ≠ n → Disjoint (P m) (P n)

section Greedy

variable {sel : ℕ → Finset α → Finset α} {c : ℕ → ℕ} {A : ℕ → Finset α} {L : Finset α}

theorem greedyAns_succ (n : ℕ) :
    greedyAns sel c A L (n + 1) = greedyAns sel c A L n ∪ greedyPick sel c A L n := rfl

theorem greedyPick_subset (hsel : ∀ k B, sel k B ⊆ B) (n : ℕ) :
    greedyPick sel c A L n ⊆ (L ∩ A n) \ greedyAns sel c A L n :=
  hsel _ _

theorem greedyAns_subset (hsel : ∀ k B, sel k B ⊆ B) (hA : Monotone A) :
    ∀ n, greedyAns sel c A L n ⊆ L ∩ A n
  | 0 => Finset.empty_subset _
  | n + 1 => by
    have hn : L ∩ A n ⊆ L ∩ A (n + 1) := Finset.inter_subset_inter_left (hA (Nat.le_succ n))
    rw [greedyAns_succ]
    exact Finset.union_subset ((greedyAns_subset hsel hA n).trans hn)
      ((greedyPick_subset hsel n).trans (Finset.sdiff_subset.trans hn))

theorem greedyAns_mono {m n : ℕ} (h : m ≤ n) :
    greedyAns sel c A L m ⊆ greedyAns sel c A L n := by
  induction h with
  | refl => exact subset_refl _
  | step _ ih => exact ih.trans Finset.subset_union_left

theorem greedyPick_subset_ans {m n : ℕ} (h : m < n) :
    greedyPick sel c A L m ⊆ greedyAns sel c A L n :=
  (Finset.subset_union_right (s₁ := greedyAns sel c A L m)).trans (greedyAns_mono h)

theorem greedyPick_disjoint (hsel : ∀ k B, sel k B ⊆ B) {m n : ℕ} (h : m ≠ n) :
    Disjoint (greedyPick sel c A L m) (greedyPick sel c A L n) := by
  have key : ∀ m n, m < n → Disjoint (greedyPick sel c A L m) (greedyPick sel c A L n) := by
    intro m n hmn
    apply Finset.disjoint_left.mpr
    intro a ham han
    have h1 := greedyPick_subset_ans hmn ham
    have h2 := greedyPick_subset hsel n han
    exact (Finset.mem_sdiff.mp h2).2 h1
  rcases Nat.lt_or_gt_of_ne h with h' | h'
  · exact key m n h'
  · exact (key n m h').symm

theorem greedyAns_eq_biUnion :
    ∀ n, greedyAns sel c A L n = (range n).biUnion (greedyPick sel c A L)
  | 0 => by simp [greedyAns]
  | n + 1 => by
    rw [greedyAns_succ, greedyAns_eq_biUnion n, Finset.range_add_one, Finset.biUnion_insert,
      Finset.union_comm]

/-- Greedy is a response plan. -/
theorem greedy_isRespPlan {w : α → ℝ} (hsel : IsTopSel w sel) (T : ℕ) :
    IsRespPlan c A T L (greedyPick sel c A L) :=
  ⟨fun n _ => (greedyPick_subset (fun k B => (hsel k B).1) n).trans Finset.sdiff_subset,
    fun _ _ => (hsel _ _).2.1,
    fun _ _ _ _ h => greedyPick_disjoint (fun k B => (hsel k B).1) h⟩

/-- Greedy only looks at profiles that arrived by period `t`. -/
theorem greedyAns_inter (hA : Monotone A) (t : ℕ) :
    ∀ n ≤ t, greedyAns sel c A (L ∩ A t) n = greedyAns sel c A L n
  | 0, _ => rfl
  | n + 1, h => by
    have hn : L ∩ A t ∩ A n = L ∩ A n := by
      rw [Finset.inter_assoc, Finset.inter_eq_right.mpr (hA (by omega : n ≤ t))]
    simp only [greedyAns]
    rw [greedyAns_inter hA t n (by omega), hn]

theorem greedyPick_inter (hA : Monotone A) (t : ℕ) :
    greedyPick sel c A (L ∩ A t) t = greedyPick sel c A L t := by
  unfold greedyPick
  rw [greedyAns_inter hA t t le_rfl, Finset.inter_assoc, Finset.inter_self]

/-- Counting by weight threshold: `#{x ∈ X \ Y : w x ≥ θ} = #{x ∈ X : …} - #{x ∈ Y : …}`
for `Y ⊆ X`. -/
theorem card_filter_sdiff_add {p : α → Prop} [DecidablePred p] {X Y : Finset α} (h : Y ⊆ X) :
    ((X \ Y).filter p).card + (Y.filter p).card = (X.filter p).card := by
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter Finset.sdiff_disjoint),
    ← Finset.filter_union, Finset.sdiff_union_of_subset h]

/-- **Greedy is optimal on every sample path**, even against a clairvoyant plan. For every
`θ > 0`, by induction over periods, greedy has answered at least as many profiles of weight
`≥ θ` as the plan. The counting criterion then compares the total weights. -/
theorem greedy_optimal {w : α → ℝ} (hw : ∀ a, 0 ≤ w a) (hsel : IsTopSel w sel)
    (hA : Monotone A) {T : ℕ} {P : ℕ → Finset α} (hP : IsRespPlan c A T L P) :
    ∑ n ∈ range T, ∑ a ∈ P n, w a ≤ greedyValue w sel c A T L := by
  have hsub : ∀ k B, sel k B ⊆ B := fun k B => (hsel k B).1
  have hPd : Set.PairwiseDisjoint (↑(range T)) P := by
    intro m hm n hn hmn
    exact hP.2.2 m (Finset.mem_range.mp hm) n (Finset.mem_range.mp hn) hmn
  have hGd : Set.PairwiseDisjoint (↑(range T)) (greedyPick sel c A L) :=
    fun m _ n _ hmn => greedyPick_disjoint hsub hmn
  unfold greedyValue
  rw [← Finset.sum_biUnion hPd, ← Finset.sum_biUnion hGd, ← greedyAns_eq_biUnion]
  apply sum_le_sum_of_count_le hw
  intro θ hθ
  -- The counting invariant, period by period.
  have inv : ∀ n ≤ T, (((range n).biUnion P).filter fun x => θ ≤ w x).card ≤
      ((greedyAns sel c A L n).filter fun x => θ ≤ w x).card := by
    intro n
    induction n with
    | zero => intro _; simp [greedyAns]
    | succ n ih =>
      intro hn
      have hnT : n < T := by omega
      have ih := ih (by omega)
      -- The plan.
      have hPU : ((range n).biUnion P) ⊆ L ∩ A n := by
        intro x hx
        obtain ⟨m, hm, hxm⟩ := Finset.mem_biUnion.mp hx
        have hm' := Finset.mem_range.mp hm
        exact Finset.inter_subset_inter_left (hA hm'.le) ((hP.1 m (by omega)) hxm)
      have hPdisj : Disjoint (P n) ((range n).biUnion P) := by
        apply (Finset.disjoint_biUnion_right _ _ _).mpr
        intro m hm
        exact hP.2.2 n hnT m (by have := Finset.mem_range.mp hm; omega)
          (by have := Finset.mem_range.mp hm; omega)
      have hPstep : (((range (n + 1)).biUnion P).filter fun x => θ ≤ w x).card =
          ((P n).filter fun x => θ ≤ w x).card +
            (((range n).biUnion P).filter fun x => θ ≤ w x).card := by
        rw [Finset.range_add_one, Finset.biUnion_insert, Finset.filter_union,
          Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hPdisj)]
      have hPc : ((P n).filter fun x => θ ≤ w x).card ≤ c n :=
        (Finset.card_filter_le _ _).trans (hP.2.1 n hnT)
      have hPN : ((P n).filter fun x => θ ≤ w x).card +
          (((range n).biUnion P).filter fun x => θ ≤ w x).card ≤
          ((L ∩ A n).filter fun x => θ ≤ w x).card := by
        rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hPdisj),
          ← Finset.filter_union]
        exact Finset.card_le_card (Finset.filter_subset_filter _
          (Finset.union_subset (hP.1 n hnT) hPU))
      -- Greedy.
      have hGsub := greedyAns_subset (L := L) (c := c) hsub hA n
      have hGstep : ((greedyAns sel c A L (n + 1)).filter fun x => θ ≤ w x).card =
          ((greedyAns sel c A L n).filter fun x => θ ≤ w x).card +
            ((greedyPick sel c A L n).filter fun x => θ ≤ w x).card := by
        have hd : Disjoint (greedyAns sel c A L n) (greedyPick sel c A L n) := by
          apply Finset.disjoint_right.mpr
          intro x hx
          exact (Finset.mem_sdiff.mp (greedyPick_subset hsub n hx)).2
        rw [greedyAns_succ, Finset.filter_union,
          Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hd)]
      have hGpick := topSel_count (hsel (c n) ((L ∩ A n) \ greedyAns sel c A L n)).1
        (hsel _ _).2.1 (hsel _ _).2.2 hθ
      have hrest := card_filter_sdiff_add (p := fun x => θ ≤ w x) hGsub
      have hGN : ((greedyAns sel c A L n).filter fun x => θ ≤ w x).card ≤
          ((L ∩ A n).filter fun x => θ ≤ w x).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ hGsub)
      unfold greedyPick at hGstep
      rw [hPstep, hGstep]
      omega
  exact inv T le_rfl

end Greedy

/-! ### The correlation gap for greedy responses -/

/-- **Correlation gap for greedy backlog responses (one responder).** Let `y n a` be a
fractional response plan: non-negative, zero unless `a` arrived before period `n`, at most
`q a` in total for each profile, and at most `c n` in total in each period. Then greedy's
expected value is at least `(1 - 1/e) ∑_n ∑_a w a · y n a`.

This is steps 2–5 of the Rel_τ proof sketch in the vault note, for one user. -/
theorem greedy_correlation_gap {w : α → ℝ} (hw : ∀ a, 0 ≤ w a)
    {sel : ℕ → Finset α → Finset α} (hsel : IsTopSel w sel) {c : ℕ → ℕ} {A : ℕ → Finset α}
    (hA : Monotone A) (T : ℕ) (U : Finset α) (q : α → ℝ)
    (hq : ∀ a ∈ U, 0 ≤ q a ∧ q a ≤ 1) (y : ℕ → α → ℝ) (hy0 : ∀ n a, 0 ≤ y n a)
    (hyA : ∀ n a, a ∉ A n → y n a = 0) (hyq : ∀ a ∈ U, ∑ n ∈ range T, y n a ≤ q a)
    (hyc : ∀ n < T, ∑ a ∈ U, y n a ≤ c n) :
    (1 - Real.exp (-1)) * ∑ n ∈ range T, ∑ a ∈ U, w a * y n a ≤
      indepExp U q (greedyValue w sel c A T) := by
  have hsub : ∀ k B, sel k B ⊆ B := fun k B => (hsel k B).1
  -- Splitting: greedy beats the sum of per-period top-`c n` values.
  have hsplit := indepExp_split_le (range T) q y U hq (fun n _ a _ => hy0 n a) hyq
    (greedyValue w sel c A T) (fun n X => topK w (c n) (X ∩ A n))
    (by
      intro X Y hXY _
      have hplan : IsRespPlan c A T Y (greedyPick sel c A X) :=
        ⟨fun n hn => ((greedy_isRespPlan (L := X) hsel T).1 n hn).trans
            (Finset.inter_subset_inter_right hXY),
          (greedy_isRespPlan (L := X) hsel T).2.1,
          (greedy_isRespPlan (L := X) hsel T).2.2⟩
      exact greedy_optimal hw hsel hA hplan)
    (by
      intro Lf X _ hLX hdisj
      choose Q hQsub hQcard hQeq using fun n => exists_topK_eq w (c n) (Lf n ∩ A n)
      have hplan : IsRespPlan c A T X Q := by
        refine ⟨fun n hn => (hQsub n).trans (Finset.inter_subset_inter_right
            (hLX n (Finset.mem_range.mpr hn))), fun n _ => hQcard n, ?_⟩
        intro m hm n hn hmn
        exact Finset.disjoint_of_subset_left ((hQsub m).trans Finset.inter_subset_left)
          (Finset.disjoint_of_subset_right ((hQsub n).trans Finset.inter_subset_left)
            (hdisj m (Finset.mem_range.mpr hm) n (Finset.mem_range.mpr hn) hmn))
      calc ∑ n ∈ range T, topK w (c n) (Lf n ∩ A n)
          = ∑ n ∈ range T, ∑ a ∈ Q n, w a := Finset.sum_congr rfl fun n _ => hQeq n
        _ ≤ _ := greedy_optimal hw hsel hA hplan)
  -- Per period: the weighted top-K correlation gap.
  have hper : ∀ n ∈ range T, (1 - Real.exp (-1)) * ∑ a ∈ U, w a * y n a ≤
      indepExp U (y n) (fun X => topK w (c n) (X ∩ A n)) := by
    intro n hn
    have hnT := Finset.mem_range.mp hn
    rw [indepExp_inter]
    have hy1 : ∀ a ∈ U ∩ A n, 0 ≤ y n a ∧ y n a ≤ 1 := by
      intro a ha
      have haU := (Finset.mem_inter.mp ha).1
      refine ⟨hy0 n a, ?_⟩
      calc y n a ≤ ∑ m ∈ range T, y m a :=
            Finset.single_le_sum (fun m _ => hy0 m a) hn
        _ ≤ q a := hyq a haU
        _ ≤ 1 := (hq a haU).2
    have hgap := topK_correlation_gap (U ∩ A n) (y n) w (y n) hy1 (fun a _ => hw a) (c n)
      (fun a ha => ⟨(hy1 a ha).1, le_rfl⟩)
      ((Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left
        (fun a _ _ => hy0 n a)).trans (hyc n hnT))
    have hsum : ∑ a ∈ U ∩ A n, w a * y n a = ∑ a ∈ U, w a * y n a := by
      apply Finset.sum_subset Finset.inter_subset_left
      intro a haU ha
      have : a ∉ A n := fun h => ha (Finset.mem_inter.mpr ⟨haU, h⟩)
      rw [hyA n a this, mul_zero]
    rw [← hsum]
    exact hgap
  calc (1 - Real.exp (-1)) * ∑ n ∈ range T, ∑ a ∈ U, w a * y n a
      = ∑ n ∈ range T, (1 - Real.exp (-1)) * ∑ a ∈ U, w a * y n a := Finset.mul_sum _ _ _
    _ ≤ ∑ n ∈ range T, indepExp U (y n) (fun X => topK w (c n) (X ∩ A n)) :=
        Finset.sum_le_sum hper
    _ ≤ _ := hsplit

end DatingAlgo
