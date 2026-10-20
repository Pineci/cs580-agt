import DatingAlgo.Basic

/-!
# Expectations over independent coin flips

Tools for `indepExp U p g`, the expectation of `g S` when each `i ∈ U` is put in `S`
independently with probability `p i` (defined in `DatingAlgo.Basic`). In the paper's
two-period model this is the distribution of who liked whom in period 1.

The results are standard facts about product distributions, written as finite sums:
- linearity;
- marginals;
- the probability generating function of `|S|`;
- conditioning on one element;
- monotonicity in the ground set;
- relabelling and restricting the coins, and independence from one coin;
- the probability of an atom (all of `A` in, none of `B`).
-/

namespace DatingAlgo

open Finset

variable {α : Type*} [DecidableEq α]

/-- Expectation only depends on `g` on subsets of `U`. -/
theorem indepExp_congr {U : Finset α} {p : α → ℝ} {g h : Finset α → ℝ}
    (hgh : ∀ S ⊆ U, g S = h S) : indepExp U p g = indepExp U p h := by
  unfold indepExp
  exact Finset.sum_congr rfl fun S hS => by rw [hgh S (Finset.mem_powerset.mp hS)]

/-- Linearity: sums. -/
theorem indepExp_add (U : Finset α) (p : α → ℝ) (g h : Finset α → ℝ) :
    indepExp U p (fun S => g S + h S) = indepExp U p g + indepExp U p h := by
  unfold indepExp
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun S _ => mul_add _ _ _

/-- Linearity: scalar multiples. -/
theorem indepExp_const_mul (U : Finset α) (p : α → ℝ) (c : ℝ) (g : Finset α → ℝ) :
    indepExp U p (fun S => c * g S) = c * indepExp U p g := by
  unfold indepExp
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ => by ring

/-- Linearity: finite sums of functions. -/
theorem indepExp_sum {ι : Type*} (s : Finset ι) (U : Finset α) (p : α → ℝ)
    (g : ι → Finset α → ℝ) :
    indepExp U p (fun S => ∑ j ∈ s, g j S) = ∑ j ∈ s, indepExp U p (g j) := by
  unfold indepExp
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- The expectation of a constant is that constant. -/
theorem indepExp_const (U : Finset α) (p : α → ℝ) (c : ℝ) :
    indepExp U p (fun _ => c) = c := by
  have h := indepExp_const_mul U p c (fun _ => 1)
  simp only [mul_one] at h
  rw [h, indepExp_one, mul_one]

/-- Conditioning on whether `a` is included. -/
theorem indepExp_insert {U : Finset α} {a : α} (ha : a ∉ U) (p : α → ℝ)
    (g : Finset α → ℝ) :
    indepExp (insert a U) p g =
      (1 - p a) * indepExp U p g + p a * indepExp U p (fun S => g (insert a S)) := by
  unfold indepExp
  rw [Finset.sum_powerset_insert ha, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro S hS
    have haS : a ∉ S := fun h => ha (Finset.mem_powerset.mp hS h)
    rw [Finset.insert_sdiff_of_notMem _ haS,
      Finset.prod_insert (fun h => ha (Finset.mem_sdiff.mp h).1)]
    ring
  · apply Finset.sum_congr rfl
    intro S hS
    have haS : a ∉ S := fun h => ha (Finset.mem_powerset.mp hS h)
    rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem ha,
      Finset.prod_insert haS]
    ring

/-- Marginalizing out one element that `g` ignores. -/
theorem indepExp_insert_erase {U : Finset α} {a : α} (ha : a ∉ U) (p : α → ℝ)
    (g : Finset α → ℝ) :
    indepExp (insert a U) p (fun S => g (S.erase a)) = indepExp U p g := by
  rw [indepExp_insert ha]
  have h1 : indepExp U p (fun S => g (S.erase a)) = indepExp U p g :=
    indepExp_congr fun S hS => by rw [Finset.erase_eq_of_notMem (fun h => ha (hS h))]
  have h2 : indepExp U p (fun S => g ((insert a S).erase a)) = indepExp U p g :=
    indepExp_congr fun S hS => by rw [Finset.erase_insert (fun h => ha (hS h))]
  rw [h1, h2]
  ring

/-- Marginals: `i` is included with probability `p i`. -/
theorem indepExp_mem {U : Finset α} {i : α} (hi : i ∈ U) (p : α → ℝ) :
    indepExp U p (fun S => if i ∈ S then 1 else 0) = p i := by
  conv_lhs => rw [← Finset.insert_erase hi]
  rw [indepExp_insert (Finset.notMem_erase i U)]
  have h1 : indepExp (U.erase i) p (fun S => if i ∈ S then 1 else 0) = 0 := by
    rw [indepExp_congr (h := fun _ => 0), indepExp_const]
    intro S hS
    have : i ∉ S := fun h => Finset.notMem_erase i U (hS h)
    simp [this]
  have h2 : indepExp (U.erase i) p (fun S => if i ∈ insert i S then 1 else 0) = 1 := by
    simp only [Finset.mem_insert_self, ite_true]
    exact indepExp_one _ _
  rw [h1, h2]
  ring

/-- The expected size of `S` is `∑ p`. -/
theorem indepExp_card (U : Finset α) (p : α → ℝ) :
    indepExp U p (fun S => (S.card : ℝ)) = ∑ i ∈ U, p i := by
  have h : indepExp U p (fun S => (S.card : ℝ)) =
      indepExp U p (fun S => ∑ i ∈ U, if i ∈ S then (1 : ℝ) else 0) := by
    apply indepExp_congr
    intro S hS
    rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hS]
  rw [h, indepExp_sum]
  exact Finset.sum_congr rfl fun i hi => indepExp_mem hi p

/-- Probability generating function of `|S|`:
`E[t^|S|] = ∏ (1 - p i + p i t)`. -/
theorem indepExp_pow_card (U : Finset α) (p : α → ℝ) (t : ℝ) :
    indepExp U p (fun S => t ^ S.card) = ∏ i ∈ U, (1 - p i + p i * t) := by
  unfold indepExp
  rw [show (∏ i ∈ U, (1 - p i + p i * t)) = ∏ i ∈ U, (p i * t + (1 - p i)) from
    Finset.prod_congr rfl fun i _ => by ring]
  rw [Finset.prod_add]
  apply Finset.sum_congr rfl
  intro S _
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  ring

/-- Enlarging the ground set can only raise the expectation of a monotone function. -/
theorem indepExp_le_of_subset_of_monotone {V V' : Finset α} {p : α → ℝ}
    (hp : ∀ i ∈ V', 0 ≤ p i ∧ p i ≤ 1) (hVV' : V ⊆ V') {h : Finset α → ℝ}
    (hh : ∀ A B, A ⊆ B → B ⊆ V' → h A ≤ h B) :
    indepExp V p h ≤ indepExp V' p h := by
  have key : ∀ T : Finset α, T ⊆ V' \ V → indepExp V p h ≤ indepExp (V ∪ T) p h := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; simp
    | insert b T hbT ih =>
      intro hT
      have hb : b ∈ V' \ V := hT (Finset.mem_insert_self b T)
      have hT' : T ⊆ V' \ V := fun x hx => hT (Finset.mem_insert_of_mem hx)
      have hbVT : b ∉ V ∪ T := by
        rw [Finset.mem_union, not_or]
        exact ⟨(Finset.mem_sdiff.mp hb).2, hbT⟩
      have hVT : V ∪ T ⊆ V' := Finset.union_subset hVV' (hT'.trans Finset.sdiff_subset)
      have hpb := hp b (Finset.mem_sdiff.mp hb).1
      rw [Finset.union_insert, indepExp_insert hbVT]
      have hmono : indepExp (V ∪ T) p h ≤ indepExp (V ∪ T) p (fun S => h (insert b S)) := by
        apply indepExp_mono (fun i hi => hp i (hVT hi))
        intro S hS
        exact hh S (insert b S) (Finset.subset_insert b S)
          (Finset.insert_subset (Finset.mem_sdiff.mp hb).1 (hS.trans hVT))
      have hih := ih hT'
      nlinarith [mul_nonneg hpb.1 (sub_nonneg.mpr hmono)]
  have := key (V' \ V) (subset_refl _)
  rwa [Finset.union_sdiff_of_subset hVV'] at this

/-- Enlarging the ground set can only lower the expectation of an antitone function. -/
theorem indepExp_le_of_subset_of_antitone {V V' : Finset α} {p : α → ℝ}
    (hp : ∀ i ∈ V', 0 ≤ p i ∧ p i ≤ 1) (hVV' : V ⊆ V') {h : Finset α → ℝ}
    (hh : ∀ A B, A ⊆ B → B ⊆ V' → h B ≤ h A) :
    indepExp V' p h ≤ indepExp V p h := by
  have hneg := indepExp_le_of_subset_of_monotone hp hVV' (h := fun S => -h S)
    (fun A B hAB hB => neg_le_neg (hh A B hAB hB))
  have e : ∀ W, indepExp W p (fun S => -h S) = -indepExp W p h := by
    intro W
    have := indepExp_const_mul W p (-1) h
    simp only [neg_one_mul] at this
    exact this
  rw [e, e] at hneg
  linarith

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

/-! ### Atoms: all of `A` in, none of `B` -/

/-- The probability that every element of `A` is in `S` and no element of `B` is:
`∏_{a ∈ A} p a · ∏_{b ∈ B} (1 - p b)`, for disjoint `A, B ⊆ U`. -/
theorem indepExp_subset_disjoint (p : α → ℝ) {U A B : Finset α}
    (hA : A ⊆ U) (hB : B ⊆ U) (hAB : Disjoint A B) :
    indepExp U p (fun S => if A ⊆ S ∧ Disjoint B S then 1 else 0) =
      (∏ a ∈ A, p a) * ∏ b ∈ B, (1 - p b) := by
  set g : Finset α → ℝ := fun S => if A ⊆ S ∧ Disjoint B S then 1 else 0
  have hg : ∀ S, g S = g (S ∩ (A ∪ B)) := by
    intro S
    have : (A ⊆ S ∧ Disjoint B S) ↔ (A ⊆ S ∩ (A ∪ B) ∧ Disjoint B (S ∩ (A ∪ B))) := by
      simp only [subset_inter_iff, subset_union_left, and_true, disjoint_left, mem_inter,
        mem_union, not_and]
      exact and_congr_right fun _ => forall₂_congr fun b hb => ⟨fun h h' => absurd h' h,
        fun h h' => h h' (Or.inr hb)⟩
    simp only [g, if_congr this rfl rfl]
  rw [indepExp_congr (h := fun S => g (S ∩ (A ∪ B))) (fun S _ => hg S), indepExp_inter,
    inter_eq_right.mpr (union_subset hA hB)]
  unfold indepExp
  rw [sum_eq_single A]
  · simp only [g, subset_refl, hAB.symm, and_self, ite_true, mul_one, union_sdiff_cancel_left hAB]
  · intro S hS hne
    have hS' : ¬(A ⊆ S ∧ Disjoint B S) := by
      rintro ⟨hAS, hBS⟩
      refine hne (subset_antisymm (fun x hx => ?_) hAS)
      rcases mem_union.mp (mem_powerset.mp hS hx) with h | h
      · exact h
      · exact absurd hx (disjoint_left.mp hBS h)
    simp [g, hS']
  · intro h; exact absurd (mem_powerset.mpr subset_union_left) h

/-- Two distinct independent coins are both included with probability `p a * p b`. -/
theorem indepExp_mem_and {U : Finset α} {a b : α} (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b)
    (p : α → ℝ) :
    indepExp U p (fun S => if a ∈ S ∧ b ∈ S then 1 else 0) = p a * p b := by
  have := indepExp_subset_disjoint p (U := U) (A := {a, b}) (B := ∅)
    (insert_subset_iff.mpr ⟨ha, singleton_subset_iff.mpr hb⟩) (empty_subset _)
    (disjoint_empty_right _)
  simpa [insert_subset_iff, prod_pair hab] using this

end DatingAlgo
