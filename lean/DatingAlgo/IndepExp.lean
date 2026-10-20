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
- monotonicity in the ground set.
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

end DatingAlgo
