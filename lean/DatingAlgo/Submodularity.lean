import DatingAlgo.TwoPeriod

/-!
# Submodularity: Lemma 4.1 and Lemma C.2

Rios & Torrico use submodularity for their polynomial-time algorithms (Appendix E)
and to motivate the correlation-gap argument.

- **Lemma 4.1.** The optimal period-2 value `f(R)` is monotone and submodular in the
  set `R` of realized period-1 likes, as long as period 2 allows no mutual views.
- **Lemma C.2.** The expected period-2 value `M²(x¹) = E_{R ∼ φ¹·x¹}[f(R)]` is
  monotone and submodular in the set of period-1 initiations.

Here `f(R)` uses the paper's per-responder form: `f(R) = ∑_ℓ f_ℓ(B_ℓ(R))`, where
`B_ℓ(R) = {ℓ' : (ℓ', ℓ) ∈ R}` is `ℓ`'s backlog and `f_ℓ` is weighted top-`K_ℓ`.
-/

namespace DatingAlgo

open Finset

variable {α : Type*} [DecidableEq α]

/-- A set function is monotone: larger sets have larger value. -/
def SetMonotone (g : Finset α → ℝ) : Prop := ∀ A B, A ⊆ B → g A ≤ g B

/-- A set function is submodular: adding an element to a smaller set helps at least
as much as adding it to a larger one. -/
def Submodular (g : Finset α → ℝ) : Prop :=
  ∀ A B a, A ⊆ B → g (insert a B) - g B ≤ g (insert a A) - g A

/-- **Lemma C.2, generic.** If `g` is monotone, so is `V ↦ E[g(S)]`, where `S`
includes each element of `V` independently. -/
theorem indepExp_setMonotone {p : α → ℝ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    {g : Finset α → ℝ} (hg : SetMonotone g) :
    SetMonotone (fun V => indepExp V p g) := by
  intro A B hAB
  exact indepExp_le_of_subset_of_monotone (fun i _ => hp i) hAB
    (fun S T hST _ => hg S T hST)

/-- The marginal value of adding `a ∉ X` to the ground set is `p a` times the expected
marginal value of `a` for `g`. -/
theorem indepExp_insert_sub {p : α → ℝ} {g : Finset α → ℝ} {X : Finset α} {a : α}
    (ha : a ∉ X) :
    indepExp (insert a X) p g - indepExp X p g =
      p a * indepExp X p (fun S => g (insert a S) - g S) := by
  rw [indepExp_insert ha]
  have h := indepExp_add X p (fun S => g (insert a S) - g S) g
  simp only [sub_add_cancel] at h
  rw [show indepExp X p (fun S => g (insert a S) - g S) =
      indepExp X p (fun S => g (insert a S)) - indepExp X p g by linarith]
  ring

/-- **Lemma C.2, generic.** If `g` is monotone and submodular, then
`V ↦ E[g(S)]` is submodular. -/
theorem indepExp_submodular {p : α → ℝ} (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    {g : Finset α → ℝ} (hg : SetMonotone g) (hgs : Submodular g) :
    Submodular (fun V => indepExp V p g) := by
  intro A B a hAB
  by_cases haB : a ∈ B
  · simp only [Finset.insert_eq_of_mem haB, sub_self]
    exact sub_nonneg.mpr (indepExp_setMonotone hp hg _ _ (Finset.subset_insert a A))
  · have haA : a ∉ A := fun h => haB (hAB h)
    simp only [indepExp_insert_sub haB, indepExp_insert_sub haA]
    apply mul_le_mul_of_nonneg_left _ (hp a).1
    exact indepExp_le_of_subset_of_antitone (fun i _ => hp i) hAB
      (fun S T hST _ => hgs S T a hST)

namespace TwoPeriodModel

variable {U D : Type*} [Fintype U] [DecidableEq U] (M : TwoPeriodModel U D)

/-- Backlog of `ℓ` given the realized likes `R` (arc `(a, b)` means `a` saw and
liked `b`). -/
def backlogOf (R : Finset (U × U)) (ℓ : U) : Finset U :=
  (R.filter (fun e => e.2 = ℓ)).image Prod.fst

omit [Fintype U] in
/-- Backlogs grow with the set of realized likes. -/
theorem backlogOf_mono {R R' : Finset (U × U)} (h : R ⊆ R') (ℓ : U) :
    backlogOf R ℓ ⊆ backlogOf R' ℓ :=
  Finset.image_subset_image (Finset.filter_subset_filter _ h)

omit [Fintype U] in
/-- Adding the arc `a` adds `a.1` to the backlog of `a.2` and changes no other backlog. -/
theorem backlogOf_insert (R : Finset (U × U)) (a : U × U) (ℓ : U) :
    backlogOf (insert a R) ℓ =
      if a.2 = ℓ then insert a.1 (backlogOf R ℓ) else backlogOf R ℓ := by
  unfold backlogOf
  rw [Finset.filter_insert]
  split_ifs <;> simp [Finset.image_insert]

/-- The paper's `f(R)`, eq. (13): the best expected period-2 reward given realized
likes `R`, with no mutual views in period 2. -/
noncomputable def secondStageValue (R : Finset (U × U)) : ℝ :=
  ∑ ℓ, topK (M.r2 ℓ) (M.K ℓ) (backlogOf R ℓ)

/-- **Lemma 4.1 (monotone).** -/
theorem secondStageValue_monotone : SetMonotone M.secondStageValue := by
  intro R R' hRR'
  unfold secondStageValue
  exact Finset.sum_le_sum fun ℓ _ => topK_mono (backlogOf_mono hRR' ℓ)

/-- **Lemma 4.1 (submodular).** -/
theorem secondStageValue_submodular : Submodular M.secondStageValue := by
  intro R R' a hRR'
  unfold secondStageValue
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro ℓ _
  rw [backlogOf_insert, backlogOf_insert]
  split_ifs
  · exact topK_submodular (M.r2_nonneg ℓ) (M.K ℓ) (backlogOf_mono hRR' ℓ) a.1
  · simp

/-- The paper's `M²(x¹)`, eq. (14): expected `f(R)` when each initiation arc
`(a, b) ∈ X` (`a` shown `b`) becomes a like independently with probability
`φ¹_{ab}`. -/
noncomputable def expectedSecondStage (X : Finset (U × U)) : ℝ :=
  indepExp X (fun e => M.φ1 e.1 e.2) M.secondStageValue

/-- **Lemma C.2 (monotone).** -/
theorem expectedSecondStage_monotone : SetMonotone M.expectedSecondStage :=
  indepExp_setMonotone (p := fun e : U × U => M.φ1 e.1 e.2)
    (fun e : U × U => ⟨M.φ1_nonneg e.1 e.2, M.φ1_le_one e.1 e.2⟩) M.secondStageValue_monotone

/-- **Lemma C.2 (submodular).** -/
theorem expectedSecondStage_submodular : Submodular M.expectedSecondStage :=
  indepExp_submodular (p := fun e : U × U => M.φ1 e.1 e.2)
    (fun e : U × U => ⟨M.φ1_nonneg e.1 e.2, M.φ1_le_one e.1 e.2⟩)
    M.secondStageValue_monotone M.secondStageValue_submodular

end TwoPeriodModel

end DatingAlgo
