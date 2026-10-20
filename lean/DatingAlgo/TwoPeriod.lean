import DatingAlgo.CorrelationGap

/-!
# The two-period model and Theorem 4.3

Rios & Torrico, Section 4 (Problem 4.2, Algorithm 2, Theorem 4.3, Lemma C.5).

## Modeling choices

**First-stage decisions are abstract.** A decision `d : D` (the paper's `(x¹, w¹)`)
is summarized by two quantities:
- `imm d`: expected period-1 reward from mutual (non-sequential) views,
  `∑_e β¹_e w¹_e`;
- `init d ℓ`: the users `ℓ'` shown `ℓ` in period 1 as an initiation
  (`x¹_{ℓ'ℓ} = 1`).

The platform design (one- or two-directional, sequential-only or not) is a predicate
`feasible : D → Prop`. Every theorem here holds for any design, which is the
paper's "uniformly across platform designs".

**Period 2.** `ℓ'` lands in `ℓ`'s backlog independently with probability `φ¹_{ℓ'ℓ}`.
`ℓ` then shows at most `K_ℓ` backlog profiles, and showing `ℓ'` earns reward
`r2 ℓ ℓ'`. The paper's assumptions apply: empty initial backlog, period-2 behavior
independent of the realized history, and no mutual views in period 2.

**Objective.** `value d` is the objective of Problem 4.2 in the form the paper's proof
of Theorem 4.3 uses: `∑ β¹ w¹ + ∑_ℓ ∑_B f_ℓ(B) P(B)`.

**Count and quality share one theorem.**
- With `r2 = φ²` and `imm = ∑ β¹ w¹`, the objective is the expected number of matches
  (the paper).
- With `r2 = φ² q` and `imm = ∑ β¹ q w¹`, it is expected match quality: result R2 in the
  vault note "Match Quality in the Dating Heuristic Framework".
-/

namespace DatingAlgo

open Finset

/-- A two-period instance with abstract first-stage decisions `D`. -/
structure TwoPeriodModel (U D : Type*) where
  /-- Display cap `K_ℓ`. -/
  K : U → ℕ
  /-- `φ1 a b`: probability that `a` likes `b` in period 1. -/
  φ1 : U → U → ℝ
  /-- `r2 ℓ ℓ'`: expected reward when `ℓ` is shown `ℓ'` from the backlog in period 2.
  `φ²_{ℓℓ'}` for match count; `φ²_{ℓℓ'} q_{ℓℓ'}` for quality. -/
  r2 : U → U → ℝ
  /-- Expected period-1 reward of a decision (mutual views). -/
  imm : D → ℝ
  /-- `init d ℓ`: the users shown `ℓ` in period 1 as an initiation. -/
  init : D → U → Finset U
  φ1_nonneg : ∀ a b, 0 ≤ φ1 a b
  φ1_le_one : ∀ a b, φ1 a b ≤ 1
  r2_nonneg : ∀ a b, 0 ≤ r2 a b
  imm_nonneg : ∀ d, 0 ≤ imm d

namespace TwoPeriodModel

variable {U D : Type*} [Fintype U] [DecidableEq U] (M : TwoPeriodModel U D)

/-- Expected period-2 reward of responder `ℓ` under decision `d`: the paper's
`∑_B f_ℓ(B) P_{x¹}(B)`. -/
noncomputable def backlogValue (d : D) (ℓ : U) : ℝ :=
  indepExp (M.init d ℓ) (fun ℓ' => M.φ1 ℓ' ℓ) (topK (M.r2 ℓ) (M.K ℓ))

/-- Objective of Problem 4.2 for first-stage decision `d`, when period 2 is played
optimally. -/
noncomputable def value (d : D) : ℝ := M.imm d + ∑ ℓ, M.backlogValue d ℓ

/-- Constraints of DH-int's program (16) on the fractional period-2 plan `y`:
`0 ≤ y_{ℓℓ'} ≤ φ¹_{ℓ'ℓ} x¹_{ℓ'ℓ}` and `∑_{ℓ'} y_{ℓℓ'} ≤ K_ℓ`. -/
def PlanFeasible (d : D) (y : U → U → ℝ) : Prop :=
  ∀ ℓ, (∀ ℓ' ∈ M.init d ℓ, 0 ≤ y ℓ ℓ' ∧ y ℓ ℓ' ≤ M.φ1 ℓ' ℓ) ∧
    ∑ ℓ' ∈ M.init d ℓ, y ℓ ℓ' ≤ M.K ℓ

/-- Objective of DH-int's program (16). -/
noncomputable def planValue (d : D) (y : U → U → ℝ) : ℝ :=
  M.imm d + ∑ ℓ, ∑ ℓ' ∈ M.init d ℓ, M.r2 ℓ ℓ' * y ℓ ℓ'

/-- `(d, y)` is an optimal solution of DH-int's program (16) for the design
`feasible`. Algorithm 2 then shows `d` in period 1 and plays period 2 optimally,
earning `value d`. -/
def IsDHIntSolution (feasible : D → Prop) (d : D) (y : U → U → ℝ) : Prop :=
  feasible d ∧ M.PlanFeasible d y ∧
    ∀ d' y', feasible d' → M.PlanFeasible d' y' → M.planValue d' y' ≤ M.planValue d y

end TwoPeriodModel

/-- **Lemma C.5, per responder.** The expected optimal period-2 value equals the
value of a fractional plan that respects the like probabilities and the display cap.
The plan `y i` is the probability that `i` is shown. -/
theorem exists_plan_eq_indepExp_topK {α : Type*} [DecidableEq α] (U : Finset α)
    (p w : α → ℝ) (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (K : ℕ) :
    ∃ y : α → ℝ, (∀ i ∈ U, 0 ≤ y i ∧ y i ≤ p i) ∧ ∑ i ∈ U, y i ≤ K ∧
      indepExp U p (topK w K) = ∑ i ∈ U, w i * y i := by
  choose sel hselsub hselcard hseleq using fun S : Finset α => exists_topK_eq w K S
  refine ⟨fun i => indepExp U p (fun S => if i ∈ sel S then 1 else 0), ?_, ?_, ?_⟩
  · intro i hi
    refine ⟨?_, ?_⟩
    · calc (0 : ℝ) = indepExp U p (fun _ => 0) := (indepExp_const U p 0).symm
        _ ≤ _ := indepExp_mono hp (fun S _ => by split_ifs <;> norm_num)
    · calc _ ≤ indepExp U p (fun S => if i ∈ S then 1 else 0) := by
            refine indepExp_mono hp (fun S _ => ?_)
            by_cases h : i ∈ sel S
            · simp [h, hselsub S h]
            · simp only [h, ↓reduceIte]
              split_ifs <;> norm_num
        _ = p i := indepExp_mem hi p
  · show ∑ i ∈ U, indepExp U p (fun S => if i ∈ sel S then (1 : ℝ) else 0) ≤ K
    rw [← indepExp_sum]
    calc _ ≤ indepExp U p (fun _ => (K : ℝ)) := by
          refine indepExp_mono hp (fun S hS => ?_)
          rw [Finset.sum_ite_mem, Finset.sum_const, nsmul_eq_mul, mul_one,
            Finset.inter_eq_right.mpr ((hselsub S).trans hS)]
          exact_mod_cast hselcard S
      _ = K := indepExp_const _ _ _
  · show _ = ∑ i ∈ U, w i * indepExp U p (fun S => if i ∈ sel S then (1 : ℝ) else 0)
    simp_rw [← indepExp_const_mul]
    rw [← indepExp_sum]
    refine indepExp_congr (fun S hS => ?_)
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr ((hselsub S).trans hS)]
    exact hseleq S

namespace TwoPeriodModel

variable {U D : Type*} [Fintype U] [DecidableEq U] (M : TwoPeriodModel U D)

/-- **Lemma C.5.** DH-int's program upper-bounds the value of every first-stage
decision, hence OPT. -/
theorem value_le_planValue (d : D) : ∃ y, M.PlanFeasible d y ∧ M.value d ≤ M.planValue d y := by
  have h := fun ℓ => exists_plan_eq_indepExp_topK (M.init d ℓ) (fun ℓ' => M.φ1 ℓ' ℓ)
    (M.r2 ℓ) (fun i _ => ⟨M.φ1_nonneg i ℓ, M.φ1_le_one i ℓ⟩) (M.K ℓ)
  choose y hy1 hy2 hy3 using h
  refine ⟨y, fun ℓ => ⟨hy1 ℓ, hy2 ℓ⟩, le_of_eq ?_⟩
  unfold value planValue backlogValue
  congr 1
  exact Finset.sum_congr rfl fun ℓ _ => hy3 ℓ

/-- **Theorem 4.3, generic form.** Suppose the realized period-2 value of each
responder is at least `c` times what the fractional plan promised. Then DH-int is a
`c`-approximation, for every design. -/
theorem approx_of_gap {feasible : D → Prop} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hgap : ∀ (d : D) (ℓ : U) (y : U → ℝ),
      (∀ ℓ' ∈ M.init d ℓ, 0 ≤ y ℓ' ∧ y ℓ' ≤ M.φ1 ℓ' ℓ) →
      ∑ ℓ' ∈ M.init d ℓ, y ℓ' ≤ M.K ℓ →
      c * ∑ ℓ' ∈ M.init d ℓ, M.r2 ℓ ℓ' * y ℓ' ≤ M.backlogValue d ℓ)
    {d : D} {y : U → U → ℝ} (hdh : M.IsDHIntSolution feasible d y)
    {d' : D} (hd' : feasible d') :
    c * M.value d' ≤ M.value d := by
  obtain ⟨y', hy'f, hy'v⟩ := M.value_le_planValue d'
  have hopt := hdh.2.2 d' y' hd' hy'f
  calc c * M.value d' ≤ c * M.planValue d y :=
        mul_le_mul_of_nonneg_left (hy'v.trans hopt) hc0
    _ = c * M.imm d + ∑ ℓ, c * ∑ ℓ' ∈ M.init d ℓ, M.r2 ℓ ℓ' * y ℓ ℓ' := by
        unfold planValue
        rw [mul_add, Finset.mul_sum]
    _ ≤ M.imm d + ∑ ℓ, M.backlogValue d ℓ := by
        apply add_le_add
        · calc c * M.imm d ≤ 1 * M.imm d := mul_le_mul_of_nonneg_right hc1 (M.imm_nonneg d)
            _ = M.imm d := one_mul _
        · exact Finset.sum_le_sum fun ℓ _ => hgap d ℓ (y ℓ) (hdh.2.1 ℓ).1 (hdh.2.1 ℓ).2
    _ = M.value d := rfl

/-- **Theorem 4.3 (Rios & Torrico).** DH-int is a `(1 - 1/e)`-approximation for the
two-period problem (Problem 4.2), for every platform design. -/
theorem dhInt_approx {feasible : D → Prop} {d : D} {y : U → U → ℝ}
    (hdh : M.IsDHIntSolution feasible d y) {d' : D} (hd' : feasible d') :
    (1 - Real.exp (-1)) * M.value d' ≤ M.value d := by
  refine M.approx_of_gap ?_ ?_ ?_ hdh hd'
  · have := Real.exp_le_one_iff.mpr (by norm_num : (-1 : ℝ) ≤ 0)
    linarith
  · have := Real.exp_pos (-1)
    linarith
  · intro d₀ ℓ y₀ hy hyK
    exact topK_correlation_gap (M.init d₀ ℓ) (fun ℓ' => M.φ1 ℓ' ℓ) (M.r2 ℓ) y₀
      (fun i _ => ⟨M.φ1_nonneg i ℓ, M.φ1_le_one i ℓ⟩) (fun i _ => M.r2_nonneg ℓ i) (M.K ℓ)
      hy hyK

/-- **Theorem 4.3 with any unweighted gap constant.** If every responder's
cardinality gap holds with constant `c`, DH-int is a `c`-approximation. With `c = c_K`
this is R1 (`dhInt_approx_cK` in `PoissonGap.lean`). -/
theorem dhInt_approx_of_card_gap {feasible : D → Prop} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hcard : ∀ (ℓ : U) (V : Finset U),
      c * min (∑ i ∈ V, M.φ1 i ℓ) (M.K ℓ) ≤
        indepExp V (fun i => M.φ1 i ℓ) (fun S => min (S.card : ℝ) (M.K ℓ)))
    {d : D} {y : U → U → ℝ} (hdh : M.IsDHIntSolution feasible d y)
    {d' : D} (hd' : feasible d') :
    c * M.value d' ≤ M.value d := by
  refine M.approx_of_gap hc0 hc1 ?_ hdh hd'
  intro d₀ ℓ y₀ hy hyK
  exact weighted_gap_of_card_gap hc0 (fun i _ => ⟨M.φ1_nonneg i ℓ, M.φ1_le_one i ℓ⟩)
    (fun V _ => hcard ℓ V) (fun i _ => M.r2_nonneg ℓ i) hy hyK

/-- The quality-weighted model behind R2: period-2 rewards `r2 · q` and period-1
rewards `immQ` (`∑ β¹_e q_e w¹_e`). -/
def withQuality (q : U → U → ℝ) (hq : ∀ a b, 0 ≤ q a b) (immQ : D → ℝ)
    (himmQ : ∀ d, 0 ≤ immQ d) : TwoPeriodModel U D :=
  { M with
    r2 := fun a b => M.r2 a b * q a b
    imm := immQ
    r2_nonneg := fun a b => mul_nonneg (M.r2_nonneg a b) (hq a b)
    imm_nonneg := himmQ }

/-- **R2 (vault note).** Quality-weighted DH-int, meaning DH-int run on the
quality-weighted model, is a `(1 - 1/e)`-approximation for expected match quality,
for every design. -/
theorem dhInt_quality_approx (q : U → U → ℝ) (hq : ∀ a b, 0 ≤ q a b) (immQ : D → ℝ)
    (himmQ : ∀ d, 0 ≤ immQ d) {feasible : D → Prop} {d : D} {y : U → U → ℝ}
    (hdh : (M.withQuality q hq immQ himmQ).IsDHIntSolution feasible d y)
    {d' : D} (hd' : feasible d') :
    (1 - Real.exp (-1)) * (M.withQuality q hq immQ himmQ).value d' ≤
      (M.withQuality q hq immQ himmQ).value d :=
  (M.withQuality q hq immQ himmQ).dhInt_approx hdh hd'

end TwoPeriodModel

end DatingAlgo
