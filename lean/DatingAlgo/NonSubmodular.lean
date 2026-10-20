import DatingAlgo.Designs

/-!
# Proposition 3.4: with mutual views in period 2, `f` is not submodular

Rios & Torrico, Proposition 3.4 and eq. (7).

**The period-2 problem.** Period 1 is fixed by display `S1`, and `R` is the set of
realized likes on period-1 initiations: `(a, b) ∈ R` means `a` saw `b` and liked them.
In period 2 each user `ℓ` may show:
- profiles from their backlog `{ℓ' : (ℓ', ℓ) ∈ R}`, earning `φ²_{ℓℓ'} q` per response;
- *fresh* profiles: mutually acceptable users who did not interact in period 1. A
  mutual fresh view earns `β² q = φ²_{ℓℓ'} φ²_{ℓ'ℓ} q`. A one-sided fresh view earns
  nothing, because it cannot be reciprocated before the horizon ends.

Each user shows at most `K_ℓ` profiles. `f(R)` is the best expected reward.

Lemma 4.1 (`Submodularity.lean`) shows `f` is submodular when there are no mutual views
in period 2. Proposition 3.4 shows that allowing them breaks submodularity.
-/

namespace DatingAlgo

open Finset

namespace Market

variable {U : Type*} [Fintype U] [DecidableEq U] (mk : Market U)

/-- Backlog of `ℓ` in period 2: users who initiated toward `ℓ` and liked them. -/
def backlogFrom (R : Finset (U × U)) (ℓ : U) : Finset U := univ.filter (fun ℓ' => (ℓ', ℓ) ∈ R)

/-- `ℓ` and `ℓ'` are mutually acceptable and did not interact in period 1. -/
def Fresh (S1 : U → Finset U) (ℓ ℓ' : U) : Prop :=
  ℓ' ∈ mk.pot ℓ ∧ ℓ ∈ mk.pot ℓ' ∧ ℓ' ∉ S1 ℓ ∧ ℓ ∉ S1 ℓ'

/-- A feasible period-2 display: backlog or fresh profiles only, within the caps. -/
def Period2Feasible (S1 : U → Finset U) (R : Finset (U × U)) (S2 : U → Finset U) : Prop :=
  ∀ ℓ, (∀ ℓ' ∈ S2 ℓ, ℓ' ∈ backlogFrom R ℓ ∨ mk.Fresh S1 ℓ ℓ') ∧ (S2 ℓ).card ≤ mk.K ℓ

open Classical in
/-- Expected period-2 reward of display `S2`, eq. (7):
- each backlog response earns `φ²_{ℓℓ'} q_{ℓℓ'}`;
- each mutual fresh view, counted once from its `I` side, earns
  `φ²_{ℓℓ'} φ²_{ℓ'ℓ} q_{ℓℓ'}`. -/
noncomputable def period2Reward (S1 : U → Finset U) (R : Finset (U × U))
    (S2 : U → Finset U) : ℝ :=
  ∑ ℓ, ∑ ℓ' ∈ S2 ℓ,
    ((if ℓ' ∈ backlogFrom R ℓ then mk.φ2 ℓ ℓ' * mk.q ℓ ℓ' else 0) +
     (if mk.Fresh S1 ℓ ℓ' ∧ ℓ ∈ S2 ℓ' ∧ mk.side ℓ = true then
        mk.φ2 ℓ ℓ' * mk.φ2 ℓ' ℓ * mk.q ℓ ℓ' else 0))

open Classical in
/-- `f(R)`: the best expected period-2 reward given period-1 display `S1` and
realized likes `R`. -/
noncomputable def period2Value (S1 : U → Finset U) (R : Finset (U × U)) : ℝ :=
  (univ.filter (mk.Period2Feasible S1 R)).sup' ⟨fun _ => ∅, by
    simp [Period2Feasible]⟩ (mk.period2Reward S1 R)

end Market

/-! ### The counterexample

A reduced version of the paper's instance. Users `i1 = 0`, `i2 = 1` are on side `I` and
`j1 = 2`, `j2 = 3` on side `J`; `K ≡ 1`, `φ1 = φ2 ≡ 1/2`, `q ≡ 1`. In period 1, `j1` sees
`i1` and `i2` sees `j2`, so the only fresh pair is `(i1, j2)` (mutual value `1/4`). With
`R = ∅`, `R' = {(j1, i1)}` and `a = (i2, j2)`:
`f ∅ = 1/4`, `f {a} = 1/2`, `f R' = 1/2`, `f (insert a R') = 1`. -/

namespace NonSubmodularEx

/-- Potentials of the example: `i1` accepts `j1, j2`; `i2` accepts `j2`; `j1` accepts `i1`;
`j2` accepts `i1, i2`. -/
def exPot : Fin 4 → Finset (Fin 4) := ![{2, 3}, {3}, {0}, {0, 1}]

/-- Period-1 display of the example: `j1` sees `i1`, `i2` sees `j2`, the others see nobody. -/
def exS1 : Fin 4 → Finset (Fin 4) := ![∅, {3}, {0}, ∅]

/-- The example market: `I = {0, 1}`, `J = {2, 3}`, `K ≡ 1`, `φ1 = φ2 ≡ 1/2`, `q ≡ 1`. -/
noncomputable def ex : Market (Fin 4) where
  side ℓ := decide (ℓ.val < 2)
  pot := exPot
  K _ := 1
  φ1 _ _ := 1 / 2
  φ2 _ _ := 1 / 2
  q _ _ := 1
  pot_other_side := by decide
  φ1_nonneg _ _ := by norm_num
  φ1_le_one _ _ := by norm_num
  φ2_nonneg _ _ := by norm_num
  q_nonneg _ _ := by norm_num

/-- A feasible period-2 row of the example is empty or a single backlog or fresh profile. -/
lemma row_cases {R : Finset (Fin 4 × Fin 4)} {S2 : Fin 4 → Finset (Fin 4)}
    (hf : ex.Period2Feasible exS1 R S2) (ℓ : Fin 4) :
    S2 ℓ = ∅ ∨ ∃ x, S2 ℓ = {x} ∧ (x ∈ Market.backlogFrom R ℓ ∨ ex.Fresh exS1 ℓ x) := by
  have hc : (S2 ℓ).card ≤ 1 := (hf ℓ).2
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hc with h | h
  · exact Or.inl (Finset.card_eq_zero.1 h)
  · obtain ⟨x, hx⟩ := Finset.card_eq_one.1 h
    exact Or.inr ⟨x, hx, (hf ℓ).1 x (by simp [hx])⟩

/-- Upper bound `f {a} ≤ 1/2`: `j2`'s single slot serves either `i2`'s like or `i1`. -/
lemma value_a_le : ex.period2Value exS1 {(1, 3)} ≤ 1 / 2 := by
  unfold Market.period2Value
  refine Finset.sup'_le _ _ (fun S2 hS2 => ?_)
  have hf : ex.Period2Feasible exS1 {(1, 3)} S2 := by simpa using hS2
  have h0 : S2 0 = ∅ ∨ S2 0 = {3} := by
    rcases row_cases hf 0 with h | ⟨x, h, hx⟩
    · exact Or.inl h
    · fin_cases x <;> simp_all [Market.Fresh, Market.backlogFrom, ex, exPot, exS1]
  have h1 : S2 1 = ∅ := by
    rcases row_cases hf 1 with h | ⟨x, h, hx⟩
    · exact h
    · fin_cases x <;> simp_all [Market.Fresh, Market.backlogFrom, ex, exPot, exS1]
  have h2 : S2 2 = ∅ := by
    rcases row_cases hf 2 with h | ⟨x, h, hx⟩
    · exact h
    · fin_cases x <;> simp_all [Market.Fresh, Market.backlogFrom, ex, exPot, exS1]
  have h3 : S2 3 = ∅ ∨ S2 3 = {0} ∨ S2 3 = {1} := by
    rcases row_cases hf 3 with h | ⟨x, h, hx⟩
    · exact Or.inl h
    · fin_cases x <;> simp_all [Market.Fresh, Market.backlogFrom, ex, exPot, exS1]
  rcases h0 with h0 | h0 <;> rcases h3 with h3 | h3 | h3 <;>
    norm_num [Market.period2Reward, Fin.sum_univ_four, h0, h1, h2, h3, Market.Fresh,
      Market.backlogFrom, ex, exPot, exS1]

/-- Upper bound `f R' ≤ 1/2`: `i1`'s single slot serves either `j1`'s like or `j2`. -/
lemma value_R'_le : ex.period2Value exS1 {(2, 0)} ≤ 1 / 2 := by
  unfold Market.period2Value
  refine Finset.sup'_le _ _ (fun S2 hS2 => ?_)
  have hf : ex.Period2Feasible exS1 {(2, 0)} S2 := by simpa using hS2
  have h0 : S2 0 = ∅ ∨ S2 0 = {2} ∨ S2 0 = {3} := by
    rcases row_cases hf 0 with h | ⟨x, h, hx⟩
    · exact Or.inl h
    · fin_cases x <;> simp_all [Market.Fresh, Market.backlogFrom, ex, exPot, exS1]
  have h1 : S2 1 = ∅ := by
    rcases row_cases hf 1 with h | ⟨x, h, hx⟩
    · exact h
    · fin_cases x <;> simp_all [Market.Fresh, Market.backlogFrom, ex, exPot, exS1]
  have h2 : S2 2 = ∅ := by
    rcases row_cases hf 2 with h | ⟨x, h, hx⟩
    · exact h
    · fin_cases x <;> simp_all [Market.Fresh, Market.backlogFrom, ex, exPot, exS1]
  have h3 : S2 3 = ∅ ∨ S2 3 = {0} := by
    rcases row_cases hf 3 with h | ⟨x, h, hx⟩
    · exact Or.inl h
    · fin_cases x <;> simp_all [Market.Fresh, Market.backlogFrom, ex, exPot, exS1]
  rcases h0 with h0 | h0 | h0 <;> rcases h3 with h3 | h3 <;>
    norm_num [Market.period2Reward, Fin.sum_univ_four, h0, h1, h2, h3, Market.Fresh,
      Market.backlogFrom, ex, exPot, exS1]

/-- Lower bound `1/4 ≤ f ∅`: the mutual fresh view between `i1` and `j2`. -/
lemma value_empty_ge : 1 / 4 ≤ ex.period2Value exS1 ∅ := by
  unfold Market.period2Value
  have hf : ex.Period2Feasible exS1 ∅ ![{3}, ∅, ∅, {0}] := by
    intro ℓ
    fin_cases ℓ <;> simp [Market.Fresh, Market.backlogFrom, ex, exPot, exS1]
  refine Finset.le_sup'_of_le _ (b := ![{3}, ∅, ∅, {0}]) (by simpa using hf) ?_
  norm_num [Market.period2Reward, Fin.sum_univ_four, Market.Fresh, Market.backlogFrom, ex,
    exPot, exS1]

/-- Lower bound `1 ≤ f (insert a R')`: `i1` answers `j1` and `j2` answers `i2`. -/
lemma value_aR'_ge : 1 ≤ ex.period2Value exS1 {(1, 3), (2, 0)} := by
  unfold Market.period2Value
  have hf : ex.Period2Feasible exS1 {(1, 3), (2, 0)} ![{2}, ∅, ∅, {1}] := by
    intro ℓ
    fin_cases ℓ <;> simp [Market.Fresh, Market.backlogFrom, ex, exPot, exS1]
  refine Finset.le_sup'_of_le _ (b := ![{2}, ∅, ∅, {1}]) (by simpa using hf) ?_
  norm_num [Market.period2Reward, Fin.sum_univ_four, Market.Fresh, Market.backlogFrom, ex,
    exPot, exS1]

end NonSubmodularEx

/-- **Proposition 3.4 (Rios & Torrico).** With mutual views allowed in period 2, the
optimal period-2 value is not submodular in the realized likes `R`. -/
theorem period2Value_not_submodular :
    ∃ (mk : Market (Fin 4)) (S1 : Fin 4 → Finset (Fin 4))
      (R R' : Finset (Fin 4 × Fin 4)) (a : Fin 4 × Fin 4),
      R ⊆ R' ∧
      mk.period2Value S1 (insert a R) - mk.period2Value S1 R <
        mk.period2Value S1 (insert a R') - mk.period2Value S1 R' := by
  refine ⟨NonSubmodularEx.ex, NonSubmodularEx.exS1, ∅, {(2, 0)}, (1, 3),
    Finset.empty_subset _, ?_⟩
  have h1 := NonSubmodularEx.value_a_le
  have h2 := NonSubmodularEx.value_R'_le
  have h3 := NonSubmodularEx.value_empty_ge
  have h4 := NonSubmodularEx.value_aR'_ge
  simp only [Finset.insert_empty]
  linarith

end DatingAlgo
