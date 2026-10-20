import DatingAlgo.IndepExp

/-!
# Theorem 5.4 fails as stated: a counterexample

Rios & Torrico, Section 5. Theorem 5.4 claims a `(1 - 1/e)`-approximation against the
best adaptive policy for the one-directional, sequential-only design. The policy
solves LP (41), rounds it (Gandhi et al.), and schedules the result with DHT
(Algorithm 3, Remark 5.5).

LP (41) pools each user's display slots over all `T` periods (`∑ y ≤ K_j T`). It
ignores two timing facts:
- a responder can't respond in period 1, because the backlog starts empty;
- likes received in the last period can never be answered.

## The instance
- `T = 2` and every display cap is 1.
- Initiators `i1, i2`; responders `j1, j2`.
- Every initiator likes every responder for sure.
- `j1` likes every initiator for sure; `j2` likes each with probability `1 - δ`
  (`δ = 1/100`).

## What happens
- LP (41) has a unique optimum: every initiator initiates toward both responders. It
  is integral, so rounding returns it unchanged.
- DHT shows each initiator `j1` in period 1, since `j1` reciprocates with higher
  probability, and `j2` in period 2.
- `j2`'s likes arrive in the last period and are never answered. `j1` can respond to
  only one initiator.
- Even with *clairvoyant* responders, DHT earns at most 1 expected match.
- The schedule "`i1 → j1`, `i2 → j2` in period 1", with responders answering whoever
  liked them, earns `2 - δ`.
- `1 < (1 - 1/e)(2 - δ)`, so the guarantee fails.

## Modeling
Likes are drawn up front: `LI` contains `(i, j)` if `i` would like `j` when shown,
`LJ` contains `(j, i)` likewise, and all are independent. In this design the
initiators' displays are a fixed schedule, and responders only show profiles that
liked them in an *earlier* period.
-/

namespace DatingAlgo

open Finset

namespace OneDirSeq

/-- A one-directional, sequential-only instance with complete potentials. -/
structure Instance (I J : Type*) where
  T : ℕ
  KI : I → ℕ
  KJ : J → ℕ
  /-- `pIJ i j`: probability that `i` likes `j` when shown. -/
  pIJ : I → J → ℝ
  /-- `pJI j i`: probability that `j` likes `i` when shown. -/
  pJI : J → I → ℝ

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- LP (41), feasibility: `0 ≤ x, y ≤ 1`, `y_{ji} ≤ x_{ij} φ_{ij}`, `∑_j x_{ij} ≤ K_i T`
and `∑_i y_{ji} ≤ K_j T`. -/
def LPFeasible (inst : Instance I J) (x : I → J → ℝ) (y : J → I → ℝ) : Prop :=
  (∀ i j, 0 ≤ x i j ∧ x i j ≤ 1) ∧ (∀ j i, 0 ≤ y j i ∧ y j i ≤ 1) ∧
  (∀ i j, y j i ≤ x i j * inst.pIJ i j) ∧
  (∀ i, ∑ j, x i j ≤ (inst.KI i : ℝ) * inst.T) ∧
  (∀ j, ∑ i, y j i ≤ (inst.KJ j : ℝ) * inst.T)

/-- LP (41), objective: `∑ y_{ji} φ_{ji}`. -/
noncomputable def LPObj (inst : Instance I J) (y : J → I → ℝ) : ℝ :=
  ∑ i, ∑ j, y j i * inst.pJI j i

/-- Initiation schedules: `sched t i` is what initiator `i` is shown in period `t`. -/
abbrev Schedule (I J : Type*) (T : ℕ) := Fin T → I → Finset J

/-- A feasible initiation schedule: at most `K_i` profiles per period, each shown once. -/
def ScheduleFeasible (inst : Instance I J) (σ : Schedule I J inst.T) : Prop :=
  (∀ t i, (σ t i).card ≤ inst.KI i) ∧ (∀ i t t' j, j ∈ σ t i → j ∈ σ t' i → t = t')

/-- A schedule DHT may produce from an integral solution `x` (Algorithm 3, steps 6–8),
with arbitrary tie-breaking:
- each initiator shows exactly its initiations `{j : x i j = 1}`, at most `K_i` per
  period and each once;
- slots are used as early as possible;
- higher reciprocation probability `φ_{ji}` comes first. -/
def IsDHTSchedule (inst : Instance I J) (x : I → J → ℝ) (σ : Schedule I J inst.T) :
    Prop :=
  (∀ i, (univ.biUnion fun t => σ t i) = univ.filter (fun j => x i j = 1)) ∧
  (∀ t i, (σ t i).card ≤ inst.KI i) ∧
  (∀ i t t' j, j ∈ σ t i → j ∈ σ t' i → t = t') ∧
  (∀ i (t t' : Fin inst.T), t < t' → (σ t' i).Nonempty → (σ t i).card = inst.KI i) ∧
  (∀ i (t t' : Fin inst.T) j j', t < t' → j ∈ σ t i → j' ∈ σ t' i →
    inst.pJI j' i ≤ inst.pJI j i)

/-- Profiles in `j`'s backlog at the start of period `t`: initiators who were shown `j`
in an earlier period and liked `j`. -/
def arrived {T : ℕ} (σ : Schedule I J T) (LI : Finset (I × J)) (t : Fin T) (j : J) : Finset I :=
  univ.filter fun i => ∃ s : Fin T, s < t ∧ j ∈ σ s i ∧ (i, j) ∈ LI

/-- A response plan for the responders: only backlog profiles, at most `K_j` per
period, and each profile at most once. -/
def RespFeasible (inst : Instance I J) (σ : Schedule I J inst.T) (LI : Finset (I × J))
    (ρ : Fin inst.T → J → Finset I) : Prop :=
  (∀ t j, ρ t j ⊆ arrived σ LI t j ∧ (ρ t j).card ≤ inst.KJ j) ∧
  (∀ t t' j i, i ∈ ρ t j → i ∈ ρ t' j → t = t')

/-- Matches produced by a response plan: shown backlog profiles that the responder likes. -/
def matchCount {T : ℕ} (ρ : Fin T → J → Finset I) (LJ : Finset (J × I)) : ℕ :=
  ∑ t, ∑ j, ((ρ t j).filter fun i => (j, i) ∈ LJ).card

open Classical in
/-- The best matches any responders could get, even *knowing their own future likes*
(clairvoyant). An upper bound on what DHT's responses realize. -/
noncomputable def bestResponse (inst : Instance I J) (σ : Schedule I J inst.T)
    (LI : Finset (I × J)) (LJ : Finset (J × I)) : ℝ :=
  (univ.filter (RespFeasible inst σ LI)).sup' ⟨fun _ _ => ∅, by
    simp [RespFeasible, arrived]⟩ (fun ρ => (matchCount ρ LJ : ℝ))

/-- Like outcomes are subsets of `(I × J) ⊕ (J × I)`. `inl (i, j)` means `i` likes `j`;
`inr (j, i)` means `j` likes `i`. -/
def likeProb (inst : Instance I J) : (I × J) ⊕ (J × I) → ℝ
  | .inl (i, j) => inst.pIJ i j
  | .inr (j, i) => inst.pJI j i

/-- The `I`-side likes in an outcome. -/
def LIof (S : Finset ((I × J) ⊕ (J × I))) : Finset (I × J) :=
  univ.filter fun e => Sum.inl e ∈ S

/-- The `J`-side likes in an outcome. -/
def LJof (S : Finset ((I × J) ⊕ (J × I))) : Finset (J × I) :=
  univ.filter fun e => Sum.inr e ∈ S

end OneDirSeq

open OneDirSeq

/-- The counterexample instance: `T = 2`, all caps 1, `j2` reciprocates with
probability `1 - δ`. Responders are `0 = j1` and `1 = j2`. -/
noncomputable def thm54Instance (δ : ℝ) : Instance (Fin 2) (Fin 2) where
  T := 2
  KI := fun _ => 1
  KJ := fun _ => 1
  pIJ := fun _ _ => 1
  pJI := fun j _ => if j = 0 then 1 else 1 - δ

/-- Two distinct independent coins are both included with probability `p a * p b`. -/
theorem indepExp_mem_and {α : Type*} [DecidableEq α] {U : Finset α} {a b : α}
    (ha : a ∈ U) (hb : b ∈ U) (hab : a ≠ b) (p : α → ℝ) :
    indepExp U p (fun S => if a ∈ S ∧ b ∈ S then 1 else 0) = p a * p b := by
  conv_lhs => rw [← Finset.insert_erase ha]
  rw [indepExp_insert (Finset.notMem_erase a U)]
  have h1 : indepExp (U.erase a) p (fun S => if a ∈ S ∧ b ∈ S then 1 else 0) = 0 := by
    rw [indepExp_congr (h := fun _ => 0), indepExp_const]
    intro S hS
    have : a ∉ S := fun h => Finset.notMem_erase a U (hS h)
    simp [this]
  have h2 : indepExp (U.erase a) p
      (fun S => if a ∈ insert a S ∧ b ∈ insert a S then 1 else 0) = p b := by
    rw [← indepExp_mem (Finset.mem_erase.mpr ⟨hab.symm, hb⟩) p]
    apply indepExp_congr
    intro S _
    simp [Finset.mem_insert, hab.symm]
  rw [h1, h2]
  ring

/-- Part 1 of the counterexample: `x ≡ 1` is the unique LP (41) optimum in `x`. -/
theorem thm54_part1 :
    ∃ y, LPFeasible (thm54Instance (1 / 100)) (fun _ _ => 1) y ∧
      ∀ x' y', LPFeasible (thm54Instance (1 / 100)) x' y' →
        LPObj (thm54Instance (1 / 100)) y' ≤ LPObj (thm54Instance (1 / 100)) y ∧
        (LPObj (thm54Instance (1 / 100)) y' = LPObj (thm54Instance (1 / 100)) y →
          ∀ i j, x' i j = 1) := by
  have hobj : ∀ y : Fin 2 → Fin 2 → ℝ, LPObj (thm54Instance (1 / 100)) y =
      y 0 0 + y 1 0 * (99 / 100) + (y 0 1 + y 1 1 * (99 / 100)) := by
    intro y
    simp [LPObj, thm54Instance, Fin.sum_univ_two]
    norm_num
  refine ⟨fun _ _ => 1, ?_, ?_⟩
  · refine ⟨fun _ _ => by norm_num, fun _ _ => by norm_num, fun _ _ => by simp [thm54Instance],
      fun _ => ?_, fun _ => ?_⟩ <;>
      simp [thm54Instance]
  · rintro x' y' ⟨hx, hy, hxy, -, -⟩
    rw [hobj, hobj]
    have hxy' : ∀ i j, y' j i ≤ x' i j := fun i j => by
      have := hxy i j
      simpa [thm54Instance] using this
    have h00 := (hy 0 0).2
    have h01 := (hy 0 1).2
    have h10 := (hy 1 0).2
    have h11 := (hy 1 1).2
    refine ⟨by linarith, fun heq i j => ?_⟩
    have hy00 : y' 0 0 = 1 := by linarith
    have hy01 : y' 0 1 = 1 := by linarith
    have hy10 : y' 1 0 = 1 := by linarith
    have hy11 : y' 1 1 = 1 := by linarith
    have hle := (hx i j).2
    have hge := hxy' i j
    fin_cases i <;> fin_cases j <;> simp_all <;> linarith

/-- Like probabilities of the counterexample lie in `[0, 1]`. -/
theorem thm54_likeProb_mem :
    ∀ e ∈ (univ : Finset ((Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2))),
      0 ≤ likeProb (thm54Instance (1 / 100)) e ∧ likeProb (thm54Instance (1 / 100)) e ≤ 1 := by
  rintro (⟨i, j⟩ | ⟨j, i⟩) -
  · simp [likeProb, thm54Instance]
  · simp only [likeProb, thm54Instance]
    split_ifs <;> norm_num

/-- In every DHT schedule for `x ≡ 1`, responder `1` is not shown in period 0. -/
theorem thm54_dht_not_one (σ : Fin 2 → Fin 2 → Finset (Fin 2))
    (hσ : IsDHTSchedule (thm54Instance (1 / 100)) (fun _ _ => 1) σ) (i : Fin 2) :
    (1 : Fin 2) ∉ σ 0 i := by
  obtain ⟨hU, hcard, -, -, hord⟩ := hσ
  have hU' : (univ.biUnion fun t : Fin 2 => σ t i) =
      univ.filter (fun _ : Fin 2 => (1 : ℝ) = 1) := hU i
  have hcard' : (σ 0 i).card ≤ 1 := hcard (0 : Fin 2) i
  have hord' : ∀ j j' : Fin 2, j ∈ σ 0 i → j' ∈ σ 1 i →
      (if j' = 0 then (1 : ℝ) else 1 - 1 / 100) ≤ (if j = 0 then 1 else 1 - 1 / 100) :=
    fun j j' => hord i (0 : Fin 2) (1 : Fin 2) j j' (by decide)
  intro h1
  have h0 : (0 : Fin 2) ∈ univ.biUnion fun t : Fin 2 => σ t i := by
    rw [hU']
    simp
  obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.mp h0
  fin_cases t
  · exact absurd (Finset.card_le_one.mp hcard' _ ht _ h1) (by decide)
  · have := hord' 1 0 h1 ht
    norm_num at this

/-- If responder `1` is never shown in period 0, every feasible response plan yields at
most one match. -/
theorem thm54_resp_le (σ : Fin 2 → Fin 2 → Finset (Fin 2)) (hσ : ∀ i, (1 : Fin 2) ∉ σ 0 i)
    (LI LJ : Finset (Fin 2 × Fin 2)) (ρ : Fin 2 → Fin 2 → Finset (Fin 2))
    (hρ : RespFeasible (thm54Instance (1 / 100)) σ LI ρ) : matchCount ρ LJ ≤ 1 := by
  have hsub : ∀ t j : Fin 2, ρ t j ⊆ (univ : Finset (Fin 2)).filter
      (fun i => ∃ s : Fin 2, s < t ∧ j ∈ σ s i ∧ (i, j) ∈ LI) ∧ (ρ t j).card ≤ 1 := hρ.1
  have h0 : ∀ j, ρ 0 j = ∅ := by
    intro j
    apply Finset.subset_empty.mp
    refine (hsub 0 j).1.trans ?_
    intro i hi
    simp at hi
  have h11 : ρ 1 1 = ∅ := by
    apply Finset.subset_empty.mp
    refine (hsub 1 1).1.trans ?_
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨s, hs, h1, -⟩ := hi
    fin_cases s
    · exact absurd h1 (hσ i)
    · exact absurd hs (by decide)
  have hc := (hsub 1 0).2
  unfold matchCount
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [h0, h11, Finset.filter_empty, Finset.card_empty, zero_add, add_zero]
  exact (Finset.card_filter_le _ _).trans hc

/-- Part 2 of the counterexample: every DHT schedule for `x ≡ 1` yields at most one
expected match, even with clairvoyant responders. -/
theorem thm54_part2 (σ : Fin 2 → Fin 2 → Finset (Fin 2))
    (hσ : IsDHTSchedule (thm54Instance (1 / 100)) (fun _ _ => 1) σ) :
    indepExp univ (likeProb (thm54Instance (1 / 100)))
      (fun S => bestResponse (thm54Instance (1 / 100)) σ (LIof S) (LJof S)) ≤ 1 := by
  have hnot := thm54_dht_not_one σ hσ
  calc _ ≤ indepExp univ (likeProb (thm54Instance (1 / 100))) (fun _ => 1) := by
        apply indepExp_mono thm54_likeProb_mem
        intro S _
        unfold bestResponse
        apply Finset.sup'_le
        intro ρ hρ
        simp only [Finset.mem_filter] at hρ
        have := thm54_resp_le σ hnot (LIof S) (LJof S) ρ hρ.2
        exact_mod_cast this
    _ = 1 := indepExp_const _ _ _

/-- The alternative schedule: initiator `k` is shown responder `k` in period 0. -/
def thm54AltSched : Fin 2 → Fin 2 → Finset (Fin 2) := fun t i => if t = 0 then {i} else ∅

/-- The alternative responses: in period 1, responder `j` answers initiator `j` if liked. -/
def thm54AltRule (LI : Finset (Fin 2 × Fin 2)) : Fin 2 → Fin 2 → Finset (Fin 2) :=
  fun t j => if t = 0 then ∅ else if (j, j) ∈ LI then {j} else ∅

/-- The alternative schedule is feasible. -/
theorem thm54AltSched_feasible :
    ScheduleFeasible (thm54Instance (1 / 100)) thm54AltSched := by
  have h : (∀ (t i : Fin 2), (thm54AltSched t i).card ≤ 1) ∧
      (∀ (i t t' j : Fin 2), j ∈ thm54AltSched t i → j ∈ thm54AltSched t' i → t = t') := by
    refine ⟨fun t i => ?_, fun i t t' j h h' => ?_⟩
    · unfold thm54AltSched
      split_ifs <;> simp
    · fin_cases t <;> fin_cases t' <;> simp_all [thm54AltSched]
  exact h

/-- The alternative responses are feasible for every realization of `I`-side likes. -/
theorem thm54AltRule_feasible (LI : Finset (Fin 2 × Fin 2)) :
    RespFeasible (thm54Instance (1 / 100)) thm54AltSched LI (thm54AltRule LI) := by
  have h : (∀ t j : Fin 2, thm54AltRule LI t j ⊆ (univ : Finset (Fin 2)).filter
      (fun i => ∃ s : Fin 2, s < t ∧ j ∈ thm54AltSched s i ∧ (i, j) ∈ LI) ∧
        (thm54AltRule LI t j).card ≤ 1) ∧
      (∀ (t t' j i : Fin 2), i ∈ thm54AltRule LI t j → i ∈ thm54AltRule LI t' j →
        t = t') := by
    refine ⟨fun t j => ⟨?_, ?_⟩, fun t t' j i h h' => ?_⟩
    · intro i hi
      unfold thm54AltRule at hi
      split_ifs at hi with ht hj
      · simp at hi
      · rw [Finset.mem_singleton] at hi
        subst hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨0, by omega, by simp [thm54AltSched], hj⟩
      · simp at hi
    · unfold thm54AltRule
      split_ifs <;> simp
    · fin_cases t <;> fin_cases t' <;> simp_all [thm54AltRule]
  exact h

/-- The alternative's match count: one match per `j` with `(j, j)` liked both ways. -/
theorem thm54AltRule_matchCount (LI LJ : Finset (Fin 2 × Fin 2)) :
    (matchCount (thm54AltRule LI) LJ : ℝ) =
      ∑ j : Fin 2, if (j, j) ∈ LI ∧ (j, j) ∈ LJ then 1 else 0 := by
  have hj : ∀ j : Fin 2, ((((if (j, j) ∈ LI then {j} else ∅ : Finset (Fin 2)).filter
      fun i => (j, i) ∈ LJ).card : ℕ) : ℝ) = if (j, j) ∈ LI ∧ (j, j) ∈ LJ then 1 else 0 := by
    intro j
    by_cases h1 : (j, j) ∈ LI <;> by_cases h2 : (j, j) ∈ LJ <;>
      simp [h1, h2, Finset.filter_singleton]
  unfold matchCount
  push_cast
  rw [Fin.sum_univ_two (fun t => ∑ j : Fin 2, _)]
  simp only [thm54AltRule, ↓reduceIte, Finset.filter_empty, Finset.card_empty,
    Nat.cast_zero, Finset.sum_const_zero, zero_add, one_ne_zero]
  exact Finset.sum_congr rfl fun j _ => hj j

/-- Part 3 of the counterexample: the alternative policy earns `2 - δ` expected matches. -/
theorem thm54_part3 :
    indepExp univ (likeProb (thm54Instance (1 / 100)))
      (fun S => (matchCount (thm54AltRule (LIof S)) (LJof S) : ℝ)) = 2 - 1 / 100 := by
  rw [indepExp_congr (h := fun S => ∑ j : Fin 2,
      if Sum.inl (j, j) ∈ S ∧ Sum.inr (j, j) ∈ S then 1 else 0)]
  · rw [indepExp_sum, Fin.sum_univ_two,
      indepExp_mem_and (mem_univ _) (mem_univ _) Sum.inl_ne_inr,
      indepExp_mem_and (mem_univ _) (mem_univ _) Sum.inl_ne_inr]
    simp [likeProb, thm54Instance]
    norm_num
  · intro S _
    rw [thm54AltRule_matchCount]
    simp [LIof, LJof]

/-- Part 4 of the counterexample: `1 < (1 - 1/e)(2 - 1/100)`. -/
theorem thm54_numeric : 1 < (1 - Real.exp (-1)) * (2 - 1 / 100) := by
  have he := Real.exp_one_gt_d9
  have hpos := Real.exp_pos 1
  have hinv : (Real.exp 1)⁻¹ < 2 / 5 := by
    rw [inv_lt_comm₀ hpos (by norm_num)]
    norm_num
    linarith
  rw [Real.exp_neg]
  nlinarith

/-- **Theorem 5.4 fails (Rios & Torrico).** With `δ = 1/100`:
1. LP (41) has a unique optimum in `x`: every initiator initiates toward both
   responders (`x ≡ 1`).
2. Every DHT schedule for `x ≡ 1` yields at most 1 expected match, even with
   clairvoyant responders.
3. Another schedule, whose responders answer only whoever liked them, yields
   `2 - δ`.
4. `1 < (1 - 1/e)(2 - δ)`.

Together, the policy of Theorem 5.4 earns less than `(1 - 1/e)` times a policy that the
benchmark (the best adaptive policy) can only beat. -/
theorem theorem_5_4_counterexample :
    let δ : ℝ := 1 / 100
    let inst := thm54Instance δ
    (∃ y, LPFeasible inst (fun _ _ => 1) y ∧
      ∀ x' y', LPFeasible inst x' y' → LPObj inst y' ≤ LPObj inst y ∧
        (LPObj inst y' = LPObj inst y → ∀ i j, x' i j = 1)) ∧
    (∀ σ, IsDHTSchedule inst (fun _ _ => 1) σ →
      indepExp univ (likeProb inst) (fun S => bestResponse inst σ (LIof S) (LJof S)) ≤ 1) ∧
    (∃ (σ : Schedule (Fin 2) (Fin 2) inst.T)
        (rule : Finset (Fin 2 × Fin 2) → Fin inst.T → Fin 2 → Finset (Fin 2)),
      ScheduleFeasible inst σ ∧ (∀ LI, RespFeasible inst σ LI (rule LI)) ∧
      indepExp univ (likeProb inst)
        (fun S => (matchCount (rule (LIof S)) (LJof S) : ℝ)) = 2 - δ) ∧
    1 < (1 - Real.exp (-1)) * (2 - δ) := by
  intro δ inst
  exact ⟨thm54_part1, fun σ hσ => thm54_part2 σ hσ,
    ⟨thm54AltSched, thm54AltRule, thm54AltSched_feasible, thm54AltRule_feasible,
      thm54_part3⟩, thm54_numeric⟩

end DatingAlgo
