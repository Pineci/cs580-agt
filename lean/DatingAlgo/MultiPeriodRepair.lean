import DatingAlgo.MultiPeriodDHT
import DatingAlgo.GreedyGap

/-!
# Theorem 5.3 repaired: the time-indexed relaxation R2 and DHT-τ

Rios & Torrico's Theorem 5.3 is false as stated (`MultiPeriodDHT.lean`). The vault note
"Counterexamples to the Multi-Period Dating Heuristic Guarantees", section "Repairing the
relaxation", item R2, proposes a repair. This file proves it.

## The repair
- **R2** is a time-indexed version of relaxation (19). It has binary `x^t_{ℓℓ'}` and `w^t_e`
  with `w^T = 0`, and `y^t_{ℓℓ'} ∈ [0, 1]`. It maximizes
  `∑_{t,e} β_e w^t_e + ∑_{t,ℓ,ℓ'} φ_{ℓℓ'} y^t_{ℓℓ'}` subject to:
  - `∑_{s ≤ t} y^s_{ℓℓ'} ≤ φ_{ℓ'ℓ} ∑_{s < t} x^s_{ℓ'ℓ}`: answer only likes received earlier;
  - `∑_t (x^t_{ℓℓ'} + x^t_{ℓ'ℓ} + w^t_e) ≤ 1`: each pair is shown at most one way;
  - `∑_{ℓ'} (x^t_{ℓℓ'} + y^t_{ℓℓ'}) + ∑_{e ∋ ℓ} w^t_e ≤ K_ℓ` for every user and period.
- **DHT-τ** takes an optimal solution of R2. It shows each initiation and mutual view in the
  period the solution chose. In every period it then fills each user's free slots from the
  backlog, best available profiles first.

## Main result (`theorem_5_3_repair`)
For every design, every optimal solution of R2 and every tie-breaking:
1. DHT-τ is a feasible semi-adaptive policy whose responses use only the backlog.
2. `E[matches of DHT-τ] ≥ (1 - 1/e) · R2`.
3. `R2 ≥ E[matches]` of every feasible semi-adaptive policy.

So DHT-τ is a `(1 - 1/e)`-approximation against the best semi-adaptive policy
(`dhtTau_approx`).

Two further results:
- Item 2 holds for every *feasible* solution of R2, optimal or not (`dhtTau_ge`).
- R2 has an optimal solution whenever it has a feasible one (`exists_isOptR2`), for example
  whenever the design allows showing nothing (`exists_isOptR2_of_empty`). So the main
  theorem's hypothesis can be met.

## Proof
- **An exact identity** (`expected_matches_eq`). Fix a feasible semi-adaptive policy. Let
  `y^t_{ℓℓ'}` be the probability that `ℓ` answers `ℓ'` from its backlog in period `t`. Then the
  expected number of matches equals R2's objective at the policy's schedule and these `y`.
  This uses that each pair is shown at most one way, and that whether `ℓ` is shown `ℓ'` does
  not depend on whether `ℓ` likes `ℓ'` (`RespBlind`).
- **Upper bound.** These `y` satisfy R2's constraints (`policySol_feasible`). So
  `R2 ≥ E[matches]` for every semi-adaptive policy.
- **Lower bound.** Apply the identity to DHT-τ. For each user, R2's response variables form a
  fractional response plan in the sense of `GreedyGap.lean`. So greedy's response value is at
  least `(1 - 1/e)` times R2's response value for that user (`greedy_correlation_gap`).

## Modeling
- **Binary variables as sets.** A solution's binary variables are a `Schedule`:
  - `x^t_{ij} = 1` iff `j ∈ sched.initI t i`, and `x^t_{ji} = 1` iff `i ∈ sched.initJ t j`;
  - `w^t_{ij} = 1` iff `j ∈ sched.mutI t i`.
- **Designs.** A design is any predicate on schedules, imposed on both R2 and the policies.
  - One-directional: `initJ = ∅`.
  - Sequential-only: `mutI = ∅`.
  - The results hold for every design.
- **Semi-adaptive policies.** A policy fixes its schedule in advance (`SchedFeasible`), with
  the paper's rule that each pair is shown at most one way. Its responses may depend on
  everything observed (`RespBlind`). The only requirement is that whether `i` is shown `j`
  does not depend on whether `i` likes `j`, which `i` reveals only on seeing `j`. Every
  non-anticipating policy has this property, and so does every rule that uses only the
  backlog (`backlogResp_blind`).
- **Like probabilities** are in `[0, 1]` and do not change over time (Section 5's assumption).
-/

namespace DatingAlgo

open Finset

namespace TwoDir

open OneDirSeq (Instance likeProb LIof LJof)

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-! ### Definitions -/

/-- How many ways the pair `(i, j)` is shown over the horizon: the left side of R2's edge
constraint, `∑_t (x^t_{ij} + x^t_{ji} + w^t_{ij})`. -/
def edgeUse {T : ℕ} (σ : Schedule I J T) (i : I) (j : J) : ℕ :=
  ∑ t, ((if j ∈ σ.initI t i then 1 else 0) + (if i ∈ σ.initJ t j then 1 else 0) +
    (if j ∈ σ.mutI t i then 1 else 0))

/-- A feasible non-adaptive part of a semi-adaptive policy (Definition 5.1), in the paper's
model:
- the design allows it;
- each pair is shown at most one way;
- no mutual views in the last period (Section 5's assumption);
- at most `K_ℓ` initiations and mutual views per user and period. -/
structure SchedFeasible (inst : Instance I J) (design : Schedule I J inst.T → Prop)
    (σ : Schedule I J inst.T) : Prop where
  design : design σ
  edge : ∀ i j, edgeUse σ i j ≤ 1
  mutI_last : ∀ t : Fin inst.T, (t : ℕ) + 1 = inst.T → ∀ i, σ.mutI t i = ∅
  capI : ∀ t i, (σ.initI t i ∪ σ.mutI t i).card ≤ inst.KI i
  capJ : ∀ t j, (σ.initJ t j ∪ σ.mutJ t j).card ≤ inst.KJ j

/-- A candidate solution of R2. The binary variables are encoded by a schedule:
`x^t_{ij} = 1` iff `j ∈ sched.initI t i`, `x^t_{ji} = 1` iff `i ∈ sched.initJ t j`, and
`w^t_{ij} = 1` iff `j ∈ sched.mutI t i`. The fractional variables are
`yI t i j = y^t_{ij}` and `yJ t j i = y^t_{ji}`. -/
structure SolR2 (I J : Type*) (T : ℕ) where
  sched : Schedule I J T
  yI : Fin T → I → J → ℝ
  yJ : Fin T → J → I → ℝ

/-- Feasibility in R2 (vault note, "Repairing the relaxation", R2), for a design:
- `w^T = 0` and `y^t ∈ [0, 1]`;
- `∑_{s ≤ t} y^s_{ℓℓ'} ≤ φ_{ℓ'ℓ} ∑_{s < t} x^s_{ℓ'ℓ}`;
- `∑_t (x^t_{ℓℓ'} + x^t_{ℓ'ℓ} + w^t_e) ≤ 1`;
- `∑_{ℓ'} (x^t_{ℓℓ'} + y^t_{ℓℓ'}) + ∑_{e ∋ ℓ} w^t_e ≤ K_ℓ` for every `ℓ` and `t`. -/
structure FeasibleR2 (inst : Instance I J) (design : Schedule I J inst.T → Prop)
    (s : SolR2 I J inst.T) : Prop where
  design : design s.sched
  edge : ∀ i j, edgeUse s.sched i j ≤ 1
  mutI_last : ∀ t : Fin inst.T, (t : ℕ) + 1 = inst.T → ∀ i, s.sched.mutI t i = ∅
  yI_mem : ∀ t i j, 0 ≤ s.yI t i j ∧ s.yI t i j ≤ 1
  yJ_mem : ∀ t j i, 0 ≤ s.yJ t j i ∧ s.yJ t j i ≤ 1
  cumI : ∀ t i j, ∑ u ∈ univ.filter (· ≤ t), s.yI u i j ≤
    inst.pJI j i * ∑ u ∈ univ.filter (· < t), (if i ∈ s.sched.initJ u j then (1 : ℝ) else 0)
  cumJ : ∀ t j i, ∑ u ∈ univ.filter (· ≤ t), s.yJ u j i ≤
    inst.pIJ i j * ∑ u ∈ univ.filter (· < t), (if j ∈ s.sched.initI u i then (1 : ℝ) else 0)
  capI : ∀ t i, ((s.sched.initI t i).card : ℝ) + (s.sched.mutI t i).card + ∑ j, s.yI t i j ≤
    inst.KI i
  capJ : ∀ t j, ((s.sched.initJ t j).card : ℝ) + (s.sched.mutJ t j).card + ∑ i, s.yJ t j i ≤
    inst.KJ j

/-- R2's objective: `∑_{t,e} β_e w^t_e + ∑_{t,ℓ,ℓ'} φ_{ℓℓ'} y^t_{ℓℓ'}`, with
`β_{ij} = φ_{ij} φ_{ji}`. -/
noncomputable def objR2 (inst : Instance I J) (s : SolR2 I J inst.T) : ℝ :=
  ∑ t, ∑ i, ∑ j, ((if j ∈ s.sched.mutI t i then inst.pIJ i j * inst.pJI j i else 0) +
    s.yI t i j * inst.pIJ i j + s.yJ t j i * inst.pJI j i)

/-- An optimal solution of R2. -/
def IsOptR2 (inst : Instance I J) (design : Schedule I J inst.T → Prop)
    (s : SolR2 I J inst.T) : Prop :=
  FeasibleR2 inst design s ∧ ∀ s', FeasibleR2 inst design s' → objR2 inst s' ≤ objR2 inst s

/-- Responses that never anticipate a like: whether `i` is shown `j` from its backlog in
period `t` does not depend on whether `i` likes `j`. That like is revealed only once `i` sees
`j`, so every non-anticipating policy has this property. `rule S` gives the responses when the
like outcome is `S`. -/
def RespBlind {T : ℕ} (rule : Finset ((I × J) ⊕ (J × I)) → Response I J T) : Prop :=
  (∀ S t i j, j ∈ (rule (insert (Sum.inl (i, j)) S)).respI t i ↔
      j ∈ (rule (S.erase (Sum.inl (i, j)))).respI t i) ∧
  (∀ S t j i, i ∈ (rule (insert (Sum.inr (j, i)) S)).respJ t j ↔
      i ∈ (rule (S.erase (Sum.inr (j, i)))).respJ t j)

/-- Profiles that initiate toward `i` before period `n`. -/
def releasedI {T : ℕ} (σ : Schedule I J T) (i : I) (n : ℕ) : Finset J :=
  univ.filter fun j => ∃ s : Fin T, (s : ℕ) < n ∧ i ∈ σ.initJ s j

/-- Profiles that initiate toward `j` before period `n`. -/
def releasedJ {T : ℕ} (σ : Schedule I J T) (j : J) (n : ℕ) : Finset I :=
  univ.filter fun i => ∃ s : Fin T, (s : ℕ) < n ∧ j ∈ σ.initI s i

/-- `i`'s free slots in period `n`, after its initiations and mutual views. -/
def freeI (inst : Instance I J) (σ : Schedule I J inst.T) (i : I) (n : ℕ) : ℕ :=
  if h : n < inst.T then inst.KI i - (σ.initI ⟨n, h⟩ i).card - (σ.mutI ⟨n, h⟩ i).card else 0

/-- `j`'s free slots in period `n`, after its initiations and mutual views. -/
def freeJ (inst : Instance I J) (σ : Schedule I J inst.T) (j : J) (n : ℕ) : ℕ :=
  if h : n < inst.T then inst.KJ j - (σ.initJ ⟨n, h⟩ j).card - (σ.mutJ ⟨n, h⟩ j).card else 0

/-- **DHT-τ's responses.** Each user answers greedily from the backlog, using only what has
arrived (`backlogResp`). In period `t`, user `i` fills its free slots with a best set of
waiting profiles: `selI i k B` is a best set of at most `k` profiles of `B`, by `i`'s like
probability (`IsTopSel`). -/
def dhtTauResp (inst : Instance I J) (σ : Schedule I J inst.T)
    (selI : I → ℕ → Finset J → Finset J) (selJ : J → ℕ → Finset I → Finset I)
    (LI : Finset (I × J)) (LJ : Finset (J × I)) : Response I J inst.T :=
  backlogResp (fun t i B => greedyPick (selI i) (freeI inst σ i) (releasedI σ i) B t)
    (fun t j B => greedyPick (selJ j) (freeJ inst σ j) (releasedJ σ j) B t) σ LI LJ

/-- `y^t_{ij}` of a policy: the probability that `i` answers `j` from its backlog in
period `t`. -/
noncomputable def respProbI (inst : Instance I J)
    (rule : Finset ((I × J) ⊕ (J × I)) → Response I J inst.T) (t : Fin inst.T) (i : I)
    (j : J) : ℝ :=
  indepExp univ (likeProb inst) (fun S => if j ∈ (rule S).respI t i then 1 else 0)

/-- `y^t_{ji}` of a policy. -/
noncomputable def respProbJ (inst : Instance I J)
    (rule : Finset ((I × J) ⊕ (J × I)) → Response I J inst.T) (t : Fin inst.T) (j : J)
    (i : I) : ℝ :=
  indepExp univ (likeProb inst) (fun S => if i ∈ (rule S).respJ t j then 1 else 0)

/-- The R2 solution induced by a semi-adaptive policy: its schedule, and its response
probabilities as `y`. -/
noncomputable def policySol (inst : Instance I J) (σ : Schedule I J inst.T)
    (rule : Finset ((I × J) ⊕ (J × I)) → Response I J inst.T) : SolR2 I J inst.T :=
  ⟨σ, respProbI inst rule, respProbJ inst rule⟩

/-- Expected matches of a semi-adaptive policy. -/
noncomputable def expMatches (inst : Instance I J) (σ : Schedule I J inst.T)
    (rule : Finset ((I × J) ⊕ (J × I)) → Response I J inst.T) : ℝ :=
  indepExp univ (likeProb inst) (fun S => (matchCount σ (rule S) (LIof S) (LJof S) : ℝ))


/-! ### The edge constraint: each pair is shown at most one way -/

/-- The ways `(i, j)` is shown: `(t, 0)` if `i` initiates toward `j` in period `t`, `(t, 1)`
if `j` initiates toward `i`, and `(t, 2)` for a mutual view. -/
def edgeUses {T : ℕ} (σ : Schedule I J T) (i : I) (j : J) : Finset (Fin T × Fin 3) :=
  univ.filter fun tk => (tk.2 = 0 ∧ j ∈ σ.initI tk.1 i) ∨ (tk.2 = 1 ∧ i ∈ σ.initJ tk.1 j) ∨
    (tk.2 = 2 ∧ j ∈ σ.mutI tk.1 i)

omit [Fintype I] [Fintype J] in
theorem edgeUse_eq_card {T : ℕ} (σ : Schedule I J T) (i : I) (j : J) :
    edgeUse σ i j = (edgeUses σ i j).card := by
  rw [edgeUses, Finset.card_filter, Fintype.sum_prod_type, edgeUse]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fin.sum_univ_three]
  simp

section Edge

variable {T : ℕ} {σ : Schedule I J T} {i : I} {j : J}

omit [Fintype I] [Fintype J]

theorem edgeUses_eq (h : edgeUse σ i j ≤ 1) {x y : Fin T × Fin 3} (hx : x ∈ edgeUses σ i j)
    (hy : y ∈ edgeUses σ i j) : x = y := by
  rw [edgeUse_eq_card] at h
  exact Finset.card_le_one.mp h x hx y hy

theorem mem_edgeUses_initI {t : Fin T} (h : j ∈ σ.initI t i) : (t, 0) ∈ edgeUses σ i j := by
  simp [edgeUses, h]

theorem mem_edgeUses_initJ {t : Fin T} (h : i ∈ σ.initJ t j) : (t, 1) ∈ edgeUses σ i j := by
  simp [edgeUses, h]

theorem mem_edgeUses_mutI {t : Fin T} (h : j ∈ σ.mutI t i) : (t, 2) ∈ edgeUses σ i j := by
  simp [edgeUses, h]

theorem edge_initI_initJ (h : edgeUse σ i j ≤ 1) {t t' : Fin T} (h1 : j ∈ σ.initI t i)
    (h2 : i ∈ σ.initJ t' j) : False := by
  have := edgeUses_eq h (mem_edgeUses_initI h1) (mem_edgeUses_initJ h2)
  simp at this

theorem edge_initI_mutI (h : edgeUse σ i j ≤ 1) {t t' : Fin T} (h1 : j ∈ σ.initI t i)
    (h2 : j ∈ σ.mutI t' i) : False := by
  have := edgeUses_eq h (mem_edgeUses_initI h1) (mem_edgeUses_mutI h2)
  simp at this

theorem edge_initJ_mutI (h : edgeUse σ i j ≤ 1) {t t' : Fin T} (h1 : i ∈ σ.initJ t j)
    (h2 : j ∈ σ.mutI t' i) : False := by
  have := edgeUses_eq h (mem_edgeUses_initJ h1) (mem_edgeUses_mutI h2)
  simp at this

theorem edge_mutI_unique (h : edgeUse σ i j ≤ 1) {t t' : Fin T} (h1 : j ∈ σ.mutI t i)
    (h2 : j ∈ σ.mutI t' i) : t = t' := by
  have := edgeUses_eq h (mem_edgeUses_mutI h1) (mem_edgeUses_mutI h2)
  simpa using this

theorem edge_initI_unique (h : edgeUse σ i j ≤ 1) {t t' : Fin T} (h1 : j ∈ σ.initI t i)
    (h2 : j ∈ σ.initI t' i) : t = t' := by
  have := edgeUses_eq h (mem_edgeUses_initI h1) (mem_edgeUses_initI h2)
  simpa using this

theorem edge_initJ_unique (h : edgeUse σ i j ≤ 1) {t t' : Fin T} (h1 : i ∈ σ.initJ t j)
    (h2 : i ∈ σ.initJ t' j) : t = t' := by
  have := edgeUses_eq h (mem_edgeUses_initJ h1) (mem_edgeUses_initJ h2)
  simpa using this

end Edge

omit [Fintype I] in
theorem mem_arrivedI {T : ℕ} {σ : Schedule I J T} {LJ : Finset (J × I)} {t : Fin T} {i : I}
    {j : J} : j ∈ arrivedI σ LJ t i ↔ ∃ s : Fin T, s < t ∧ i ∈ σ.initJ s j ∧ (j, i) ∈ LJ := by
  simp [arrivedI]

omit [Fintype J] in
theorem mem_arrivedJ {T : ℕ} {σ : Schedule I J T} {LI : Finset (I × J)} {t : Fin T} {j : J}
    {i : I} : i ∈ arrivedJ σ LI t j ↔ ∃ s : Fin T, s < t ∧ j ∈ σ.initI s i ∧ (i, j) ∈ LI := by
  simp [arrivedJ]

/-- A sum of indicators of an event that holds for at most one index is the indicator that it
holds for some index. -/
theorem sum_ite_unique {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P]
    (h : ∀ t t', P t → P t' → t = t') :
    (∑ t, if P t then (1 : ℝ) else 0) = if ∃ t, P t then 1 else 0 := by
  split_ifs with hex
  · obtain ⟨t0, ht0⟩ := hex
    rw [Finset.sum_eq_single t0]
    · simp [ht0]
    · intro t _ ht
      simp [show ¬ P t from fun hP => ht (h t t0 hP ht0)]
    · simp
  · simp only [not_exists] at hex
    simp [hex]

/-- A sum of indicators of an event that holds for at most one index is at most 1. -/
theorem sum_ite_le_one {ι : Type*} (s : Finset ι) (P : ι → Prop) [DecidablePred P]
    (h : ∀ t t', P t → P t' → t = t') : (∑ t ∈ s, if P t then (1 : ℝ) else 0) ≤ 1 := by
  rw [Finset.sum_boole]
  exact_mod_cast Finset.card_le_one.mpr fun a ha b hb =>
    h a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2

/-! ### Matches of a feasible policy, pair by pair -/

/-- **Matches, pair by pair.** If each pair is shown at most one way and responses come from
the backlog, each at most once, then `(i, j)` match exactly when one of these happens:
- a mutual view that both like;
- `i` answers `j` and likes `j`;
- `j` answers `i` and likes `i`.

At most one of them can happen. -/
theorem match_pair_eq {T : ℕ} {σ : Schedule I J T} {ρ : Response I J T}
    {LI : Finset (I × J)} {LJ : Finset (J × I)} {i : I} {j : J} (hedge : edgeUse σ i j ≤ 1)
    (hsubI : ∀ t, ρ.respI t i ⊆ arrivedI σ LJ t i) (hsubJ : ∀ t, ρ.respJ t j ⊆ arrivedJ σ LI t j)
    (honceI : ∀ t t', j ∈ ρ.respI t i → j ∈ ρ.respI t' i → t = t')
    (honceJ : ∀ t t', i ∈ ρ.respJ t j → i ∈ ρ.respJ t' j → t = t') :
    (if j ∈ seenI σ ρ i ∧ i ∈ seenJ σ ρ j ∧ (i, j) ∈ LI ∧ (j, i) ∈ LJ then (1 : ℝ) else 0) =
      ∑ t, ((if j ∈ σ.mutI t i ∧ (i, j) ∈ LI ∧ (j, i) ∈ LJ then 1 else 0) +
        (if j ∈ ρ.respI t i ∧ (i, j) ∈ LI then 1 else 0) +
        (if i ∈ ρ.respJ t j ∧ (j, i) ∈ LJ then 1 else 0)) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_ite_unique _ (fun t t' h h' => edge_mutI_unique hedge h.1 h'.1),
    sum_ite_unique _ (fun t t' h h' => honceI t t' h.1 h'.1),
    sum_ite_unique _ (fun t t' h h' => honceJ t t' h.1 h'.1)]
  -- What a response implies about the schedule.
  have hRI : ∀ t, j ∈ ρ.respI t i → ∃ s, i ∈ σ.initJ s j ∧ (j, i) ∈ LJ := by
    intro t ht
    obtain ⟨s, _, hs, hl⟩ := mem_arrivedI.mp (hsubI t ht)
    exact ⟨s, hs, hl⟩
  have hRJ : ∀ t, i ∈ ρ.respJ t j → ∃ s, j ∈ σ.initI s i ∧ (i, j) ∈ LI := by
    intro t ht
    obtain ⟨s, _, hs, hl⟩ := mem_arrivedJ.mp (hsubJ t ht)
    exact ⟨s, hs, hl⟩
  -- The three events are exclusive.
  have hx1 : (∃ t, j ∈ σ.mutI t i ∧ (i, j) ∈ LI ∧ (j, i) ∈ LJ) →
      ¬ ∃ t, j ∈ ρ.respI t i ∧ (i, j) ∈ LI := by
    rintro ⟨t, hm, -⟩ ⟨t', hr, -⟩
    obtain ⟨s, hs, -⟩ := hRI t' hr
    exact edge_initJ_mutI hedge hs hm
  have hx2 : (∃ t, j ∈ σ.mutI t i ∧ (i, j) ∈ LI ∧ (j, i) ∈ LJ) →
      ¬ ∃ t, i ∈ ρ.respJ t j ∧ (j, i) ∈ LJ := by
    rintro ⟨t, hm, -⟩ ⟨t', hr, -⟩
    obtain ⟨s, hs, -⟩ := hRJ t' hr
    exact edge_initI_mutI hedge hs hm
  have hx3 : (∃ t, j ∈ ρ.respI t i ∧ (i, j) ∈ LI) → ¬ ∃ t, i ∈ ρ.respJ t j ∧ (j, i) ∈ LJ := by
    rintro ⟨t, hr, -⟩ ⟨t', hr', -⟩
    obtain ⟨s, hs, -⟩ := hRI t hr
    obtain ⟨s', hs', -⟩ := hRJ t' hr'
    exact edge_initI_initJ hedge hs' hs
  -- A match is one of the three events.
  have hiff : (j ∈ seenI σ ρ i ∧ i ∈ seenJ σ ρ j ∧ (i, j) ∈ LI ∧ (j, i) ∈ LJ) ↔
      ((∃ t, j ∈ σ.mutI t i ∧ (i, j) ∈ LI ∧ (j, i) ∈ LJ) ∨
        (∃ t, j ∈ ρ.respI t i ∧ (i, j) ∈ LI) ∨ (∃ t, i ∈ ρ.respJ t j ∧ (j, i) ∈ LJ)) := by
    simp only [seenI, seenJ, shownI, shownJ, Schedule.mutJ, Finset.mem_biUnion,
      Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨⟨t, (hI | hM) | hR⟩, ⟨t', (hJ | hM') | hR'⟩, hl, hl'⟩
      · exact absurd hJ fun h => edge_initI_initJ hedge hI h
      · exact absurd hM' fun h => edge_initI_mutI hedge hI h
      · exact Or.inr (Or.inr ⟨t', hR', hl'⟩)
      · exact Or.inl ⟨t, hM, hl, hl'⟩
      · exact Or.inl ⟨t, hM, hl, hl'⟩
      · exact Or.inl ⟨t, hM, hl, hl'⟩
      · exact Or.inr (Or.inl ⟨t, hR, hl⟩)
      · exact Or.inr (Or.inl ⟨t, hR, hl⟩)
      · exact Or.inr (Or.inl ⟨t, hR, hl⟩)
    · rintro (⟨t, hM, hl, hl'⟩ | ⟨t, hR, hl⟩ | ⟨t, hR, hl'⟩)
      · exact ⟨⟨t, Or.inl (Or.inr hM)⟩, ⟨t, Or.inl (Or.inr hM)⟩, hl, hl'⟩
      · obtain ⟨s, hs, hl'⟩ := hRI t hR
        exact ⟨⟨t, Or.inr hR⟩, ⟨s, Or.inl (Or.inl hs)⟩, hl, hl'⟩
      · obtain ⟨s, hs, hl⟩ := hRJ t hR
        exact ⟨⟨s, Or.inl (Or.inl hs)⟩, ⟨t, Or.inr hR⟩, hl, hl'⟩
  rw [if_congr hiff rfl rfl]
  by_cases h1 : ∃ t, j ∈ σ.mutI t i ∧ (i, j) ∈ LI ∧ (j, i) ∈ LJ
  · simp [h1, hx1 h1, hx2 h1]
  · by_cases h2 : ∃ t, j ∈ ρ.respI t i ∧ (i, j) ∈ LI
    · simp [h1, h2, hx3 h2]
    · simp [h1, h2]

/-- The number of matches of a feasible policy, written as R2's objective on one sample
path. -/
theorem matchCount_eq {T : ℕ} (σ : Schedule I J T) (ρ : Response I J T) (LI : Finset (I × J))
    (LJ : Finset (J × I)) (hedge : ∀ i j, edgeUse σ i j ≤ 1)
    (hsubI : ∀ t i, ρ.respI t i ⊆ arrivedI σ LJ t i)
    (hsubJ : ∀ t j, ρ.respJ t j ⊆ arrivedJ σ LI t j)
    (honceI : ∀ i j t t', j ∈ ρ.respI t i → j ∈ ρ.respI t' i → t = t')
    (honceJ : ∀ j i t t', i ∈ ρ.respJ t j → i ∈ ρ.respJ t' j → t = t') :
    (matchCount σ ρ LI LJ : ℝ) = ∑ i, ∑ j, ∑ t,
      ((if j ∈ σ.mutI t i ∧ (i, j) ∈ LI ∧ (j, i) ∈ LJ then 1 else 0) +
        (if j ∈ ρ.respI t i ∧ (i, j) ∈ LI then 1 else 0) +
        (if i ∈ ρ.respJ t j ∧ (j, i) ∈ LJ then 1 else 0)) := by
  unfold matchCount
  push_cast
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    match_pair_eq (hedge i j) (fun t => hsubI t i) (fun t => hsubJ t j) (honceI i j)
      (honceJ j i)

/-! ### Expected matches of a semi-adaptive policy equal R2's objective -/

omit [DecidableEq I] [DecidableEq J] in
/-- Reorder a triple sum over pairs and periods. -/
theorem sum_rotate {T : ℕ} (f : Fin T → I → J → ℝ) :
    ∑ i, ∑ j, ∑ t, f t i j = ∑ t, ∑ i, ∑ j, f t i j := by
  calc ∑ i, ∑ j, ∑ t, f t i j = ∑ i, ∑ t, ∑ j, f t i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ t, ∑ i, ∑ j, f t i j := Finset.sum_comm

omit [DecidableEq I] [DecidableEq J] in
theorem likeProb_mem {inst : Instance I J}
    (hp : ∀ i j, 0 ≤ inst.pIJ i j ∧ inst.pIJ i j ≤ 1 ∧ 0 ≤ inst.pJI j i ∧ inst.pJI j i ≤ 1) :
    ∀ e ∈ (univ : Finset ((I × J) ⊕ (J × I))), 0 ≤ likeProb inst e ∧ likeProb inst e ≤ 1 := by
  rintro (⟨i, j⟩ | ⟨j, i⟩) -
  · exact ⟨(hp i j).1, (hp i j).2.1⟩
  · exact ⟨(hp i j).2.2.1, (hp i j).2.2.2⟩

/-- Every response rule that uses only the backlog never anticipates a like. -/
theorem backlogResp_blind {T : ℕ} (fI : Fin T → I → Finset J → Finset J)
    (fJ : Fin T → J → Finset I → Finset I) (σ : Schedule I J T) :
    RespBlind (fun S => backlogResp fI fJ σ (LIof S) (LJof S)) := by
  have hLJ : ∀ (S : Finset ((I × J) ⊕ (J × I))) (x : I × J),
      LJof (insert (Sum.inl x) S) = LJof (S.erase (Sum.inl x)) := by
    intro S x; ext e; simp [LJof]
  have hLI : ∀ (S : Finset ((I × J) ⊕ (J × I))) (x : J × I),
      LIof (insert (Sum.inr x) S) = LIof (S.erase (Sum.inr x)) := by
    intro S x; ext e; simp [LIof]
  refine ⟨fun S t i j => ?_, fun S t j i => ?_⟩
  · simp only [backlogResp, hLJ]
  · simp only [backlogResp, hLI]

/-- **Expected matches equal R2's objective.** For a policy whose schedule shows each pair at
most one way, with feasible responses that never anticipate a like, the expected number of
matches is R2's objective at the policy's schedule and response probabilities. -/
theorem expected_matches_eq (inst : Instance I J) (σ : Schedule I J inst.T)
    (rule : Finset ((I × J) ⊕ (J × I)) → Response I J inst.T)
    (hedge : ∀ i j, edgeUse σ i j ≤ 1)
    (hrule : ∀ S, RespFeasible inst σ (LIof S) (LJof S) (rule S)) (hblind : RespBlind rule) :
    expMatches inst σ rule = objR2 inst (policySol inst σ rule) := by
  unfold expMatches
  rw [indepExp_congr (fun S _ => matchCount_eq σ (rule S) (LIof S) (LJof S) hedge
    (hrule S).subI (hrule S).subJ (hrule S).onceI (hrule S).onceJ)]
  rw [indepExp_sum]
  simp_rw [indepExp_sum, indepExp_add]
  -- The three expectations.
  have hM : ∀ t i j, indepExp univ (likeProb inst)
      (fun S => if j ∈ σ.mutI t i ∧ (i, j) ∈ LIof S ∧ (j, i) ∈ LJof S then (1 : ℝ) else 0) =
      if j ∈ σ.mutI t i then inst.pIJ i j * inst.pJI j i else 0 := by
    intro t i j
    by_cases hm : j ∈ σ.mutI t i
    · simp only [hm, true_and, ↓reduceIte, LIof, LJof, Finset.mem_filter, Finset.mem_univ]
      exact indepExp_mem_and (Finset.mem_univ _) (Finset.mem_univ _) Sum.inl_ne_inr _
    · simp only [hm, false_and, ↓reduceIte]
      exact indepExp_const _ _ _
  have hRI : ∀ t i j, indepExp univ (likeProb inst)
      (fun S => if j ∈ (rule S).respI t i ∧ (i, j) ∈ LIof S then (1 : ℝ) else 0) =
      respProbI inst rule t i j * inst.pIJ i j := by
    intro t i j
    have := indepExp_mul_mem_of_blind (Finset.mem_univ (Sum.inl (i, j))) (likeProb inst)
      (fun S => if j ∈ (rule S).respI t i then (1 : ℝ) else 0)
      (fun S => by simp only [hblind.1 S t i j])
    rw [mul_comm, show inst.pIJ i j = likeProb inst (Sum.inl (i, j)) from rfl, respProbI,
      ← this]
    apply indepExp_congr
    intro S _
    simp only [LIof, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> simp_all
  have hRJ : ∀ t i j, indepExp univ (likeProb inst)
      (fun S => if i ∈ (rule S).respJ t j ∧ (j, i) ∈ LJof S then (1 : ℝ) else 0) =
      respProbJ inst rule t j i * inst.pJI j i := by
    intro t i j
    have := indepExp_mul_mem_of_blind (Finset.mem_univ (Sum.inr (j, i))) (likeProb inst)
      (fun S => if i ∈ (rule S).respJ t j then (1 : ℝ) else 0)
      (fun S => by simp only [hblind.2 S t j i])
    rw [mul_comm, show inst.pJI j i = likeProb inst (Sum.inr (j, i)) from rfl, respProbJ,
      ← this]
    apply indepExp_congr
    intro S _
    simp only [LJof, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> simp_all
  simp_rw [hM, hRI, hRJ]
  exact sum_rotate _


/-! ### Upper bound: R2 bounds every semi-adaptive policy -/

theorem indepExp_ite_mem {inst : Instance I J}
    (hp : ∀ i j, 0 ≤ inst.pIJ i j ∧ inst.pIJ i j ≤ 1 ∧ 0 ≤ inst.pJI j i ∧ inst.pJI j i ≤ 1)
    (P : Finset ((I × J) ⊕ (J × I)) → Prop) [DecidablePred P] :
    0 ≤ indepExp univ (likeProb inst) (fun S => if P S then 1 else 0) ∧
      indepExp univ (likeProb inst) (fun S => if P S then 1 else 0) ≤ 1 := by
  constructor
  · calc (0 : ℝ) = indepExp univ (likeProb inst) (fun _ => 0) := (indepExp_const _ _ _).symm
      _ ≤ _ := indepExp_mono (likeProb_mem hp) fun S _ => by split_ifs <;> norm_num
  · calc _ ≤ indepExp univ (likeProb inst) (fun _ => 1) :=
          indepExp_mono (likeProb_mem hp) fun S _ => by split_ifs <;> norm_num
      _ = 1 := indepExp_const _ _ _

/-- **R2 is a relaxation (step 1 of the proof sketch).** A semi-adaptive policy's schedule,
with its response probabilities as `y`, is feasible in R2. -/
theorem policySol_feasible (inst : Instance I J)
    (hp : ∀ i j, 0 ≤ inst.pIJ i j ∧ inst.pIJ i j ≤ 1 ∧ 0 ≤ inst.pJI j i ∧ inst.pJI j i ≤ 1)
    (design : Schedule I J inst.T → Prop) (σ : Schedule I J inst.T)
    (rule : Finset ((I × J) ⊕ (J × I)) → Response I J inst.T)
    (hσ : SchedFeasible inst design σ)
    (hrule : ∀ S, RespFeasible inst σ (LIof S) (LJof S) (rule S)) :
    FeasibleR2 inst design (policySol inst σ rule) where
  design := hσ.design
  edge := hσ.edge
  mutI_last := hσ.mutI_last
  yI_mem t i j := indepExp_ite_mem hp _
  yJ_mem t j i := indepExp_ite_mem hp _
  cumI t i j := by
    show ∑ u ∈ univ.filter (· ≤ t), respProbI inst rule u i j ≤
      inst.pJI j i * ∑ u ∈ univ.filter (· < t), (if i ∈ σ.initJ u j then (1 : ℝ) else 0)
    set N := ∑ u ∈ univ.filter (· < t), (if i ∈ σ.initJ u j then (1 : ℝ) else 0)
    have hN0 : 0 ≤ N := Finset.sum_nonneg fun u _ => by split_ifs <;> norm_num
    have hR : inst.pJI j i * N = indepExp univ (likeProb inst)
        (fun S => N * if Sum.inr (j, i) ∈ S then 1 else 0) := by
      rw [indepExp_const_mul, indepExp_mem (Finset.mem_univ _)]
      simp only [likeProb]
      ring
    unfold respProbI
    rw [← indepExp_sum, hR]
    apply indepExp_mono (likeProb_mem hp)
    intro S _
    by_cases hex : ∃ u ∈ univ.filter (· ≤ t), j ∈ (rule S).respI u i
    · obtain ⟨u, hu, hj⟩ := hex
      obtain ⟨s, hsu, hs, hl⟩ := mem_arrivedI.mp ((hrule S).subI u i hj)
      have h1 := sum_ite_le_one (univ.filter (· ≤ t)) (fun u => j ∈ (rule S).respI u i)
        (fun a b ha hb => (hrule S).onceI i j a b ha hb)
      have hst : s ∈ univ.filter (· < t) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        exact lt_of_lt_of_le hsu hu
      have h2 : 1 ≤ N := by
        calc (1 : ℝ) = if i ∈ σ.initJ s j then (1 : ℝ) else 0 := by simp [hs]
          _ ≤ N := Finset.single_le_sum (f := fun u => if i ∈ σ.initJ u j then (1 : ℝ) else 0)
              (fun _ _ => by split_ifs <;> norm_num) hst
      have h3 : Sum.inr (j, i) ∈ S := by simpa [LJof] using hl
      simp only [h3, ↓reduceIte, mul_one]
      linarith
    · have h0 : ∑ u ∈ univ.filter (· ≤ t), (if j ∈ (rule S).respI u i then (1 : ℝ) else 0) = 0 :=
        Finset.sum_eq_zero fun u hu => by
          simp only [show j ∉ (rule S).respI u i from fun h => hex ⟨u, hu, h⟩, ↓reduceIte]
      rw [h0]
      exact mul_nonneg hN0 (by split_ifs <;> norm_num)
  cumJ t j i := by
    show ∑ u ∈ univ.filter (· ≤ t), respProbJ inst rule u j i ≤
      inst.pIJ i j * ∑ u ∈ univ.filter (· < t), (if j ∈ σ.initI u i then (1 : ℝ) else 0)
    set N := ∑ u ∈ univ.filter (· < t), (if j ∈ σ.initI u i then (1 : ℝ) else 0)
    have hN0 : 0 ≤ N := Finset.sum_nonneg fun u _ => by split_ifs <;> norm_num
    have hR : inst.pIJ i j * N = indepExp univ (likeProb inst)
        (fun S => N * if Sum.inl (i, j) ∈ S then 1 else 0) := by
      rw [indepExp_const_mul, indepExp_mem (Finset.mem_univ _)]
      simp only [likeProb]
      ring
    unfold respProbJ
    rw [← indepExp_sum, hR]
    apply indepExp_mono (likeProb_mem hp)
    intro S _
    by_cases hex : ∃ u ∈ univ.filter (· ≤ t), i ∈ (rule S).respJ u j
    · obtain ⟨u, hu, hi⟩ := hex
      obtain ⟨s, hsu, hs, hl⟩ := mem_arrivedJ.mp ((hrule S).subJ u j hi)
      have h1 := sum_ite_le_one (univ.filter (· ≤ t)) (fun u => i ∈ (rule S).respJ u j)
        (fun a b ha hb => (hrule S).onceJ j i a b ha hb)
      have hst : s ∈ univ.filter (· < t) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
        exact lt_of_lt_of_le hsu hu
      have h2 : 1 ≤ N := by
        calc (1 : ℝ) = if j ∈ σ.initI s i then (1 : ℝ) else 0 := by simp [hs]
          _ ≤ N := Finset.single_le_sum (f := fun u => if j ∈ σ.initI u i then (1 : ℝ) else 0)
              (fun _ _ => by split_ifs <;> norm_num) hst
      have h3 : Sum.inl (i, j) ∈ S := by simpa [LIof] using hl
      simp only [h3, ↓reduceIte, mul_one]
      linarith
    · have h0 : ∑ u ∈ univ.filter (· ≤ t), (if i ∈ (rule S).respJ u j then (1 : ℝ) else 0) = 0 :=
        Finset.sum_eq_zero fun u hu => by
          simp only [show i ∉ (rule S).respJ u j from fun h => hex ⟨u, hu, h⟩, ↓reduceIte]
      rw [h0]
      exact mul_nonneg hN0 (by split_ifs <;> norm_num)
  capI t i := by
    show ((σ.initI t i).card : ℝ) + (σ.mutI t i).card + ∑ j, respProbI inst rule t i j ≤
      inst.KI i
    have hsum : ∑ j, respProbI inst rule t i j =
        indepExp univ (likeProb inst) (fun S => (((rule S).respI t i).card : ℝ)) := by
      unfold respProbI
      rw [← indepExp_sum]
      apply indepExp_congr
      intro S _
      rw [Finset.sum_boole]
      simp
    have hpt : ∀ S, ((((rule S).respI t i).card : ℕ) : ℝ) ≤
        (inst.KI i : ℝ) - (σ.initI t i).card - (σ.mutI t i).card := by
      intro S
      have hd1 : Disjoint (σ.initI t i) (σ.mutI t i) :=
        Finset.disjoint_left.mpr fun j h1 h2 => edge_initI_mutI (hσ.edge i j) h1 h2
      have hd2 : Disjoint (σ.initI t i ∪ σ.mutI t i) ((rule S).respI t i) := by
        apply Finset.disjoint_left.mpr
        intro j hj hr
        obtain ⟨s, -, hs, -⟩ := mem_arrivedI.mp ((hrule S).subI t i hr)
        rcases Finset.mem_union.mp hj with h | h
        · exact edge_initI_initJ (hσ.edge i j) h hs
        · exact edge_initJ_mutI (hσ.edge i j) hs h
      have hcap := (hrule S).capI t i
      rw [shownI, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1] at hcap
      have : (((σ.initI t i).card + (σ.mutI t i).card + ((rule S).respI t i).card : ℕ) : ℝ) ≤
          inst.KI i := by exact_mod_cast hcap
      push_cast at this
      linarith
    have hE : indepExp univ (likeProb inst) (fun S => (((rule S).respI t i).card : ℝ)) ≤
        (inst.KI i : ℝ) - (σ.initI t i).card - (σ.mutI t i).card := by
      calc _ ≤ indepExp univ (likeProb inst)
            (fun _ => (inst.KI i : ℝ) - (σ.initI t i).card - (σ.mutI t i).card) :=
            indepExp_mono (likeProb_mem hp) fun S _ => hpt S
        _ = _ := indepExp_const _ _ _
    rw [hsum]
    linarith
  capJ t j := by
    show ((σ.initJ t j).card : ℝ) + (σ.mutJ t j).card + ∑ i, respProbJ inst rule t j i ≤
      inst.KJ j
    have hsum : ∑ i, respProbJ inst rule t j i =
        indepExp univ (likeProb inst) (fun S => (((rule S).respJ t j).card : ℝ)) := by
      unfold respProbJ
      rw [← indepExp_sum]
      apply indepExp_congr
      intro S _
      rw [Finset.sum_boole]
      simp
    have hpt : ∀ S, ((((rule S).respJ t j).card : ℕ) : ℝ) ≤
        (inst.KJ j : ℝ) - (σ.initJ t j).card - (σ.mutJ t j).card := by
      intro S
      have hd1 : Disjoint (σ.initJ t j) (σ.mutJ t j) := by
        apply Finset.disjoint_left.mpr
        intro i h1 h2
        simp only [Schedule.mutJ, Finset.mem_filter, Finset.mem_univ, true_and] at h2
        exact edge_initJ_mutI (hσ.edge i j) h1 h2
      have hd2 : Disjoint (σ.initJ t j ∪ σ.mutJ t j) ((rule S).respJ t j) := by
        apply Finset.disjoint_left.mpr
        intro i hi hr
        obtain ⟨s, -, hs, -⟩ := mem_arrivedJ.mp ((hrule S).subJ t j hr)
        rcases Finset.mem_union.mp hi with h | h
        · exact edge_initI_initJ (hσ.edge i j) hs h
        · simp only [Schedule.mutJ, Finset.mem_filter, Finset.mem_univ, true_and] at h
          exact edge_initI_mutI (hσ.edge i j) hs h
      have hcap := (hrule S).capJ t j
      rw [shownJ, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1] at hcap
      have : (((σ.initJ t j).card + (σ.mutJ t j).card + ((rule S).respJ t j).card : ℕ) : ℝ) ≤
          inst.KJ j := by exact_mod_cast hcap
      push_cast at this
      linarith
    have hE : indepExp univ (likeProb inst) (fun S => (((rule S).respJ t j).card : ℝ)) ≤
        (inst.KJ j : ℝ) - (σ.initJ t j).card - (σ.mutJ t j).card := by
      calc _ ≤ indepExp univ (likeProb inst)
            (fun _ => (inst.KJ j : ℝ) - (σ.initJ t j).card - (σ.mutJ t j).card) :=
            indepExp_mono (likeProb_mem hp) fun S _ => hpt S
        _ = _ := indepExp_const _ _ _
    rw [hsum]
    linarith


/-! ### DHT-τ is a feasible semi-adaptive policy -/

omit [Fintype I] [DecidableEq J] in
theorem releasedI_mono {T : ℕ} (σ : Schedule I J T) (i : I) : Monotone (releasedI σ i) := by
  intro m n hmn j hj
  simp only [releasedI, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  obtain ⟨s, hs, h⟩ := hj
  exact ⟨s, lt_of_lt_of_le hs hmn, h⟩

omit [Fintype J] [DecidableEq I] in
theorem releasedJ_mono {T : ℕ} (σ : Schedule I J T) (j : J) : Monotone (releasedJ σ j) := by
  intro m n hmn i hi
  simp only [releasedJ, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  obtain ⟨s, hs, h⟩ := hi
  exact ⟨s, lt_of_lt_of_le hs hmn, h⟩

omit [Fintype I] in
/-- `i`'s backlog in period `t`: the profiles that like `i` and initiated toward `i` before. -/
theorem arrivedI_eq_inter {T : ℕ} (σ : Schedule I J T) (LJ : Finset (J × I)) (t : Fin T)
    (i : I) : arrivedI σ LJ t i = (univ.filter fun j => (j, i) ∈ LJ) ∩ releasedI σ i t := by
  ext j
  simp only [mem_arrivedI, releasedI, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨s, hs, h1, h2⟩
    exact ⟨h2, s, hs, h1⟩
  · rintro ⟨h2, s, hs, h1⟩
    exact ⟨s, hs, h1, h2⟩

omit [Fintype J] in
theorem arrivedJ_eq_inter {T : ℕ} (σ : Schedule I J T) (LI : Finset (I × J)) (t : Fin T)
    (j : J) : arrivedJ σ LI t j = (univ.filter fun i => (i, j) ∈ LI) ∩ releasedJ σ j t := by
  ext i
  simp only [mem_arrivedJ, releasedJ, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨s, hs, h1, h2⟩
    exact ⟨h2, s, hs, h1⟩
  · rintro ⟨h2, s, hs, h1⟩
    exact ⟨s, hs, h1, h2⟩

/-- DHT-τ's responses are greedy's picks from everyone who likes the user. -/
theorem dhtTau_respI (inst : Instance I J) (σ : Schedule I J inst.T)
    (selI : I → ℕ → Finset J → Finset J) (selJ : J → ℕ → Finset I → Finset I)
    (LI : Finset (I × J)) (LJ : Finset (J × I)) (t : Fin inst.T) (i : I) :
    (dhtTauResp inst σ selI selJ LI LJ).respI t i =
      greedyPick (selI i) (freeI inst σ i) (releasedI σ i)
        (univ.filter fun j => (j, i) ∈ LJ) t := by
  simp only [dhtTauResp, backlogResp]
  rw [arrivedI_eq_inter]
  exact greedyPick_inter (releasedI_mono σ i) t

theorem dhtTau_respJ (inst : Instance I J) (σ : Schedule I J inst.T)
    (selI : I → ℕ → Finset J → Finset J) (selJ : J → ℕ → Finset I → Finset I)
    (LI : Finset (I × J)) (LJ : Finset (J × I)) (t : Fin inst.T) (j : J) :
    (dhtTauResp inst σ selI selJ LI LJ).respJ t j =
      greedyPick (selJ j) (freeJ inst σ j) (releasedJ σ j)
        (univ.filter fun i => (i, j) ∈ LI) t := by
  simp only [dhtTauResp, backlogResp]
  rw [arrivedJ_eq_inter]
  exact greedyPick_inter (releasedJ_mono σ j) t

omit [Fintype J] [DecidableEq I] [DecidableEq J] in
-- `freeI` takes `[Fintype I]`, so the linter's advice to omit it is wrong here.
set_option linter.unusedSectionVars false in
theorem freeI_val (inst : Instance I J) (σ : Schedule I J inst.T) (i : I) (t : Fin inst.T) :
    freeI inst σ i t = inst.KI i - (σ.initI t i).card - (σ.mutI t i).card := by
  simp [freeI, t.isLt]

omit [Fintype J] [DecidableEq I] in
theorem freeJ_val (inst : Instance I J) (σ : Schedule I J inst.T) (j : J) (t : Fin inst.T) :
    freeJ inst σ j t = inst.KJ j - (σ.initJ t j).card - (σ.mutJ t j).card := by
  simp [freeJ, t.isLt]

/-- In a feasible solution of R2, initiations and mutual views fit in each period. -/
theorem FeasibleR2.init_mut_le {inst : Instance I J} {design : Schedule I J inst.T → Prop}
    {s : SolR2 I J inst.T} (hs : FeasibleR2 inst design s) :
    (∀ t i, (s.sched.initI t i).card + (s.sched.mutI t i).card ≤ inst.KI i) ∧
      ∀ t j, (s.sched.initJ t j).card + (s.sched.mutJ t j).card ≤ inst.KJ j := by
  constructor
  · intro t i
    have h := hs.capI t i
    have hy : 0 ≤ ∑ j, s.yI t i j := Finset.sum_nonneg fun j _ => (hs.yI_mem t i j).1
    have : (((s.sched.initI t i).card + (s.sched.mutI t i).card : ℕ) : ℝ) ≤ inst.KI i := by
      push_cast; linarith
    exact_mod_cast this
  · intro t j
    have h := hs.capJ t j
    have hy : 0 ≤ ∑ i, s.yJ t j i := Finset.sum_nonneg fun i _ => (hs.yJ_mem t j i).1
    have : (((s.sched.initJ t j).card + (s.sched.mutJ t j).card : ℕ) : ℝ) ≤ inst.KJ j := by
      push_cast; linarith
    exact_mod_cast this

/-- DHT-τ's schedule, the one an R2 solution chose, is feasible. -/
theorem FeasibleR2.schedFeasible {inst : Instance I J} {design : Schedule I J inst.T → Prop}
    {s : SolR2 I J inst.T} (hs : FeasibleR2 inst design s) :
    SchedFeasible inst design s.sched where
  design := hs.design
  edge := hs.edge
  mutI_last := hs.mutI_last
  capI t i := (Finset.card_union_le _ _).trans (hs.init_mut_le.1 t i)
  capJ t j := (Finset.card_union_le _ _).trans (hs.init_mut_le.2 t j)

/-- DHT-τ's responses are feasible: from the backlog, within the free slots, and each
profile at most once. -/
theorem dhtTau_respFeasible {inst : Instance I J} {design : Schedule I J inst.T → Prop}
    {s : SolR2 I J inst.T} (hs : FeasibleR2 inst design s)
    {selI : I → ℕ → Finset J → Finset J} (hselI : ∀ i, IsTopSel (inst.pIJ i) (selI i))
    {selJ : J → ℕ → Finset I → Finset I}
    (hselJ : ∀ j, IsTopSel (fun i => inst.pJI j i) (selJ j))
    (LI : Finset (I × J)) (LJ : Finset (J × I)) :
    RespFeasible inst s.sched LI LJ (dhtTauResp inst s.sched selI selJ LI LJ) where
  subI t i := by
    simp only [dhtTauResp, backlogResp]
    exact (greedyPick_subset (fun k B => (hselI i k B).1) t).trans
      (Finset.sdiff_subset.trans Finset.inter_subset_left)
  subJ t j := by
    simp only [dhtTauResp, backlogResp]
    exact (greedyPick_subset (fun k B => (hselJ j k B).1) t).trans
      (Finset.sdiff_subset.trans Finset.inter_subset_left)
  capI t i := by
    have hc : ((dhtTauResp inst s.sched selI selJ LI LJ).respI t i).card ≤
        freeI inst s.sched i t := (hselI i _ _).2.1
    have hle := hs.init_mut_le.1 t i
    rw [freeI_val] at hc
    calc (shownI s.sched (dhtTauResp inst s.sched selI selJ LI LJ) t i).card
        ≤ (s.sched.initI t i ∪ s.sched.mutI t i).card +
            ((dhtTauResp inst s.sched selI selJ LI LJ).respI t i).card :=
          Finset.card_union_le _ _
      _ ≤ (s.sched.initI t i).card + (s.sched.mutI t i).card +
            ((dhtTauResp inst s.sched selI selJ LI LJ).respI t i).card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ inst.KI i := by omega
  capJ t j := by
    have hc : ((dhtTauResp inst s.sched selI selJ LI LJ).respJ t j).card ≤
        freeJ inst s.sched j t := (hselJ j _ _).2.1
    have hle := hs.init_mut_le.2 t j
    rw [freeJ_val] at hc
    calc (shownJ s.sched (dhtTauResp inst s.sched selI selJ LI LJ) t j).card
        ≤ (s.sched.initJ t j ∪ s.sched.mutJ t j).card +
            ((dhtTauResp inst s.sched selI selJ LI LJ).respJ t j).card :=
          Finset.card_union_le _ _
      _ ≤ (s.sched.initJ t j).card + (s.sched.mutJ t j).card +
            ((dhtTauResp inst s.sched selI selJ LI LJ).respJ t j).card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ inst.KJ j := by omega
  onceI i j t t' h h' := by
    rw [dhtTau_respI] at h h'
    by_contra hne
    exact Finset.disjoint_left.mp (greedyPick_disjoint (fun k B => (hselI i k B).1)
      (fun heq => hne (Fin.ext heq))) h h'
  onceJ j i t t' h h' := by
    rw [dhtTau_respJ] at h h'
    by_contra hne
    exact Finset.disjoint_left.mp (greedyPick_disjoint (fun k B => (hselJ j k B).1)
      (fun heq => hne (Fin.ext heq))) h h'


/-! ### Lower bound: DHT-τ earns `(1 - 1/e)` of R2 -/

/-- **DHT-τ's responses for one user `i` (steps 2–5 of the proof sketch).** `i`'s expected
response value under DHT-τ is at least `(1 - 1/e)` times R2's response value for `i`. This
holds for every feasible solution of R2, optimal or not. -/
theorem dhtTau_valueI (inst : Instance I J)
    (hp : ∀ i j, 0 ≤ inst.pIJ i j ∧ inst.pIJ i j ≤ 1 ∧ 0 ≤ inst.pJI j i ∧ inst.pJI j i ≤ 1)
    {design : Schedule I J inst.T → Prop} {s : SolR2 I J inst.T}
    (hs : FeasibleR2 inst design s) {selI : I → ℕ → Finset J → Finset J}
    (hselI : ∀ i, IsTopSel (inst.pIJ i) (selI i)) (selJ : J → ℕ → Finset I → Finset I)
    (i : I) :
    (1 - Real.exp (-1)) * ∑ t, ∑ j, s.yI t i j * inst.pIJ i j ≤
      ∑ t, ∑ j, respProbI inst (fun S => dhtTauResp inst s.sched selI selJ (LIof S) (LJof S))
        t i j * inst.pIJ i j := by
  set G := greedyValue (inst.pIJ i) (selI i) (freeI inst s.sched i) (releasedI s.sched i)
    inst.T with hG
  -- R2's response variables for `i`, indexed by `ℕ`.
  set y : ℕ → J → ℝ := fun n j => if h : n < inst.T then s.yI ⟨n, h⟩ i j else 0 with hy_def
  have hyval : ∀ (t : Fin inst.T) j, y t j = s.yI t i j := by
    intro t j; simp [hy_def, t.isLt]
  -- The right side is greedy's expected value.
  have hR : ∑ t, ∑ j, respProbI inst
      (fun S => dhtTauResp inst s.sched selI selJ (LIof S) (LJof S)) t i j * inst.pIJ i j =
      indepExp univ (fun j => inst.pJI j i) G := by
    have hcomap := indepExp_comap (e := fun j : J => (Sum.inr (j, i) : (I × J) ⊕ (J × I)))
      (fun a b h => by simpa using h) (likeProb inst) univ univ G
      (fun _ _ => Finset.mem_univ _)
    rw [show (fun j => inst.pJI j i) = fun j => likeProb inst (Sum.inr (j, i)) from rfl,
      ← hcomap]
    have h1 : ∀ t j, respProbI inst
        (fun S => dhtTauResp inst s.sched selI selJ (LIof S) (LJof S)) t i j * inst.pIJ i j =
        indepExp univ (likeProb inst) (fun S => inst.pIJ i j *
          if j ∈ (dhtTauResp inst s.sched selI selJ (LIof S) (LJof S)).respI t i then 1
          else 0) := by
      intro t j
      rw [indepExp_const_mul, mul_comm]
      rfl
    rw [Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => h1 t j,
      Finset.sum_congr rfl fun t _ => (indepExp_sum _ _ _ _).symm, ← indepExp_sum]
    apply indepExp_congr
    intro S _
    have hfilt : (univ.filter fun j => (j, i) ∈ LJof S) =
        univ.filter fun j => Sum.inr (j, i) ∈ S := by
      ext j; simp [LJof]
    simp only [dhtTau_respI, hfilt, mul_ite, mul_one, mul_zero]
    rw [hG, greedyValue, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  -- The left side is R2's response value for `i`, in the form of `greedy_correlation_gap`.
  have hL : ∑ t, ∑ j, s.yI t i j * inst.pIJ i j =
      ∑ n ∈ range inst.T, ∑ j, inst.pIJ i j * y n j := by
    rw [← Fin.sum_univ_eq_sum_range (fun n => ∑ j, inst.pIJ i j * y n j)]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro j _
    rw [hyval]
    ring
  have hy0 : ∀ n j, 0 ≤ y n j := by
    intro n j
    simp only [hy_def]
    split_ifs
    · exact (hs.yI_mem _ i j).1
    · exact le_rfl
  have hyA : ∀ n j, j ∉ releasedI s.sched i n → y n j = 0 := by
    intro n j hj
    simp only [hy_def]
    split_ifs with hn
    · set t : Fin inst.T := ⟨n, hn⟩
      have hc := hs.cumI t i j
      have hz : ∑ u ∈ univ.filter (· < t),
          (if i ∈ s.sched.initJ u j then (1 : ℝ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
        have : i ∉ s.sched.initJ u j := fun h => hj (by
          simp only [releasedI, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨u, hu, h⟩)
        simp [this]
      rw [hz, mul_zero] at hc
      have hle : s.yI t i j ≤ ∑ u ∈ univ.filter (· ≤ t), s.yI u i j :=
        Finset.single_le_sum (f := fun u => s.yI u i j) (fun u _ => (hs.yI_mem u i j).1)
          (by simp)
      linarith [(hs.yI_mem t i j).1]
    · rfl
  have hyq : ∀ j ∈ (univ : Finset J), ∑ n ∈ range inst.T, y n j ≤ inst.pJI j i := by
    intro j _
    rw [← Fin.sum_univ_eq_sum_range (fun n => y n j)]
    simp only [hyval]
    rcases Nat.eq_zero_or_pos inst.T with hT | hT
    · have : (univ : Finset (Fin inst.T)) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro t _
        have := t.isLt
        omega
      rw [this, Finset.sum_empty]
      exact (hp i j).2.2.1
    · set tl : Fin inst.T := ⟨inst.T - 1, by omega⟩
      have hall : univ.filter (· ≤ tl) = univ := by
        apply Finset.filter_true_of_mem
        intro u _
        show (u : ℕ) ≤ inst.T - 1
        have := u.isLt
        omega
      have hc := hs.cumI tl i j
      rw [hall] at hc
      have h1 := sum_ite_le_one (univ.filter (· < tl)) (fun u => i ∈ s.sched.initJ u j)
        (fun a b ha hb => edge_initJ_unique (hs.edge i j) ha hb)
      have := mul_le_mul_of_nonneg_left h1 (hp i j).2.2.1
      linarith
  have hyc : ∀ n < inst.T, ∑ j, y n j ≤ freeI inst s.sched i n := by
    intro n hn
    set t : Fin inst.T := ⟨n, hn⟩
    have hyt : ∀ j, y n j = s.yI t i j := fun j => hyval t j
    simp only [hyt]
    have hc := hs.capI t i
    have hle := hs.init_mut_le.1 t i
    rw [show n = (t : ℕ) from rfl, freeI_val, Nat.sub_sub, Nat.cast_sub hle]
    push_cast
    linarith
  have hgap := greedy_correlation_gap (fun j => (hp i j).1) (hselI i)
    (releasedI_mono s.sched i) inst.T univ (fun j => inst.pJI j i)
    (fun j _ => ⟨(hp i j).2.2.1, (hp i j).2.2.2⟩) y hy0 hyA hyq hyc
  rw [hR, hL]
  exact hgap

/-- **DHT-τ's responses for one user `j`.** The mirror image of `dhtTau_valueI`. -/
theorem dhtTau_valueJ (inst : Instance I J)
    (hp : ∀ i j, 0 ≤ inst.pIJ i j ∧ inst.pIJ i j ≤ 1 ∧ 0 ≤ inst.pJI j i ∧ inst.pJI j i ≤ 1)
    {design : Schedule I J inst.T → Prop} {s : SolR2 I J inst.T}
    (hs : FeasibleR2 inst design s) (selI : I → ℕ → Finset J → Finset J)
    {selJ : J → ℕ → Finset I → Finset I}
    (hselJ : ∀ j, IsTopSel (fun i => inst.pJI j i) (selJ j)) (j : J) :
    (1 - Real.exp (-1)) * ∑ t, ∑ i, s.yJ t j i * inst.pJI j i ≤
      ∑ t, ∑ i, respProbJ inst (fun S => dhtTauResp inst s.sched selI selJ (LIof S) (LJof S))
        t j i * inst.pJI j i := by
  set G := greedyValue (fun i => inst.pJI j i) (selJ j) (freeJ inst s.sched j)
    (releasedJ s.sched j) inst.T with hG
  set y : ℕ → I → ℝ := fun n i => if h : n < inst.T then s.yJ ⟨n, h⟩ j i else 0 with hy_def
  have hyval : ∀ (t : Fin inst.T) i, y t i = s.yJ t j i := by
    intro t i; simp [hy_def, t.isLt]
  have hR : ∑ t, ∑ i, respProbJ inst
      (fun S => dhtTauResp inst s.sched selI selJ (LIof S) (LJof S)) t j i * inst.pJI j i =
      indepExp univ (fun i => inst.pIJ i j) G := by
    have hcomap := indepExp_comap (e := fun i : I => (Sum.inl (i, j) : (I × J) ⊕ (J × I)))
      (fun a b h => by simpa using h) (likeProb inst) univ univ G
      (fun _ _ => Finset.mem_univ _)
    rw [show (fun i => inst.pIJ i j) = fun i => likeProb inst (Sum.inl (i, j)) from rfl,
      ← hcomap]
    have h1 : ∀ t i, respProbJ inst
        (fun S => dhtTauResp inst s.sched selI selJ (LIof S) (LJof S)) t j i * inst.pJI j i =
        indepExp univ (likeProb inst) (fun S => inst.pJI j i *
          if i ∈ (dhtTauResp inst s.sched selI selJ (LIof S) (LJof S)).respJ t j then 1
          else 0) := by
      intro t i
      rw [indepExp_const_mul, mul_comm]
      rfl
    rw [Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => h1 t i,
      Finset.sum_congr rfl fun t _ => (indepExp_sum _ _ _ _).symm, ← indepExp_sum]
    apply indepExp_congr
    intro S _
    have hfilt : (univ.filter fun i => (i, j) ∈ LIof S) =
        univ.filter fun i => Sum.inl (i, j) ∈ S := by
      ext i; simp [LIof]
    simp only [dhtTau_respJ, hfilt, mul_ite, mul_one, mul_zero]
    rw [hG, greedyValue, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro t _
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hL : ∑ t, ∑ i, s.yJ t j i * inst.pJI j i =
      ∑ n ∈ range inst.T, ∑ i, inst.pJI j i * y n i := by
    rw [← Fin.sum_univ_eq_sum_range (fun n => ∑ i, inst.pJI j i * y n i)]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro i _
    rw [hyval]
    ring
  have hy0 : ∀ n i, 0 ≤ y n i := by
    intro n i
    simp only [hy_def]
    split_ifs
    · exact (hs.yJ_mem _ j i).1
    · exact le_rfl
  have hyA : ∀ n i, i ∉ releasedJ s.sched j n → y n i = 0 := by
    intro n i hi
    simp only [hy_def]
    split_ifs with hn
    · set t : Fin inst.T := ⟨n, hn⟩
      have hc := hs.cumJ t j i
      have hz : ∑ u ∈ univ.filter (· < t),
          (if j ∈ s.sched.initI u i then (1 : ℝ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
        have : j ∉ s.sched.initI u i := fun h => hi (by
          simp only [releasedJ, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨u, hu, h⟩)
        simp [this]
      rw [hz, mul_zero] at hc
      have hle : s.yJ t j i ≤ ∑ u ∈ univ.filter (· ≤ t), s.yJ u j i :=
        Finset.single_le_sum (f := fun u => s.yJ u j i) (fun u _ => (hs.yJ_mem u j i).1)
          (by simp)
      linarith [(hs.yJ_mem t j i).1]
    · rfl
  have hyq : ∀ i ∈ (univ : Finset I), ∑ n ∈ range inst.T, y n i ≤ inst.pIJ i j := by
    intro i _
    rw [← Fin.sum_univ_eq_sum_range (fun n => y n i)]
    simp only [hyval]
    rcases Nat.eq_zero_or_pos inst.T with hT | hT
    · have : (univ : Finset (Fin inst.T)) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro t _
        have := t.isLt
        omega
      rw [this, Finset.sum_empty]
      exact (hp i j).1
    · set tl : Fin inst.T := ⟨inst.T - 1, by omega⟩
      have hall : univ.filter (· ≤ tl) = univ := by
        apply Finset.filter_true_of_mem
        intro u _
        show (u : ℕ) ≤ inst.T - 1
        have := u.isLt
        omega
      have hc := hs.cumJ tl j i
      rw [hall] at hc
      have h1 := sum_ite_le_one (univ.filter (· < tl)) (fun u => j ∈ s.sched.initI u i)
        (fun a b ha hb => edge_initI_unique (hs.edge i j) ha hb)
      have := mul_le_mul_of_nonneg_left h1 (hp i j).1
      linarith
  have hyc : ∀ n < inst.T, ∑ i, y n i ≤ freeJ inst s.sched j n := by
    intro n hn
    set t : Fin inst.T := ⟨n, hn⟩
    have hyt : ∀ i, y n i = s.yJ t j i := fun i => hyval t i
    simp only [hyt]
    have hc := hs.capJ t j
    have hle := hs.init_mut_le.2 t j
    rw [show n = (t : ℕ) from rfl, freeJ_val, Nat.sub_sub, Nat.cast_sub hle]
    push_cast
    linarith
  have hgap := greedy_correlation_gap (fun i => (hp i j).2.2.1) (hselJ j)
    (releasedJ_mono s.sched j) inst.T univ (fun i => inst.pIJ i j)
    (fun i _ => ⟨(hp i j).1, (hp i j).2.1⟩) y hy0 hyA hyq hyc
  rw [hR, hL]
  exact hgap

omit [DecidableEq I] in
/-- R2's objective, split into mutual views and each user's responses. -/
theorem objR2_split (inst : Instance I J) (s : SolR2 I J inst.T) :
    objR2 inst s =
      ∑ t, ∑ i, ∑ j, (if j ∈ s.sched.mutI t i then inst.pIJ i j * inst.pJI j i else 0) +
        ∑ i, ∑ t, ∑ j, s.yI t i j * inst.pIJ i j + ∑ j, ∑ t, ∑ i, s.yJ t j i * inst.pJI j i := by
  unfold objR2
  simp only [Finset.sum_add_distrib]
  have h2 : ∑ t, ∑ i, ∑ j, s.yI t i j * inst.pIJ i j =
      ∑ i, ∑ t, ∑ j, s.yI t i j * inst.pIJ i j := Finset.sum_comm
  have h3 : ∑ t, ∑ i, ∑ j, s.yJ t j i * inst.pJI j i =
      ∑ j, ∑ t, ∑ i, s.yJ t j i * inst.pJI j i := by
    calc ∑ t, ∑ i, ∑ j, s.yJ t j i * inst.pJI j i =
        ∑ t, ∑ j, ∑ i, s.yJ t j i * inst.pJI j i :=
          Finset.sum_congr rfl fun t _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [h2, h3]

/-- **DHT-τ earns `(1 - 1/e)` of R2**, for every feasible solution of R2 and every
tie-breaking. -/
theorem dhtTau_ge (inst : Instance I J)
    (hp : ∀ i j, 0 ≤ inst.pIJ i j ∧ inst.pIJ i j ≤ 1 ∧ 0 ≤ inst.pJI j i ∧ inst.pJI j i ≤ 1)
    {design : Schedule I J inst.T → Prop} {s : SolR2 I J inst.T}
    (hs : FeasibleR2 inst design s) {selI : I → ℕ → Finset J → Finset J}
    (hselI : ∀ i, IsTopSel (inst.pIJ i) (selI i)) {selJ : J → ℕ → Finset I → Finset I}
    (hselJ : ∀ j, IsTopSel (fun i => inst.pJI j i) (selJ j)) :
    (1 - Real.exp (-1)) * objR2 inst s ≤
      expMatches inst s.sched (fun S => dhtTauResp inst s.sched selI selJ (LIof S) (LJof S)) := by
  rw [expected_matches_eq inst s.sched _ hs.edge
    (fun S => dhtTau_respFeasible hs hselI hselJ _ _)
    (backlogResp_blind (fun t i B => greedyPick (selI i) (freeI inst s.sched i)
      (releasedI s.sched i) B t) (fun t j B => greedyPick (selJ j) (freeJ inst s.sched j)
        (releasedJ s.sched j) B t) s.sched)]
  rw [objR2_split, objR2_split]
  simp only [policySol]
  have he1 : 1 - Real.exp (-1) ≤ 1 := by
    have := Real.exp_pos (-1)
    linarith
  have hM : 0 ≤ ∑ t, ∑ i, ∑ j,
      (if j ∈ s.sched.mutI t i then inst.pIJ i j * inst.pJI j i else 0) :=
    Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by
      split_ifs
      · exact mul_nonneg (hp i j).1 (hp i j).2.2.1
      · exact le_rfl
  have hI := Finset.sum_le_sum fun i (_ : i ∈ univ) => dhtTau_valueI inst hp hs hselI selJ i
  have hJ := Finset.sum_le_sum fun j (_ : j ∈ univ) => dhtTau_valueJ inst hp hs selI hselJ j
  rw [← Finset.mul_sum] at hI hJ
  have hMe := mul_le_mul_of_nonneg_right he1 hM
  rw [mul_add, mul_add]
  exact add_le_add (add_le_add (hMe.trans_eq (one_mul _)) hI) hJ

/-- **Theorem 5.3, repaired (vault note, R2).** Take any design, any optimal solution `s` of
R2 and any tie-breaking (`selI`, `selJ`). Then:
1. DHT-τ's schedule is feasible.
2. DHT-τ's responses are feasible and use only the backlog (`dhtTauResp` is a
   `backlogResp`).
3. DHT-τ earns at least `(1 - 1/e)` times R2's optimal value.
4. R2's optimal value bounds every feasible semi-adaptive policy whose responses never
   anticipate a like, including every policy that responds from the backlog only. -/
theorem theorem_5_3_repair (inst : Instance I J)
    (hp : ∀ i j, 0 ≤ inst.pIJ i j ∧ inst.pIJ i j ≤ 1 ∧ 0 ≤ inst.pJI j i ∧ inst.pJI j i ≤ 1)
    (design : Schedule I J inst.T → Prop) (s : SolR2 I J inst.T) (hs : IsOptR2 inst design s)
    (selI : I → ℕ → Finset J → Finset J) (hselI : ∀ i, IsTopSel (inst.pIJ i) (selI i))
    (selJ : J → ℕ → Finset I → Finset I)
    (hselJ : ∀ j, IsTopSel (fun i => inst.pJI j i) (selJ j)) :
    SchedFeasible inst design s.sched ∧
    (∀ LI LJ, RespFeasible inst s.sched LI LJ (dhtTauResp inst s.sched selI selJ LI LJ)) ∧
    (1 - Real.exp (-1)) * objR2 inst s ≤
      expMatches inst s.sched (fun S => dhtTauResp inst s.sched selI selJ (LIof S) (LJof S)) ∧
    ∀ (σ : Schedule I J inst.T) (rule : Finset ((I × J) ⊕ (J × I)) → Response I J inst.T),
      SchedFeasible inst design σ → (∀ S, RespFeasible inst σ (LIof S) (LJof S) (rule S)) →
      RespBlind rule → expMatches inst σ rule ≤ objR2 inst s := by
  refine ⟨hs.1.schedFeasible, dhtTau_respFeasible hs.1 hselI hselJ,
    dhtTau_ge inst hp hs.1 hselI hselJ, fun σ rule hσ hrule hblind => ?_⟩
  rw [expected_matches_eq inst σ rule hσ.edge hrule hblind]
  exact hs.2 _ (policySol_feasible inst hp design σ rule hσ hrule)

/-- **DHT-τ is a `(1 - 1/e)`-approximation against every semi-adaptive policy**, for every
design. -/
theorem dhtTau_approx (inst : Instance I J)
    (hp : ∀ i j, 0 ≤ inst.pIJ i j ∧ inst.pIJ i j ≤ 1 ∧ 0 ≤ inst.pJI j i ∧ inst.pJI j i ≤ 1)
    (design : Schedule I J inst.T → Prop) (s : SolR2 I J inst.T) (hs : IsOptR2 inst design s)
    (selI : I → ℕ → Finset J → Finset J) (hselI : ∀ i, IsTopSel (inst.pIJ i) (selI i))
    (selJ : J → ℕ → Finset I → Finset I)
    (hselJ : ∀ j, IsTopSel (fun i => inst.pJI j i) (selJ j))
    (σ : Schedule I J inst.T) (rule : Finset ((I × J) ⊕ (J × I)) → Response I J inst.T)
    (hσ : SchedFeasible inst design σ) (hrule : ∀ S, RespFeasible inst σ (LIof S) (LJof S) (rule S))
    (hblind : RespBlind rule) :
    (1 - Real.exp (-1)) * expMatches inst σ rule ≤
      expMatches inst s.sched (fun S => dhtTauResp inst s.sched selI selJ (LIof S) (LJof S)) := by
  obtain ⟨-, -, hlow, hup⟩ := theorem_5_3_repair inst hp design s hs selI hselI selJ hselJ
  have he0 : 0 ≤ 1 - Real.exp (-1) := by
    have : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    linarith
  exact (mul_le_mul_of_nonneg_left (hup σ rule hσ hrule hblind) he0).trans hlow


/-! ### R2 has an optimal solution -/

/-- Feasibility in R2, as one conjunction. -/
theorem feasibleR2_mk_iff (inst : Instance I J) (design : Schedule I J inst.T → Prop)
    (σ : Schedule I J inst.T) (yI : Fin inst.T → I → J → ℝ) (yJ : Fin inst.T → J → I → ℝ) :
    FeasibleR2 inst design ⟨σ, yI, yJ⟩ ↔
      (design σ ∧ (∀ i j, edgeUse σ i j ≤ 1) ∧
        ∀ t : Fin inst.T, (t : ℕ) + 1 = inst.T → ∀ i, σ.mutI t i = ∅) ∧
      (∀ t i j, 0 ≤ yI t i j) ∧ (∀ t i j, yI t i j ≤ 1) ∧
      (∀ t j i, 0 ≤ yJ t j i) ∧ (∀ t j i, yJ t j i ≤ 1) ∧
      (∀ t i j, ∑ u ∈ univ.filter (· ≤ t), yI u i j ≤
        inst.pJI j i * ∑ u ∈ univ.filter (· < t), (if i ∈ σ.initJ u j then (1 : ℝ) else 0)) ∧
      (∀ t j i, ∑ u ∈ univ.filter (· ≤ t), yJ u j i ≤
        inst.pIJ i j * ∑ u ∈ univ.filter (· < t), (if j ∈ σ.initI u i then (1 : ℝ) else 0)) ∧
      (∀ t i, ((σ.initI t i).card : ℝ) + (σ.mutI t i).card + ∑ j, yI t i j ≤ inst.KI i) ∧
      (∀ t j, ((σ.initJ t j).card : ℝ) + (σ.mutJ t j).card + ∑ i, yJ t j i ≤ inst.KJ j) :=
  ⟨fun h => ⟨⟨h.design, h.edge, h.mutI_last⟩, fun t i j => (h.yI_mem t i j).1,
      fun t i j => (h.yI_mem t i j).2, fun t j i => (h.yJ_mem t j i).1,
      fun t j i => (h.yJ_mem t j i).2, h.cumI, h.cumJ, h.capI, h.capJ⟩,
    fun ⟨⟨h1, h2, h3⟩, h4, h5, h6, h7, h8, h9, h10, h11⟩ =>
      ⟨h1, h2, h3, fun t i j => ⟨h4 t i j, h5 t i j⟩, fun t j i => ⟨h6 t j i, h7 t j i⟩, h8, h9,
        h10, h11⟩⟩

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem schedule_finite [Finite I] [Finite J] (T : ℕ) : Finite (Schedule I J T) :=
  Finite.of_injective (fun σ : Schedule I J T => (σ.initI, σ.initJ, σ.mutI)) (by
    rintro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl)

/-- The fractional variables of an R2 solution, `(yI, yJ)`. -/
abbrev YVars (I J : Type*) (T : ℕ) := (Fin T → I → J → ℝ) × (Fin T → J → I → ℝ)

/-- **R2 has an optimal solution** whenever it has a feasible one. There are finitely many
schedules, and for each, the feasible `y` form a compact polytope. So `IsOptR2` in
`theorem_5_3_repair` can be met. -/
theorem exists_isOptR2 (inst : Instance I J) (design : Schedule I J inst.T → Prop)
    (hne : ∃ s, FeasibleR2 inst design s) : ∃ s, IsOptR2 inst design s := by
  let Y : Schedule I J inst.T → Set (YVars I J inst.T) :=
    fun σ => {v | FeasibleR2 inst design ⟨σ, v.1, v.2⟩}
  let F : Schedule I J inst.T → YVars I J inst.T → ℝ := fun σ v => objR2 inst ⟨σ, v.1, v.2⟩
  have hFc : ∀ σ, Continuous (F σ) := by
    intro σ
    show Continuous fun v : YVars I J inst.T => ∑ t, ∑ i, ∑ j,
      ((if j ∈ σ.mutI t i then inst.pIJ i j * inst.pJI j i else 0) + v.1 t i j * inst.pIJ i j +
        v.2 t j i * inst.pJI j i)
    refine continuous_finsetSum _ fun t _ => continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ => ?_
    refine Continuous.add (Continuous.add continuous_const ?_) ?_ <;> fun_prop
  have hYc : ∀ σ, IsCompact (Y σ) := by
    intro σ
    have hclosed : IsClosed (Y σ) := by
      simp only [Y, feasibleR2_mk_iff, Set.ofPred_and, Set.ofPred_forall]
      repeat' first
        | exact isClosed_const
        | apply IsClosed.inter
        | (apply isClosed_iInter; intro _)
        | (apply isClosed_le <;> first | exact continuous_const | fun_prop)
    have hsub : Y σ ⊆ Set.Icc (0 : YVars I J inst.T) 1 := by
      intro v hv
      have hv' := (feasibleR2_mk_iff inst design σ v.1 v.2).mp hv
      simp only [Set.mem_Icc, Prod.le_def, Pi.le_def, Prod.fst_zero, Prod.snd_zero,
        Prod.fst_one, Prod.snd_one, Pi.zero_apply, Pi.one_apply]
      exact ⟨⟨hv'.2.1, hv'.2.2.2.1⟩, ⟨hv'.2.2.1, hv'.2.2.2.2.1⟩⟩
    exact isCompact_Icc.of_isClosed_subset hclosed hsub
  -- The best `y` for each schedule.
  have hbest : ∀ σ, (Y σ).Nonempty → ∃ v ∈ Y σ, ∀ w ∈ Y σ, F σ w ≤ F σ v := by
    intro σ h
    obtain ⟨v, hv, hmax⟩ := (hYc σ).exists_isMaxOn h (hFc σ).continuousOn
    exact ⟨v, hv, fun w hw => hmax hw⟩
  choose! v hv hvmax using hbest
  -- The best schedule.
  have := schedule_finite (I := I) (J := J) inst.T
  obtain ⟨s0, hs0⟩ := hne
  have hS0 : (s0.yI, s0.yJ) ∈ Y s0.sched := hs0
  obtain ⟨σ, hσ, hσmax⟩ := Set.exists_max_image {σ | (Y σ).Nonempty} (fun σ => F σ (v σ))
    (Set.toFinite _) ⟨s0.sched, _, hS0⟩
  refine ⟨⟨σ, (v σ).1, (v σ).2⟩, hv σ hσ, fun s' hs' => ?_⟩
  have hs'Y : (s'.yI, s'.yJ) ∈ Y s'.sched := hs'
  calc objR2 inst s' = F s'.sched (s'.yI, s'.yJ) := rfl
    _ ≤ F s'.sched (v s'.sched) := hvmax s'.sched ⟨_, hs'Y⟩ _ hs'Y
    _ ≤ F σ (v σ) := hσmax s'.sched ⟨_, hs'Y⟩


/-- The schedule that shows nothing. -/
def Schedule.empty (I J : Type*) (T : ℕ) : Schedule I J T :=
  ⟨fun _ _ => ∅, fun _ _ => ∅, fun _ _ => ∅⟩

/-- Showing nothing is feasible in R2 if the design allows it, as every standard design does. -/
theorem feasibleR2_empty (inst : Instance I J) (design : Schedule I J inst.T → Prop)
    (hd : design (Schedule.empty I J inst.T)) :
    FeasibleR2 inst design ⟨Schedule.empty I J inst.T, 0, 0⟩ where
  design := hd
  edge i j := by simp [edgeUse, Schedule.empty]
  mutI_last _ _ _ := rfl
  yI_mem _ _ _ := by simp
  yJ_mem _ _ _ := by simp
  cumI _ _ _ := by simp [Schedule.empty]
  cumJ _ _ _ := by simp [Schedule.empty]
  capI _ _ := by simp [Schedule.empty]
  capJ _ _ := by simp [Schedule.empty, Schedule.mutJ]

/-- So R2 has an optimal solution for every design that allows showing nothing. -/
theorem exists_isOptR2_of_empty (inst : Instance I J) (design : Schedule I J inst.T → Prop)
    (hd : design (Schedule.empty I J inst.T)) : ∃ s, IsOptR2 inst design s :=
  exists_isOptR2 inst design ⟨_, feasibleR2_empty inst design hd⟩

end TwoDir

end DatingAlgo
