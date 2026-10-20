import DatingAlgo.MultiPeriodModel

/-!
# Theorem 5.3 fails as stated: a counterexample

Rios & Torrico, Section 5. Theorem 5.3 claims that DHT (Algorithm 3) is a
`(1 - 1/e)`-approximation against the best semi-adaptive policy, for every design and every
`T`. DHT solves relaxation (19) once and then, in each period:
- shows each user's initiations, as early as possible and in decreasing order of the
  target's like probability for the user (Steps 6–8);
- adds mutual views (Steps 9–12);
- fills the remaining slots from the backlog (Step 14).

Relaxation (19) pools each user's display slots over all periods (`≤ K_ℓ T`). A response
costs only `φ` of the responder's budget, so (19) may spend a user's whole budget on
responses, though nobody can respond in period 1.

## The instance
- `T = 2` and every display cap is 1. The design is two-directional, with or without
  non-sequential matches.
- `I = {i}` and `J = {j, a₁, …, a₄}`. User `i` likes everyone for sure.
- `j` likes `i` with probability `99/100`; each `aₖ` likes `i` with probability `1/2`.

## What happens
- In (19), each unit of `i`'s budget earns at most 1, and an initiation or mutual view by
  `i` earns at most `99/100`. Responding to the four `aₖ` earns exactly 2. So every optimal
  solution has `i` initiate nothing and no mutual views.
- DHT then shows `i` nothing in period 1, because its backlog starts empty. In period 2, `i`
  sees at most one profile. Every match involves `i`, so DHT earns at most 1 expected match,
  even with clairvoyant responders.
- A semi-adaptive policy does better. In period 1, `i` is shown `j` and each `aₖ` is shown
  `i`. In period 2, `i` answers the first `aₖ` who liked it, and `j` answers `i`. It earns
  `99/100 + 15/16 = 1.9275`.
- `1 < (1 - 1/e) · 1.9275`, so the guarantee fails: the ratio is at most `0.519`.

## Modeling
- Likes are drawn up front and are independent. The instance data, the like
  encoding and `IsDHTInit` are in `MultiPeriodModel.lean`.
- A match is a pair who have both seen and liked each other. That happens sequentially (one
  initiates, the other answers from the backlog later) or in a mutual view.
- `IsDHTSchedule` lists properties of the schedule that Steps 6–12 build, whatever the
  tie-breaking. Every run has them when the solution has no mutual views (`w = 0`), and every
  optimal solution here has none (part 1). With mutual views a run can break them: Step 12
  can fill a user's slot before that user's Steps 6–8, delaying an initiation. The bound
  holds for every schedule with these properties.
- The bound covers every feasible response plan, so DHT's Step 14 needs no separate model.
-/

namespace DatingAlgo

open Finset

namespace TwoDir

open TPeriod

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- A candidate solution of relaxation (19), for complete bipartite potentials. -/
structure Sol19 (I J : Type*) where
  /-- `xIJ i j = 1`: `i` is shown `j` to start a sequential interaction. -/
  xIJ : I → J → ℝ
  /-- `xJI j i = 1`: `j` is shown `i` to start a sequential interaction. -/
  xJI : J → I → ℝ
  /-- `w i j = 1`: `i` and `j` see each other in the same period. -/
  w : I → J → ℝ
  /-- `yIJ i j`: the probability that `i` sees `j` as a response, from the backlog. -/
  yIJ : I → J → ℝ
  /-- `yJI j i`: the probability that `j` sees `i` as a response, from the backlog. -/
  yJI : J → I → ℝ

/-- Feasibility in relaxation (19), two-directional design, complete potentials:
- `x, w` binary and `y ∈ [0, 1]`;
- `y_{ℓℓ'} ≤ x_{ℓ'ℓ} φ_{ℓ'ℓ}`;
- `x_{ℓℓ'} + x_{ℓ'ℓ} + w_e ≤ 1`;
- `∑ x_{ℓ·} + ∑_{e ∋ ℓ} w_e + ∑ y_{ℓ·} ≤ K_ℓ T`.

`nonSeq` says whether the design allows non-sequential (mutual) views; if not, `w = 0`. -/
structure Feasible19 (inst : Instance I J) (nonSeq : Bool) (s : Sol19 I J) : Prop where
  xIJ_bin : ∀ i j, s.xIJ i j = 0 ∨ s.xIJ i j = 1
  xJI_bin : ∀ j i, s.xJI j i = 0 ∨ s.xJI j i = 1
  w_bin : ∀ i j, s.w i j = 0 ∨ s.w i j = 1
  yIJ_mem : ∀ i j, 0 ≤ s.yIJ i j ∧ s.yIJ i j ≤ 1
  yJI_mem : ∀ j i, 0 ≤ s.yJI j i ∧ s.yJI j i ≤ 1
  yIJ_le : ∀ i j, s.yIJ i j ≤ s.xJI j i * inst.pJI j i
  yJI_le : ∀ j i, s.yJI j i ≤ s.xIJ i j * inst.pIJ i j
  edge : ∀ i j, s.xIJ i j + s.xJI j i + s.w i j ≤ 1
  budgetI : ∀ i, ∑ j, s.xIJ i j + ∑ j, s.w i j + ∑ j, s.yIJ i j ≤ (inst.KI i : ℝ) * inst.T
  budgetJ : ∀ j, ∑ i, s.xJI j i + ∑ i, s.w i j + ∑ i, s.yJI j i ≤ (inst.KJ j : ℝ) * inst.T
  seqOnly : nonSeq = false → ∀ i j, s.w i j = 0

/-- Objective of (19): `∑_e w_e β_e + ∑_ℓ ∑_{ℓ'} y_{ℓℓ'} φ_{ℓℓ'}`, with `β_{ij} = φ_{ij} φ_{ji}`. -/
noncomputable def obj19 (inst : Instance I J) (s : Sol19 I J) : ℝ :=
  ∑ i, ∑ j, s.w i j * (inst.pIJ i j * inst.pJI j i) +
    (∑ i, ∑ j, s.yIJ i j * inst.pIJ i j + ∑ j, ∑ i, s.yJI j i * inst.pJI j i)

/-- An optimal solution of (19). -/
def IsOpt19 (inst : Instance I J) (nonSeq : Bool) (s : Sol19 I J) : Prop :=
  Feasible19 inst nonSeq s ∧ ∀ s', Feasible19 inst nonSeq s' → obj19 inst s' ≤ obj19 inst s

/-- The non-adaptive part of a semi-adaptive policy (Definition 5.1), period by period:
- `initI t i`: profiles `i` is shown in period `t` to start a sequential interaction;
- `initJ t j`: likewise for `j`;
- `mutI t i`: profiles `j` such that `i` and `j` see each other in period `t`. -/
structure Schedule (I J : Type*) (T : ℕ) where
  initI : Fin T → I → Finset J
  initJ : Fin T → J → Finset I
  mutI : Fin T → I → Finset J

/-- Users `i` whom `j` sees in a mutual view in period `t`. -/
def Schedule.mutJ {T : ℕ} (σ : Schedule I J T) (t : Fin T) (j : J) : Finset I :=
  univ.filter fun i => j ∈ σ.mutI t i

/-- The adaptive part of a semi-adaptive policy: `respI t i` are the profiles `i` sees from
its backlog in period `t`, and likewise `respJ t j`. -/
structure Response (I J : Type*) (T : ℕ) where
  respI : Fin T → I → Finset J
  respJ : Fin T → J → Finset I

/-- Profiles that reached `i`'s backlog before period `t`: users `j` who were shown `i` as an
initiation in an earlier period and liked `i`. -/
def arrivedI {T : ℕ} (σ : Schedule I J T) (LJ : Finset (J × I)) (t : Fin T) (i : I) :
    Finset J :=
  univ.filter fun j => ∃ s : Fin T, s < t ∧ i ∈ σ.initJ s j ∧ (j, i) ∈ LJ

/-- Profiles that reached `j`'s backlog before period `t`. -/
def arrivedJ {T : ℕ} (σ : Schedule I J T) (LI : Finset (I × J)) (t : Fin T) (j : J) :
    Finset I :=
  univ.filter fun i => ∃ s : Fin T, s < t ∧ j ∈ σ.initI s i ∧ (i, j) ∈ LI

/-- What `i` is shown in period `t`: initiations, mutual views and responses. -/
def shownI {T : ℕ} (σ : Schedule I J T) (ρ : Response I J T) (t : Fin T) (i : I) :
    Finset J :=
  σ.initI t i ∪ σ.mutI t i ∪ ρ.respI t i

/-- What `j` is shown in period `t`. -/
def shownJ {T : ℕ} (σ : Schedule I J T) (ρ : Response I J T) (t : Fin T) (j : J) :
    Finset I :=
  σ.initJ t j ∪ σ.mutJ t j ∪ ρ.respJ t j

/-- Everyone `i` is shown over the horizon. -/
def seenI {T : ℕ} (σ : Schedule I J T) (ρ : Response I J T) (i : I) : Finset J :=
  univ.biUnion fun t => shownI σ ρ t i

/-- Everyone `j` is shown over the horizon. -/
def seenJ {T : ℕ} (σ : Schedule I J T) (ρ : Response I J T) (j : J) : Finset I :=
  univ.biUnion fun t => shownJ σ ρ t j

/-- A feasible non-adaptive schedule: at most `K_ℓ` initiations and mutual views per period,
each initiation once, and mutual views only if the design allows them and not in the last
period (Section 5's assumption). -/
structure ScheduleFeasible (inst : Instance I J) (nonSeq : Bool) (σ : Schedule I J inst.T) :
    Prop where
  capI : ∀ t i, (σ.initI t i ∪ σ.mutI t i).card ≤ inst.KI i
  capJ : ∀ t j, (σ.initJ t j ∪ σ.mutJ t j).card ≤ inst.KJ j
  onceI : ∀ i j t t', j ∈ σ.initI t i → j ∈ σ.initI t' i → t = t'
  onceJ : ∀ j i t t', i ∈ σ.initJ t j → i ∈ σ.initJ t' j → t = t'
  mutI_last : ∀ t : Fin inst.T, (t : ℕ) + 1 = inst.T → ∀ i, σ.mutI t i = ∅
  seqOnly : nonSeq = false → ∀ t i, σ.mutI t i = ∅

/-- A feasible response plan: only profiles already in the backlog, at most `K_ℓ` profiles
shown per period in total, and each backlog profile at most once. -/
structure RespFeasible (inst : Instance I J) (σ : Schedule I J inst.T) (LI : Finset (I × J))
    (LJ : Finset (J × I)) (ρ : Response I J inst.T) : Prop where
  subI : ∀ t i, ρ.respI t i ⊆ arrivedI σ LJ t i
  subJ : ∀ t j, ρ.respJ t j ⊆ arrivedJ σ LI t j
  capI : ∀ t i, (shownI σ ρ t i).card ≤ inst.KI i
  capJ : ∀ t j, (shownJ σ ρ t j).card ≤ inst.KJ j
  onceI : ∀ i j t t', j ∈ ρ.respI t i → j ∈ ρ.respI t' i → t = t'
  onceJ : ∀ j i t t', i ∈ ρ.respJ t j → i ∈ ρ.respJ t' j → t = t'

/-- Matches: pairs who have both seen and liked each other. Likes are drawn up front: `LI`
holds `(i, j)` if `i` likes `j` when shown, and `LJ` likewise. -/
def matchCount {T : ℕ} (σ : Schedule I J T) (ρ : Response I J T) (LI : Finset (I × J))
    (LJ : Finset (J × I)) : ℕ :=
  ∑ i, ∑ j, if j ∈ seenI σ ρ i ∧ i ∈ seenJ σ ρ j ∧ (i, j) ∈ LI ∧ (j, i) ∈ LJ then 1 else 0

/-- Responses chosen from the backlog only: in period `t`, user `ℓ` shows `f t ℓ B`, where `B`
is what has reached `ℓ`'s backlog so far. Such a rule uses only observed likes. -/
def backlogResp {T : ℕ} (fI : Fin T → I → Finset J → Finset J)
    (fJ : Fin T → J → Finset I → Finset I) (σ : Schedule I J T) (LI : Finset (I × J))
    (LJ : Finset (J × I)) : Response I J T where
  respI t i := fI t i (arrivedI σ LJ t i)
  respJ t j := fJ t j (arrivedJ σ LI t j)

/-- Properties of the schedule that Algorithm 3 (DHT), Steps 6–12, builds from a solution `s`
of (19), with any tie-breaking. Every run has them when `s` has no mutual views. With mutual
views, Step 12 can take a user's slot before that user's Steps 6–8 run, which delays an
initiation and breaks the "as early as possible" clause of `IsDHTInit`.
The properties:
- initiations follow Steps 6–8 for every user;
- mutual views are pairs with `w = 1`, each at most once, within the period caps. -/
structure IsDHTSchedule (inst : Instance I J) (s : Sol19 I J) (σ : Schedule I J inst.T) :
    Prop where
  initI : ∀ i, IsDHTInit (inst.KI i) (univ.filter fun j => s.xIJ i j = 1)
    (fun j => inst.pJI j i) (fun t => σ.initI t i)
  initJ : ∀ j, IsDHTInit (inst.KJ j) (univ.filter fun i => s.xJI j i = 1)
    (fun i => inst.pIJ i j) (fun t => σ.initJ t j)
  mutI_w : ∀ t i j, j ∈ σ.mutI t i → s.w i j = 1
  mutI_once : ∀ t t' i j, j ∈ σ.mutI t i → j ∈ σ.mutI t' i → t = t'
  capI : ∀ t i, (σ.initI t i ∪ σ.mutI t i).card ≤ inst.KI i
  capJ : ∀ t j, (σ.initJ t j ∪ σ.mutJ t j).card ≤ inst.KJ j

end TwoDir

open TwoDir
open TPeriod

/-- The counterexample instance: `T = 2`, all caps 1, `I = {i}`, `J = {j, a₁, a₂, a₃, a₄}` with
`j = 0`. User `i` likes everyone for sure; `j` likes `i` with probability `99/100` and each
`aₖ` with probability `1/2`. -/
noncomputable def thm53Instance : Instance (Fin 1) (Fin 5) where
  T := 2
  KI := fun _ => 1
  KJ := fun _ => 1
  pIJ := fun _ _ => 1
  pJI := fun l _ => if l = 0 then 99 / 100 else 1 / 2

@[simp] theorem thm53Instance_T : thm53Instance.T = 2 := rfl
@[simp] theorem thm53Instance_KI (i : Fin 1) : thm53Instance.KI i = 1 := rfl
@[simp] theorem thm53Instance_KJ (l : Fin 5) : thm53Instance.KJ l = 1 := rfl
@[simp] theorem thm53Instance_pIJ (i : Fin 1) (l : Fin 5) : thm53Instance.pIJ i l = 1 := rfl

theorem thm53_pJI_mem (l : Fin 5) (i : Fin 1) :
    0 ≤ thm53Instance.pJI l i ∧ thm53Instance.pJI l i ≤ 99 / 100 := by
  simp only [thm53Instance]
  split_ifs <;> norm_num

/-- An optimal solution of (19): each `aₖ` initiates toward `i`, and `i` spends both of its
slots on responses. -/
noncomputable def thm53Sol : Sol19 (Fin 1) (Fin 5) where
  xIJ := fun _ _ => 0
  xJI := fun l _ => if l = 0 then 0 else 1
  w := fun _ _ => 0
  yIJ := fun _ l => if l = 0 then 0 else 1 / 2
  yJI := fun _ _ => 0

theorem thm53Sol_feasible (nonSeq : Bool) : Feasible19 thm53Instance nonSeq thm53Sol where
  xIJ_bin := fun _ _ => Or.inl rfl
  xJI_bin := fun l _ => by simp only [thm53Sol]; split_ifs <;> simp
  w_bin := fun _ _ => Or.inl rfl
  yIJ_mem := fun _ l => by simp only [thm53Sol]; split_ifs <;> norm_num
  yJI_mem := fun _ _ => by simp [thm53Sol]
  yIJ_le := fun _ l => by simp only [thm53Sol, thm53Instance]; split_ifs <;> norm_num
  yJI_le := fun _ _ => by simp [thm53Sol]
  edge := fun _ l => by simp only [thm53Sol]; split_ifs <;> norm_num
  budgetI := fun _ => by simp [thm53Sol, Fin.sum_univ_five]; norm_num
  budgetJ := fun l => by simp only [thm53Sol]; split_ifs <;> simp
  seqOnly := fun _ _ _ => rfl

theorem thm53Sol_obj : obj19 thm53Instance thm53Sol = 2 := by
  simp [obj19, thm53Sol, Fin.sum_univ_five]
  norm_num

/-- Every feasible solution of (19) has value at most `2 - (∑ x_{i·} + ∑ w_{i·}) / 100`:
each unit of `i`'s budget earns at most 1, and initiations and mutual views by `i` earn at most
`99/100`. -/
theorem thm53_obj_le (nonSeq : Bool) (s : Sol19 (Fin 1) (Fin 5))
    (hs : Feasible19 thm53Instance nonSeq s) :
    obj19 thm53Instance s ≤ 2 - (∑ l, s.xIJ 0 l + ∑ l, s.w 0 l) / 100 := by
  have hw : ∀ l, s.w 0 l * (thm53Instance.pIJ 0 l * thm53Instance.pJI l 0) ≤
      99 / 100 * s.w 0 l := by
    intro l
    have h0 : 0 ≤ s.w 0 l := by rcases hs.w_bin 0 l with h | h <;> simp [h]
    have hp := thm53_pJI_mem l 0
    rw [thm53Instance_pIJ, one_mul]
    nlinarith
  have hy : ∀ l, s.yJI l 0 * thm53Instance.pJI l 0 ≤ 99 / 100 * s.xIJ 0 l := by
    intro l
    have h0 := (hs.yJI_mem l 0).1
    have h1 := hs.yJI_le l 0
    rw [thm53Instance_pIJ, mul_one] at h1
    have hp := thm53_pJI_mem l 0
    nlinarith
  have hb := hs.budgetI 0
  simp only [thm53Instance_KI, thm53Instance_T] at hb
  have hsw := Finset.sum_le_sum fun l (_ : l ∈ univ) => hw l
  have hsy := Finset.sum_le_sum fun l (_ : l ∈ univ) => hy l
  rw [← Finset.mul_sum] at hsw hsy
  simp only [thm53Instance_pIJ, one_mul] at hsw
  simp only [obj19, Fin.sum_univ_one, thm53Instance_pIJ, mul_one, one_mul]
  norm_num at hb
  linarith

/-- Part 1: (19) has optimal value 2, and every optimal solution has `i` initiate nothing and
no mutual views. -/
theorem thm53_part1 (nonSeq : Bool) :
    IsOpt19 thm53Instance nonSeq thm53Sol ∧ obj19 thm53Instance thm53Sol = 2 ∧
    ∀ s, IsOpt19 thm53Instance nonSeq s → ∀ l, s.xIJ 0 l = 0 ∧ s.w 0 l = 0 := by
  have hx0 : ∀ s : Sol19 (Fin 1) (Fin 5), Feasible19 thm53Instance nonSeq s →
      ∀ l, 0 ≤ s.xIJ 0 l ∧ 0 ≤ s.w 0 l := by
    intro s hs l
    exact ⟨by rcases hs.xIJ_bin 0 l with h | h <;> simp [h],
      by rcases hs.w_bin 0 l with h | h <;> simp [h]⟩
  refine ⟨⟨thm53Sol_feasible nonSeq, fun s' hs' => ?_⟩, thm53Sol_obj, fun s hs l => ?_⟩
  · have h := thm53_obj_le nonSeq s' hs'
    have h1 : 0 ≤ ∑ l, s'.xIJ 0 l := Finset.sum_nonneg fun l _ => (hx0 s' hs' l).1
    have h2 : 0 ≤ ∑ l, s'.w 0 l := Finset.sum_nonneg fun l _ => (hx0 s' hs' l).2
    rw [thm53Sol_obj]
    linarith
  · have h := thm53_obj_le nonSeq s hs.1
    have hge := hs.2 thm53Sol (thm53Sol_feasible nonSeq)
    rw [thm53Sol_obj] at hge
    have h1 : 0 ≤ ∑ l, s.xIJ 0 l := Finset.sum_nonneg fun l _ => (hx0 s hs.1 l).1
    have h2 : 0 ≤ ∑ l, s.w 0 l := Finset.sum_nonneg fun l _ => (hx0 s hs.1 l).2
    have e1 : ∑ l, s.xIJ 0 l = 0 := by linarith
    have e2 : ∑ l, s.w 0 l = 0 := by linarith
    rw [Finset.sum_eq_zero_iff_of_nonneg fun l _ => (hx0 s hs.1 l).1] at e1
    rw [Finset.sum_eq_zero_iff_of_nonneg fun l _ => (hx0 s hs.1 l).2] at e2
    exact ⟨e1 l (mem_univ l), e2 l (mem_univ l)⟩

/-- In a DHT schedule for an optimal solution, `i` has no initiations and no mutual views. -/
theorem thm53_dht_empty (nonSeq : Bool) (s : Sol19 (Fin 1) (Fin 5))
    (hs : IsOpt19 thm53Instance nonSeq s) (σ : Schedule (Fin 1) (Fin 5) 2)
    (hσ : IsDHTSchedule thm53Instance s σ) (t : Fin 2) :
    σ.initI t 0 = ∅ ∧ σ.mutI t 0 = ∅ := by
  have hz := (thm53_part1 nonSeq).2.2 s hs
  constructor
  · apply Finset.eq_empty_of_forall_notMem
    intro l hl
    have hcov : (univ.biUnion fun t => σ.initI t 0) = univ.filter fun l => s.xIJ 0 l = 1 :=
      (hσ.initI 0).1
    have : l ∈ univ.biUnion fun t => σ.initI t 0 := Finset.mem_biUnion.mpr ⟨t, mem_univ _, hl⟩
    rw [hcov, Finset.mem_filter] at this
    rw [(hz l).1] at this
    norm_num at this
  · apply Finset.eq_empty_of_forall_notMem
    intro l hl
    have := hσ.mutI_w t 0 l hl
    rw [(hz l).2] at this
    norm_num at this

/-- Pathwise bound: if `i` has no initiations and no mutual views, every feasible response
plan, even a clairvoyant one, yields at most one match. `i` sees nobody in period 1 (its backlog
starts empty) and at most one profile in period 2, and every match involves `i`. -/
theorem thm53_match_le (σ : Schedule (Fin 1) (Fin 5) 2)
    (hσ : ∀ t, σ.initI t 0 = ∅ ∧ σ.mutI t 0 = ∅) (LI : Finset (Fin 1 × Fin 5))
    (LJ : Finset (Fin 5 × Fin 1)) (ρ : Response (Fin 1) (Fin 5) 2)
    (hρ : RespFeasible thm53Instance σ LI LJ ρ) : matchCount σ ρ LI LJ ≤ 1 := by
  have h0 : shownI σ ρ 0 0 = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro l hl
    simp only [shownI, (hσ 0).1, (hσ 0).2, Finset.empty_union] at hl
    have := hρ.subI (0 : Fin 2) 0 hl
    simp [arrivedI] at this
  have hseen : seenI σ ρ 0 ⊆ shownI σ ρ 1 0 := by
    intro l hl
    simp only [seenI, Finset.mem_biUnion, mem_univ, true_and] at hl
    obtain ⟨t, ht⟩ := hl
    fin_cases t
    · simp [h0] at ht
    · exact ht
  have hcard : (seenI σ ρ 0).card ≤ 1 :=
    (Finset.card_le_card hseen).trans (hρ.capI (1 : Fin 2) 0)
  calc matchCount σ ρ LI LJ
      ≤ ∑ l : Fin 5, if l ∈ seenI σ ρ 0 then 1 else 0 := by
        unfold matchCount
        rw [Fin.sum_univ_one]
        apply Finset.sum_le_sum
        intro l _
        split_ifs with h1 h2 <;> simp_all
    _ = (seenI σ ρ 0).card := by simp
    _ ≤ 1 := hcard

theorem thm53_likeProb_mem :
    ∀ e ∈ (univ : Finset ((Fin 1 × Fin 5) ⊕ (Fin 5 × Fin 1))),
      0 ≤ likeProb thm53Instance e ∧ likeProb thm53Instance e ≤ 1 :=
  likeProb_mem fun i l => by
    have := thm53_pJI_mem l i
    exact ⟨by simp, by simp, this.1, by linarith [this.2]⟩

/-- Part 2: for every optimal solution of (19) and every DHT schedule for it, every feasible
response rule yields at most 1 expected match. The rule may depend on the whole like outcome,
so this covers clairvoyant responders and, in particular, DHT's own responses (Step 14). -/
theorem thm53_part2 (nonSeq : Bool) (s : Sol19 (Fin 1) (Fin 5))
    (hs : IsOpt19 thm53Instance nonSeq s) (σ : Schedule (Fin 1) (Fin 5) 2)
    (hσ : IsDHTSchedule thm53Instance s σ)
    (rule : Finset ((Fin 1 × Fin 5) ⊕ (Fin 5 × Fin 1)) → Response (Fin 1) (Fin 5) 2)
    (hrule : ∀ S, RespFeasible thm53Instance σ (LIof S) (LJof S) (rule S)) :
    indepExp univ (likeProb thm53Instance)
      (fun S => (matchCount σ (rule S) (LIof S) (LJof S) : ℝ)) ≤ 1 := by
  calc _ ≤ indepExp univ (likeProb thm53Instance) (fun _ => 1) := by
        apply indepExp_mono thm53_likeProb_mem
        intro S _
        exact_mod_cast thm53_match_le σ (thm53_dht_empty nonSeq s hs σ hσ) _ _ _ (hrule S)
    _ = 1 := indepExp_const _ _ _

/-- The alternative schedule: in period 1, `i` is shown `j` and every `aₖ` is shown `i`. -/
def thm53AltSched : Schedule (Fin 1) (Fin 5) 2 where
  initI := fun t _ => if t = 0 then {0} else ∅
  initJ := fun t l => if t = 0 ∧ l ≠ 0 then {0} else ∅
  mutI := fun _ _ => ∅

/-- The lowest-indexed elements of a set (at most one). -/
def firstOf {β : Type*} [LinearOrder β] (A : Finset β) : Finset β :=
  A.filter fun b => ∀ c ∈ A, b ≤ c

/-- The alternative responses, chosen from the backlog only: `i` answers the first `aₖ` who
liked it, and `j` answers `i` if `i` liked `j`. -/
def thm53AltResp (LI : Finset (Fin 1 × Fin 5)) (LJ : Finset (Fin 5 × Fin 1)) :
    Response (Fin 1) (Fin 5) 2 :=
  backlogResp (fun _ _ B => firstOf B) (fun _ _ B => B) thm53AltSched LI LJ

theorem thm53Alt_arrivedI (LJ : Finset (Fin 5 × Fin 1)) (t : Fin 2) (k : Fin 5) :
    k ∈ arrivedI thm53AltSched LJ t 0 ↔ t = 1 ∧ k ≠ 0 ∧ (k, 0) ∈ LJ := by
  by_cases hk : k = 0 <;> fin_cases t <;> simp [arrivedI, thm53AltSched, hk]

theorem thm53Alt_arrivedJ (LI : Finset (Fin 1 × Fin 5)) (t : Fin 2) (l : Fin 5) (i : Fin 1) :
    i ∈ arrivedJ thm53AltSched LI t l ↔ t = 1 ∧ l = 0 ∧ (0, 0) ∈ LI := by
  obtain rfl : i = 0 := Subsingleton.elim _ _
  by_cases hl : l = 0
  · subst hl
    fin_cases t <;> simp [arrivedJ, thm53AltSched]
  · fin_cases t <;> simp [arrivedJ, thm53AltSched, hl]

theorem thm53Alt_seenI (LI : Finset (Fin 1 × Fin 5)) (LJ : Finset (Fin 5 × Fin 1)) (l : Fin 5) :
    l ∈ seenI thm53AltSched (thm53AltResp LI LJ) 0 ↔
      l = 0 ∨ (l ≠ 0 ∧ (l, 0) ∈ LJ ∧ ∀ c, c ≠ 0 → (c, 0) ∈ LJ → l ≤ c) := by
  simp only [seenI, shownI, thm53AltResp, backlogResp, firstOf, mem_biUnion, mem_univ, true_and,
    Fin.exists_fin_two, mem_union, mem_filter, thm53Alt_arrivedI]
  by_cases hl : l = 0 <;> simp [thm53AltSched, hl]

theorem thm53Alt_seenJ (LI : Finset (Fin 1 × Fin 5)) (LJ : Finset (Fin 5 × Fin 1)) (l : Fin 5) :
    (0 : Fin 1) ∈ seenJ thm53AltSched (thm53AltResp LI LJ) l ↔
      l ≠ 0 ∨ (l = 0 ∧ (0, 0) ∈ LI) := by
  simp only [seenJ, shownJ, thm53AltResp, backlogResp, Schedule.mutJ, mem_biUnion, mem_univ,
    true_and, Fin.exists_fin_two, mem_union, mem_filter, thm53Alt_arrivedJ]
  by_cases hl : l = 0 <;> simp [thm53AltSched, hl]

/-- The like coins `i likes l` and `l likes i`. -/
def thm53A (l : Fin 5) : Finset ((Fin 1 × Fin 5) ⊕ (Fin 5 × Fin 1)) :=
  {Sum.inl (0, l), Sum.inr (l, 0)}

/-- The like coins `aₖ likes i`, for the `aₖ` with index below `l`. -/
def thm53B (l : Fin 5) : Finset ((Fin 1 × Fin 5) ⊕ (Fin 5 × Fin 1)) :=
  (univ.filter fun c : Fin 5 => c ≠ 0 ∧ c < l).image fun c => Sum.inr (c, 0)

/-- The alternative policy matches `i` with `l` exactly when both like each other and, for
`l = aₖ`, no earlier `aₖ'` liked `i`. -/
theorem thm53Alt_match (S : Finset ((Fin 1 × Fin 5) ⊕ (Fin 5 × Fin 1))) :
    (matchCount thm53AltSched (thm53AltResp (LIof S) (LJof S)) (LIof S) (LJof S) : ℝ) =
      ∑ l : Fin 5, if thm53A l ⊆ S ∧ Disjoint (thm53B l) S then 1 else 0 := by
  unfold matchCount
  rw [Fin.sum_univ_one]
  push_cast
  apply Finset.sum_congr rfl
  intro l _
  have key : (l ∈ seenI thm53AltSched (thm53AltResp (LIof S) (LJof S)) 0 ∧
      0 ∈ seenJ thm53AltSched (thm53AltResp (LIof S) (LJof S)) l ∧
      (0, l) ∈ LIof S ∧ (l, 0) ∈ LJof S) ↔ (thm53A l ⊆ S ∧ Disjoint (thm53B l) S) := by
    rw [thm53Alt_seenI, thm53Alt_seenJ]
    simp only [thm53A, thm53B, LIof, LJof, mem_filter, mem_univ, true_and, insert_subset_iff,
      singleton_subset_iff, disjoint_left, mem_image]
    by_cases hl : l = 0
    · subst hl
      simp
    · simp [hl]
      constructor
      · rintro ⟨⟨_, h2⟩, h3, h4⟩
        refine ⟨⟨h3, h4⟩, fun a x hx hxl hxa hS => ?_⟩
        subst hxa
        exact absurd (h2 x hx hS) (not_le.mpr hxl)
      · rintro ⟨⟨h3, h4⟩, h⟩
        refine ⟨⟨h4, fun c hc hS => ?_⟩, h3, h4⟩
        by_contra hlc
        exact h c c hc (not_le.mp hlc) rfl hS
  simp only [key]

theorem thm53AB_disjoint (l : Fin 5) : Disjoint (thm53A l) (thm53B l) := by
  simp only [thm53A, thm53B, disjoint_left, mem_insert, mem_singleton, mem_image, mem_filter,
    mem_univ, true_and, not_exists, not_and]
  rintro a (rfl | rfl) c hc h
  · simp at h
  · simp only [Sum.inr.injEq, Prod.mk.injEq, and_true] at h
    exact absurd (h ▸ hc.2) (lt_irrefl l)

/-- Part 3: the alternative semi-adaptive policy earns `99/100 + 15/16 = 771/400` expected
matches. -/
theorem thm53_part3 :
    indepExp univ (likeProb thm53Instance)
      (fun S => (matchCount thm53AltSched (thm53AltResp (LIof S) (LJof S)) (LIof S) (LJof S) :
        ℝ)) = 771 / 400 := by
  rw [indepExp_congr (h := fun S => ∑ l : Fin 5,
    if thm53A l ⊆ S ∧ Disjoint (thm53B l) S then 1 else 0) (fun S _ => thm53Alt_match S),
    indepExp_sum, Finset.sum_congr rfl fun l _ => indepExp_subset_disjoint _ (subset_univ _)
      (subset_univ _) (thm53AB_disjoint l)]
  have hA : ∀ l, ∏ a ∈ thm53A l, likeProb thm53Instance a = thm53Instance.pJI l 0 := by
    intro l
    rw [thm53A, Finset.prod_pair Sum.inl_ne_inr]
    simp [likeProb]
  have hB : ∀ l, ∏ b ∈ thm53B l, (1 - likeProb thm53Instance b) =
      (1 / 2) ^ (univ.filter fun c : Fin 5 => c ≠ 0 ∧ c < l).card := by
    intro l
    rw [thm53B, Finset.prod_image (by intro a _ b _ h; simpa using h),
      Finset.prod_congr rfl (g := fun _ => 1 / 2), Finset.prod_const]
    intro c hc
    simp only [mem_filter, mem_univ, true_and] at hc
    simp only [likeProb, thm53Instance, hc.1, ite_false]
    norm_num
  have c0 : (univ.filter fun c : Fin 5 => c ≠ 0 ∧ c < 0).card = 0 := by decide
  have c1 : (univ.filter fun c : Fin 5 => c ≠ 0 ∧ c < 1).card = 0 := by decide
  have c2 : (univ.filter fun c : Fin 5 => c ≠ 0 ∧ c < 2).card = 1 := by decide
  have c3 : (univ.filter fun c : Fin 5 => c ≠ 0 ∧ c < 3).card = 2 := by decide
  have c4 : (univ.filter fun c : Fin 5 => c ≠ 0 ∧ c < 4).card = 3 := by decide
  simp only [hA, hB, Fin.sum_univ_five, c0, c1, c2, c3, c4]
  simp [thm53Instance]
  norm_num

/-- Part 4: `1 < (1 - 1/e) · 771/400`. -/
theorem thm53_numeric : 1 < (1 - Real.exp (-1)) * (771 / 400) :=
  one_lt_one_sub_exp_neg_one_mul (by norm_num)

theorem firstOf_subset {β : Type*} [LinearOrder β] (A : Finset β) : firstOf A ⊆ A :=
  Finset.filter_subset _ _

theorem firstOf_card_le_one {β : Type*} [LinearOrder β] (A : Finset β) :
    (firstOf A).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  simp only [firstOf, mem_filter] at ha hb
  exact le_antisymm (ha.2 b hb.1) (hb.2 a ha.1)

/-- The alternative schedule is feasible, in either two-directional design. -/
theorem thm53AltSched_feasible (nonSeq : Bool) :
    ScheduleFeasible thm53Instance nonSeq thm53AltSched where
  capI := fun (t : Fin 2) i => by
    simp only [thm53AltSched, Finset.union_empty, thm53Instance_KI]
    split_ifs <;> simp
  capJ := fun (t : Fin 2) l => by
    simp only [thm53AltSched, Schedule.mutJ, thm53Instance_KJ]
    split_ifs <;> simp
  onceI := fun i j (t t' : Fin 2) h h' => by
    simp only [thm53AltSched] at h h'
    split_ifs at h h' with h1 h2 <;> simp_all
  onceJ := fun j i (t t' : Fin 2) h h' => by
    simp only [thm53AltSched] at h h'
    split_ifs at h h' with h1 h2 <;> simp_all
  mutI_last := fun _ _ _ => rfl
  seqOnly := fun _ _ _ => rfl

/-- The alternative responses are feasible for every like outcome. -/
theorem thm53AltResp_feasible (LI : Finset (Fin 1 × Fin 5)) (LJ : Finset (Fin 5 × Fin 1)) :
    RespFeasible thm53Instance thm53AltSched LI LJ (thm53AltResp LI LJ) where
  subI := fun _ _ => firstOf_subset _
  subJ := fun _ _ => subset_refl _
  capI := fun (t : Fin 2) i => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    simp only [thm53Instance_KI, shownI]
    fin_cases t
    · have : (thm53AltResp LI LJ).respI 0 0 = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro l hl
        have := (thm53Alt_arrivedI LJ 0 l).mp (firstOf_subset _ hl)
        exact absurd this.1 (by decide)
      simp [this, thm53AltSched]
    · simp only [thm53AltSched, thm53AltResp, backlogResp]
      simpa using firstOf_card_le_one _
  capJ := fun _ _ => (Finset.card_le_univ _).trans (by simp)
  onceI := fun i j (t t' : Fin 2) h h' => by
    obtain rfl : i = 0 := Subsingleton.elim _ _
    have h1 := ((thm53Alt_arrivedI LJ t j).mp (firstOf_subset _ h)).1
    have h2 := ((thm53Alt_arrivedI LJ t' j).mp (firstOf_subset _ h')).1
    rw [h1, h2]
  onceJ := fun j i (t t' : Fin 2) h h' => by
    have h1 := ((thm53Alt_arrivedJ LI t j i).mp h).1
    have h2 := ((thm53Alt_arrivedJ LI t' j i).mp h').1
    rw [h1, h2]

/-- The DHT schedule for `thm53Sol`: each `aₖ` is shown `i` in period 1. -/
def thm53DHTSched : Schedule (Fin 1) (Fin 5) 2 where
  initI := fun _ _ => ∅
  initJ := fun t l => if t = 0 ∧ l ≠ 0 then {0} else ∅
  mutI := fun _ _ => ∅

/-- `thm53DHTSched` is a DHT schedule for `thm53Sol`, so the DHT hypothesis of part 2 is not
vacuous. -/
theorem thm53DHTSched_isDHT : IsDHTSchedule thm53Instance thm53Sol thm53DHTSched where
  initI := fun i => by
    refine ⟨?_, fun _ => by simp [thm53DHTSched], fun _ _ _ h => by simp [thm53DHTSched] at h,
      fun _ _ _ h => by simp [thm53DHTSched] at h, fun _ _ _ _ _ h => by simp [thm53DHTSched] at h⟩
    ext l
    simp [thm53DHTSched, thm53Sol]
  initJ := fun l => by
    refine ⟨?_, fun (t : Fin 2) => ?_, fun (t t' : Fin 2) b h h' => ?_,
      fun (t t' : Fin 2) htt' h => ?_, fun (t t' : Fin 2) b b' htt' _ h' => ?_⟩
    · ext i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      by_cases hl : l = 0
      · simp [thm53DHTSched, thm53Sol, hl]
      · simp [thm53DHTSched, thm53Sol, Fin.exists_fin_two, hl]
        exact Finset.mem_univ _
    · simp only [thm53DHTSched]
      split_ifs <;> simp
    · simp only [thm53DHTSched] at h h'
      split_ifs at h h' with h1 h2 <;> simp_all
    · obtain ⟨b, hb⟩ := h
      fin_cases t <;> fin_cases t' <;> simp_all [thm53DHTSched]
    · fin_cases t <;> fin_cases t' <;> simp_all [thm53DHTSched]
  mutI_w := fun _ _ _ h => by simp [thm53DHTSched] at h
  mutI_once := fun _ _ _ _ h => by simp [thm53DHTSched] at h
  capI := fun _ _ => by simp [thm53DHTSched]
  capJ := fun (t : Fin 2) l => by
    simp only [thm53DHTSched, Schedule.mutJ, thm53Instance_KJ]
    split_ifs <;> simp

/-- **Theorem 5.3 fails (Rios & Torrico).** Two-directional design, `T = 2`, with or without
non-sequential matches (`nonSeq`):
1. `thm53Sol` is an optimal solution of (19), with value 2, and DHT can run on it.
2. For every optimal solution of (19), every DHT schedule for it and every feasible response
   rule, even a clairvoyant one, the expected number of matches is at most 1.
3. A semi-adaptive policy earns `771/400 = 1.9275`. In period 1, `i` is shown `j` and every
   `aₖ` is shown `i`. In period 2, `i` answers the first `aₖ` who liked it, and `j` answers `i`
   if `i` liked `j`. Responses depend only on the backlog.
4. `1 < (1 - 1/e) · 1.9275`.

So DHT earns at most `1/1.9275 ≈ 0.519` times what a semi-adaptive policy earns, below the
claimed `1 - 1/e ≈ 0.632`. -/
theorem theorem_5_3_counterexample (nonSeq : Bool) :
    let inst := thm53Instance
    (IsOpt19 inst nonSeq thm53Sol ∧ obj19 inst thm53Sol = 2 ∧
      ∃ σ, IsDHTSchedule inst thm53Sol σ) ∧
    (∀ s, IsOpt19 inst nonSeq s → ∀ σ, IsDHTSchedule inst s σ →
      ∀ rule : Finset ((Fin 1 × Fin 5) ⊕ (Fin 5 × Fin 1)) → Response (Fin 1) (Fin 5) inst.T,
        (∀ S, RespFeasible inst σ (LIof S) (LJof S) (rule S)) →
        indepExp univ (likeProb inst)
          (fun S => (matchCount σ (rule S) (LIof S) (LJof S) : ℝ)) ≤ 1) ∧
    (∃ (σ : Schedule (Fin 1) (Fin 5) inst.T)
        (fI : Fin inst.T → Fin 1 → Finset (Fin 5) → Finset (Fin 5))
        (fJ : Fin inst.T → Fin 5 → Finset (Fin 1) → Finset (Fin 1)),
      ScheduleFeasible inst nonSeq σ ∧
      (∀ LI LJ, RespFeasible inst σ LI LJ (backlogResp fI fJ σ LI LJ)) ∧
      indepExp univ (likeProb inst)
        (fun S => (matchCount σ (backlogResp fI fJ σ (LIof S) (LJof S)) (LIof S) (LJof S) :
          ℝ)) = 771 / 400) ∧
    1 < (1 - Real.exp (-1)) * (771 / 400) := by
  intro inst
  obtain ⟨hopt, hobj, -⟩ := thm53_part1 nonSeq
  exact ⟨⟨hopt, hobj, thm53DHTSched, thm53DHTSched_isDHT⟩,
    fun s hs σ hσ rule hrule => thm53_part2 nonSeq s hs σ hσ rule hrule,
    ⟨thm53AltSched, fun _ _ B => firstOf B, fun _ _ B => B, thm53AltSched_feasible nonSeq,
      thm53AltResp_feasible, thm53_part3⟩, thm53_numeric⟩

end DatingAlgo
