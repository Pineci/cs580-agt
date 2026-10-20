import DatingAlgo.TwoPeriod

/-!
# Concrete markets and platform designs

Rios & Torrico, Sections 3.1, 4.1 and 4.3, plus the structure lemmas of Appendix E.

## Markets and displays
A concrete market has two sides, potentials, display caps, like probabilities, and a
match quality `q` (`q ≡ 1` counts matches). A period-1 decision is a display set
`S ℓ` for each user. It determines the paper's variables:
- a mutual view `w¹_{ℓℓ'} = 1` when `ℓ` and `ℓ'` see each other;
- an initiation `x¹_{ℓℓ'} = 1` when `ℓ` sees `ℓ'` but not the other way round.

`Market.toModel` packages this as a `TwoPeriodModel`, so Theorem 4.3 applies to every
design below.

## Designs
- **two-directional:** any feasible display;
- **sequential-only:** no mutual views;
- **one-directional (side `I` initiates):** a `J` user in period 1 sees only users who
  see them, since the backlog starts empty.

## Appendix E
The feasible regions of the sequential designs are intersections of partition
matroids: Lemma E.5 and the one-directional case of Section E.1.
-/

namespace DatingAlgo

open Finset

/-- A two-sided market for the two-period problem. `side ℓ = true` means `ℓ ∈ I`. -/
structure Market (U : Type*) where
  side : U → Bool
  pot : U → Finset U
  K : U → ℕ
  φ1 : U → U → ℝ
  φ2 : U → U → ℝ
  /-- Match quality; `q ≡ 1` counts matches. -/
  q : U → U → ℝ
  pot_other_side : ∀ a b, b ∈ pot a → side b ≠ side a
  φ1_nonneg : ∀ a b, 0 ≤ φ1 a b
  φ1_le_one : ∀ a b, φ1 a b ≤ 1
  φ2_nonneg : ∀ a b, 0 ≤ φ2 a b
  q_nonneg : ∀ a b, 0 ≤ q a b

namespace Market

variable {U : Type*} [Fintype U] [DecidableEq U] (mk : Market U)

/-- Period-1 displays respect potentials and caps. -/
def Feasible (S : U → Finset U) : Prop := ∀ ℓ, S ℓ ⊆ mk.pot ℓ ∧ (S ℓ).card ≤ mk.K ℓ

/-- `ℓ` and `ℓ'` see each other in period 1 (a mutual view, `w¹ = 1`). -/
def Mutual (S : U → Finset U) (ℓ ℓ' : U) : Prop := ℓ' ∈ S ℓ ∧ ℓ ∈ S ℓ'

/-- Users who initiated toward `ℓ` in period 1: they saw `ℓ`, and `ℓ` didn't see them
(`x¹_{ℓ'ℓ} = 1`). -/
def initOf (S : U → Finset U) (ℓ : U) : Finset U :=
  univ.filter (fun ℓ' => ℓ ∈ S ℓ' ∧ ℓ' ∉ S ℓ)

/-- Expected period-1 reward: each mutual view, counted once from its `I` side,
earns `β¹ q = φ¹_{ℓℓ'} φ¹_{ℓ'ℓ} q_{ℓℓ'}`. -/
noncomputable def immOf (S : U → Finset U) : ℝ :=
  ∑ ℓ, ∑ ℓ' ∈ S ℓ,
    if ℓ ∈ S ℓ' ∧ mk.side ℓ = true then mk.φ1 ℓ ℓ' * mk.φ1 ℓ' ℓ * mk.q ℓ ℓ' else 0

theorem immOf_nonneg (S : U → Finset U) : 0 ≤ mk.immOf S := by
  unfold immOf
  refine Finset.sum_nonneg fun ℓ _ => Finset.sum_nonneg fun ℓ' _ => ?_
  split_ifs
  · exact mul_nonneg (mul_nonneg (mk.φ1_nonneg _ _) (mk.φ1_nonneg _ _)) (mk.q_nonneg _ _)
  · exact le_refl 0

/-- The market as an abstract two-period model. Decisions are display sets, and
period-2 rewards are `φ² q`. -/
noncomputable def toModel : TwoPeriodModel U (U → Finset U) where
  K := mk.K
  φ1 := mk.φ1
  r2 := fun a b => mk.φ2 a b * mk.q a b
  imm := mk.immOf
  init := initOf
  φ1_nonneg := mk.φ1_nonneg
  φ1_le_one := mk.φ1_le_one
  r2_nonneg := fun a b => mul_nonneg (mk.φ2_nonneg a b) (mk.q_nonneg a b)
  imm_nonneg := mk.immOf_nonneg

/-- Two-directional design, non-sequential matches allowed in period 1 (Problem 4.2
as stated). -/
def TwoDirectional (S : U → Finset U) : Prop := mk.Feasible S

/-- Sequential-only design: no mutual views. -/
def SequentialOnly (S : U → Finset U) : Prop :=
  mk.Feasible S ∧ ∀ ℓ ℓ', ¬ Mutual S ℓ ℓ'

/-- One-directional design with side `I` initiating: a `J` user sees only users who
see them. -/
def OneDirectional (S : U → Finset U) : Prop :=
  mk.Feasible S ∧ ∀ j, mk.side j = false → ∀ i ∈ S j, j ∈ S i

/-- One-directional, sequential-only design (Appendix E.1): `J` users see nobody in
period 1. -/
def OneDirectionalSequential (S : U → Finset U) : Prop :=
  mk.Feasible S ∧ ∀ j, mk.side j = false → S j = ∅

/-- **Theorem 4.3 for concrete markets and every design.** For any design predicate,
an optimal solution of DH-int's program is a `(1 - 1/e)`-approximation for the
expected quality (expected number of matches when `q ≡ 1`). -/
theorem dhInt_approx_market (design : (U → Finset U) → Prop) {S : U → Finset U}
    {y : U → U → ℝ} (hdh : mk.toModel.IsDHIntSolution design S y)
    {S' : U → Finset U} (hS' : design S') :
    (1 - Real.exp (-1)) * mk.toModel.value S' ≤ mk.toModel.value S :=
  mk.toModel.dhInt_approx hdh hS'

/-! ### Appendix E: matroid structure of the feasible regions -/

/-- Independence in a partition matroid: at most `cap b` chosen elements in each block
`b`, where `blk` assigns elements to blocks. -/
def PartitionIndep {E β : Type*} [DecidableEq β] (blk : E → β) (cap : β → ℕ)
    (A : Finset E) : Prop :=
  ∀ b, (A.filter (fun e => blk e = b)).card ≤ cap b

/-- The arcs of a display: `(ℓ, ℓ')` with `ℓ' ∈ S ℓ`. -/
def arcsOf (S : U → Finset U) : Finset (U × U) :=
  univ.filter (fun e => e.2 ∈ S e.1)

/-- An arc lies in `arcsOf S` exactly when its head is displayed to its tail. -/
theorem mem_arcsOf {S : U → Finset U} {e : U × U} : e ∈ arcsOf S ↔ e.2 ∈ S e.1 := by
  simp [arcsOf]

/-- The viewer block of `ℓ` in `arcsOf S` has exactly `(S ℓ).card` arcs. -/
theorem card_viewer_block (S : U → Finset U) (ℓ : U) :
    ((arcsOf S).filter (fun e : U × U => e.1 = ℓ)).card = (S ℓ).card := by
  have h : (arcsOf S).filter (fun e : U × U => e.1 = ℓ) = ({ℓ} : Finset U) ×ˢ S ℓ := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_arcsOf, mem_product, mem_singleton]
    constructor
    · rintro ⟨hb, rfl⟩; exact ⟨rfl, hb⟩
    · rintro ⟨rfl, hb⟩; exact ⟨hb, rfl⟩
  rw [h, card_product, card_singleton, one_mul]

/-- Viewer-partition independence of `arcsOf S` is exactly the cap condition. -/
theorem viewer_indep_iff (S : U → Finset U) :
    PartitionIndep (fun e : U × U => e.1) mk.K (arcsOf S) ↔ ∀ ℓ, (S ℓ).card ≤ mk.K ℓ := by
  simp only [PartitionIndep, card_viewer_block]

/-- **Lemma E.5.** A display satisfies the caps and has no mutual views exactly when its
arc set is independent in two partition matroids:
- blocks by viewer, with capacity `K_ℓ`;
- blocks by unordered pair, with capacity 1.

Potentials are a ground-set restriction. -/
theorem sequential_iff_partition (S : U → Finset U) (hpot : ∀ ℓ, S ℓ ⊆ mk.pot ℓ) :
    mk.SequentialOnly S ↔
      PartitionIndep (fun e : U × U => e.1) mk.K (arcsOf S) ∧
      PartitionIndep (fun e : U × U => s(e.1, e.2)) (fun _ => 1) (arcsOf S) := by
  unfold SequentialOnly Feasible
  constructor
  · rintro ⟨hf, hmut⟩
    refine ⟨(viewer_indep_iff mk S).mpr fun ℓ => (hf ℓ).2, fun b => ?_⟩
    rw [card_le_one]
    rintro ⟨x1, x2⟩ hx ⟨y1, y2⟩ hy
    simp only [mem_filter, mem_arcsOf] at hx hy
    obtain ⟨hx, rfl⟩ := hx
    obtain ⟨hy, hxy⟩ := hy
    rcases Sym2.eq_iff.mp hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact (hmut _ _ ⟨hx, hy⟩).elim
  · rintro ⟨h1, h2⟩
    refine ⟨fun ℓ => ⟨hpot ℓ, (viewer_indep_iff mk S).mp h1 ℓ⟩, ?_⟩
    rintro a b ⟨hab, hba⟩
    have hne : a ≠ b := by
      rintro rfl
      exact mk.pot_other_side a a (hpot a hab) rfl
    have h := card_le_one.mp (h2 s(a, b)) (a, b)
      (by simp only [mem_filter, mem_arcsOf]; exact ⟨hab, trivial⟩) (b, a)
      (by simp only [mem_filter, mem_arcsOf]; exact ⟨hba, Sym2.eq_swap⟩)
    exact hne (congrArg Prod.fst h)

/-- **Section E.1.** In the one-directional sequential design the feasible region is
a partition matroid on the arcs leaving `I`. -/
theorem oneDirSequential_iff_partition (S : U → Finset U)
    (hpot : ∀ ℓ, S ℓ ⊆ mk.pot ℓ) :
    mk.OneDirectionalSequential S ↔
      PartitionIndep (fun e : U × U => e.1) mk.K (arcsOf S) ∧
      ∀ e ∈ arcsOf S, mk.side e.1 = true := by
  unfold OneDirectionalSequential Feasible
  rw [viewer_indep_iff]
  constructor
  · rintro ⟨hf, hJ⟩
    refine ⟨fun ℓ => (hf ℓ).2, fun e he => ?_⟩
    rw [mem_arcsOf] at he
    cases hs : mk.side e.1
    · rw [hJ e.1 hs] at he
      exact absurd he (Finset.notMem_empty _)
    · rfl
  · rintro ⟨h1, h2⟩
    refine ⟨fun ℓ => ⟨hpot ℓ, h1 ℓ⟩, fun j hj => ?_⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    have := h2 (j, x) (mem_arcsOf.mpr hx)
    rw [hj] at this
    exact Bool.false_ne_true this

end Market

end DatingAlgo
