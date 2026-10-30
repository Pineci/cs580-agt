import DatingAlgo.MaxMinSDH

/-!
# The note's max-min guarantee fails for SDH's own selection

The vault note "Max-Min Match Quality and Egalitarian Matching" claims that SDH run on a
max-min optimal plan gives every user at least `c_K^2 θ*`. With SDH's selection step, the
best capped set of found pairs (`sdhValue`), that is false: the guarantee of
`lpValue_le_sdhValue` is on total weight, and maximizing total weight can starve the
worst-off user.

**The market.** Initiators `0` and `1`, one responder `j`, values known (a single value
combination), every cap 1, every cost 1.
* `0` gains `1` from `j` and `j` gains `10` from `0`: net weight 11.
* `1` gains `2` from `j` and `j` gains `1` from `1`: net weight 3.

The max-min plan must split `j`: `x₀ ≥ θ`, `2 x₁ ≥ θ` and `x₀ + x₁ ≤ 1` force
`θ* = 2/3`, with `x₀ = 2/3` and `x₁ = 1/3`. SDH queries each pair with probability
`τ = x`. When both pairs are found it keeps `(0, j)`, the heavier one, so `1` matches
only when its pair is found and `0`'s is not:
`E[u₁] = 2 · (1/3) · (1/3) = 2/9 = θ*/3 < c_1^2 θ* ≈ 0.40 θ*`.

(Uniformly random selection, `MaxMinSDH.lean`, gives `1` twice that, `4/9 = 2θ*/3`.)
-/

namespace DatingAlgo

open Finset

namespace ScreenedMarket

variable {I J C : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype C] [DecidableEq C] (M : ScreenedMarket I J C)

/-- SDH's selection step, with any tie-breaking: for every found set `F` and weights `w`,
a capped subset of `F` of maximum weight. -/
def IsMaxWeightSel (sel : Finset (I × J) → (I × J → ℝ) → Finset (I × J)) : Prop :=
  ∀ F w, sel F w ⊆ F ∧ M.CapOK (sel F w) ∧ ∑ e ∈ sel F w, w e = M.bestMatch F w

/-- Initiator `i`'s expected utility under SDH with query probabilities `τ` and selection
`sel`: query each pair independently, then select among the pairs found acceptable. -/
noncomputable def sdhUtilI (sel : Finset (I × J) → (I × J → ℝ) → Finset (I × J))
    (τ : I × J → ℝ) (i : I) : ℝ :=
  prodExp (M.screenLaw τ) fun ω =>
    ∑ e ∈ (sel (univ.filter fun e => (ω e).2 = true ∧ M.Acc e (ω e).1)
        fun e => M.wt e (ω e).1).filter (fun e => e.1 = i),
      (M.valI e (ω e).1 - M.costI i)

end ScreenedMarket

/-- The market of the module docstring. -/
def mmExample : ScreenedMarket (Fin 2) Unit Unit where
  π := fun _ _ => 1
  valI := fun e _ => if e.1 = 0 then 2 else 3
  valJ := fun e _ => if e.1 = 0 then 11 else 2
  costI := fun _ => 1
  costJ := fun _ => 1
  capI := fun _ => 1
  capJ := fun _ => 1

/-- The max-min plan: `(0, j)` two thirds of the time, `(1, j)` one third. -/
noncomputable def mmExamplePlan : Fin 2 × Unit → Unit → ℝ :=
  fun e _ => if e.1 = 0 then 2 / 3 else 1 / 3

/-- Every pair is acceptable. -/
theorem mmExample_acc (e : Fin 2 × Unit) (c : Unit) : mmExample.Acc e c := by
  obtain ⟨i, ⟨⟩⟩ := e
  fin_cases i <;> norm_num [ScreenedMarket.Acc, mmExample]

/-- The net weights, `11` for `(0, j)` and `3` for `(1, j)`. -/
def mmWt (e : Fin 2 × Unit) : ℝ := if e.1 = 0 then 11 else 3

/-- The example's net weights are `mmWt`. -/
theorem mmExample_wt (e : Fin 2 × Unit) (c : Unit) : mmExample.wt e c = mmWt e := by
  by_cases h : e.1 = 0 <;> norm_num [ScreenedMarket.wt, mmExample, mmWt, h]

/-- The plan is max-min optimal, with value `θ* = 2/3`. -/
theorem mmExample_maxMin : mmExample.IsMaxMinOptimal mmExamplePlan (2 / 3) := by
  refine ⟨⟨fun e c => ?_, fun e c hc => (hc (mmExample_acc e c)).elim, fun i => ?_,
    fun j => ?_⟩, fun i => ?_, fun j => ?_, fun x' θ' hx' hI _ => ?_⟩
  · unfold mmExamplePlan
    split_ifs <;> norm_num [mmExample]
  · fin_cases i <;> norm_num [mmExamplePlan, mmExample]
  · norm_num [mmExamplePlan, mmExample, Fin.sum_univ_two]
  · fin_cases i <;> norm_num [ScreenedMarket.lpSurplusI, mmExamplePlan, mmExample]
  · norm_num [ScreenedMarket.lpSurplusJ, mmExamplePlan, mmExample, Fin.sum_univ_two]
  · have h0 := hI 0
    have h1 := hI 1
    have hc := hx'.2.2.2 ()
    simp only [ScreenedMarket.lpSurplusI, mmExample, Fintype.sum_unique,
      Fin.sum_univ_two] at h0 h1 hc
    norm_num at h0 h1 hc
    linarith

/-- SDH queries each pair with probability `x`. -/
theorem mmExample_sdhTau : mmExample.sdhTau mmExamplePlan = fun e => mmExamplePlan e () := by
  funext e
  refine le_antisymm (sup'_le _ _ fun c _ => ?_) (le_sup'_of_le _ (mem_univ ()) ?_) <;>
    simp [mmExample]

/-- Both pairs share the responder, whose cap is 1, so a capped set has at most one pair. -/
theorem mmExample_capOK (S : Finset (Fin 2 × Unit)) : mmExample.CapOK S ↔ S.card ≤ 1 := by
  have hsnd : S.filter (fun e => e.2 = ()) = S :=
    filter_true_of_mem fun e _ => Subsingleton.elim _ _
  constructor
  · intro h
    simpa [hsnd, mmExample] using h.2 ()
  · intro h
    refine ⟨fun i => ?_, fun j => ?_⟩
    · exact (card_filter_le _ _).trans (by simpa [mmExample] using h)
    · simpa [hsnd, mmExample] using h

/-- The best capped set within `F` is its heavier pair. -/
theorem mmExample_bestMatch (F : Finset (Fin 2 × Unit)) :
    mmExample.bestMatch F mmWt =
      if ((0 : Fin 2), ()) ∈ F then 11 else if ((1 : Fin 2), ()) ∈ F then 3 else 0 := by
  apply le_antisymm
  · obtain ⟨S, hSF, hS, hEq⟩ := mmExample.exists_bestMatch_eq F mmWt
    rw [hEq]
    obtain ⟨e, he⟩ := card_le_one_iff_subset_singleton.mp ((mmExample_capOK S).mp hS)
    rcases subset_singleton_iff.mp he with rfl | rfl
    · split_ifs <;> norm_num
    · have heF := hSF (mem_singleton_self e)
      obtain ⟨i, ⟨⟩⟩ := e
      rw [sum_singleton]
      fin_cases i <;> split_ifs <;> simp_all [mmWt]
      norm_num
  · have hle : ∀ e ∈ F, mmWt e ≤ mmExample.bestMatch F mmWt := fun e he => by
      simpa using mmExample.sum_le_bestMatch mmWt (singleton_subset_iff.mpr he)
        ((mmExample_capOK _).mpr (card_singleton e).le)
    have h0 : 0 ≤ mmExample.bestMatch F mmWt := by
      simpa using mmExample.sum_le_bestMatch mmWt (empty_subset F)
        ((mmExample_capOK _).mpr (by simp))
    split_ifs with h1 h2
    · simpa [mmWt] using hle _ h1
    · simpa [mmWt] using hle _ h2
    · exact h0

/-- A max-weight selection keeps `(1, j)` exactly when it is found and `(0, j)` is not. -/
theorem mmExample_sel_mem
    {sel : Finset (Fin 2 × Unit) → (Fin 2 × Unit → ℝ) → Finset (Fin 2 × Unit)}
    (hsel : mmExample.IsMaxWeightSel sel) (F : Finset (Fin 2 × Unit)) :
    ((1 : Fin 2), ()) ∈ sel F mmWt ↔ ((1 : Fin 2), ()) ∈ F ∧ ((0 : Fin 2), ()) ∉ F := by
  obtain ⟨hSF, hS, hsum⟩ := hsel F mmWt
  rw [mmExample_bestMatch] at hsum
  obtain ⟨e, he⟩ := card_le_one_iff_subset_singleton.mp ((mmExample_capOK _).mp hS)
  rcases subset_singleton_iff.mp he with h | h
  · rw [h] at hsum ⊢
    rw [sum_empty] at hsum
    split_ifs at hsum with h0 h1 <;> norm_num at hsum
    simp [h1]
  · have heF := hSF (h ▸ mem_singleton_self e)
    rw [h] at hsum ⊢
    obtain ⟨i, ⟨⟩⟩ := e
    rw [sum_singleton] at hsum
    fin_cases i <;> split_ifs at hsum <;> simp_all [mmWt]

/-- An expectation over the two pairs' outcomes, written out. -/
theorem prodExp_fin2Unit {Ω : Type*} [Fintype Ω] (μ : Fin 2 × Unit → Ω → ℝ)
    (g : (Fin 2 × Unit → Ω) → ℝ) :
    prodExp μ g = ∑ a, ∑ b, μ (0, ()) a * μ (1, ()) b * g (fun e => ![a, b] e.1) := by
  let E : (Fin 2 × Unit → Ω) ≃ Ω × Ω :=
    { toFun := fun ω => (ω (0, ()), ω (1, ()))
      invFun := fun t e => ![t.1, t.2] e.1
      left_inv := fun ω => by
        funext e
        obtain ⟨i, ⟨⟩⟩ := e
        fin_cases i <;> rfl
      right_inv := fun t => rfl }
  unfold prodExp
  refine (Fintype.sum_equiv E _ (fun t => μ (0, ()) t.1 * μ (1, ()) t.2 *
    g (fun e => ![t.1, t.2] e.1)) fun ω => ?_).trans ?_
  · have hω : (fun e : Fin 2 × Unit => ![(E ω).1, (E ω).2] e.1) = ω := E.left_inv ω
    rw [hω]
    simp only [Fintype.prod_prod_type, Fintype.prod_unique, Fin.prod_univ_two]
    rfl
  · simp only [Fintype.sum_prod_type]

/-- What initiator `1` gets from one run of SDH: 2 when its pair is found and `0`'s is
not, else nothing. -/
theorem mmExample_gain
    {sel : Finset (Fin 2 × Unit) → (Fin 2 × Unit → ℝ) → Finset (Fin 2 × Unit)}
    (hsel : mmExample.IsMaxWeightSel sel) (ω : Fin 2 × Unit → Unit × Bool) :
    ∑ e ∈ (sel (univ.filter fun e => (ω e).2 = true ∧ mmExample.Acc e (ω e).1)
        fun e => mmExample.wt e (ω e).1).filter (fun e => e.1 = 1),
      (mmExample.valI e (ω e).1 - mmExample.costI 1) =
    if (ω (1, ())).2 = true ∧ (ω (0, ())).2 = false then 2 else 0 := by
  have hw : (fun e => mmExample.wt e (ω e).1) = mmWt := funext fun e => mmExample_wt e _
  have hF : (univ.filter fun e => (ω e).2 = true ∧ mmExample.Acc e (ω e).1) =
      univ.filter fun e => (ω e).2 = true :=
    filter_congr fun e _ => by simp [mmExample_acc]
  rw [hw, hF]
  have hmem := mmExample_sel_mem hsel (univ.filter fun e => (ω e).2 = true)
  generalize sel (univ.filter fun e => (ω e).2 = true) mmWt = S at hmem
  have hfilt : S.filter (fun e => e.1 = 1) =
      if ((1 : Fin 2), ()) ∈ S then {((1 : Fin 2), ())} else ∅ := by
    ext ⟨i, u⟩
    cases u
    fin_cases i <;> split_ifs <;> simp_all
  rw [hfilt]
  split_ifs with h1 h2 h2 <;> simp_all [mmExample]
  norm_num

/-- Under SDH, with any tie-breaking, initiator `1` gets `2/9 = θ*/3`. -/
theorem mmExample_sdhUtil {sel : Finset (Fin 2 × Unit) → (Fin 2 × Unit → ℝ) → Finset (Fin 2 × Unit)}
    (hsel : mmExample.IsMaxWeightSel sel) :
    mmExample.sdhUtilI sel (mmExample.sdhTau mmExamplePlan) 1 = 2 / 9 := by
  unfold ScreenedMarket.sdhUtilI
  rw [prodExp_congr _ (mmExample_gain hsel), prodExp_fin2Unit, mmExample_sdhTau]
  simp [ScreenedMarket.screenLaw, mmExample, mmExamplePlan, Fintype.sum_prod_type]
  norm_num

/-- **The note's max-min guarantee fails for SDH's selection.** On a max-min optimal plan
with `θ* = 2/3` and every cap 1, SDH gives initiator `1` less than `c_1^2 θ*`. -/
theorem maxMin_sdh_counterexample
    {sel : Finset (Fin 2 × Unit) → (Fin 2 × Unit → ℝ) → Finset (Fin 2 × Unit)}
    (hsel : mmExample.IsMaxWeightSel sel) :
    mmExample.sdhUtilI sel (mmExample.sdhTau mmExamplePlan) 1 < cK 1 ^ 2 * (2 / 3) := by
  have hxy : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
  have hx : Real.exp (-1) < 0.4 := by
    nlinarith [Real.exp_pos (-1), Real.exp_one_gt_d9]
  rw [mmExample_sdhUtil hsel, cK_one]
  nlinarith [Real.exp_pos (-1)]

end DatingAlgo
