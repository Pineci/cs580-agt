import DatingAlgo.ProdExp

/-!
# Screened DH: welfare and oracle calls

Theorem 3(b)–(d) of the vault note "Truthful Swiping with an LLM Oracle", for size caps
(additive, top-`k` and general subadditive users). The matroid case of Theorem 3(b),
with constant `(1 - 1/e)^2`, is not formalized.

**Model.** Two sides `I`, `J`; every pair `e = (i, j)` may match. Each pair has an
independent random *value combination* `c : C` with law `π e`. Under `c`, `i` values `j`
at `valI e c` and `j` values `i` at `valJ e c`; matches cost `costI i` and `costJ j`.
The pair is *acceptable* when both values exceed their costs, and its *net weight* is
`wt e c = (valI - costI) + (valJ - costJ)`. Each user has a cap `capI i` or `capJ j`
on its IR set (the note's `b'`).
* `optIR`: the expected best capped set of acceptable pairs, knowing every value.
* The plan (the LP): `x e c ∈ [0, π e c]`, zero on unacceptable combinations, with
  `∑_j ∑_c x (i, j) c ≤ capI i` and `∑_i ∑_c x (i, j) c ≤ capJ j`.
* `sdhValue τ`: query each pair independently with probability `τ e`, then take the best
  capped set of pairs found acceptable.
* `sdhTau x e = max_c x e c / π e c`: SDH's query probability.

**Results.**
* `optIR_le_lpValue`: the LP bounds `OPT_IR` (proof of Theorem 3(b), first step).
* `lpValue_le_sdhValue`: `c_K^2 · LP ≤ SDH` for every feasible plan, where `K` is at most
  every cap (Theorem 3(b)). `sdh_welfare` combines the two.
* `sdhTau_le` and `sum_callsI_le` (Theorem 3(c)) for plans that fill each pair from
  its highest weights down (`BarShaped`); `exists_barShaped` shows an optimal plan can be
  taken bar-shaped.
* `sdh_budget` (Theorem 3(d)): scaling the plan by `λ` scales calls by `λ` and keeps
  `c_K^2 λ OPT_IR`.
* `welfare_eq_sum_wt`: on capped sets, users' utilities are additive, so welfare is the
  sum of net weights.

**A correction to the note.** The note's Theorem 3(c) fills each pair's highest-weight
combinations first in an arbitrary order. When two combinations tie at the bar, that can
give `τ_e = 1` with `x_e < p̂_e`, breaking `τ_e ≤ x_e / p̂_e`. `BarShaped` splits the bar
level proportionally instead, and `pHat` is defined precisely: the mass strictly above
the bar if positive, otherwise the mass at the bar.
-/

namespace DatingAlgo

open Finset

/-- A two-sided market with a truthful oracle; see the module docstring. -/
structure ScreenedMarket (I J C : Type*) where
  π : I × J → C → ℝ
  valI : I × J → C → ℝ
  valJ : I × J → C → ℝ
  costI : I → ℝ
  costJ : J → ℝ
  capI : I → ℕ
  capJ : J → ℕ

namespace ScreenedMarket

variable {I J C : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype C] [DecidableEq C] (M : ScreenedMarket I J C)

/-- Pair `e` is acceptable under combination `c`. -/
def Acc (e : I × J) (c : C) : Prop :=
  M.costI e.1 < M.valI e c ∧ M.costJ e.2 < M.valJ e c

noncomputable instance (e : I × J) : DecidablePred (M.Acc e) := fun _ => Classical.dec _

/-- Net weight of pair `e` under combination `c`. -/
def wt (e : I × J) (c : C) : ℝ :=
  (M.valI e c - M.costI e.1) + (M.valJ e c - M.costJ e.2)

/-- A match set respects every user's cap. -/
def CapOK (S : Finset (I × J)) : Prop :=
  (∀ i, (S.filter fun e => e.1 = i).card ≤ M.capI i) ∧
    ∀ j, (S.filter fun e => e.2 = j).card ≤ M.capJ j

noncomputable instance (S : Finset (I × J)) : Decidable (M.CapOK S) := Classical.dec _

/-- The best total weight of a capped match set inside `F`. -/
noncomputable def bestMatch (F : Finset (I × J)) (w : I × J → ℝ) : ℝ :=
  (F.powerset.filter M.CapOK).sup'
    ⟨∅, mem_filter.mpr ⟨empty_mem_powerset F, by simp [CapOK]⟩⟩ fun S => ∑ e ∈ S, w e

/-- `OPT_IR`: the expected best capped set of acceptable pairs, knowing every value. -/
noncomputable def optIR : ℝ :=
  prodExp M.π fun ω =>
    M.bestMatch (univ.filter fun e => M.Acc e (ω e)) fun e => M.wt e (ω e)

/-- Feasible plans: the constraints of the note's value-indexed LP. -/
def LPFeasible (x : I × J → C → ℝ) : Prop :=
  (∀ e c, 0 ≤ x e c ∧ x e c ≤ M.π e c) ∧ (∀ e c, ¬ M.Acc e c → x e c = 0) ∧
    (∀ i, ∑ j, ∑ c, x (i, j) c ≤ M.capI i) ∧ ∀ j, ∑ i, ∑ c, x (i, j) c ≤ M.capJ j

/-- The LP objective. -/
def lpValue (x : I × J → C → ℝ) : ℝ :=
  ∑ e, ∑ c, M.wt e c * x e c

/-- An optimal plan. -/
def IsLPOptimal (x : I × J → C → ℝ) : Prop :=
  M.LPFeasible x ∧ ∀ x', M.LPFeasible x' → M.lpValue x' ≤ M.lpValue x

/-- Law of a pair's (combination, queried?) outcome when it is queried with probability
`τ e`, independently of its values. -/
def screenLaw (τ : I × J → ℝ) (e : I × J) (o : C × Bool) : ℝ :=
  M.π e o.1 * if o.2 then τ e else 1 - τ e

/-- SDH's expected welfare with query probabilities `τ`: query each pair independently,
then take the best capped set among the pairs found acceptable. -/
noncomputable def sdhValue (τ : I × J → ℝ) : ℝ :=
  prodExp (M.screenLaw τ) fun ω =>
    M.bestMatch (univ.filter fun e => (ω e).2 = true ∧ M.Acc e (ω e).1)
      fun e => M.wt e (ω e).1

/-- SDH's query probability `τ_e = max_c x_{e,c} / π_{e,c}` (with `0 / 0 = 0`). -/
noncomputable def sdhTau [Nonempty C] (x : I × J → C → ℝ) (e : I × J) : ℝ :=
  univ.sup' univ_nonempty fun c => x e c / M.π e c

/-! ### Theorem 3(b): welfare -/

omit [Fintype C] [DecidableEq C] [Fintype I] in
/-- `i`'s number of matches in `S`, as a sum over partners. -/
theorem card_filter_fst (S : Finset (I × J)) (i : I) :
    ((S.filter fun e => e.1 = i).card : ℝ) = ∑ j, if (i, j) ∈ S then 1 else 0 := by
  rw [sum_boole]
  congr 1
  refine card_nbij' (fun e => e.2) (fun j => (i, j)) ?_ ?_ ?_ ?_
  · intro e he
    obtain ⟨heS, hei⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_univ _, by rw [← hei]; exact heS⟩
  · intro j hj
    exact mem_filter.mpr ⟨(mem_filter.mp hj).2, rfl⟩
  · intro e he
    obtain ⟨_, hei⟩ := mem_filter.mp he
    ext <;> simp [hei]
  · intro j _
    rfl

omit [Fintype C] [DecidableEq C] [Fintype J] in
/-- `j`'s number of matches in `S`, as a sum over partners. -/
theorem card_filter_snd (S : Finset (I × J)) (j : J) :
    ((S.filter fun e => e.2 = j).card : ℝ) = ∑ i, if (i, j) ∈ S then 1 else 0 := by
  rw [sum_boole]
  congr 1
  refine card_nbij' (fun e => e.1) (fun i => (i, j)) ?_ ?_ ?_ ?_
  · intro e he
    obtain ⟨heS, hej⟩ := mem_filter.mp he
    exact mem_filter.mpr ⟨mem_univ _, by rw [← hej]; exact heS⟩
  · intro i hi
    exact mem_filter.mpr ⟨(mem_filter.mp hi).2, rfl⟩
  · intro e he
    obtain ⟨_, hej⟩ := mem_filter.mp he
    ext <;> simp [hej]
  · intro i _
    rfl

omit [Fintype I] [Fintype J] [Fintype C] [DecidableEq C] in
/-- The best capped set inside `F` is attained. -/
theorem exists_bestMatch_eq (F : Finset (I × J)) (w : I × J → ℝ) :
    ∃ S, S ⊆ F ∧ M.CapOK S ∧ M.bestMatch F w = ∑ e ∈ S, w e := by
  unfold bestMatch
  obtain ⟨S, hS, hEq⟩ := exists_mem_eq_sup' (⟨∅, mem_filter.mpr ⟨empty_mem_powerset F, by
    simp [CapOK]⟩⟩ : (F.powerset.filter M.CapOK).Nonempty) (fun S => ∑ e ∈ S, w e)
  obtain ⟨hSF, hScap⟩ := mem_filter.mp hS
  exact ⟨S, mem_powerset.mp hSF, hScap, hEq⟩

omit [Fintype I] [Fintype J] [Fintype C] [DecidableEq C] in
/-- Every capped set inside `F` is a lower bound. -/
theorem sum_le_bestMatch {F S : Finset (I × J)} (w : I × J → ℝ) (hSF : S ⊆ F)
    (hS : M.CapOK S) : ∑ e ∈ S, w e ≤ M.bestMatch F w := by
  unfold bestMatch
  exact le_sup' (fun S => ∑ e ∈ S, w e) (mem_filter.mpr ⟨mem_powerset.mpr hSF, hS⟩)

omit [Fintype I] [Fintype J] [Fintype C] [DecidableEq C] in
/-- A larger ground set never hurts. -/
theorem bestMatch_mono {F F' : Finset (I × J)} (w : I × J → ℝ) (h : F ⊆ F') :
    M.bestMatch F w ≤ M.bestMatch F' w := by
  obtain ⟨S, hSF, hS, hEq⟩ := M.exists_bestMatch_eq F w
  rw [hEq]
  exact M.sum_le_bestMatch w (hSF.trans h) hS

/-- **Theorem 3(b), first step: the LP bounds `OPT_IR`.** The marginals of an optimal
capped set form a feasible plan whose value is `OPT_IR`. -/
theorem exists_lpValue_eq_optIR (hπ : IsDist M.π) :
    ∃ x, M.LPFeasible x ∧ M.lpValue x = M.optIR := by
  choose opt hoptF hoptCap hval using fun ω : I × J → C =>
    M.exists_bestMatch_eq (univ.filter fun e => M.Acc e (ω e)) fun e => M.wt e (ω e)
  set x : I × J → C → ℝ := fun e c =>
    prodExp M.π fun ω => if e ∈ opt ω ∧ ω e = c then 1 else 0 with hx_def
  -- Summing the indicator over combinations.
  have hsumc : ∀ (S : Finset (I × J)) (ω : I × J → C) (e : I × J),
      ∑ c, (if e ∈ S ∧ ω e = c then (1 : ℝ) else 0) = if e ∈ S then 1 else 0 := by
    intro S ω e
    by_cases he : e ∈ S <;> simp [he]
  -- Expected number of `i`'s matches.
  have hdegI : ∀ i, ∑ j, ∑ c, x (i, j) c =
      prodExp M.π fun ω => (((opt ω).filter fun e => e.1 = i).card : ℝ) := by
    intro i
    simp only [hx_def]
    simp_rw [← prodExp_sum]
    refine prodExp_congr _ fun ω => ?_
    rw [card_filter_fst]
    exact sum_congr rfl fun j _ => hsumc _ ω (i, j)
  have hdegJ : ∀ j, ∑ i, ∑ c, x (i, j) c =
      prodExp M.π fun ω => (((opt ω).filter fun e => e.2 = j).card : ℝ) := by
    intro j
    simp only [hx_def]
    simp_rw [← prodExp_sum]
    refine prodExp_congr _ fun ω => ?_
    rw [card_filter_snd]
    exact sum_congr rfl fun i _ => hsumc _ ω (i, j)
  refine ⟨x, ⟨fun e c => ⟨?_, ?_⟩, fun e c hc => ?_, fun i => ?_, fun j => ?_⟩, ?_⟩
  · exact prodExp_nonneg hπ.1 fun ω => by split_ifs <;> norm_num
  · calc x e c ≤ prodExp M.π (fun ω => if ω e = c then 1 else 0) :=
          prodExp_mono hπ.1 fun ω => by split_ifs <;> simp_all
      _ = M.π e c := by
          rw [prodExp_coord hπ.2 e (fun o => if o = c then 1 else 0)]
          simp
  · refine (prodExp_congr _ (h := fun _ => 0) fun ω => ?_).trans (prodExp_const hπ.2 0)
    split_ifs with h
    · exact absurd (h.2 ▸ (mem_filter.mp (hoptF ω h.1)).2) hc
    · rfl
  · rw [hdegI]
    calc _ ≤ prodExp M.π (fun _ => (M.capI i : ℝ)) :=
          prodExp_mono hπ.1 fun ω => by exact_mod_cast (hoptCap ω).1 i
      _ = M.capI i := prodExp_const hπ.2 _
  · rw [hdegJ]
    calc _ ≤ prodExp M.π (fun _ => (M.capJ j : ℝ)) :=
          prodExp_mono hπ.1 fun ω => by exact_mod_cast (hoptCap ω).2 j
      _ = M.capJ j := prodExp_const hπ.2 _
  · unfold lpValue optIR
    simp only [hx_def]
    simp_rw [← prodExp_const_mul, ← prodExp_sum]
    refine prodExp_congr _ fun ω => ?_
    rw [hval ω, ← sum_filter_add_sum_filter_not univ (· ∈ opt ω)]
    have hin : ∀ e, ∑ c, M.wt e c * (if e ∈ opt ω ∧ ω e = c then 1 else 0) =
        if e ∈ opt ω then M.wt e (ω e) else 0 := by
      intro e
      by_cases he : e ∈ opt ω <;> simp [he]
    simp_rw [hin]
    rw [sum_ite_of_false (fun e he => (mem_filter.mp he).2), sum_const_zero, add_zero,
      sum_ite_of_true (fun e he => (mem_filter.mp he).2)]
    exact (sum_congr (by ext e; simp) fun _ _ => rfl)

omit [DecidableEq I] [DecidableEq J] [DecidableEq C] in
/-- The feasible plans form a closed set. -/
theorem isClosed_lpFeasible : IsClosed {x : I × J → C → ℝ | M.LPFeasible x} := by
  simp only [LPFeasible, Set.ofPred_and, Set.ofPred_forall]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ (IsClosed.inter ?_ ?_))
  · exact isClosed_iInter fun e => isClosed_iInter fun c =>
      (isClosed_le continuous_const (by fun_prop)).inter (isClosed_le (by fun_prop) continuous_const)
  · exact isClosed_iInter fun e => isClosed_iInter fun c => isClosed_iInter fun _ =>
      isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const
  · exact isClosed_iInter fun j => isClosed_le (by fun_prop) continuous_const

omit [DecidableEq I] [DecidableEq J] [DecidableEq C] in
/-- The LP has an optimal plan: the feasible plans form a non-empty compact set and the
objective is continuous. -/
theorem exists_isLPOptimal (hπ : IsDist M.π) : ∃ x, M.IsLPOptimal x := by
  have hbox : IsCompact (Set.univ.pi fun e : I × J => Set.univ.pi fun c : C => Set.Icc 0 (M.π e c)) :=
    isCompact_univ_pi fun e => isCompact_univ_pi fun c => isCompact_Icc
  have hcpt : IsCompact {x : I × J → C → ℝ | M.LPFeasible x} :=
    hbox.of_isClosed_subset M.isClosed_lpFeasible fun x hx =>
      Set.mem_univ_pi.mpr fun e => Set.mem_univ_pi.mpr fun c => hx.1 e c
  have h0 : M.LPFeasible fun _ _ => 0 := by
    refine ⟨fun e c => ⟨le_rfl, hπ.1 e c⟩, fun _ _ _ => rfl, fun i => ?_, fun j => ?_⟩ <;> simp
  have hcont : Continuous M.lpValue := by unfold lpValue; fun_prop
  obtain ⟨x, hx, hmax⟩ := hcpt.exists_isMaxOn ⟨_, h0⟩ hcont.continuousOn
  exact ⟨x, hx, fun x' hx' => hmax hx'⟩

theorem optIR_le_lpValue (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.IsLPOptimal x) :
    M.optIR ≤ M.lpValue x := by
  obtain ⟨x', hx', hEq⟩ := M.exists_lpValue_eq_optIR hπ
  exact hEq ▸ hx.2 x' hx'

/-! #### The two-stage selection on thinned candidates

For the analysis only, thin the pairs SDH finds so that pair `e` is a candidate with
combination `c` with probability exactly `x e c` (`candLaw`). Stage 1: each `J`-side
user keeps its best `capJ j` candidates (`sel1`). Stage 2: each `I`-side user keeps its
best `capI i` of what was kept for it (`sel2`). The result (`twoStage`) is capped. -/

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype C] [DecidableEq C] in
theorem wt_pos {e : I × J} {c : C} (h : M.Acc e c) : 0 < M.wt e c := by
  unfold wt
  linarith [h.1, h.2]

/-- A candidate's weight: its net weight if acceptable, otherwise 0. -/
noncomputable def candWt (e : I × J) (o : Option C) : ℝ :=
  o.elim 0 fun c => if M.Acc e c then M.wt e c else 0

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype C] [DecidableEq C] in
theorem candWt_nonneg (e : I × J) (o : Option C) : 0 ≤ M.candWt e o := by
  cases o with
  | none => simp [candWt]
  | some c =>
    simp only [candWt, Option.elim]
    split_ifs with h
    · exact (M.wt_pos h).le
    · exact le_rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype C] [DecidableEq C] in
theorem candWt_none (e : I × J) : M.candWt e none = 0 := rfl

/-- Law of the thinned candidates: `e` is a candidate with combination `c` with
probability `x e c`. -/
def candLaw (x : I × J → C → ℝ) (e : I × J) (o : Option C) : ℝ :=
  o.elim (1 - ∑ c, x e c) fun c => x e c

omit [DecidableEq I] [DecidableEq J] [DecidableEq C] in
theorem sum_x_le_one (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasible x)
    (e : I × J) : ∑ c, x e c ≤ 1 := by
  rw [← hπ.2 e]
  exact sum_le_sum fun c _ => (hx.1 e c).2

omit [DecidableEq I] [DecidableEq J] [DecidableEq C] in
theorem isDist_candLaw (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasible x) :
    IsDist (candLaw x) := by
  refine ⟨fun e o => ?_, fun e => ?_⟩
  · cases o with
    | none => simp only [candLaw, Option.elim]; linarith [M.sum_x_le_one hπ hx e]
    | some c => exact (hx.1 e c).1
  · rw [Fintype.sum_option]
    simp [candLaw]

/-- Stage 1: the best `capJ j` candidates of column `j` with positive weight. -/
noncomputable def sel1 (j : J) (b : I → Option C) : Finset I :=
  (Classical.choose (exists_topK_eq (fun i => M.candWt (i, j) (b i)) (M.capJ j) univ)).filter
    fun i => 0 < M.candWt (i, j) (b i)

omit [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype C] [DecidableEq C] in
theorem sel1_spec (j : J) (b : I → Option C) :
    (M.sel1 j b).card ≤ M.capJ j ∧ (∀ i ∈ M.sel1 j b, 0 < M.candWt (i, j) (b i)) ∧
      ∑ i ∈ M.sel1 j b, M.candWt (i, j) (b i) =
        topK (fun i => M.candWt (i, j) (b i)) (M.capJ j) univ := by
  obtain ⟨_, hcard, hEq⟩ :=
    Classical.choose_spec (exists_topK_eq (fun i => M.candWt (i, j) (b i)) (M.capJ j) univ)
  refine ⟨(card_filter_le _ _).trans hcard, fun i hi => (mem_filter.mp hi).2, ?_⟩
  rw [hEq, sel1, sum_filter_of_ne]
  intro i _ hne
  exact lt_of_le_of_ne (M.candWt_nonneg _ _) (Ne.symm hne)

/-- What stage 1 passes on to row `i` from column `j`. -/
noncomputable def kept (i : I) (j : J) (b : I → Option C) : Option C :=
  if i ∈ M.sel1 j b then b i else none

/-- Stage 2: the best `capI i` of what row `i` was passed, with positive weight. -/
noncomputable def sel2 (i : I) (y : J → Option C) : Finset J :=
  (Classical.choose (exists_topK_eq (fun j => M.candWt (i, j) (y j)) (M.capI i) univ)).filter
    fun j => 0 < M.candWt (i, j) (y j)

omit [Fintype I] [DecidableEq I] [DecidableEq J] [Fintype C] [DecidableEq C] in
theorem sel2_spec (i : I) (y : J → Option C) :
    (M.sel2 i y).card ≤ M.capI i ∧ (∀ j ∈ M.sel2 i y, 0 < M.candWt (i, j) (y j)) ∧
      ∑ j ∈ M.sel2 i y, M.candWt (i, j) (y j) =
        topK (fun j => M.candWt (i, j) (y j)) (M.capI i) univ := by
  obtain ⟨_, hcard, hEq⟩ :=
    Classical.choose_spec (exists_topK_eq (fun j => M.candWt (i, j) (y j)) (M.capI i) univ)
  refine ⟨(card_filter_le _ _).trans hcard, fun j hj => (mem_filter.mp hj).2, ?_⟩
  rw [hEq, sel2, sum_filter_of_ne]
  intro j _ hne
  exact lt_of_le_of_ne (M.candWt_nonneg _ _) (Ne.symm hne)

/-- Row `i`'s view after stage 1. -/
noncomputable def rowView (η : I × J → Option C) (i : I) : J → Option C :=
  fun j => M.kept i j fun i' => η (i', j)

/-- The two-stage selection. -/
noncomputable def twoStage (η : I × J → Option C) : Finset (I × J) :=
  univ.filter fun e => e.2 ∈ M.sel2 e.1 (M.rowView η e.1)

omit [DecidableEq J] [Fintype C] in
theorem mem_sel1_of_mem_sel2 {η : I × J → Option C} {i : I} {j : J}
    (h : j ∈ M.sel2 i (M.rowView η i)) :
    i ∈ M.sel1 j (fun i' => η (i', j)) ∧ M.rowView η i j = η (i, j) := by
  have hpos := (M.sel2_spec i _).2.1 j h
  by_contra hcon
  have : M.rowView η i j = none := by
    simp only [rowView, kept]
    split_ifs with h1
    · exact absurd ⟨h1, by simp [rowView, kept, h1]⟩ hcon
    · rfl
  rw [this, candWt_none] at hpos
  exact lt_irrefl 0 hpos

omit [Fintype C] in
theorem twoStage_capOK (η : I × J → Option C) : M.CapOK (M.twoStage η) := by
  constructor
  · intro i
    have h := card_filter_fst (M.twoStage η) i
    have hrow : ∑ j, (if (i, j) ∈ M.twoStage η then (1 : ℝ) else 0) =
        ((M.sel2 i (M.rowView η i)).card : ℝ) := by
      rw [sum_boole]
      congr 2
      ext j
      simp [twoStage]
    have h' : ((M.twoStage η).filter fun e => e.1 = i).card =
        (M.sel2 i (M.rowView η i)).card := by exact_mod_cast h.trans hrow
    rw [h']
    exact (M.sel2_spec i _).1
  · intro j
    have h := card_filter_snd (M.twoStage η) j
    have hcol : ∑ i, (if (i, j) ∈ M.twoStage η then (1 : ℝ) else 0) ≤
        ((M.sel1 j (fun i' => η (i', j))).card : ℝ) := by
      rw [sum_boole]
      exact_mod_cast card_le_card fun i hi => by
        simp only [twoStage, mem_filter, mem_univ, true_and] at hi
        exact (M.mem_sel1_of_mem_sel2 hi).1
    have h' : ((M.twoStage η).filter fun e => e.2 = j).card ≤
        (M.sel1 j fun i' => η (i', j)).card := by exact_mod_cast h ▸ hcol
    exact h'.trans (M.sel1_spec j _).1

omit [Fintype C] in
/-- The two-stage selection is worth the sum of the rows' stage-2 values. -/
theorem sum_twoStage (η : I × J → Option C) :
    ∑ e ∈ M.twoStage η, M.candWt e (η e) =
      ∑ i, topK (fun j => M.candWt (i, j) (M.rowView η i j)) (M.capI i) univ := by
  rw [twoStage, sum_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  rw [← (M.sel2_spec i _).2.2, ← sum_filter]
  refine sum_congr (by ext j; simp) fun j hj => ?_
  rw [(M.mem_sel1_of_mem_sel2 hj).2]

omit [Fintype J] [DecidableEq J] [Fintype C] [DecidableEq C] in
/-- Stage 1 passes on exactly the column's best value. -/
theorem sum_rowView (η : I × J → Option C) (j : J) :
    ∑ i, M.candWt (i, j) (M.rowView η i j) =
      topK (fun i => M.candWt (i, j) (η (i, j))) (M.capJ j) univ := by
  rw [← (M.sel1_spec j _).2.2, ← sum_filter_add_sum_filter_not univ
    (· ∈ M.sel1 j fun i' => η (i', j))]
  have h2 : ∑ i ∈ univ.filter (fun i => i ∉ M.sel1 j fun i' => η (i', j)),
      M.candWt (i, j) (M.rowView η i j) = 0 :=
    sum_eq_zero fun i hi => by
      simp only [rowView, kept, (mem_filter.mp hi).2, ↓reduceIte, candWt_none]
  rw [h2, add_zero]
  refine sum_congr (by ext i; simp) fun i hi => ?_
  simp only [rowView, kept, hi, ↓reduceIte]

/-- Expected candidate weight in one pair. -/
theorem prodExp_candWt (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasible x)
    (e : I × J) :
    prodExp (candLaw x) (fun η => M.candWt e (η e)) = ∑ c, x e c * M.wt e c := by
  rw [prodExp_coord (M.isDist_candLaw hπ hx).2 e, Fintype.sum_option]
  simp only [candLaw, candWt, Option.elim, mul_zero, zero_add]
  refine sum_congr rfl fun c _ => ?_
  split_ifs with h
  · rfl
  · rw [hx.2.1 e c h, zero_mul, zero_mul]

/-- Probability that a pair's candidate weight is positive. -/
theorem prodExp_candWt_pos_le (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasible x)
    (e : I × J) :
    prodExp (candLaw x) (fun η => if 0 < M.candWt e (η e) then 1 else 0) ≤ ∑ c, x e c := by
  rw [prodExp_coord (M.isDist_candLaw hπ hx).2 e (fun o => if 0 < M.candWt e o then 1 else 0),
    Fintype.sum_option]
  simp only [candLaw, candWt_none, lt_irrefl, ↓reduceIte, mul_zero, zero_add, Option.elim]
  refine sum_le_sum fun c _ => ?_
  split_ifs
  · rw [mul_one]
  · rw [mul_zero]; exact (hx.1 e c).1

/-- **Theorem 3(b) on the thinned candidates.** The best capped set of candidates is
worth at least `c_K^2 · LP` in expectation. -/
theorem lpValue_le_candidates (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasible x)
    (K : ℕ) (hKI : ∀ i, K ≤ M.capI i) (hKJ : ∀ j, K ≤ M.capJ j) :
    cK K ^ 2 * M.lpValue x ≤
      prodExp (candLaw x) (fun η => M.bestMatch univ fun e => M.candWt e (η e)) := by
  have hν := M.isDist_candLaw hπ hx
  have hcK := cK_nonneg K
  -- Row values after stage 1.
  set A : I → ℝ := fun i =>
    prodExp (candLaw x) (fun η => ∑ j, M.candWt (i, j) (M.rowView η i j)) with hA_def
  set B : J → ℝ := fun j =>
    prodExp (candLaw x) (fun η => ∑ i, M.candWt (i, j) (η (i, j))) with hB_def
  have hA0 : ∀ i, 0 ≤ A i := fun i =>
    prodExp_nonneg hν.1 fun η => sum_nonneg fun j _ => M.candWt_nonneg _ _
  have hB0 : ∀ j, 0 ≤ B j := fun j =>
    prodExp_nonneg hν.1 fun η => sum_nonneg fun i _ => M.candWt_nonneg _ _
  -- The best capped set beats the two-stage selection.
  have h1 : ∑ i, prodExp (candLaw x)
      (fun η => topK (fun j => M.candWt (i, j) (M.rowView η i j)) (M.capI i) univ) ≤
      prodExp (candLaw x) (fun η => M.bestMatch univ fun e => M.candWt e (η e)) := by
    rw [← prodExp_sum]
    refine prodExp_mono hν.1 fun η => ?_
    rw [← M.sum_twoStage]
    exact M.sum_le_bestMatch _ (subset_univ _) (M.twoStage_capOK η)
  -- Stage 2: each row keeps `c_{capI i}` of what it was passed.
  have h2 : ∀ i, cK K * A i ≤ prodExp (candLaw x)
      (fun η => topK (fun j => M.candWt (i, j) (M.rowView η i j)) (M.capI i) univ) := by
    intro i
    refine le_trans (mul_le_mul_of_nonneg_right (cK_mono (hKI i)) (hA0 i)) ?_
    refine prodExp_columns_gap hν (fun j b => M.kept i j b) (fun j o => M.candWt (i, j) o)
      (fun j o => M.candWt_nonneg _ _) (M.capI i) ?_
    refine le_trans (sum_le_sum fun j _ => ?_) (hx.2.2.1 i)
    refine le_trans (prodExp_mono hν.1 fun η => ?_) (M.prodExp_candWt_pos_le hπ hx (i, j))
    by_cases hmem : i ∈ M.sel1 j (fun i' => η (i', j))
    · simp only [kept, hmem, ↓reduceIte]
      exact le_rfl
    · simp only [kept, hmem, ↓reduceIte, candWt_none, lt_irrefl]
      split_ifs <;> norm_num
  -- Stage 1 output equals the columns' values.
  have h3 : ∑ i, A i = ∑ j, prodExp (candLaw x)
      (fun η => topK (fun i => M.candWt (i, j) (η (i, j))) (M.capJ j) univ) := by
    simp only [hA_def]
    rw [← prodExp_sum, ← prodExp_sum]
    refine prodExp_congr _ fun η => ?_
    rw [sum_comm]
    exact sum_congr rfl fun j _ => M.sum_rowView η j
  -- Stage 1: each column keeps `c_{capJ j}` of its candidates.
  have h4 : ∀ j, cK K * B j ≤ prodExp (candLaw x)
      (fun η => topK (fun i => M.candWt (i, j) (η (i, j))) (M.capJ j) univ) := by
    intro j
    refine le_trans (mul_le_mul_of_nonneg_right (cK_mono (hKJ j)) (hB0 j)) ?_
    simp only [hB_def]
    rw [prodExp_column hν.2 j (fun b => ∑ i, M.candWt (i, j) (b i)),
      prodExp_column hν.2 j (fun b => topK (fun i => M.candWt (i, j) (b i)) (M.capJ j) univ)]
    have hνj : IsDist (fun i o => candLaw x (i, j) o) := ⟨fun i o => hν.1 _ o, fun i => hν.2 _⟩
    refine prodExp_randomWeight_gap (ρ := fun i o => candLaw x (i, j) o) hνj (M.capJ j)
      (fun i o => M.candWt (i, j) o) (fun i o => M.candWt_nonneg _ _) ?_
    refine le_trans (sum_le_sum fun i _ => ?_) (hx.2.2.2 j)
    have := M.prodExp_candWt_pos_le hπ hx (i, j)
    rw [prodExp_coord hν.2 (i, j) (fun o => if 0 < M.candWt (i, j) o then 1 else 0)] at this
    rw [sum_filter]
    simpa [mul_ite, mul_one, mul_zero] using this
  -- The columns' candidates carry the LP's value.
  have h5 : ∑ j, B j = M.lpValue x := by
    simp only [hB_def]
    rw [lpValue, Fintype.sum_prod_type, sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [prodExp_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [M.prodExp_candWt hπ hx (i, j)]
    exact sum_congr rfl fun c _ => mul_comm _ _
  calc cK K ^ 2 * M.lpValue x = cK K * ∑ j, cK K * B j := by
        rw [← h5, mul_sum, mul_sum]; exact sum_congr rfl fun j _ => by ring
    _ ≤ cK K * ∑ i, A i := mul_le_mul_of_nonneg_left (h3 ▸ sum_le_sum fun j _ => h4 j) hcK
    _ = ∑ i, cK K * A i := mul_sum _ _ _
    _ ≤ _ := (sum_le_sum fun i _ => h2 i).trans h1

/-! #### Thinning: SDH's found pairs contain the candidates

Each pair's outcome is extended with a *keep* coin: a pair found with combination `c` is
kept with probability `x e c / (τ e π e c)`. Forgetting the keep coin gives SDH's
screening (`screenLaw`); keeping only kept acceptable pairs gives the candidates
(`candLaw`). Every candidate is found, so SDH does at least as well. -/

omit [Fintype I] [Fintype J] [Fintype C] [DecidableEq C] in
theorem CapOK.subset {S T : Finset (I × J)} (hS : M.CapOK S) (hTS : T ⊆ S) : M.CapOK T :=
  ⟨fun i => (card_le_card (filter_subset_filter _ hTS)).trans (hS.1 i),
    fun j => (card_le_card (filter_subset_filter _ hTS)).trans (hS.2 j)⟩

/-- Probability of keeping a found pair with combination `c`. -/
noncomputable def keepProb (x : I × J → C → ℝ) (τ : I × J → ℝ) (e : I × J) (c : C) : ℝ :=
  x e c / (τ e * M.π e c)

/-- Law of (combination, queried?, kept?). -/
noncomputable def thinLaw (x : I × J → C → ℝ) (τ : I × J → ℝ) (e : I × J)
    (o : C × Bool × Bool) : ℝ :=
  M.π e o.1 * (if o.2.1 then τ e else 1 - τ e) *
    if o.2.2 then M.keepProb x τ e o.1 else 1 - M.keepProb x τ e o.1

/-- The candidate an extended outcome produces. -/
noncomputable def candOf (e : I × J) (o : C × Bool × Bool) : Option C :=
  if o.2.1 = true ∧ o.2.2 = true ∧ M.Acc e o.1 then some o.1 else none

omit [DecidableEq I] [DecidableEq J] [DecidableEq C] in
theorem keepProb_mem (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasible x)
    {τ : I × J → ℝ} (hτ : ∀ e, 0 ≤ τ e ∧ τ e ≤ 1) (hτx : ∀ e c, x e c ≤ τ e * M.π e c)
    (e : I × J) (c : C) : 0 ≤ M.keepProb x τ e c ∧ M.keepProb x τ e c ≤ 1 := by
  have hden : 0 ≤ τ e * M.π e c := mul_nonneg (hτ e).1 (hπ.1 e c)
  refine ⟨div_nonneg (hx.1 e c).1 hden, ?_⟩
  rcases hden.eq_or_lt with h0 | h0
  · rw [keepProb, ← h0, div_zero]; exact zero_le_one
  · exact (div_le_one h0).mpr (hτx e c)

omit [DecidableEq I] [DecidableEq J] [DecidableEq C] in
theorem thinLaw_true_true (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasible x)
    {τ : I × J → ℝ} (hτ : ∀ e, 0 ≤ τ e ∧ τ e ≤ 1) (hτx : ∀ e c, x e c ≤ τ e * M.π e c)
    (e : I × J) (c : C) : M.thinLaw x τ e (c, true, true) = x e c := by
  simp only [thinLaw, keepProb, ↓reduceIte]
  have hden : 0 ≤ τ e * M.π e c := mul_nonneg (hτ e).1 (hπ.1 e c)
  rcases hden.eq_or_lt with h0 | h0
  · have hx0 : x e c = 0 := le_antisymm (h0 ▸ hτx e c) (hx.1 e c).1
    rw [hx0, zero_div, mul_zero]
  · rw [mul_comm (M.π e c) (τ e), mul_div_cancel₀ _ h0.ne']

omit [DecidableEq I] [DecidableEq J] [DecidableEq C] in
theorem isDist_thinLaw (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasible x)
    {τ : I × J → ℝ} (hτ : ∀ e, 0 ≤ τ e ∧ τ e ≤ 1) (hτx : ∀ e c, x e c ≤ τ e * M.π e c) :
    IsDist (M.thinLaw x τ) := by
  refine ⟨fun e o => ?_, fun e => ?_⟩
  · have hk := M.keepProb_mem hπ hx hτ hτx e o.1
    refine mul_nonneg (mul_nonneg (hπ.1 e o.1) ?_) ?_
    · split_ifs
      · exact (hτ e).1
      · linarith [(hτ e).2]
    · split_ifs
      · exact hk.1
      · linarith [hk.2]
  · rw [Fintype.sum_prod_type, ← hπ.2 e]
    refine sum_congr rfl fun c _ => ?_
    rw [Fintype.sum_prod_type]
    simp only [thinLaw, Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]
    ring

/-- Forgetting the keep coin gives SDH's screening. -/
theorem sdhValue_eq_thin (x : I × J → C → ℝ) (τ : I × J → ℝ) :
    M.sdhValue τ = prodExp (M.thinLaw x τ) fun ω =>
      M.bestMatch (univ.filter fun e => (ω e).2.1 = true ∧ M.Acc e (ω e).1)
        fun e => M.wt e (ω e).1 := by
  rw [prodExp_map (M.thinLaw x τ) (fun _ o => (o.1, o.2.1)) (fun ω =>
      M.bestMatch (univ.filter fun e => (ω e).2 = true ∧ M.Acc e (ω e).1)
        fun e => M.wt e (ω e).1)]
  unfold sdhValue
  congr 1
  funext e o
  obtain ⟨c, q⟩ := o
  rw [sum_filter, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [Prod.mk.injEq]
  rw [sum_eq_single c (fun c' _ hc' => by simp [hc']) (fun h => absurd (mem_univ c) h)]
  simp only [true_and]
  rw [sum_eq_single q (fun q' _ hq' => by simp [hq']) (fun h => absurd (mem_univ q) h)]
  simp only [↓reduceIte, Fintype.sum_bool, thinLaw, screenLaw, Bool.false_eq_true]
  ring

/-- Keeping only kept acceptable pairs gives the candidates. -/
theorem candidates_eq_thin (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasible x)
    {τ : I × J → ℝ} (hτ : ∀ e, 0 ≤ τ e ∧ τ e ≤ 1) (hτx : ∀ e c, x e c ≤ τ e * M.π e c)
    (H : (I × J → Option C) → ℝ) :
    prodExp (M.thinLaw x τ) (fun ω => H fun e => M.candOf e (ω e)) =
      prodExp (candLaw x) H := by
  rw [prodExp_map (M.thinLaw x τ) M.candOf H]
  have hsome : ∀ e c, ∑ o ∈ univ.filter (fun o => M.candOf e o = some c),
      M.thinLaw x τ e o = x e c := by
    intro e c
    have hiff : ∀ o, M.candOf e o = some c ↔ (M.Acc e c ∧ o = (c, true, true)) := by
      rintro ⟨c', q, k⟩
      simp only [candOf]
      split_ifs with h
      · simp only [Option.some.injEq, Prod.mk.injEq]
        constructor
        · rintro rfl
          exact ⟨h.2.2, rfl, h.1, h.2.1⟩
        · rintro ⟨-, rfl, -, -⟩
          rfl
      · simp only [false_iff, not_and, Prod.mk.injEq]
        rintro hc rfl rfl rfl
        exact h ⟨rfl, rfl, hc⟩
    rw [filter_congr fun o _ => hiff o]
    by_cases hc : M.Acc e c
    · simp only [hc, true_and, filter_eq', mem_univ, ↓reduceIte, sum_singleton]
      exact M.thinLaw_true_true hπ hx hτ hτx e c
    · simp [hc, hx.2.1 e c hc]
  congr 1
  funext e o
  cases o with
  | some c => exact hsome e c
  | none =>
    have htot := (isDist_map (M.isDist_thinLaw hπ hx hτ hτx) M.candOf).2 e
    rw [Fintype.sum_option] at htot
    simp only [hsome] at htot
    simp only [candLaw, Option.elim]
    linarith

omit [Fintype C] [DecidableEq C] in
/-- Every candidate is found, with the same weight. -/
theorem bestMatch_cand_le (ω : I × J → C × Bool × Bool) :
    M.bestMatch univ (fun e => M.candWt e (M.candOf e (ω e))) ≤
      M.bestMatch (univ.filter fun e => (ω e).2.1 = true ∧ M.Acc e (ω e).1)
        fun e => M.wt e (ω e).1 := by
  obtain ⟨S, -, hS, hEq⟩ := M.exists_bestMatch_eq univ fun e => M.candWt e (M.candOf e (ω e))
  rw [hEq, ← sum_filter_of_ne (p := fun e => 0 < M.candWt e (M.candOf e (ω e)))
    (fun e _ hne => lt_of_le_of_ne (M.candWt_nonneg _ _) (Ne.symm hne))]
  have hpos : ∀ e, 0 < M.candWt e (M.candOf e (ω e)) →
      ((ω e).2.1 = true ∧ M.Acc e (ω e).1) ∧
        M.candWt e (M.candOf e (ω e)) = M.wt e (ω e).1 := by
    intro e h
    unfold candOf at h ⊢
    split_ifs at h ⊢ with hc
    · refine ⟨⟨hc.1, hc.2.2⟩, ?_⟩
      simp [candWt, hc.2.2]
    · exact absurd h (lt_irrefl 0)
  calc ∑ e ∈ S.filter _, M.candWt e (M.candOf e (ω e))
      = ∑ e ∈ S.filter (fun e => 0 < M.candWt e (M.candOf e (ω e))), M.wt e (ω e).1 :=
        sum_congr rfl fun e he => (hpos e (mem_filter.mp he).2).2
    _ ≤ _ := M.sum_le_bestMatch _ (fun e he => mem_filter.mpr ⟨mem_univ _,
        (hpos e (mem_filter.mp he).2).1⟩) (CapOK.subset M hS (filter_subset _ _))

/-- **Theorem 3(b), main step.** For every feasible plan `x` and query probabilities `τ`
that find each combination at least as often as the plan uses it
(`x e c ≤ τ e · π e c`), SDH earns at least `c_K^2` times the plan's value, where `K`
is at most every cap. -/
theorem lpValue_le_sdhValue (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasible x)
    {τ : I × J → ℝ} (hτ : ∀ e, 0 ≤ τ e ∧ τ e ≤ 1) (hτx : ∀ e c, x e c ≤ τ e * M.π e c)
    (K : ℕ) (hKI : ∀ i, K ≤ M.capI i) (hKJ : ∀ j, K ≤ M.capJ j) :
    cK K ^ 2 * M.lpValue x ≤ M.sdhValue τ := by
  refine (M.lpValue_le_candidates hπ hx K hKI hKJ).trans ?_
  rw [← M.candidates_eq_thin hπ hx hτ hτx, M.sdhValue_eq_thin x τ]
  exact prodExp_mono (M.isDist_thinLaw hπ hx hτ hτx).1 fun ω => M.bestMatch_cand_le ω

omit [DecidableEq I] [DecidableEq J] [DecidableEq C] in
/-- SDH's `τ_e = max_c x_{e,c} / π_{e,c}` is a probability and finds each combination
at least as often as the plan uses it. -/
theorem sdhTau_spec [Nonempty C] {x : I × J → C → ℝ} (hx : M.LPFeasible x) :
    (∀ e, 0 ≤ M.sdhTau x e ∧ M.sdhTau x e ≤ 1) ∧ ∀ e c, x e c ≤ M.sdhTau x e * M.π e c := by
  have hdiv : ∀ e c, 0 ≤ x e c / M.π e c ∧ x e c / M.π e c ≤ 1 := fun e c => by
    obtain ⟨h0, h1⟩ := hx.1 e c
    refine ⟨div_nonneg h0 (h0.trans h1), ?_⟩
    rcases (h0.trans h1).eq_or_lt with hπ0 | hπ0
    · rw [← hπ0, div_zero]; exact zero_le_one
    · exact (div_le_one hπ0).mpr h1
  refine ⟨fun e => ⟨?_, ?_⟩, fun e c => ?_⟩
  · obtain ⟨c⟩ := ‹Nonempty C›
    exact (hdiv e c).1.trans (le_sup' (fun c => x e c / M.π e c) (mem_univ c))
  · exact sup'_le _ _ fun c _ => (hdiv e c).2
  · obtain ⟨h0, h1⟩ := hx.1 e c
    rcases (h0.trans h1).eq_or_lt with hπ0 | hπ0
    · rw [← hπ0, mul_zero]; rw [← hπ0] at h1; exact h1
    · have := le_sup' (fun c => x e c / M.π e c) (mem_univ c)
      exact (div_le_iff₀ hπ0).mp this

/-- **Theorem 3(b).** SDH run on an optimal plan earns at least `c_K^2 · OPT_IR`, where
`K` is at most every cap (the note's `b' = min_ℓ b'_ℓ`). -/
theorem sdh_welfare [Nonempty C] (hπ : IsDist M.π) {x : I × J → C → ℝ}
    (hx : M.IsLPOptimal x) (K : ℕ) (hKI : ∀ i, K ≤ M.capI i) (hKJ : ∀ j, K ≤ M.capJ j) :
    cK K ^ 2 * M.optIR ≤ M.sdhValue (M.sdhTau x) := by
  have hspec := M.sdhTau_spec hx.1
  calc cK K ^ 2 * M.optIR ≤ cK K ^ 2 * M.lpValue x :=
        mul_le_mul_of_nonneg_left (M.optIR_le_lpValue hπ hx) (sq_nonneg _)
    _ ≤ _ := M.lpValue_le_sdhValue hπ hx.1 hspec.1 hspec.2 K hKI hKJ

/-! ### Theorem 3(c): oracle calls -/

/-- Probability that `i` accepts `j` (pair `e`). -/
noncomputable def phiI (e : I × J) : ℝ :=
  ∑ c ∈ univ.filter (fun c => M.costI e.1 < M.valI e c), M.π e c

/-- Probability that `j` accepts `i` (pair `e`). -/
noncomputable def phiJ (e : I × J) : ℝ :=
  ∑ c ∈ univ.filter (fun c => M.costJ e.2 < M.valJ e c), M.π e c

/-- Expected calls charged to `i` for pair `e`: the side less likely to accept is asked
first (`i` on ties), and the other side only if the first accepts. -/
noncomputable def callsI (τ : I × J → ℝ) (e : I × J) : ℝ :=
  τ e * if M.phiI e ≤ M.phiJ e then 1 else M.phiJ e

/-- Expected calls charged to `j` for pair `e`. -/
noncomputable def callsJ (τ : I × J → ℝ) (e : I × J) : ℝ :=
  τ e * if M.phiI e ≤ M.phiJ e then M.phiI e else 1

/-- The plan for pair `e` is *bar-shaped* with bar `θ` and fraction `f`: acceptable
combinations above the bar are used whenever they occur, those at the bar a fraction `f`
of the time, those below never. -/
def BarShaped (x : I × J → C → ℝ) (e : I × J) (θ f : ℝ) : Prop :=
  0 ≤ f ∧ f ≤ 1 ∧ ∀ c, M.Acc e c →
    (θ < M.wt e c → x e c = M.π e c) ∧ (M.wt e c = θ → x e c = f * M.π e c) ∧
      (M.wt e c < θ → x e c = 0)

/-- `p̂_e` for bar `θ`: the probability of an acceptable combination strictly above the bar
if that is positive, otherwise the probability of one at the bar. -/
noncomputable def pHat (e : I × J) (θ : ℝ) : ℝ :=
  if 0 < ∑ c ∈ univ.filter (fun c => M.Acc e c ∧ θ < M.wt e c), M.π e c then
    ∑ c ∈ univ.filter (fun c => M.Acc e c ∧ θ < M.wt e c), M.π e c
  else ∑ c ∈ univ.filter (fun c => M.Acc e c ∧ M.wt e c = θ), M.π e c

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [DecidableEq C] in
/-- A pair's calls are at most `τ_e`, charged to either side. -/
theorem phiI_mem (hπ : IsDist M.π) (e : I × J) : 0 ≤ M.phiI e ∧ M.phiI e ≤ 1 := by
  refine ⟨sum_nonneg fun c _ => hπ.1 e c, ?_⟩
  rw [← hπ.2 e]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun c _ _ => hπ.1 e c

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [DecidableEq C] in
theorem phiJ_mem (hπ : IsDist M.π) (e : I × J) : 0 ≤ M.phiJ e ∧ M.phiJ e ≤ 1 := by
  refine ⟨sum_nonneg fun c _ => hπ.1 e c, ?_⟩
  rw [← hπ.2 e]
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun c _ _ => hπ.1 e c

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [DecidableEq C] in
theorem callsI_le (τ : I × J → ℝ) (hτ : ∀ e, 0 ≤ τ e) (hπ : IsDist M.π) (e : I × J) :
    M.callsI τ e ≤ τ e := by
  unfold callsI
  split_ifs
  · rw [mul_one]
  · exact mul_le_of_le_one_right (hτ e) (M.phiJ_mem hπ e).2

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [DecidableEq C] in
theorem callsJ_le (τ : I × J → ℝ) (hτ : ∀ e, 0 ≤ τ e) (hπ : IsDist M.π) (e : I × J) :
    M.callsJ τ e ≤ τ e := by
  unfold callsJ
  split_ifs
  · exact mul_le_of_le_one_right (hτ e) (M.phiI_mem hπ e).2
  · rw [mul_one]

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [DecidableEq C] in
/-- A queried pair costs `1 + min(φ_I, φ_J) ≤ 1 + √(φ_I φ_J)` calls in expectation. -/
theorem callsI_add_callsJ (τ : I × J → ℝ) (hτ : ∀ e, 0 ≤ τ e) (hπ : IsDist M.π)
    (e : I × J) :
    M.callsI τ e + M.callsJ τ e ≤ τ e * (1 + Real.sqrt (M.phiI e * M.phiJ e)) := by
  have hI := M.phiI_mem hπ e
  have hJ := M.phiJ_mem hπ e
  have hmin : min (M.phiI e) (M.phiJ e) ≤ Real.sqrt (M.phiI e * M.phiJ e) := by
    apply Real.le_sqrt_of_sq_le
    rcases le_total (M.phiI e) (M.phiJ e) with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  have hsum : M.callsI τ e + M.callsJ τ e = τ e * (1 + min (M.phiI e) (M.phiJ e)) := by
    unfold callsI callsJ
    split_ifs with h
    · rw [min_eq_left h]; ring
    · rw [min_eq_right (not_le.mp h).le]; ring
  rw [hsum]
  exact mul_le_mul_of_nonneg_left (by linarith) (hτ e)

omit [DecidableEq I] [DecidableEq J] [DecidableEq C] in
/-- **Theorem 3(c), one pair.** For a bar-shaped plan, `τ_e ≤ x_e / p̂_e`. -/
theorem sdhTau_le [Nonempty C] (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasible x)
    {e : I × J} {θ f : ℝ} (hbar : M.BarShaped x e θ f) (hxe : 0 < ∑ c, x e c) :
    M.sdhTau x e ≤ (∑ c, x e c) / M.pHat e θ := by
  obtain ⟨hf0, hf1, hshape⟩ := hbar
  have hspec := M.sdhTau_spec hx
  set above := ∑ c ∈ univ.filter (fun c => M.Acc e c ∧ θ < M.wt e c), M.π e c
  set atBar := ∑ c ∈ univ.filter (fun c => M.Acc e c ∧ M.wt e c = θ), M.π e c
  unfold pHat
  split_ifs with habove
  · -- Combinations above the bar are always used, so `x_e ≥ p̂_e` and `τ_e ≤ 1`.
    have hge : above ≤ ∑ c, x e c := by
      calc above = ∑ c ∈ univ.filter (fun c => M.Acc e c ∧ θ < M.wt e c), x e c :=
            sum_congr rfl fun c hc => ((hshape c (mem_filter.mp hc).2.1).1
              (mem_filter.mp hc).2.2).symm
        _ ≤ ∑ c, x e c := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            fun c _ _ => (hx.1 e c).1
    exact (hspec.1 e).2.trans ((one_le_div habove).mpr hge)
  · -- Nothing above the bar has mass: `τ_e ≤ f` and `x_e = f · p̂_e`.
    have habove0 : ∀ c, M.Acc e c → θ < M.wt e c → M.π e c = 0 := by
      have h0 : above = 0 := le_antisymm (not_lt.mp habove)
        (sum_nonneg fun c _ => hπ.1 e c)
      intro c hc hθ
      exact (sum_eq_zero_iff_of_nonneg fun c _ => hπ.1 e c).mp h0 c
        (mem_filter.mpr ⟨mem_univ _, hc, hθ⟩)
    have hxc : ∀ c, x e c = if M.Acc e c ∧ M.wt e c = θ then f * M.π e c else 0 := by
      intro c
      split_ifs with h
      · exact (hshape c h.1).2.1 h.2
      · by_cases hc : M.Acc e c
        · have hne : M.wt e c ≠ θ := fun h' => h ⟨hc, h'⟩
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact (hshape c hc).2.2 hlt
          · rw [(hshape c hc).1 hgt, habove0 c hc hgt]
        · exact hx.2.1 e c hc
    have hsum : ∑ c, x e c = f * atBar := by
      rw [sum_congr rfl fun c _ => hxc c, ← sum_filter, mul_sum]
    have hτf : M.sdhTau x e ≤ f := by
      refine sup'_le _ _ fun c _ => ?_
      rw [hxc c]
      split_ifs
      · rcases (hπ.1 e c).eq_or_lt with h0 | h0
        · rw [← h0, mul_zero, div_zero]; exact hf0
        · rw [mul_div_assoc, div_self h0.ne', mul_one]
      · rw [zero_div]; exact hf0
    have hat : 0 < atBar := by
      rw [hsum] at hxe
      by_contra h
      push Not at h
      nlinarith [sum_nonneg fun c (_ : c ∈ univ.filter
        (fun c => M.Acc e c ∧ M.wt e c = θ)) => hπ.1 e c]
    rw [hsum, mul_div_assoc, div_self hat.ne', mul_one]
    exact hτf

omit [DecidableEq I] [DecidableEq J] [DecidableEq C] in
/-- **Theorem 3(c).** If every pair `i` takes part in is bar-shaped with `p̂_e ≥ p > 0`
(over the pairs the plan uses), the expected calls charged to `i` are at most
`capI i / p`. The same holds for `J`-side users by symmetry. -/
theorem sum_callsI_le [Nonempty C] (hπ : IsDist M.π) {x : I × J → C → ℝ}
    (hx : M.LPFeasible x) {θ f : I × J → ℝ} {p : ℝ} (hp : 0 < p) (i : I)
    (hbar : ∀ j, 0 < ∑ c, x (i, j) c →
      M.BarShaped x (i, j) (θ (i, j)) (f (i, j)) ∧ p ≤ M.pHat (i, j) (θ (i, j))) :
    ∑ j, M.callsI (M.sdhTau x) (i, j) ≤ M.capI i / p := by
  have hspec := M.sdhTau_spec hx
  have hpair : ∀ j, M.callsI (M.sdhTau x) (i, j) ≤ (∑ c, x (i, j) c) / p := by
    intro j
    refine (M.callsI_le _ (fun e => (hspec.1 e).1) hπ (i, j)).trans ?_
    rcases (sum_nonneg fun c _ => (hx.1 (i, j) c).1 :
        0 ≤ ∑ c, x (i, j) c).eq_or_lt with h0 | h0
    · -- An unused pair is never queried.
      have hzero : ∀ c, x (i, j) c = 0 := fun c =>
        (sum_eq_zero_iff_of_nonneg fun c _ => (hx.1 (i, j) c).1).mp h0.symm c (mem_univ c)
      rw [← h0, zero_div]
      exact sup'_le _ _ fun c _ => by rw [hzero c, zero_div]
    · obtain ⟨hbar', hp'⟩ := hbar j h0
      refine (M.sdhTau_le hπ hx hbar' h0).trans ?_
      exact div_le_div_of_nonneg_left h0.le hp hp'
  calc ∑ j, M.callsI (M.sdhTau x) (i, j) ≤ ∑ j, (∑ c, x (i, j) c) / p := sum_le_sum fun j _ => hpair j
    _ = (∑ j, ∑ c, x (i, j) c) / p := by rw [sum_div]
    _ ≤ M.capI i / p := div_le_div_of_nonneg_right (hx.2.2.1 i) hp.le

omit [DecidableEq I] [DecidableEq J] [DecidableEq C] in
/-- **Theorem 3(c), `J` side.** The same bound for the calls charged to `j`. -/
theorem sum_callsJ_le [Nonempty C] (hπ : IsDist M.π) {x : I × J → C → ℝ}
    (hx : M.LPFeasible x) {θ f : I × J → ℝ} {p : ℝ} (hp : 0 < p) (j : J)
    (hbar : ∀ i, 0 < ∑ c, x (i, j) c →
      M.BarShaped x (i, j) (θ (i, j)) (f (i, j)) ∧ p ≤ M.pHat (i, j) (θ (i, j))) :
    ∑ i, M.callsJ (M.sdhTau x) (i, j) ≤ M.capJ j / p := by
  have hspec := M.sdhTau_spec hx
  have hpair : ∀ i, M.callsJ (M.sdhTau x) (i, j) ≤ (∑ c, x (i, j) c) / p := by
    intro i
    refine (M.callsJ_le _ (fun e => (hspec.1 e).1) hπ (i, j)).trans ?_
    rcases (sum_nonneg fun c _ => (hx.1 (i, j) c).1 :
        0 ≤ ∑ c, x (i, j) c).eq_or_lt with h0 | h0
    · have hzero : ∀ c, x (i, j) c = 0 := fun c =>
        (sum_eq_zero_iff_of_nonneg fun c _ => (hx.1 (i, j) c).1).mp h0.symm c (mem_univ c)
      rw [← h0, zero_div]
      exact sup'_le _ _ fun c _ => by rw [hzero c, zero_div]
    · obtain ⟨hbar', hp'⟩ := hbar i h0
      refine (M.sdhTau_le hπ hx hbar' h0).trans ?_
      exact div_le_div_of_nonneg_left h0.le hp hp'
  calc ∑ i, M.callsJ (M.sdhTau x) (i, j) ≤ ∑ i, (∑ c, x (i, j) c) / p := sum_le_sum fun i _ => hpair i
    _ = (∑ i, ∑ c, x (i, j) c) / p := by rw [sum_div]
    _ ≤ M.capJ j / p := div_le_div_of_nonneg_right (hx.2.2.2 j) hp.le

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype C] [DecidableEq C] in
/-- The exchange argument: moving mass toward weights above `θ` and away from weights
below `θ`, with the same total, never lowers the value. -/
theorem sum_mul_le_of_bar {ι : Type*} (s : Finset ι) (w x y : ι → ℝ) (θ : ℝ)
    (hsum : ∑ i ∈ s, y i = ∑ i ∈ s, x i) (hab : ∀ i ∈ s, θ < w i → x i ≤ y i)
    (hbe : ∀ i ∈ s, w i < θ → y i ≤ x i) :
    ∑ i ∈ s, w i * x i ≤ ∑ i ∈ s, w i * y i := by
  have hterm : ∀ i ∈ s, 0 ≤ (w i - θ) * (y i - x i) := by
    intro i hi
    rcases lt_trichotomy θ (w i) with h | h | h
    · exact mul_nonneg (by linarith) (by linarith [hab i hi h])
    · rw [← h, sub_self, zero_mul]
    · exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [hbe i hi h])
  have key : ∑ i ∈ s, (w i - θ) * (y i - x i) =
      (∑ i ∈ s, w i * y i - ∑ i ∈ s, w i * x i) - θ * (∑ i ∈ s, y i - ∑ i ∈ s, x i) := by
    rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [hsum, sub_self, mul_zero, sub_zero] at key
  linarith [sum_nonneg hterm]

omit [DecidableEq I] [DecidableEq J] in
/-- **Bar shape for one pair.** Fill the pair's acceptable combinations from the highest
weight down until the plan's total is reached, splitting the last level proportionally.
The total is unchanged and the value does not drop. -/
theorem exists_bar_pair (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasible x)
    (e : I × J) :
    ∃ y : C → ℝ, (∀ c, 0 ≤ y c ∧ y c ≤ M.π e c) ∧ (∀ c, ¬ M.Acc e c → y c = 0) ∧
      ∑ c, y c = ∑ c, x e c ∧ ∑ c, M.wt e c * x e c ≤ ∑ c, M.wt e c * y c ∧
      ∃ θ f, 0 ≤ f ∧ f ≤ 1 ∧ ∀ c, M.Acc e c →
        (θ < M.wt e c → y c = M.π e c) ∧ (M.wt e c = θ → y c = f * M.π e c) ∧
          (M.wt e c < θ → y c = 0) := by
  set t := ∑ c, x e c with ht_def
  have hx0 : ∀ c, 0 ≤ x e c := fun c => (hx.1 e c).1
  rcases (sum_nonneg fun c _ => hx0 c : 0 ≤ t).eq_or_lt with ht | ht <;> rw [← ht_def] at ht
  · -- An unused pair: the empty plan, with the bar above every weight.
    have hxz : ∀ c, x e c = 0 := fun c =>
      (sum_eq_zero_iff_of_nonneg fun c _ => hx0 c).mp ht.symm c (mem_univ c)
    refine ⟨fun _ => 0, fun c => ⟨le_rfl, hπ.1 e c⟩, fun _ _ => rfl, by simp [← ht], ?_,
      ∑ c, |M.wt e c| + 1, 0, le_rfl, zero_le_one, fun c _ => ?_⟩
    · simp [hxz]
    · have hle : M.wt e c < ∑ c, |M.wt e c| + 1 := by
        have := single_le_sum (f := fun c => |M.wt e c|) (fun c _ => abs_nonneg _) (mem_univ c)
        linarith [le_abs_self (M.wt e c)]
      exact ⟨fun h => absurd h (not_lt.mpr hle.le), fun h => absurd h hle.ne, fun _ => rfl⟩
  -- Masses at or above, and strictly above, a level.
  set Ge : ℝ → ℝ := fun w =>
    ∑ c ∈ univ.filter (fun c => M.Acc e c ∧ w ≤ M.wt e c), M.π e c with hGe
  set Gt : ℝ → ℝ := fun w =>
    ∑ c ∈ univ.filter (fun c => M.Acc e c ∧ w < M.wt e c), M.π e c with hGt
  set At : ℝ → ℝ := fun w =>
    ∑ c ∈ univ.filter (fun c => M.Acc e c ∧ M.wt e c = w), M.π e c with hAt
  have hsplit : ∀ w, Ge w = Gt w + At w := by
    intro w
    simp only [hGe, hGt, hAt]
    rw [← sum_union (disjoint_filter.mpr fun c _ h1 h2 => absurd h2.2 h1.2.ne')]
    refine sum_congr ?_ fun _ _ => rfl
    ext c
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · rintro ⟨hc, hw⟩
      rcases hw.lt_or_eq with h | h
      · exact Or.inl ⟨hc, h⟩
      · exact Or.inr ⟨hc, h.symm⟩
    · rintro (⟨hc, h⟩ | ⟨hc, h⟩)
      · exact ⟨hc, h.le⟩
      · exact ⟨hc, h.ge⟩
  set A := univ.filter (M.Acc e) with hA
  have hxA : t = ∑ c ∈ A, x e c := by
    rw [ht_def, ← sum_filter_add_sum_filter_not univ (M.Acc e)]
    have : ∑ c ∈ univ.filter (fun c => ¬ M.Acc e c), x e c = 0 :=
      sum_eq_zero fun c hc => hx.2.1 e c (mem_filter.mp hc).2
    rw [this, add_zero]
  have hAne : A.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [hxA, h, sum_empty] at ht
    exact lt_irrefl 0 ht
  -- The bar: the highest weight level with at least `t` mass at or above it.
  set Lv := (A.image (M.wt e)).filter fun w => t ≤ Ge w with hLv
  have hLvne : Lv.Nonempty := by
    obtain ⟨w0, hw0, hmin⟩ := exists_min_image A (M.wt e) hAne
    refine ⟨M.wt e w0, mem_filter.mpr ⟨mem_image_of_mem _ hw0, ?_⟩⟩
    rw [hxA]
    calc ∑ c ∈ A, x e c ≤ ∑ c ∈ A, M.π e c := sum_le_sum fun c _ => (hx.1 e c).2
      _ = Ge (M.wt e w0) := by
        simp only [hGe]
        refine sum_congr ?_ fun _ _ => rfl
        ext c
        simp only [hA, mem_filter, mem_univ, true_and]
        exact ⟨fun h => ⟨h, hmin c (mem_filter.mpr ⟨mem_univ _, h⟩)⟩, fun h => h.1⟩
  set θ := Lv.max' hLvne with hθ
  have hθLv : θ ∈ Lv := max'_mem _ _
  have htGe : t ≤ Ge θ := (mem_filter.mp hθLv).2
  have hGtlt : Gt θ < t := by
    by_contra hcon
    push Not at hcon
    set P := A.filter fun c => θ < M.wt e c
    rcases P.eq_empty_or_nonempty with hP | hP
    · have : Gt θ = 0 := by
        simp only [hGt]
        refine sum_eq_zero fun c hc => ?_
        have : c ∈ P := mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hc).2.1⟩,
          (mem_filter.mp hc).2.2⟩
        rw [hP] at this
        exact absurd this (notMem_empty c)
      linarith
    · obtain ⟨cp, hcp, hminp⟩ := exists_min_image P (M.wt e) hP
      have hcpA : cp ∈ A := (mem_filter.mp hcp).1
      have hθcp : θ < M.wt e cp := (mem_filter.mp hcp).2
      have hGeq : Ge (M.wt e cp) = Gt θ := by
        simp only [hGe, hGt]
        refine sum_congr ?_ fun _ _ => rfl
        ext c
        simp only [mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨hc, h⟩; exact ⟨hc, hθcp.trans_le h⟩
        · rintro ⟨hc, h⟩
          exact ⟨hc, hminp c (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hc⟩, h⟩)⟩
      have hmem : M.wt e cp ∈ Lv :=
        mem_filter.mpr ⟨mem_image_of_mem _ hcpA, hGeq ▸ hcon⟩
      exact absurd (le_max' Lv _ hmem) (not_le.mpr hθcp)
  have hAtpos : 0 < At θ := by linarith [hsplit θ]
  set f := (t - Gt θ) / At θ with hf
  have hf0 : 0 ≤ f := div_nonneg (by linarith) hAtpos.le
  have hf1 : f ≤ 1 := (div_le_one hAtpos).mpr (by linarith [hsplit θ])
  set y : C → ℝ := fun c =>
    if M.Acc e c ∧ θ < M.wt e c then M.π e c
    else if M.Acc e c ∧ M.wt e c = θ then f * M.π e c else 0 with hy
  have hysum : ∑ c, y c = t := by
    have h1 : ∀ c, y c = (if M.Acc e c ∧ θ < M.wt e c then M.π e c else 0) +
        if M.Acc e c ∧ M.wt e c = θ then f * M.π e c else 0 := by
      intro c
      simp only [hy]
      split_ifs with ha hb hb
      · exact absurd hb.2 ha.2.ne'
      all_goals ring
    rw [sum_congr rfl fun c _ => h1 c, sum_add_distrib, ← sum_filter, ← sum_filter, ← mul_sum]
    change Gt θ + f * At θ = t
    rw [hf, div_mul_cancel₀ _ hAtpos.ne']
    ring
  refine ⟨y, fun c => ⟨?_, ?_⟩, fun c hc => ?_, hysum, ?_, θ, f, hf0, hf1, fun c hc => ?_⟩
  · simp only [hy]
    split_ifs
    · exact hπ.1 e c
    · exact mul_nonneg hf0 (hπ.1 e c)
    · exact le_rfl
  · simp only [hy]
    split_ifs
    · exact le_rfl
    · nlinarith [hπ.1 e c]
    · exact hπ.1 e c
  · simp [hy, hc]
  · refine sum_mul_le_of_bar univ (M.wt e) (x e) y θ hysum (fun c _ h => ?_) (fun c _ h => ?_)
    · by_cases hc : M.Acc e c
      · simp only [hy, hc, h, and_self, ↓reduceIte]; exact (hx.1 e c).2
      · rw [hx.2.1 e c hc]; simp [hy, hc]
    · by_cases hc : M.Acc e c
      · simp only [hy, hc, true_and, not_lt.mpr h.le, h.ne, ↓reduceIte]; exact hx0 c
      · rw [hx.2.1 e c hc]; simp [hy, hc]
  · refine ⟨fun h => by simp [hy, hc, h], fun h => ?_, fun h => ?_⟩
    · simp [hy, hc, h]
    · simp [hy, hc, not_lt.mpr h.le, h.ne]

omit [DecidableEq I] [DecidableEq J] in
/-- **Bar shape is without loss of generality.** Every feasible plan can be replaced by
one that is bar-shaped on every pair, with the same per-pair totals and at least the same
value. So an optimal plan can be taken bar-shaped. -/
theorem exists_barShaped (hπ : IsDist M.π) {x : I × J → C → ℝ} (hx : M.LPFeasible x) :
    ∃ x', M.LPFeasible x' ∧ M.lpValue x ≤ M.lpValue x' ∧ (∀ e, ∑ c, x' e c = ∑ c, x e c) ∧
      ∀ e, ∃ θ f, M.BarShaped x' e θ f := by
  choose y hy0 hyacc hysum hyval hybar using fun e => M.exists_bar_pair hπ hx e
  refine ⟨y, ⟨hy0, hyacc, fun i => ?_, fun j => ?_⟩, sum_le_sum fun e _ => hyval e, hysum,
    fun e => ?_⟩
  · simp_rw [hysum]; exact hx.2.2.1 i
  · simp_rw [hysum]; exact hx.2.2.2 j
  · obtain ⟨θ, f, hf0, hf1, h⟩ := hybar e
    exact ⟨θ, f, hf0, hf1, h⟩

omit [DecidableEq I] [DecidableEq J] in
/-- An optimal plan that is bar-shaped on every pair exists, so Theorems 3(b) and 3(c)
apply to the same plan. -/
theorem exists_optimal_barShaped (hπ : IsDist M.π) :
    ∃ x, M.IsLPOptimal x ∧ ∀ e, ∃ θ f, M.BarShaped x e θ f := by
  obtain ⟨x, hx⟩ := M.exists_isLPOptimal hπ
  obtain ⟨x', hx', hle, -, hbar⟩ := M.exists_barShaped hπ hx.1
  exact ⟨x', ⟨hx', fun x'' h'' => (hx.2 x'' h'').trans hle⟩, hbar⟩

/-! ### Theorem 3(d): a call budget -/

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [DecidableEq C] in
/-- Scaling the plan by `λ ≥ 0` scales every query probability by `λ`. -/
theorem sdhTau_smul [Nonempty C] (x : I × J → C → ℝ) {lam : ℝ} (hl0 : 0 ≤ lam) (e : I × J) :
    M.sdhTau (fun e c => lam * x e c) e = lam * M.sdhTau x e := by
  apply le_antisymm
  · refine sup'_le _ _ fun c _ => ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (le_sup' (fun c => x e c / M.π e c) (mem_univ c)) hl0
  · obtain ⟨c, _, hc⟩ := exists_mem_eq_sup' univ_nonempty fun c => x e c / M.π e c
    rw [sdhTau, hc, ← mul_div_assoc]
    exact le_sup' (fun c => lam * x e c / M.π e c) (mem_univ c)

omit [DecidableEq I] [DecidableEq J] [DecidableEq C] in
/-- **Theorem 3(d), calls.** With the plan scaled by `λ ≥ 0`, user `i`'s expected calls
are at most `λ · capI i / p`, hence at most a budget `Q` once `λ ≤ Q p / capI i`. -/
theorem sum_callsI_budget [Nonempty C] (hπ : IsDist M.π) {x : I × J → C → ℝ}
    (hx : M.LPFeasible x) {θ f : I × J → ℝ} {p : ℝ} (hp : 0 < p) (i : I)
    (hbar : ∀ j, 0 < ∑ c, x (i, j) c →
      M.BarShaped x (i, j) (θ (i, j)) (f (i, j)) ∧ p ≤ M.pHat (i, j) (θ (i, j)))
    {lam : ℝ} (hl0 : 0 ≤ lam) :
    ∑ j, M.callsI (M.sdhTau fun e c => lam * x e c) (i, j) ≤ lam * (M.capI i / p) := by
  have h : ∀ j, M.callsI (M.sdhTau fun e c => lam * x e c) (i, j) =
      lam * M.callsI (M.sdhTau x) (i, j) := fun j => by
    unfold callsI
    rw [M.sdhTau_smul x hl0, mul_assoc]
  rw [sum_congr rfl fun j _ => h j, ← mul_sum]
  exact mul_le_mul_of_nonneg_left (M.sum_callsI_le hπ hx hp i hbar) hl0

/-- **Theorem 3(d).** Scaling an optimal plan by `λ ∈ [0, 1]` scales every pair's query
probability by `λ`, so calls scale by `λ`, and SDH still earns `c_K^2 λ OPT_IR`. -/
theorem sdh_budget [Nonempty C] (hπ : IsDist M.π) {x : I × J → C → ℝ}
    (hx : M.IsLPOptimal x) {lam : ℝ} (hlam : 0 ≤ lam ∧ lam ≤ 1) (K : ℕ)
    (hKI : ∀ i, K ≤ M.capI i) (hKJ : ∀ j, K ≤ M.capJ j) :
    (∀ e, M.sdhTau (fun e c => lam * x e c) e = lam * M.sdhTau x e) ∧
      cK K ^ 2 * lam * M.optIR ≤ M.sdhValue (M.sdhTau fun e c => lam * x e c) := by
  obtain ⟨hl0, hl1⟩ := hlam
  have htau := M.sdhTau_smul x hl0
  have hfeas : M.LPFeasible fun e c => lam * x e c := by
    obtain ⟨h1, h2, h3, h4⟩ := hx.1
    refine ⟨fun e c => ⟨mul_nonneg hl0 (h1 e c).1, ?_⟩, fun e c hc => by simp [h2 e c hc],
      fun i => ?_, fun j => ?_⟩
    · nlinarith [(h1 e c).1, (h1 e c).2]
    · simp_rw [← mul_sum]
      nlinarith [h3 i, sum_nonneg fun j (_ : j ∈ univ) =>
        sum_nonneg fun c (_ : c ∈ univ) => (h1 (i, j) c).1, (Nat.cast_nonneg (M.capI i) : (0 : ℝ) ≤ _)]
    · simp_rw [← mul_sum]
      nlinarith [h4 j, sum_nonneg fun i (_ : i ∈ univ) =>
        sum_nonneg fun c (_ : c ∈ univ) => (h1 (i, j) c).1, (Nat.cast_nonneg (M.capJ j) : (0 : ℝ) ≤ _)]
  refine ⟨htau, ?_⟩
  have hspec := M.sdhTau_spec hfeas
  have hlp : M.lpValue (fun e c => lam * x e c) = lam * M.lpValue x := by
    unfold lpValue
    rw [mul_sum]
    exact sum_congr rfl fun e _ => by rw [mul_sum]; exact sum_congr rfl fun c _ => by ring
  calc cK K ^ 2 * lam * M.optIR ≤ cK K ^ 2 * lam * M.lpValue x :=
        mul_le_mul_of_nonneg_left (M.optIR_le_lpValue hπ hx)
          (mul_nonneg (sq_nonneg _) hl0)
    _ = cK K ^ 2 * M.lpValue (fun e c => lam * x e c) := by rw [hlp]; ring
    _ ≤ _ := M.lpValue_le_sdhValue hπ hfeas hspec.1 hspec.2 K hKI hKJ

/-! ### Welfare on capped sets -/

omit [Fintype C] [DecidableEq C] in
/-- **Welfare on IR sets is the sum of net weights.** Suppose each user's value is
additive on sets within its cap (true for additive users, for top-`k` users with cap at
most `k`, and for any user with cap 1). Then on a capped match set `S`, the sum of all
users' utilities is `∑_{e ∈ S} wt e (ω e)`. -/
theorem welfare_eq_sum_wt (ω : I × J → C) (vI : I → Finset J → ℝ) (vJ : J → Finset I → ℝ)
    (hvI : ∀ i T, T.card ≤ M.capI i → vI i T = ∑ j ∈ T, M.valI (i, j) (ω (i, j)))
    (hvJ : ∀ j T, T.card ≤ M.capJ j → vJ j T = ∑ i ∈ T, M.valJ (i, j) (ω (i, j)))
    {S : Finset (I × J)} (hS : M.CapOK S) :
    (∑ i, (vI i (univ.filter fun j => (i, j) ∈ S) -
        M.costI i * (univ.filter fun j => (i, j) ∈ S).card)) +
      (∑ j, (vJ j (univ.filter fun i => (i, j) ∈ S) -
        M.costJ j * (univ.filter fun i => (i, j) ∈ S).card)) =
      ∑ e ∈ S, M.wt e (ω e) := by
  -- Each user's partners in `S` fit in its cap.
  have hrow : ∀ i, (univ.filter fun j => (i, j) ∈ S).card ≤ M.capI i := by
    intro i
    have h := card_filter_fst S i
    rw [sum_boole] at h
    have : (univ.filter fun j => (i, j) ∈ S).card = (S.filter fun e => e.1 = i).card := by
      exact_mod_cast h.symm
    rw [this]
    exact hS.1 i
  have hcol : ∀ j, (univ.filter fun i => (i, j) ∈ S).card ≤ M.capJ j := by
    intro j
    have h := card_filter_snd S j
    rw [sum_boole] at h
    have : (univ.filter fun i => (i, j) ∈ S).card = (S.filter fun e => e.2 = j).card := by
      exact_mod_cast h.symm
    rw [this]
    exact hS.2 j
  have hI : ∀ i, vI i (univ.filter fun j => (i, j) ∈ S) -
      M.costI i * (univ.filter fun j => (i, j) ∈ S).card =
      ∑ j ∈ univ.filter (fun j => (i, j) ∈ S), (M.valI (i, j) (ω (i, j)) - M.costI i) := by
    intro i
    rw [hvI i _ (hrow i), sum_sub_distrib, sum_const, nsmul_eq_mul, mul_comm]
  have hJ : ∀ j, vJ j (univ.filter fun i => (i, j) ∈ S) -
      M.costJ j * (univ.filter fun i => (i, j) ∈ S).card =
      ∑ i ∈ univ.filter (fun i => (i, j) ∈ S), (M.valJ (i, j) (ω (i, j)) - M.costJ j) := by
    intro j
    rw [hvJ j _ (hcol j), sum_sub_distrib, sum_const, nsmul_eq_mul, mul_comm]
  simp_rw [hI, hJ, sum_filter]
  rw [sum_comm (s := (univ : Finset J)) (t := (univ : Finset I)), ← sum_add_distrib]
  have hR : ∑ e ∈ S, M.wt e (ω e) =
      ∑ i, ∑ j, if (i, j) ∈ S then M.wt (i, j) (ω (i, j)) else 0 := by
    rw [← Fintype.sum_prod_type (f := fun e => if e ∈ S then M.wt e (ω e) else 0), sum_ite_mem,
      univ_inter]
  rw [hR]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  split_ifs <;> simp [wt]

end ScreenedMarket

end DatingAlgo
