import DatingAlgo.TopK

/-!
# Truthful swiping: when sincere swiping is dominant

Theorem 1 and Theorems 3(a), 5(a, d, e) of the vault note "Truthful Swiping with an LLM
Oracle".

A user who swipes on the profiles `N` it is shown ends up matched with `D ∩ R`. Here `D`
is the set it likes and `R` is the set of profiles that would match it given a like.
Under a swipe-local policy `R` does not depend on the user's own swipes (the note's
Lemma 1′). The user's utility is `v S - c |S|`. *Sincere* swiping likes exactly the
acceptable profiles, those with `q x > c`.

* `sincere_best` (Theorem 1(a)): if the acceptable profiles seen are cost-separable,
  sincere swiping is a best choice against every `R`, i.e. whatever the others do.
* `sincere_not_best` (Theorem 1(b)): otherwise some `R` makes another choice strictly
  better.
* `costSeparable_sum` and `costSeparable_topK_iff`: the additive and top-`k`
  corollaries.
* `sdh_dsic` (Theorems 3(a), 5(a)): SDH's two-period game, with the others playing
  arbitrary strategies that may react to what they see. If each user's acceptable
  planned partners are cost-separable, sincere swiping is dominant.
  `sdh_dsic_topK` specializes to top-`k` users with at most `k` planned partners.
* `sdh_sincere_nonneg` (Theorem 5(d)) and `sdh_arc_matches` (the step behind
  Theorem 5(e)).

Everything holds for a fixed realization of values and platform coins, so for every
realization ("universally").
-/

namespace DatingAlgo

open Finset

section CostSeparable

variable {β : Type*} [DecidableEq β]

/-- Utility of a match set `S`: value minus a cost `c` per match. -/
def swipeUtil (v : Finset β → ℝ) (c : ℝ) (S : Finset β) : ℝ :=
  v S - c * S.card

/-- `A` is *cost-separable* if every member adds at least `c` to every set of the
other members. -/
def CostSeparable (v : Finset β → ℝ) (c : ℝ) (A : Finset β) : Prop :=
  ∀ x ∈ A, ∀ T ⊆ A.erase x, c ≤ v (insert x T) - v T

/-- The acceptable profiles among those seen: the ones sincere swiping likes. -/
noncomputable def sincereSet (q : β → ℝ) (c : ℝ) (N : Finset β) : Finset β :=
  N.filter fun x => c < q x

/-- **Theorem 1(a).** Let `v` be subadditive with `v {x} = q x`. If the acceptable
profiles seen are cost-separable, then liking exactly them is a best choice for every
set `R` of profiles that would match: for every set `D ⊆ N` of likes,
`u(D ∩ R) ≤ u(A ∩ R)`. Since `R` is arbitrary, this holds whatever the others do. -/
theorem sincere_best {v : Finset β → ℝ} {q : β → ℝ} {c : ℝ}
    (hsub : ∀ S T, v (S ∪ T) ≤ v S + v T) (hsingle : ∀ x, v {x} = q x)
    {N : Finset β} (hA : CostSeparable v c (sincereSet q c N)) (R : Finset β)
    {D : Finset β} (hD : D ⊆ N) :
    swipeUtil v c (D ∩ R) ≤ swipeUtil v c (sincereSet q c N ∩ R) := by
  set A := sincereSet q c N
  -- Removing unacceptable profiles never lowers utility.
  have hremove : ∀ Z : Finset β, (∀ z ∈ Z, q z ≤ c) → ∀ Y, swipeUtil v c (Y ∪ Z) ≤ swipeUtil v c Y := by
    intro Z
    induction Z using Finset.induction_on with
    | empty => intro _ Y; simp
    | insert z Z hz ih =>
      intro hZ Y
      have ih' := ih (fun z' hz' => hZ z' (mem_insert_of_mem hz')) Y
      rw [union_insert]
      by_cases hzYZ : z ∈ Y ∪ Z
      · rwa [insert_eq_of_mem hzYZ]
      · refine le_trans ?_ ih'
        have h := hsub {z} (Y ∪ Z)
        rw [← insert_eq, hsingle] at h
        unfold swipeUtil
        rw [card_insert_of_notMem hzYZ]
        push_cast
        linarith [hZ z (mem_insert_self z Z)]
  -- Adding acceptable profiles never lowers utility.
  have hadd : ∀ Z : Finset β, Z ⊆ A → ∀ Y, Y ⊆ A → swipeUtil v c Y ≤ swipeUtil v c (Y ∪ Z) := by
    intro Z
    induction Z using Finset.induction_on with
    | empty => intro _ Y _; simp
    | insert z Z hz ih =>
      intro hZ Y hY
      have hZ' : Z ⊆ A := (subset_insert z Z).trans hZ
      refine (ih hZ' Y hY).trans ?_
      rw [union_insert]
      by_cases hzYZ : z ∈ Y ∪ Z
      · rw [insert_eq_of_mem hzYZ]
      · have hsep := hA z (hZ (mem_insert_self z Z)) (Y ∪ Z) (fun y hy =>
          mem_erase.mpr ⟨fun h => hzYZ (h ▸ hy), union_subset hY hZ' hy⟩)
        unfold swipeUtil
        rw [card_insert_of_notMem hzYZ]
        push_cast
        linarith
  set X := D ∩ R
  have hsplit : X = X.filter (fun x => c < q x) ∪ X.filter (fun x => ¬ c < q x) :=
    (filter_union_filter_not_eq (fun x => c < q x) X).symm
  have h1 : swipeUtil v c X ≤ swipeUtil v c (X.filter fun x => c < q x) := by
    conv_lhs => rw [hsplit]
    exact hremove _ (fun z hz => not_lt.mp (mem_filter.mp hz).2) _
  have hXA : X.filter (fun x => c < q x) ⊆ A ∩ R := fun x hx => by
    obtain ⟨hxX, hxq⟩ := mem_filter.mp hx
    obtain ⟨hxD, hxR⟩ := mem_inter.mp hxX
    exact mem_inter.mpr ⟨mem_filter.mpr ⟨hD hxD, hxq⟩, hxR⟩
  have h2 := hadd (A ∩ R) inter_subset_left _ (hXA.trans inter_subset_left)
  rw [union_eq_right.mpr hXA] at h2
  exact h1.trans h2

/-- **Theorem 1(b).** If the acceptable profiles seen are not cost-separable, then for
some set `R` of profiles that would match, some other set of likes `D ⊆ N` does strictly
better than sincere swiping. So sincere swiping is not dominant. -/
theorem sincere_not_best {v : Finset β → ℝ} {q : β → ℝ} {c : ℝ} {N : Finset β}
    (hA : ¬ CostSeparable v c (sincereSet q c N)) :
    ∃ R D : Finset β, D ⊆ N ∧
      swipeUtil v c (sincereSet q c N ∩ R) < swipeUtil v c (D ∩ R) := by
  unfold CostSeparable at hA
  push Not at hA
  obtain ⟨x, hxA, T, hTA, hlt⟩ := hA
  have hxT : x ∉ T := fun h => (mem_erase.mp (hTA h)).1 rfl
  have hTA' : T ⊆ sincereSet q c N := hTA.trans (erase_subset x _)
  refine ⟨insert x T, T, hTA'.trans (filter_subset _ N), ?_⟩
  rw [inter_eq_right.mpr (insert_subset hxA hTA'), inter_eq_left.mpr (subset_insert x T)]
  unfold swipeUtil
  rw [card_insert_of_notMem hxT]
  push_cast
  linarith

/-- **Theorem 1, additive corollary.** With additive utility the acceptable profiles
are always cost-separable. -/
theorem costSeparable_sum (q : β → ℝ) (c : ℝ) (N : Finset β) :
    CostSeparable (fun S => ∑ x ∈ S, q x) c (sincereSet q c N) := by
  intro x hx T hT
  have hxT : x ∉ T := fun h => (mem_erase.mp (hT h)).1 rfl
  dsimp only
  rw [sum_insert hxT]
  linarith [(mem_filter.mp hx).2]

/-- Top-`k` value is subadditive. -/
theorem topK_union_le (q : β → ℝ) (k : ℕ) (S T : Finset β) :
    topK q k (S ∪ T) ≤ topK q k S + topK q k T := by
  obtain ⟨W, hW, hWk, hEq⟩ := exists_topK_eq q k (S ∪ T)
  rw [hEq, ← sum_filter_add_sum_filter_not W (· ∈ S)]
  refine add_le_add (sum_le_topK (fun x hx => (mem_filter.mp hx).2)
    ((card_filter_le _ _).trans hWk)) (sum_le_topK (fun x hx => ?_)
    ((card_filter_le _ _).trans hWk))
  obtain ⟨hxW, hxS⟩ := mem_filter.mp hx
  rcases mem_union.mp (hW hxW) with h | h
  · exact absurd h hxS
  · exact h

omit [DecidableEq β] in
/-- Top-`k` value of one profile, for `k ≥ 1`. -/
theorem topK_singleton {q : β → ℝ} (hq : ∀ x, 0 ≤ q x) {k : ℕ} (hk : 1 ≤ k) (x : β) :
    topK q k {x} = q x := by
  rw [topK_eq_sum_of_card_le hq (by simpa using hk), sum_singleton]

/-- **Theorem 1, top-`k` corollary.** For a top-`k` user with `c > 0`, a set of
acceptable profiles is cost-separable iff it has at most `k` members. -/
theorem costSeparable_topK_iff {q : β → ℝ} (hq : ∀ x, 0 ≤ q x) (k : ℕ) {c : ℝ}
    (hc : 0 < c) {A : Finset β} (hA : ∀ x ∈ A, c < q x) :
    CostSeparable (topK q k) c A ↔ A.card ≤ k := by
  constructor
  · intro hsep
    by_contra hlt
    push Not at hlt
    obtain ⟨B, hBA, hBcard⟩ := exists_subset_card_eq (s := A) (n := k + 1) hlt
    have hBne : B.Nonempty := card_pos.mp (by omega)
    obtain ⟨x, hxB, hxmin⟩ := exists_min_image B q hBne
    set T := B.erase x
    have hTcard : T.card = k := by rw [card_erase_of_mem hxB]; omega
    -- The best `k` of `B` are worth no more than `T`.
    have hle : topK q k (insert x T) ≤ topK q k T := by
      rw [insert_erase hxB]
      obtain ⟨W, hWB, hWk, hEq⟩ := exists_topK_eq q k B
      rw [hEq]
      by_cases hxW : x ∈ W
      · have hWlt : W.card < B.card := by omega
        obtain ⟨y, hyB, hyW⟩ := exists_of_ssubset (ssubset_of_subset_of_ne hWB
          (fun h => by rw [h] at hWlt; exact lt_irrefl _ hWlt))
        have hyx : y ≠ x := fun h => hyW (h ▸ hxW)
        have hsub : insert y (W.erase x) ⊆ T := insert_subset (mem_erase.mpr ⟨hyx, hyB⟩)
          (erase_subset_erase x hWB)
        have hcard : (insert y (W.erase x)).card ≤ k := by
          rw [card_insert_of_notMem (fun h => hyW (mem_of_mem_erase h)),
            card_erase_of_mem hxW]
          have : 1 ≤ W.card := card_pos.mpr ⟨x, hxW⟩
          omega
        calc ∑ i ∈ W, q i = q x + ∑ i ∈ W.erase x, q i := (add_sum_erase W q hxW).symm
          _ ≤ q y + ∑ i ∈ W.erase x, q i := by linarith [hxmin y hyB]
          _ = ∑ i ∈ insert y (W.erase x), q i :=
              (sum_insert (fun h => hyW (mem_of_mem_erase h))).symm
          _ ≤ topK q k T := sum_le_topK hsub hcard
      · exact sum_le_topK (fun i hi => mem_erase.mpr ⟨fun h => hxW (h ▸ hi), hWB hi⟩) hWk
    have := hsep x (hBA hxB) T (erase_subset_erase x hBA)
    linarith
  · intro hcard x hx T hT
    have hxT : x ∉ T := fun h => (mem_erase.mp (hT h)).1 rfl
    have hTA : T ⊆ A := hT.trans (erase_subset x A)
    have hins : insert x T ⊆ A := insert_subset hx hTA
    rw [topK_eq_sum_of_card_le hq ((card_le_card hins).trans hcard),
      topK_eq_sum_of_card_le hq ((card_le_card hTA).trans hcard), sum_insert hxT]
    linarith [hA x hx]

/-- Subsets of a cost-separable set are cost-separable. -/
theorem CostSeparable.subset {v : Finset β → ℝ} {c : ℝ} {A B : Finset β}
    (hA : CostSeparable v c A) (hBA : B ⊆ A) : CostSeparable v c B :=
  fun x hx T hT => hA x (hBA hx) T (hT.trans (erase_subset_erase x hBA))

/-- On a cost-separable set every subset is worth at least its costs (given
`v ∅ = 0`). This is individual rationality. -/
theorem swipeUtil_nonneg_of_costSeparable {v : Finset β → ℝ} {c : ℝ} (hv0 : v ∅ = 0)
    {A : Finset β} (hA : CostSeparable v c A) {S : Finset β} (hS : S ⊆ A) :
    0 ≤ swipeUtil v c S := by
  induction S using Finset.induction_on with
  | empty => simp [swipeUtil, hv0]
  | insert x S hxS ih =>
    have hSA : S ⊆ A := (subset_insert x S).trans hS
    have h := hA x (hS (mem_insert_self x S)) S
      (fun y hy => mem_erase.mpr ⟨fun h => hxS (h ▸ hy), hSA hy⟩)
    have ih' := ih hSA
    unfold swipeUtil at ih' ⊢
    rw [card_insert_of_notMem hxS]
    push_cast
    linarith

end CostSeparable

/-! ### SDH's two-period game -/

section Game

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- A strategy profile in SDH's two-period game, for a fixed realization of values and
platform coins. `like1 u r` says whether `u` likes `r` when initiating in period 1.
`resp r B` is the set `r` likes back in period 2 when shown `B`; it may depend on `B` in
any way, so strategies can react to what a user sees. -/
structure SwipeProfile (U : Type*) where
  like1 : U → U → Bool
  resp : U → Finset U → Finset U

/-- `r`'s period-2 display under SDH: the planned initiators who liked it. `arcs` are
SDH's planned matches, oriented from initiator to responder. -/
def display2 (arcs : Finset (U × U)) (σ : SwipeProfile U) (r : U) : Finset U :=
  univ.filter fun s => (s, r) ∈ arcs ∧ σ.like1 s r = true

/-- `ℓ`'s matches: planned partners it initiated toward and who liked it back, and
planned initiators who liked it and whom it liked back. -/
def matchesOf (arcs : Finset (U × U)) (σ : SwipeProfile U) (ℓ : U) : Finset U :=
  (univ.filter fun r => (ℓ, r) ∈ arcs ∧ σ.like1 ℓ r = true ∧
      ℓ ∈ σ.resp r (display2 arcs σ r)) ∪
    (univ.filter fun s => (s, ℓ) ∈ arcs ∧ σ.like1 s ℓ = true ∧
      s ∈ σ.resp ℓ (display2 arcs σ ℓ))

/-- `ℓ`'s planned partners. -/
def plannedPartners (arcs : Finset (U × U)) (ℓ : U) : Finset U :=
  (univ.filter fun r => (ℓ, r) ∈ arcs) ∪ (univ.filter fun s => (s, ℓ) ∈ arcs)

/-- Replace `ℓ`'s strategy by `(L, ρ)`. -/
def SwipeProfile.update (σ : SwipeProfile U) (ℓ : U) (L : U → Bool)
    (ρ : Finset U → Finset U) : SwipeProfile U where
  like1 u := if u = ℓ then L else σ.like1 u
  resp u := if u = ℓ then ρ else σ.resp u

/-- Sincere period-1 likes: like `r` iff `q ℓ r > c ℓ`. -/
noncomputable def sincereLike (q : U → U → ℝ) (c : U → ℝ) (ℓ : U) : U → Bool :=
  fun r => decide (c ℓ < q ℓ r)

/-- Sincere period-2 responses: like back exactly the acceptable profiles shown. -/
noncomputable def sincereResp (q : U → U → ℝ) (c : U → ℝ) (ℓ : U) : Finset U → Finset U :=
  fun B => B.filter fun s => c ℓ < q ℓ s

omit [Fintype U] in
theorem SwipeProfile.update_like1_self (σ : SwipeProfile U) (ℓ : U) (L : U → Bool)
    (ρ : Finset U → Finset U) : (σ.update ℓ L ρ).like1 ℓ = L := by
  simp [SwipeProfile.update]

omit [Fintype U] in
theorem SwipeProfile.update_like1_of_ne (σ : SwipeProfile U) {ℓ u : U} (h : u ≠ ℓ)
    (L : U → Bool) (ρ : Finset U → Finset U) : (σ.update ℓ L ρ).like1 u = σ.like1 u := by
  simp [SwipeProfile.update, h]

omit [Fintype U] in
theorem SwipeProfile.update_resp_self (σ : SwipeProfile U) (ℓ : U) (L : U → Bool)
    (ρ : Finset U → Finset U) : (σ.update ℓ L ρ).resp ℓ = ρ := by
  simp [SwipeProfile.update]

omit [Fintype U] in
theorem SwipeProfile.update_resp_of_ne (σ : SwipeProfile U) {ℓ u : U} (h : u ≠ ℓ)
    (L : U → Bool) (ρ : Finset U → Finset U) : (σ.update ℓ L ρ).resp u = σ.resp u := by
  simp [SwipeProfile.update, h]

/-- **The note's Lemma 1′ for SDH.** Whatever `ℓ` does, its matches are `D ∩ R`: `D` is
the set it likes among the profiles it sees (its planned partners as initiator, and its
backlog `display2 arcs σ ℓ`), and `R` does not depend on `ℓ`'s strategy. A planned
partner `r` of `ℓ` is in `R` iff `r` would like `ℓ` back when `ℓ`'s like is in its
backlog. -/
theorem matchesOf_update {arcs : Finset (U × U)}
    (hone : ∀ a b, (a, b) ∈ arcs → (b, a) ∉ arcs) (hloop : ∀ a, (a, a) ∉ arcs)
    (σ : SwipeProfile U) (ℓ : U) (L : U → Bool) (ρ : Finset U → Finset U) :
    matchesOf arcs (σ.update ℓ L ρ) ℓ =
      ((univ.filter fun r => (ℓ, r) ∈ arcs ∧ L r = true) ∪
          (display2 arcs σ ℓ).filter (· ∈ ρ (display2 arcs σ ℓ))) ∩
        ((univ.filter fun r => (ℓ, r) ∈ arcs ∧
            ℓ ∈ σ.resp r (display2 arcs (σ.update ℓ (fun _ => true) (σ.resp ℓ)) r)) ∪
          display2 arcs σ ℓ) := by
  -- `ℓ`'s backlog does not depend on `ℓ`.
  have hB : display2 arcs (σ.update ℓ L ρ) ℓ = display2 arcs σ ℓ := by
    ext s
    simp only [display2, mem_filter, mem_univ, true_and]
    refine and_congr_right fun h1 => ?_
    have : s ≠ ℓ := fun h => hloop ℓ (h ▸ h1)
    rw [SwipeProfile.update_like1_of_ne σ this]
  -- After `ℓ` likes `r`, `r`'s backlog is the same as if `ℓ` liked everyone.
  have hD : ∀ r, L r = true → display2 arcs (σ.update ℓ L ρ) r =
      display2 arcs (σ.update ℓ (fun _ => true) (σ.resp ℓ)) r := by
    intro r hr
    ext s
    simp only [display2, mem_filter, mem_univ, true_and]
    refine and_congr_right fun _ => ?_
    by_cases hs : s = ℓ
    · subst hs
      rw [SwipeProfile.update_like1_self, SwipeProfile.update_like1_self, hr]
    · rw [SwipeProfile.update_like1_of_ne σ hs, SwipeProfile.update_like1_of_ne σ hs]
  ext x
  simp only [matchesOf, mem_union, mem_inter, mem_filter, mem_univ, true_and, hB,
    SwipeProfile.update_like1_self, SwipeProfile.update_resp_self]
  constructor
  · rintro (⟨hx1, hx2, hx3⟩ | ⟨hx1, hx2, hx3⟩)
    · have hxℓ : x ≠ ℓ := fun h => hloop ℓ (h ▸ hx1)
      rw [SwipeProfile.update_resp_of_ne σ hxℓ, hD x hx2] at hx3
      exact ⟨Or.inl ⟨hx1, hx2⟩, Or.inl ⟨hx1, hx3⟩⟩
    · have hxℓ : x ≠ ℓ := fun h => hloop ℓ (h ▸ hx1)
      rw [SwipeProfile.update_like1_of_ne σ hxℓ] at hx2
      have hxB : x ∈ display2 arcs σ ℓ := by
        simp only [display2, mem_filter, mem_univ, true_and]; exact ⟨hx1, hx2⟩
      exact ⟨Or.inr ⟨hxB, hx3⟩, Or.inr hxB⟩
  · rintro ⟨⟨hx1, hx2⟩ | ⟨hxB, hx3⟩, ⟨hy1, hR⟩ | hR⟩
    · have hxℓ : x ≠ ℓ := fun h => hloop ℓ (h ▸ hx1)
      left
      rw [SwipeProfile.update_resp_of_ne σ hxℓ, hD x hx2]
      exact ⟨hx1, hx2, hR⟩
    · simp only [display2, mem_filter, mem_univ, true_and] at hR
      exact absurd hR.1 (hone ℓ x hx1)
    · simp only [display2, mem_filter, mem_univ, true_and] at hxB
      exact absurd hy1 (hone x ℓ hxB.1)
    · simp only [display2, mem_filter, mem_univ, true_and] at hxB
      have hxℓ : x ≠ ℓ := fun h => hloop ℓ (h ▸ hxB.1)
      right
      rw [SwipeProfile.update_like1_of_ne σ hxℓ]
      exact ⟨hxB.1, hxB.2, hx3⟩

/-- **Theorems 3(a) and 5(a): SDH is DSIC.** Fix values `q`, costs `c` and SDH's plan
`arcs` (each pair oriented at most one way, no self-pairs). Suppose `ℓ`'s value `v ℓ` is
subadditive with `v ℓ {x} = q ℓ x`, and `ℓ`'s acceptable planned partners are
cost-separable. Then for every behavior `σ` of the others, adaptive or not, and every
deviation `(L, ρ)` of `ℓ`, sincere swiping gives `ℓ` at least as much utility. -/
theorem sdh_dsic {arcs : Finset (U × U)} (hone : ∀ a b, (a, b) ∈ arcs → (b, a) ∉ arcs)
    (hloop : ∀ a, (a, a) ∉ arcs) {q : U → U → ℝ} {c : U → ℝ} {ℓ : U}
    {v : Finset U → ℝ} (hsub : ∀ S T, v (S ∪ T) ≤ v S + v T) (hsingle : ∀ x, v {x} = q ℓ x)
    (hsep : CostSeparable v (c ℓ) (sincereSet (q ℓ) (c ℓ) (plannedPartners arcs ℓ)))
    (σ : SwipeProfile U) (L : U → Bool) (ρ : Finset U → Finset U) :
    swipeUtil v (c ℓ) (matchesOf arcs (σ.update ℓ L ρ) ℓ) ≤
      swipeUtil v (c ℓ)
        (matchesOf arcs (σ.update ℓ (sincereLike q c ℓ) (sincereResp q c ℓ)) ℓ) := by
  set B := display2 arcs σ ℓ
  set out := univ.filter fun r => (ℓ, r) ∈ arcs
  rw [matchesOf_update hone hloop, matchesOf_update hone hloop]
  set R := (univ.filter fun r => (ℓ, r) ∈ arcs ∧
      ℓ ∈ σ.resp r (display2 arcs (σ.update ℓ (fun _ => true) (σ.resp ℓ)) r)) ∪ B
  -- Sincere play likes exactly the acceptable profiles seen.
  have hsinc : ((univ.filter fun r => (ℓ, r) ∈ arcs ∧ sincereLike q c ℓ r = true) ∪
      B.filter (· ∈ sincereResp q c ℓ B)) = sincereSet (q ℓ) (c ℓ) (out ∪ B) := by
    ext x
    simp only [sincereSet, sincereResp, sincereLike, mem_union, mem_filter, mem_univ, true_and,
      decide_eq_true_eq, out]
    tauto
  rw [hsinc]
  have hBin : B ⊆ univ.filter fun s => (s, ℓ) ∈ arcs := fun s hs => by
    simp only [B, display2, mem_filter, mem_univ, true_and] at hs ⊢
    exact hs.1
  have hsep' : CostSeparable v (c ℓ) (sincereSet (q ℓ) (c ℓ) (out ∪ B)) :=
    hsep.subset (filter_subset_filter _ (union_subset_union subset_rfl hBin))
  refine sincere_best hsub hsingle hsep' R (union_subset (fun r hr => ?_) ?_)
  · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hr).2.1⟩)
  · exact (filter_subset _ B).trans subset_union_right

/-- **SDH is DSIC for top-`k` users.** A top-`k` user has at most `k` planned partners
in SDH (its IR family caps it at `min(b, k)`), so sincere swiping is dominant. This does
not even need the planned partners to be acceptable, which SDH's screening also
guarantees. -/
theorem sdh_dsic_topK {arcs : Finset (U × U)} (hone : ∀ a b, (a, b) ∈ arcs → (b, a) ∉ arcs)
    (hloop : ∀ a, (a, a) ∉ arcs) {q : U → U → ℝ} (hq : ∀ a b, 0 ≤ q a b) {c : U → ℝ}
    {ℓ : U} {k : ℕ} (hk : 1 ≤ k) (hc : 0 < c ℓ)
    (hcard : (plannedPartners arcs ℓ).card ≤ k)
    (σ : SwipeProfile U) (L : U → Bool) (ρ : Finset U → Finset U) :
    swipeUtil (topK (q ℓ) k) (c ℓ) (matchesOf arcs (σ.update ℓ L ρ) ℓ) ≤
      swipeUtil (topK (q ℓ) k) (c ℓ)
        (matchesOf arcs (σ.update ℓ (sincereLike q c ℓ) (sincereResp q c ℓ)) ℓ) := by
  have hA : ∀ x ∈ sincereSet (q ℓ) (c ℓ) (plannedPartners arcs ℓ), c ℓ < q ℓ x :=
    fun x hx => (mem_filter.mp hx).2
  refine sdh_dsic hone hloop (topK_union_le (q ℓ) k) (topK_singleton (hq ℓ) hk)
    ((costSeparable_topK_iff (hq ℓ) k hc hA).mpr ?_) σ L ρ
  exact (card_le_card (filter_subset _ _)).trans hcard

/-- **Theorem 5(d): individual rationality.** Under SDH a sincere user's utility is at
least 0, whatever the others do. -/
theorem sdh_sincere_nonneg {arcs : Finset (U × U)} {q : U → U → ℝ} {c : U → ℝ}
    {ℓ : U} {v : Finset U → ℝ} (hv0 : v ∅ = 0)
    (hsep : CostSeparable v (c ℓ) (sincereSet (q ℓ) (c ℓ) (plannedPartners arcs ℓ)))
    (σ : SwipeProfile U) :
    0 ≤ swipeUtil v (c ℓ)
      (matchesOf arcs (σ.update ℓ (sincereLike q c ℓ) (sincereResp q c ℓ)) ℓ) := by
  refine swipeUtil_nonneg_of_costSeparable hv0 hsep fun x hx => ?_
  simp only [matchesOf, mem_union, mem_filter, mem_univ, true_and,
    SwipeProfile.update_like1_self, SwipeProfile.update_resp_self] at hx
  simp only [sincereSet, plannedPartners, mem_filter, mem_union, mem_univ, true_and]
  rcases hx with ⟨hx1, hx2, _⟩ | ⟨hx1, _, hx3⟩
  · simp only [sincereLike, decide_eq_true_eq] at hx2
    exact ⟨Or.inl hx1, hx2⟩
  · simp only [sincereResp, mem_filter] at hx3
    exact ⟨Or.inr hx1, hx3.2⟩

/-- **The step behind Theorem 5(e).** A planned pair whose two ends are sincere and
find each other acceptable always matches, whatever everyone else does. -/
theorem sdh_arc_matches {arcs : Finset (U × U)} {q : U → U → ℝ} {c : U → ℝ}
    {σ : SwipeProfile U} {s r : U} (hsr : (s, r) ∈ arcs)
    (hs : σ.like1 s = sincereLike q c s) (hr : σ.resp r = sincereResp q c r)
    (hqs : c s < q s r) (hqr : c r < q r s) :
    r ∈ matchesOf arcs σ s ∧ s ∈ matchesOf arcs σ r := by
  have hlike : σ.like1 s r = true := by rw [hs]; simpa [sincereLike] using hqs
  have hdisp : s ∈ display2 arcs σ r := by
    simp only [display2, mem_filter, mem_univ, true_and]; exact ⟨hsr, hlike⟩
  have hresp : s ∈ σ.resp r (display2 arcs σ r) := by
    rw [hr]; exact mem_filter.mpr ⟨hdisp, hqr⟩
  constructor
  · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hsr, hlike, hresp⟩)
  · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hsr, hlike, hresp⟩)

end Game

end DatingAlgo
