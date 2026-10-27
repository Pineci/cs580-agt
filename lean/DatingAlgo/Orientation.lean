import DatingAlgo.TruthfulSwiping

/-!
# Lemma R: realizability in two-directional designs

Lemma R of the vault note "Truthful Swiping with an LLM Oracle": if likes are certain, a
match set can be shown in a two-directional design with display cap `K` iff every user
has at most `2K` matches.

* `exists_balanced` : every finite multigraph (a multiset of edges, each given as an
  ordered pair) can be re-oriented so that at every vertex out-degree and in-degree
  differ by at most one. The note uses Euler tours; the proof here instead splits off
  two edges at a vertex of degree at least 2 and inducts on the number of edges.
* `lemmaR` : a match set in which every user has at most `2K` partners has an
  orientation in which every user initiates at most `K` of its matches and responds to
  at most `K`. Out-arcs are period-1 initiations and in-arcs period-2 responses.
* `lemmaR_realize` : with that orientation as SDH's planned arcs, if every pair is
  mutually acceptable and everyone swipes sincerely, exactly the pairs of the match set
  match, and each user is shown at most `K` profiles per period.
* `matchesOf_card_le` : conversely, a user shown at most `K` profiles per period has at
  most `2K` matches.

One-directional designs need no lemma: orient every pair from initiator to responder.
-/

namespace DatingAlgo

open Finset

section Multigraph

variable {V : Type*} [DecidableEq V]

/-- Out-degree minus in-degree of `v` in a multiset of arcs. -/
def imbalance (O : Multiset (V × V)) (v : V) : ℤ :=
  (O.map fun a => ((if a.1 = v then 1 else 0) - (if a.2 = v then 1 else 0) : ℤ)).sum

/-- `O` re-orients `G`: the same edges, each possibly reversed. -/
def Reorients (G O : Multiset (V × V)) : Prop :=
  Multiset.Rel (fun e f => f = e ∨ f = e.swap) G O

/-- Adding an arc `a` changes `v`'s imbalance by `[a.1 = v] - [a.2 = v]`. -/
theorem imbalance_cons (a : V × V) (O : Multiset (V × V)) (v : V) :
    imbalance (a ::ₘ O) v =
      ((if a.1 = v then 1 else 0) - (if a.2 = v then 1 else 0)) + imbalance O v := by
  simp only [imbalance, Multiset.map_cons, Multiset.sum_cons]

/-- Imbalance is out-degree minus in-degree. -/
theorem imbalance_eq (O : Multiset (V × V)) (v : V) :
    imbalance O v =
      (Multiset.card (O.filter (·.1 = v)) : ℤ) - Multiset.card (O.filter (·.2 = v)) := by
  induction O using Multiset.induction_on with
  | empty => simp [imbalance]
  | cons a O ih =>
    rw [imbalance_cons, ih, Multiset.filter_cons, Multiset.filter_cons]
    split_ifs <;>
      simp only [Multiset.card_add, Multiset.card_singleton, Multiset.card_zero, Nat.cast_add,
        Nat.cast_one, Nat.cast_zero] <;> ring

/-- **Balanced orientation.** Every finite multigraph has an orientation in which
out-degree and in-degree differ by at most one at every vertex. -/
theorem exists_balanced (G : Multiset (V × V)) :
    ∃ O, Reorients G O ∧ ∀ v, |imbalance O v| ≤ 1 := by
  obtain ⟨n, hn⟩ : ∃ n, Multiset.card G = n := ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing G with
  | _ n ih =>
  by_cases hdeg : ∃ v, 2 ≤ Multiset.card (G.filter fun e => e.1 = v ∨ e.2 = v)
  · obtain ⟨v, hv⟩ := hdeg
    -- Two edges `e1, e2` at `v`.
    obtain ⟨e1, he1⟩ := Multiset.card_pos_iff_exists_mem.mp
      (by omega : 0 < Multiset.card (G.filter fun e => e.1 = v ∨ e.2 = v))
    obtain ⟨G1, rfl⟩ := Multiset.exists_cons_of_mem (Multiset.mem_of_mem_filter he1)
    have hp1 := Multiset.of_mem_filter he1
    rw [Multiset.filter_cons_of_pos (p := fun e : V × V => e.1 = v ∨ e.2 = v) _ hp1,
      Multiset.card_cons] at hv
    obtain ⟨e2, he2⟩ := Multiset.card_pos_iff_exists_mem.mp
      (by omega : 0 < Multiset.card (G1.filter fun e => e.1 = v ∨ e.2 = v))
    obtain ⟨G2, rfl⟩ := Multiset.exists_cons_of_mem (Multiset.mem_of_mem_filter he2)
    have hp2 := Multiset.of_mem_filter he2
    -- An edge at `v` is `(u, v)` or `(v, u)` for its other end `u`.
    have hend : ∀ e : V × V, (e.1 = v ∨ e.2 = v) →
        ∃ u, ((u, v) = e ∨ (u, v) = e.swap) ∧ ((v, u) = e ∨ (v, u) = e.swap) := by
      rintro ⟨a, b⟩ (h | h) <;> simp only at h <;> subst h
      · exact ⟨b, Or.inr rfl, Or.inl rfl⟩
      · exact ⟨a, Or.inl rfl, Or.inr rfl⟩
    obtain ⟨u, hu1, hu2⟩ := hend e1 hp1
    obtain ⟨w, hw1, hw2⟩ := hend e2 hp2
    -- Replace them by one edge `(u, w)`, orient the smaller multigraph, and split the
    -- arc between `u` and `w` back into two arcs through `v`.
    simp only [Multiset.card_cons] at hn
    obtain ⟨O0, hO0, hbal⟩ :=
      ih (Multiset.card G2 + 1) (by omega) ((u, w) ::ₘ G2) (Multiset.card_cons _ _)
    obtain ⟨g, O', hg, hO', rfl⟩ := Multiset.rel_cons_left.mp hO0
    rcases hg with rfl | rfl
    · refine ⟨(u, v) ::ₘ (v, w) ::ₘ O', Multiset.Rel.cons hu1 (Multiset.Rel.cons hw2 hO'),
        fun x => ?_⟩
      have heq : imbalance ((u, v) ::ₘ (v, w) ::ₘ O') x = imbalance ((u, w) ::ₘ O') x := by
        simp only [imbalance_cons]; ring
      rw [heq]
      exact hbal x
    · refine ⟨(v, u) ::ₘ (w, v) ::ₘ O', Multiset.Rel.cons hu2 (Multiset.Rel.cons hw1 hO'),
        fun x => ?_⟩
      have heq : imbalance ((v, u) ::ₘ (w, v) ::ₘ O') x =
          imbalance ((u, w).swap ::ₘ O') x := by
        simp only [imbalance_cons, Prod.fst_swap, Prod.snd_swap]; ring
      rw [heq]
      exact hbal x
  · -- Every vertex has at most one edge: keep the orientation.
    push Not at hdeg
    refine ⟨G, Multiset.rel_refl_of_refl_on fun e _ => Or.inl rfl, fun v => ?_⟩
    rw [imbalance_eq, abs_le]
    have h1 : Multiset.card (G.filter (·.1 = v)) ≤
        Multiset.card (G.filter fun e => e.1 = v ∨ e.2 = v) :=
      Multiset.card_le_card (Multiset.monotone_filter_right G fun e h => Or.inl h)
    have h2 : Multiset.card (G.filter (·.2 = v)) ≤
        Multiset.card (G.filter fun e => e.1 = v ∨ e.2 = v) :=
      Multiset.card_le_card (Multiset.monotone_filter_right G fun e h => Or.inr h)
    have h3 := hdeg v
    constructor <;> omega

end Multigraph

section Graph

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **Lemma R, two-directional designs.** Let `E` be a match set (unordered pairs, no
user matched to itself) in which every user has at most `2K` partners. Then `E` has an
orientation `arcs`, each pair oriented exactly one way, in which every user has at most
`K` out-arcs (period-1 initiations) and at most `K` in-arcs (period-2 responses). -/
theorem lemmaR (E : Finset (Sym2 U)) (hE : ∀ e ∈ E, ¬ e.IsDiag) (K : ℕ)
    (hdeg : ∀ u, (E.filter fun e => u ∈ e).card ≤ 2 * K) :
    ∃ arcs : Finset (U × U), (∀ a b, (a, b) ∈ arcs → (b, a) ∉ arcs) ∧
      (∀ a, (a, a) ∉ arcs) ∧ arcs.image (fun a => s(a.1, a.2)) = E ∧
      (∀ u, (univ.filter fun r => (u, r) ∈ arcs).card ≤ K) ∧
      ∀ u, (univ.filter fun s => (s, u) ∈ arcs).card ≤ K := by
  obtain ⟨O, hO, hbal⟩ := exists_balanced (E.val.map Quot.out)
  -- `O` lists the pairs of `E`, each oriented one way.
  have hmap : O.map (fun a : U × U => s(a.1, a.2)) = E.val := by
    have h1 : Multiset.Rel (fun e f : U × U => s(e.1, e.2) = s(f.1, f.2))
        (E.val.map Quot.out) O :=
      Multiset.Rel.mono hO fun e _ f _ h => by
        rcases h with rfl | rfl
        · rfl
        · exact Sym2.eq_swap
    rw [← Multiset.rel_eq.mp ((Multiset.rel_map (p := (· = ·))
      (f := fun a : U × U => s(a.1, a.2)) (g := fun a : U × U => s(a.1, a.2))).mpr h1),
      Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id E.val]
    exact Multiset.map_congr rfl fun e _ => Sym2.mk_fst_out_snd_out e
  have hnd' : (O.map fun a : U × U => s(a.1, a.2)).Nodup := by rw [hmap]; exact E.nodup
  have hnd : O.Nodup := Multiset.Nodup.of_map _ hnd'
  have hmemO : ∀ a b, (a, b) ∈ O → s(a, b) ∈ E := fun a b h => by
    have := Multiset.mem_map_of_mem (fun a : U × U => s(a.1, a.2)) h
    rw [hmap] at this
    exact this
  have hloop : ∀ a, (a, a) ∉ O := fun a h => hE _ (hmemO a a h) (Sym2.mk_isDiag_iff.mpr rfl)
  -- Out- and in-degrees in `O` are at most `K`.
  have hdeg' : ∀ u, Multiset.card (O.filter (·.1 = u)) ≤ K ∧
      Multiset.card (O.filter (·.2 = u)) ≤ K := by
    intro u
    have hsum : Multiset.card (O.filter (·.1 = u)) + Multiset.card (O.filter (·.2 = u)) ≤
        2 * K := by
      have hnil : O.filter (fun a : U × U => a.1 = u ∧ a.2 = u) = 0 :=
        Multiset.filter_eq_nil.mpr fun a ha h =>
          hloop u ((Prod.ext h.1 h.2 : a = (u, u)) ▸ ha)
      rw [← Multiset.card_add, Multiset.filter_add_filter, hnil, add_zero]
      calc Multiset.card (O.filter fun a => a.1 = u ∨ a.2 = u)
          = Multiset.card ((O.map fun a : U × U => s(a.1, a.2)).filter (u ∈ ·)) := by
            rw [Multiset.filter_map, Multiset.card_map]
            exact congrArg Multiset.card (Multiset.filter_congr fun a _ => by
              simp only [Function.comp_apply, Sym2.mem_iff]
              exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩)
        _ ≤ 2 * K := by rw [hmap]; exact hdeg u
    have hb := abs_le.mp (hbal u)
    rw [imbalance_eq] at hb
    omega
  refine ⟨⟨O, hnd⟩, fun a b hab hba => ?_, hloop, ?_, fun u => ?_, fun u => ?_⟩
  · have := Multiset.inj_on_of_nodup_map hnd' _ hab _ hba Sym2.eq_swap
    obtain ⟨rfl, -⟩ := Prod.mk.inj this
    exact hloop a hab
  · ext e
    rw [mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact hmemO a.1 a.2 ha
    · intro he
      have : e ∈ O.map (fun a : U × U => s(a.1, a.2)) := by rw [hmap]; exact he
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp this
      exact ⟨a, ha, rfl⟩
  · calc (univ.filter fun r => (u, r) ∈ (⟨O, hnd⟩ : Finset (U × U))).card
        ≤ ((⟨O, hnd⟩ : Finset (U × U)).filter (·.1 = u)).card :=
          card_le_card_of_injOn (fun r => (u, r)) (fun r hr => by
            rw [mem_coe, mem_filter] at hr ⊢
            exact ⟨hr.2, rfl⟩) (fun r1 _ r2 _ h => (Prod.mk.inj h).2)
      _ ≤ K := (hdeg' u).1
  · calc (univ.filter fun s => (s, u) ∈ (⟨O, hnd⟩ : Finset (U × U))).card
        ≤ ((⟨O, hnd⟩ : Finset (U × U)).filter (·.2 = u)).card :=
          card_le_card_of_injOn (fun s => (s, u)) (fun s hs => by
            rw [mem_coe, mem_filter] at hs ⊢
            exact ⟨hs.2, rfl⟩) (fun s1 _ s2 _ h => (Prod.mk.inj h).1)
      _ ≤ K := (hdeg' u).2

/-- Everyone swipes sincerely. -/
noncomputable def sincereProfile (q : U → U → ℝ) (c : U → ℝ) : SwipeProfile U where
  like1 := sincereLike q c
  resp := sincereResp q c

/-- **Lemma R, realizability.** Take planned arcs with every user having at most `K`
out-arcs and `K` in-arcs (as `lemmaR` provides), every planned pair mutually acceptable,
and everyone sincere. Then every user matches exactly its planned partners, and is shown
at most `K` profiles in each period. -/
theorem lemmaR_realize {arcs : Finset (U × U)} {K : ℕ}
    (hin : ∀ u, (univ.filter fun s => (s, u) ∈ arcs).card ≤ K)
    {q : U → U → ℝ} {c : U → ℝ} (hacc : ∀ a b, (a, b) ∈ arcs → c a < q a b ∧ c b < q b a)
    (ℓ : U) :
    matchesOf arcs (sincereProfile q c) ℓ = plannedPartners arcs ℓ ∧
      (display2 arcs (sincereProfile q c) ℓ).card ≤ K := by
  constructor
  · ext x
    constructor
    · intro hx
      simp only [matchesOf, plannedPartners, mem_union, mem_filter, mem_univ, true_and]
        at hx ⊢
      rcases hx with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    · intro hx
      simp only [plannedPartners, mem_union, mem_filter, mem_univ, true_and] at hx
      rcases hx with h | h
      · exact (sdh_arc_matches (σ := sincereProfile q c) h rfl rfl (hacc ℓ x h).1
          (hacc ℓ x h).2).1
      · exact (sdh_arc_matches (σ := sincereProfile q c) h rfl rfl (hacc x ℓ h).1
          (hacc x ℓ h).2).2
  · refine (card_le_card fun s hs => ?_).trans (hin ℓ)
    simp only [display2, mem_filter, mem_univ, true_and] at hs ⊢
    exact hs.1

/-- **Lemma R, the converse.** If every user is shown at most `K` profiles in period 1
(out-arcs) and has at most `K` planned initiators (in-arcs), every user has at most `2K`
matches, whatever anyone does. -/
theorem matchesOf_card_le {arcs : Finset (U × U)} {K : ℕ}
    (hout : ∀ u, (univ.filter fun r => (u, r) ∈ arcs).card ≤ K)
    (hin : ∀ u, (univ.filter fun s => (s, u) ∈ arcs).card ≤ K)
    (σ : SwipeProfile U) (ℓ : U) : (matchesOf arcs σ ℓ).card ≤ 2 * K := by
  calc (matchesOf arcs σ ℓ).card
      ≤ ((univ.filter fun r => (ℓ, r) ∈ arcs) ∪ (univ.filter fun s => (s, ℓ) ∈ arcs)).card :=
        card_le_card fun x hx => by
          simp only [matchesOf, mem_union, mem_filter, mem_univ, true_and] at hx ⊢
          rcases hx with h | h
          · exact Or.inl h.1
          · exact Or.inr h.1
    _ ≤ (univ.filter fun r => (ℓ, r) ∈ arcs).card + (univ.filter fun s => (s, ℓ) ∈ arcs).card :=
        card_union_le _ _
    _ ≤ 2 * K := by linarith [hout ℓ, hin ℓ]

/-- A user's planned partners are its neighbors in the match set. -/
theorem plannedPartners_eq_neighbors {arcs : Finset (U × U)} {E : Finset (Sym2 U)}
    (hE : arcs.image (fun a => s(a.1, a.2)) = E) (ℓ : U) :
    plannedPartners arcs ℓ = univ.filter fun x => s(ℓ, x) ∈ E := by
  subst hE
  ext x
  simp only [plannedPartners, mem_union, mem_filter, mem_univ, true_and, mem_image,
    Sym2.eq_iff, Prod.exists]
  constructor
  · rintro (h | h)
    · exact ⟨ℓ, x, h, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨x, ℓ, h, Or.inr ⟨rfl, rfl⟩⟩
  · rintro ⟨a, b, hab, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact Or.inl hab
    · exact Or.inr hab

end Graph

end DatingAlgo
