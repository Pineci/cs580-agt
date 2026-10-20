import DatingAlgo.IndepExp

/-!
# The `T`-period model

Shared by the multi-period files (Rios & Torrico, Section 5): the Theorem 5.4 counterexample
(`MultiPeriod.lean`), the Theorem 5.3 counterexample (`MultiPeriodDHT.lean`), and the repaired
Theorem 5.3 (`MultiPeriodRepair.lean`).
- `Instance`: `T` periods, display caps, and like probabilities that don't change over time.
- Like outcomes are drawn up front and are independent: `likeProb`, `LIof`, `LJof`.
- `IsDHTInit`: Steps 6–8 of Algorithm 3 (DHT) for one user.
-/

namespace DatingAlgo

open Finset

namespace TPeriod

/-- A `T`-period instance with complete bipartite potentials. Like probabilities don't change
over time. -/
structure Instance (I J : Type*) where
  T : ℕ
  KI : I → ℕ
  KJ : J → ℕ
  /-- `pIJ i j`: probability that `i` likes `j` when shown. -/
  pIJ : I → J → ℝ
  /-- `pJI j i`: probability that `j` likes `i` when shown. -/
  pJI : J → I → ℝ

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

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

omit [DecidableEq I] [DecidableEq J] in
/-- Like probabilities lie in `[0, 1]` when the instance's do. -/
theorem likeProb_mem {inst : Instance I J}
    (hp : ∀ i j, 0 ≤ inst.pIJ i j ∧ inst.pIJ i j ≤ 1 ∧ 0 ≤ inst.pJI j i ∧ inst.pJI j i ≤ 1) :
    ∀ e ∈ (univ : Finset ((I × J) ⊕ (J × I))), 0 ≤ likeProb inst e ∧ likeProb inst e ≤ 1 := by
  rintro (⟨i, j⟩ | ⟨j, i⟩) -
  · exact ⟨(hp i j).1, (hp i j).2.1⟩
  · exact ⟨(hp i j).2.2.1, (hp i j).2.2.2⟩

/-- Steps 6–8 of Algorithm 3 for one user. The user's initiation displays `d t`:
- show exactly `X` over the horizon, at most `K` per period, each once;
- use slots as early as possible;
- come in decreasing order of `q`, the target's like probability for the user. -/
def IsDHTInit {β : Type*} [DecidableEq β] {T : ℕ} (K : ℕ) (X : Finset β) (q : β → ℝ)
    (d : Fin T → Finset β) : Prop :=
  (univ.biUnion d = X) ∧ (∀ t, (d t).card ≤ K) ∧ (∀ t t' b, b ∈ d t → b ∈ d t' → t = t') ∧
  (∀ t t' : Fin T, t < t' → (d t').Nonempty → (d t).card = K) ∧
  (∀ (t t' : Fin T) b b', t < t' → b ∈ d t → b' ∈ d t' → q b' ≤ q b)

end TPeriod

end DatingAlgo
