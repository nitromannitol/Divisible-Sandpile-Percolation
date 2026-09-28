import Sandpile.Support.IncrementBall
import Mathlib

/-!
# Bounded-step path enumeration and a union bound

Finite enumeration of bounded-step lattice paths and a union bound from joint vertex-event
probabilities.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section
namespace Sandpile

/-- The finite set of length-`(n + 1)` lists of sites forming a bounded-step (`boxDist`-radius-`1`)
path of `n` steps starting at `a`: at `n = 0` just `[a]`, and at `n + 1` the union over each
neighbour `b` in the radius-`1` box of `a` of `a :: Γ` for `Γ` a bounded path of length `n` from
`b`. -/
def boxWalkLists {d : ℕ} : ℕ → Site d → Finset (List (Site d))
  | 0, a => {[a]}
  | n + 1, a => (boxFinset a 1).biUnion (fun b => (boxWalkLists n b).image (List.cons a))

/-- `boxWalkLists n a` has at most `(3 ^ d) ^ n` elements, by induction using that each step
ranges over the `3 ^ d`-element radius-`1` box (`card_boxFinset`) and `List.cons` is injective. -/
lemma card_boxWalkLists_le {d : ℕ} (n : ℕ) (a : Site d) :
    (boxWalkLists n a).card ≤ (3 ^ d) ^ n := by
  induction n generalizing a with
  | zero => simp [boxWalkLists]
  | succ n ih =>
    calc
      _ ≤ ∑ b ∈ boxFinset a 1, ((boxWalkLists n b).image (List.cons a)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ boxFinset a 1, (3 ^ d) ^ n :=
        Finset.sum_le_sum (fun b _ => Finset.card_image_le.trans (ih b))
      _ = _ := by simp [card_boxFinset, pow_succ, Nat.mul_comm]

/-- Every list in `boxWalkLists n a` has length exactly `n + 1`, by induction on the recursive
definition. -/
lemma length_of_mem_boxWalkLists {d : ℕ} {n : ℕ} {a : Site d} {Γ : List (Site d)}
    (hΓ : Γ ∈ boxWalkLists n a) : Γ.length = n + 1 := by
  induction n generalizing a Γ with
  | zero =>
    have he : Γ = [a] := by simpa [boxWalkLists] using hΓ
    simp [he]
  | succ n ih =>
    obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp hΓ
    obtain ⟨Γ', hΓ', rfl⟩ := Finset.mem_image.mp hb
    simp only [List.length_cons, ih hΓ']

/-- If every edge of `G` moves by `boxDist` at most `1`, the support of any `G`-walk `p` from `a`
lies in `boxWalkLists p.length a`, so `boxWalkLists` enumerates every possible walk support. -/
lemma walk_support_mem_boxWalkLists {d : ℕ} {G : SimpleGraph (Site d)}
    (hstep : ∀ a b, G.Adj a b → boxDist a b ≤ 1) {a b : Site d} (p : G.Walk a b) :
    p.support ∈ boxWalkLists p.length a := by
  induction p with
  | nil => simp [boxWalkLists]
  | @cons a b c hab p ih =>
    exact Finset.mem_biUnion.mpr ⟨b, mem_boxFinset (hstep a b hab),
      Finset.mem_image.mpr ⟨p.support, ih, rfl⟩⟩

/-- The union of `boxWalkLists n a` over every starting site `a` in the finite set `S`: the
family of length-`(n + 1)` bounded-step lists starting anywhere in `S`. -/
def boxWalkListFamily {d : ℕ} (n : ℕ) (S : Finset (Site d)) : Finset (List (Site d)) :=
  S.biUnion (boxWalkLists n)

/-- `boxWalkListFamily n S` has at most `S.card * (3 ^ d) ^ n` elements, summing the per-start
bound `card_boxWalkLists_le` over `S`. -/
lemma card_boxWalkListFamily_le {d : ℕ} (n : ℕ) (S : Finset (Site d)) :
    (boxWalkListFamily n S).card ≤ S.card * (3 ^ d) ^ n := by
  calc
    _ ≤ ∑ a ∈ S, (boxWalkLists n a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ S, (3 ^ d) ^ n := Finset.sum_le_sum (fun a _ => card_boxWalkLists_le n a)
    _ = _ := by simp

/-- Every list in `boxWalkListFamily n S` has length exactly `n + 1`, inherited from
`length_of_mem_boxWalkLists`. -/
lemma length_of_mem_boxWalkListFamily {d : ℕ} {n : ℕ} {S : Finset (Site d)} {Γ : List (Site d)}
    (hΓ : Γ ∈ boxWalkListFamily n S) : Γ.length = n + 1 := by
  obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hΓ
  exact length_of_mem_boxWalkLists ha

/-- If every edge of `G` moves by `boxDist` at most `1` and `p` starts in `S`, the support of `p`
lies in `boxWalkListFamily p.length S`. -/
lemma walk_support_mem_boxWalkListFamily {d : ℕ} {G : SimpleGraph (Site d)}
    (hstep : ∀ a b, G.Adj a b → boxDist a b ≤ 1) {a b : Site d} (p : G.Walk a b)
    (S : Finset (Site d)) (ha : a ∈ S) : p.support ∈ boxWalkListFamily p.length S :=
  Finset.mem_biUnion.mpr ⟨a, ha, walk_support_mem_boxWalkLists hstep p⟩

/-- The event that some nodup (self-avoiding) bounded-step list `Γ` from `boxWalkListFamily n S`
has every one of its sites' events `E a` occurring: the event that a self-avoiding path of the
enumerated shape lies entirely inside the events `E`. -/
def boxPathEvent {d : ℕ} {Ω : Type*} (n : ℕ) (S : Finset (Site d)) (E : Site d → Set Ω) : Set Ω :=
  {ω | ∃ Γ ∈ boxWalkListFamily n S, Γ.Nodup ∧ ∀ a ∈ Γ, ω ∈ E a}

/-- Union bound on `boxPathEvent`: if every set of at least `m ≤ n + 1` distinct sites has joint
probability at most `p`, the whole event has probability at most `S.card * (3 ^ d) ^ n * p`,
summing this bound over the (at most `S.card * (3 ^ d) ^ n`) candidate lists via
`measure_biUnion_finset_le`. -/
lemma measure_boxPathEvent_le {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (n m : ℕ) (hm : m ≤ n + 1) (S : Finset (Site d)) (E : Site d → Set Ω) {p : ℝ≥0∞}
    (hT : ∀ T : Finset (Site d), m ≤ T.card → μ {ω | ∀ a ∈ T, ω ∈ E a} ≤ p) :
    μ (boxPathEvent n S E) ≤ (S.card : ℝ≥0∞) * (3 ^ d : ℝ≥0∞) ^ n * p := by
  classical
  let A (Γ : List (Site d)) := {ω | Γ.Nodup ∧ ∀ a ∈ Γ, ω ∈ E a}
  have hA (Γ : List (Site d)) (hΓ : Γ ∈ boxWalkListFamily n S) : μ (A Γ) ≤ p := by
    by_cases hn : Γ.Nodup
    · have he : A Γ = {ω | ∀ a ∈ Γ.toFinset, ω ∈ E a} := by
        ext ω
        simp only [A, mem_setOf_eq, hn, true_and, List.mem_toFinset]
      rw [he]
      apply hT
      rw [List.toFinset_card_of_nodup hn, length_of_mem_boxWalkListFamily hΓ]
      exact hm
    · have he : A Γ = ∅ := by ext ω; simp [A, hn]
      rw [he, measure_empty]
      exact bot_le
  have he : boxPathEvent n S E = ⋃ Γ ∈ boxWalkListFamily n S, A Γ := by
    ext ω
    simp only [boxPathEvent, A, mem_setOf_eq, mem_iUnion, exists_prop]
  rw [he]
  calc
    _ ≤ ∑ Γ ∈ boxWalkListFamily n S, μ (A Γ) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _Γ ∈ boxWalkListFamily n S, p := Finset.sum_le_sum hA
    _ = ((boxWalkListFamily n S).card : ℝ≥0∞) * p := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      apply mul_le_mul_left
      exact_mod_cast card_boxWalkListFamily_le n S

end Sandpile
