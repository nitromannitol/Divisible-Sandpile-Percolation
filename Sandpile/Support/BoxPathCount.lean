/-
Finite enumeration of bounded-step lattice paths and a union bound
from joint vertex-event probabilities.
-/
import Sandpile.Support.IncrementBall
import Mathlib

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section
namespace Sandpile

def boxWalkLists {d : ℕ} : ℕ → Site d → Finset (List (Site d))
  | 0, a => {[a]}
  | n + 1, a => (boxFinset a 1).biUnion (fun b => (boxWalkLists n b).image (List.cons a))

lemma card_boxWalkLists_le {d : ℕ} (n : ℕ) (a : Site d) :
    (boxWalkLists n a).card ≤ (3 ^ d) ^ n := by
  induction n generalizing a with
  | zero => simp [boxWalkLists]
  | succ n ih =>
    calc
      _ ≤ ∑ b ∈ boxFinset a 1, ((boxWalkLists n b).image (List.cons a)).card := Finset.card_biUnion_le
      _ ≤ ∑ _b ∈ boxFinset a 1, (3 ^ d) ^ n :=
        Finset.sum_le_sum (fun b _ => Finset.card_image_le.trans (ih b))
      _ = _ := by simp [card_boxFinset, pow_succ, Nat.mul_comm]

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

lemma walk_support_mem_boxWalkLists {d : ℕ} {G : SimpleGraph (Site d)}
    (hstep : ∀ a b, G.Adj a b → boxDist a b ≤ 1) {a b : Site d} (p : G.Walk a b) :
    p.support ∈ boxWalkLists p.length a := by
  induction p with
  | nil => simp [boxWalkLists]
  | @cons a b c hab p ih =>
    exact Finset.mem_biUnion.mpr ⟨b, mem_boxFinset (hstep a b hab),
      Finset.mem_image.mpr ⟨p.support, ih, rfl⟩⟩

def boxWalkListFamily {d : ℕ} (n : ℕ) (S : Finset (Site d)) : Finset (List (Site d)) :=
  S.biUnion (boxWalkLists n)

lemma card_boxWalkListFamily_le {d : ℕ} (n : ℕ) (S : Finset (Site d)) :
    (boxWalkListFamily n S).card ≤ S.card * (3 ^ d) ^ n := by
  calc
    _ ≤ ∑ a ∈ S, (boxWalkLists n a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ S, (3 ^ d) ^ n := Finset.sum_le_sum (fun a _ => card_boxWalkLists_le n a)
    _ = _ := by simp

lemma length_of_mem_boxWalkListFamily {d : ℕ} {n : ℕ} {S : Finset (Site d)} {Γ : List (Site d)}
    (hΓ : Γ ∈ boxWalkListFamily n S) : Γ.length = n + 1 := by
  obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp hΓ
  exact length_of_mem_boxWalkLists ha

lemma walk_support_mem_boxWalkListFamily {d : ℕ} {G : SimpleGraph (Site d)}
    (hstep : ∀ a b, G.Adj a b → boxDist a b ≤ 1) {a b : Site d} (p : G.Walk a b)
    (S : Finset (Site d)) (ha : a ∈ S) : p.support ∈ boxWalkListFamily p.length S :=
  Finset.mem_biUnion.mpr ⟨a, ha, walk_support_mem_boxWalkLists hstep p⟩

def boxPathEvent {d : ℕ} {Ω : Type*} (n : ℕ) (S : Finset (Site d)) (E : Site d → Set Ω) : Set Ω :=
  {ω | ∃ Γ ∈ boxWalkListFamily n S, Γ.Nodup ∧ ∀ a ∈ Γ, ω ∈ E a}

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
