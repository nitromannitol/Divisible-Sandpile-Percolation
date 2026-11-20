import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# Measurable selection from finitely many balls

A finite family of balls covering a set admits a measurable choice of a
covering ball, with a separate label for points outside the cover.
-/

open MeasureTheory

/-- Choose the first covering ball from a finite indexed family, using the
last index as a fallback outside the covered set. -/
theorem Sandpile.Support.exists_measurable_finite_ball_selector
    {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] [BorelSpace α]
    (K : Set α) (N : ℕ) (c : ℕ → α) (δ : ℝ)
    (hcover : ∀ x ∈ K, ∃ n < N, dist x (c n) < δ) :
    ∃ k : α → ℕ, Measurable k ∧ (∀ x, k x ≤ N) ∧
      ∀ x ∈ K, k x < N ∧ dist x (c (k x)) < δ := by
  classical
  let p : α → ℕ → Prop := fun x n => n = N ∨ (n < N ∧ dist x (c n) < δ)
  have hp : ∀ x, ∃ n, p x n := fun x => ⟨N, Or.inl rfl⟩
  have hpm : ∀ n, MeasurableSet {x | p x n} := by
    intro n
    exact MeasurableSet.union (MeasurableSet.const (n = N))
      ((MeasurableSet.const (n < N)).inter (Metric.isOpen_ball.measurableSet))
  let k : α → ℕ := fun x => Nat.find (hp x)
  refine ⟨k, measurable_find hp hpm, ?_, ?_⟩
  · intro x
    exact Nat.find_min' (hp x) (Or.inl rfl)
  · intro x hx
    obtain ⟨n, hn, hdist⟩ := hcover x hx
    have hkn : k x ≤ n := Nat.find_min' (hp x) (Or.inr ⟨hn, hdist⟩)
    have hkN : k x < N := hkn.trans_lt hn
    have hspec := Nat.find_spec (hp x)
    have hspec' : k x = N ∨ (k x < N ∧ dist x (c (k x)) < δ) := hspec
    exact hspec'.resolve_left (ne_of_lt hkN)

/-- A compact set has a measurable finite-ball selector with centres in that
set and one fallback label. -/
theorem Sandpile.Support.exists_measurable_compact_ball_selector
    {α : Type*} [PseudoMetricSpace α] [MeasurableSpace α] [BorelSpace α]
    (K : Set α) (hK : IsCompact K) (x₀ : α) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (N : ℕ) (c : ℕ → α) (k : α → ℕ), Measurable k ∧ (∀ x, k x ≤ N) ∧
      ∀ x ∈ K, k x < N ∧ c (k x) ∈ K ∧ dist x (c (k x)) < δ := by
  classical
  obtain ⟨S, hSK, hS, hcover⟩ := hK.finite_cover_balls hδ
  let : Fintype S := hS.fintype
  let N := Fintype.card S
  let e : Fin N ≃ S := (Fintype.equivFin S).symm
  let c : ℕ → α := fun n => if h : n < N then (e ⟨n, h⟩).1 else x₀
  have hc : ∀ n, n < N → c n ∈ K := by
    intro n hn
    exact hSK (by simpa only [c, dif_pos hn] using (e ⟨n, hn⟩).2)
  have hcover' : ∀ x ∈ K, ∃ n < N, dist x (c n) < δ := by
    intro x hx
    obtain ⟨z, hz⟩ := Set.mem_iUnion.1 (hcover hx)
    obtain ⟨hzS, hxz⟩ := Set.mem_iUnion.1 hz
    let j : Fin N := e.symm ⟨z, hzS⟩
    refine ⟨j, j.2, ?_⟩
    have he : c j = z := by
      simp only [c, dif_pos j.2]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨z, hzS⟩)
    rw [he]
    exact hxz
  obtain ⟨k, hkm, hkN, hk⟩ :=
    Sandpile.Support.exists_measurable_finite_ball_selector K N c δ hcover'
  exact ⟨N, c, k, hkm, hkN, fun x hx => ⟨(hk x hx).1, hc _ (hk x hx).1, (hk x hx).2⟩⟩
