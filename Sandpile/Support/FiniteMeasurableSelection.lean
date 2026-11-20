import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Data.Fintype.EquivFin

/-!
# Selection from a finite measurable cover

A finite measurable cover admits a measurable choice of a covering member,
with a fallback label outside the covered set.
-/

open MeasureTheory

/-- Select a member of a finite measurable cover using a bounded natural-valued
measurable label, with one additional fallback label. -/
theorem Sandpile.Support.exists_measurable_finite_cover_selector
    {α β : Type*} [MeasurableSpace α] (K : Set α) (S : Finset β) (z₀ : β)
    (U : β → Set α) (hUm : ∀ z, MeasurableSet (U z))
    (hcover : ∀ x ∈ K, ∃ z ∈ S, x ∈ U z) :
    ∃ (N : ℕ) (c : ℕ → β) (k : α → ℕ), Measurable k ∧ (∀ x, k x ≤ N) ∧
      ∀ x ∈ K, k x < N ∧ c (k x) ∈ S ∧ x ∈ U (c (k x)) := by
  classical
  let I := {z // z ∈ S}
  let N := Fintype.card I
  let e : Fin N ≃ I := (Fintype.equivFin I).symm
  let c : ℕ → β := fun n => if h : n < N then (e ⟨n, h⟩).1 else z₀
  have hc : ∀ n, n < N → c n ∈ S := by
    intro n hn
    simpa only [c, dite_eq_left hn] using (e ⟨n, hn⟩).2
  let p : α → ℕ → Prop := fun x n => n = N ∨ (n < N ∧ x ∈ U (c n))
  have hp : ∀ x, ∃ n, p x n := fun x => ⟨N, Or.inl rfl⟩
  have hpm : ∀ n, MeasurableSet {x | p x n} := fun n =>
    (MeasurableSet.const (n = N)).union ((MeasurableSet.const (n < N)).inter (hUm (c n)))
  let k : α → ℕ := fun x => Nat.find (hp x)
  have hkm : Measurable k := measurable_find hp hpm
  have hkN : ∀ x, k x ≤ N := fun x => Nat.find_min' (hp x) (Or.inl rfl)
  refine ⟨N, c, k, hkm, hkN, ?_⟩
  intro x hx
  obtain ⟨z, hzS, hz⟩ := hcover x hx
  let j : Fin N := e.symm ⟨z, hzS⟩
  have he : c j = z := by
    simp only [c, dite_eq_left j.2]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨z, hzS⟩)
  have hkj : k x ≤ j := Nat.find_min' (hp x) (Or.inr ⟨j.2, he.symm ▸ hz⟩)
  have hklt : k x < N := hkj.trans_lt j.2
  have hspec : k x = N ∨ (k x < N ∧ x ∈ U (c (k x))) := Nat.find_spec (hp x)
  exact ⟨hklt, hc _ hklt, (hspec.resolve_left (ne_of_lt hklt)).2⟩
