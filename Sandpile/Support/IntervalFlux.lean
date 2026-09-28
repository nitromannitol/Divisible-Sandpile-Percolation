import Mathlib

/-!
# Interval incidence sums and characteristic-two telescoping

Two combinatorial identities for a finite sequence bracketed between two boundary values.
`sum_interval_incidence`, and its version `sum_interval_mapped_incidence` for values pushed
through a map `f`, resum a weighted sum of `Fin.cons`/`Fin.snoc` insertions into a boundary
contribution plus an interior sum weighted by consecutive pairs of weights. Over `ZMod 2`,
`sum_interval_differences_mod_two` shows the consecutive-pair sum of a sequence telescopes to
its two endpoint values.
-/

open scoped BigOperators
namespace Sandpile

/-- For weights `A : Fin (n + 1) → R` and an interior sequence `F : Fin n → R` capped by
boundary values `B` and `T`, the sum of `A j * (Fin.cons B F j + Fin.snoc F T j)` over all
`n + 1` weights splits as the boundary terms `A 0 * B + A (Fin.last n) * T` plus the interior
sum `∑ j, (A j.castSucc + A j.succ) * F j`, since each value `F j` is weighted once by
`Fin.cons` at index `j.succ` and once by `Fin.snoc` at index `j.castSucc`. -/
lemma sum_interval_incidence {R : Type*} [CommRing R] {n : ℕ}
    (A : Fin (n + 1) → R) (B T : R) (F : Fin n → R) :
    (∑ j, A j * (Fin.cons (α := fun _ => R) B F j + Fin.snoc (α := fun _ => R) F T j)) =
      A 0 * B + A (Fin.last n) * T +
        ∑ j : Fin n, (A j.castSucc + A j.succ) * F j := by
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  rw [Fin.sum_univ_succ (fun j => A j * Fin.cons (α := fun _ => R) B F j),
    Fin.sum_univ_castSucc (fun j => A j * Fin.snoc (α := fun _ => R) F T j)]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.snoc_castSucc, Fin.snoc_last]
  simp_rw [add_mul, Finset.sum_add_distrib]
  ring

/-- The incidence identity `sum_interval_incidence`, transported along a map `f : V → R` applied
to boundary values `B, T : V` and an interior sequence `F : Fin n → V`, by rewriting
`f ∘ Fin.cons` and `f ∘ Fin.snoc` as `Fin.cons`/`Fin.snoc` of the composed sequence `f ∘ F`. -/
lemma sum_interval_mapped_incidence {R : Type*} [CommRing R] {V : Type*} {n : ℕ}
    (A : Fin (n + 1) → R) (B T : V) (F : Fin n → V) (f : V → R) :
    (∑ j, A j * (f (Fin.cons (α := fun _ => V) B F j) +
      f (Fin.snoc (α := fun _ => V) F T j))) =
      A 0 * f B + A (Fin.last n) * f T +
        ∑ j : Fin n, (A j.castSucc + A j.succ) * f (F j) := by
  have hc (j : Fin (n + 1)) : f (Fin.cons (α := fun _ => V) B F j) =
      Fin.cons (α := fun _ => R) (f B) (fun k => f (F k)) j := congr_fun (Fin.comp_cons f B F) j
  have hs (j : Fin (n + 1)) : f (Fin.snoc (α := fun _ => V) F T j) =
      Fin.snoc (α := fun _ => R) (fun k => f (F k)) (f T) j := congr_fun (Fin.comp_snoc f F T) j
  simp_rw [hc, hs]
  exact sum_interval_incidence A (f B) (f T) (fun k => f (F k))

/-- Over `ZMod 2`, consecutive-pair sums telescope: `∑ j, (A j.castSucc + A j.succ)` equals
`A 0 + A (Fin.last n)`, since `Fin.sum_univ_succ` and `Fin.sum_univ_castSucc` both compute
`∑ j, A j` and the interior terms cancel via `CharTwo.add_self_eq_zero`. -/
lemma sum_interval_differences_mod_two {n : ℕ} (A : Fin (n + 1) → ZMod 2) :
    (∑ j : Fin n, (A j.castSucc + A j.succ)) = A 0 + A (Fin.last n) := by
  have h1 := Fin.sum_univ_succ A
  have h2 := Fin.sum_univ_castSucc A
  rw [Finset.sum_add_distrib]
  have hh : (∑ j : Fin n, A j.castSucc) + (∑ j : Fin n, A j.succ) +
      (A 0 + A (Fin.last n)) = 0 := by
    calc
      _ = (A 0 + ∑ j : Fin n, A j.succ) + ((∑ j : Fin n, A j.castSucc) + A (Fin.last n)) := by ring
      _ = (∑ j, A j) + (∑ j, A j) := by rw [← h1, ← h2]
      _ = 0 := CharTwo.add_self_eq_zero _
  have he := congrArg (fun x : ZMod 2 => x + (A 0 + A (Fin.last n))) hh
  simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using he

end Sandpile
