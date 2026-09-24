/-
Interval incidence sums and characteristic-two telescoping for finite grids.
-/
import Mathlib

open scoped BigOperators
namespace Sandpile

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
