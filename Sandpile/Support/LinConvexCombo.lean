import Mathlib

/-!
# Convexity of nonnegative combinations

A nonnegative combination of coordinatewise convex functions is convex. This is
the convexity of the tested field `F_R = ∑_x a_R(x) u_{n_R}(x)` used in Step 2 of
`lem:dgt4-linearization-from-survival` (`sandpile.tex:5803-5817`): each `u_{n_R}(x)`
is coordinatewise convex in the scenery (`prop:finite-time-concentration-scale`),
and `a_R(x) = R^{(d-4)/2} φ_R(x) ≥ 0` for `φ ≥ 0`.
-/

open Set

namespace Sandpile

/-- A finite nonnegative combination of coordinatewise convex functions is
coordinatewise convex. -/
theorem convexOn_sum_mul {ι : Type*} [DecidableEq ι] {s : Finset ι} {a : ι → ℝ}
    {f : ι → (ι → ℝ) → ℝ}
    (ha : ∀ x ∈ s, 0 ≤ a x) (hf : ∀ x ∈ s, ConvexOn ℝ Set.univ (f x)) :
    ConvexOn ℝ Set.univ (fun v => ∑ x ∈ s, a x * f x v) := by
  have h : ∀ x ∈ s, ConvexOn ℝ Set.univ (fun v => a x * f x v) :=
    fun x hx => (hf x hx).smul (ha x hx)
  induction s using Finset.induction with
  | empty => simpa using (convexOn_const (c := (0:ℝ)) convex_univ)
  | insert y t hy ih =>
      have hsum : (fun v => ∑ x ∈ insert y t, a x * f x v)
          = fun v => a y * f y v + ∑ x ∈ t, a x * f x v := by
        funext v; rw [Finset.sum_insert hy]
      rw [hsum]
      exact (h y (Finset.mem_insert_self y t)).add
        (ih (fun x hx => ha x (Finset.mem_insert_of_mem hx))
            (fun x hx => hf x (Finset.mem_insert_of_mem hx))
            (fun x hx => h x (Finset.mem_insert_of_mem hx)))

end Sandpile
