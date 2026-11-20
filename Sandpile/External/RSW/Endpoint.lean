import Sandpile.External.RSW.CascadeBound

/-!
# Positivity in the quasi-crossing induction

An increasing interval isomorphism preserves the endpoints. A strict upper bound at the next
scale therefore forces the preceding complement, and its image under another increasing
isomorphism, to be positive.
-/

open Set

namespace Sandpile.External.RSW

/-- The nontrivial endpoint branch of the quasi-crossing induction has a positive
intermediate probability. -/
theorem positive_of_interval_comparison
    (f g : Icc (0 : ℝ) 1 ≃o Icc (0 : ℝ) 1)
    (x y z : Icc (0 : ℝ) 1) (q : ℝ)
    (hxy : f x ≤ y) (hy : (y : ℝ) < 1) (hz : (z : ℝ) = 1 - (x : ℝ))
    (hq : (g z : ℝ) ≤ q) : 0 < q := by
  have hx : (x : ℝ) < 1 := by
    by_contra! hnot
    have hxone : (x : ℝ) = 1 := le_antisymm x.property.2 hnot
    have hxtop : x = ⊤ := Subtype.ext hxone
    have hfone : (f x : ℝ) = 1 := by
      rw [hxtop, OrderIso.map_top]
      rfl
    have hxy' : (f x : ℝ) ≤ (y : ℝ) := hxy
    linarith
  have hzpos : (0 : ℝ) < (z : ℝ) := by rw [hz]; linarith
  have hbot : (⊥ : Icc (0 : ℝ) 1) < z := hzpos
  have hgpos := g.strictMono hbot
  rw [OrderIso.map_bot] at hgpos
  have hgpos' : (0 : ℝ) < (g z : ℝ) := hgpos
  linarith

end Sandpile.External.RSW
