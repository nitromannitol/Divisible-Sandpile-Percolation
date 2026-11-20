import Sandpile.External.RSW.WiredDualBoundary

/-!
# Dual bonds at the upper arm boundary

Wiring leaves every dual bond in the arm strip unchanged, except possibly for
horizontal dual bonds on its upper boundary.
-/

namespace Sandpile.External.RSW

/-- A dual bond in the closed strip retains its state unless it lies on the upper row. -/
theorem dualBondConfig_wiredArm_eq_of_adjacent_strip (m : ℕ)
    (ω : Sym2 (Site 2) → Bool) {x y : Site 2} (hxy : (lattice 2).Adj x y)
    (hx : -(m : ℤ) ≤ x 1 ∧ x 1 ≤ m)
    (hy : -(m : ℤ) ≤ y 1 ∧ y 1 ≤ m)
    (htop : ¬ (x 1 = m ∧ y 1 = m)) :
    dualBondConfig (wiredArmConfig m ω) s(x, y) = dualBondConfig ω s(x, y) := by
  obtain h | h | h | h := lattice_two_adj_cases hxy
  · have he : x = y - Pi.single 0 1 := by
      ext i
      fin_cases i <;> simp <;> omega
    rw [he]
    apply dualBondConfig_wiredArm_vertical_interior m ω y <;> omega
  · have he : y = x - Pi.single 0 1 := by
      ext i
      fin_cases i <;> simp <;> omega
    rw [Sym2.eq_swap, he]
    apply dualBondConfig_wiredArm_vertical_interior m ω x <;> omega
  · have he : x = y - Pi.single 1 1 := by
      ext i
      fin_cases i <;> simp <;> omega
    rw [he]
    apply dualBondConfig_wiredArm_horizontal_interior m ω y <;> omega
  · have he : y = x - Pi.single 1 1 := by
      ext i
      fin_cases i <;> simp <;> omega
    rw [Sym2.eq_swap, he]
    apply dualBondConfig_wiredArm_horizontal_interior m ω x <;> omega

end Sandpile.External.RSW
