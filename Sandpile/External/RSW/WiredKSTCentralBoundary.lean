import Sandpile.External.RSW.WiredKSTDualEdges
import Sandpile.External.RSW.WiredDualStrip

/-!
# Central vertices of the wired dual boundary

Inside the central target interval, a boundary vertex has only its inward
vertical neighbor available to an open dual walk.
-/

namespace Sandpile.External.RSW

/-- An open edge from the central lower row and staying above it points upward. -/
theorem wiredKST_dual_lower_central_neighbor (m : ℕ) (ω : Sym2 (Site 2) → Bool)
    {x y : Site 2} (hxy : (lattice 2).Adj x y)
    (hx : x 1 = -((m : ℤ) + 1)) (hy : -((m : ℤ) + 1) ≤ y 1)
    (hl : -((m / 12 : ℕ) : ℤ) ≤ x 0) (hu : x 0 < m / 12)
    (hop : dualBondConfig (wiredKSTConfig m ω) s(x, y) = true) :
    y = x + Pi.single 1 1 := by
  obtain h | h | h | h := lattice_two_adj_cases hxy
  · have he : x = y - Pi.single 0 1 := by
      ext i
      fin_cases i <;> simp <;> omega
    have hc := dualBondConfig_wiredKST_lower_connector m ω y (by omega) (by omega) (by omega)
    rw [he, hc] at hop
    contradiction
  · have he : y = x - Pi.single 0 1 := by
      ext i
      fin_cases i <;> simp <;> omega
    have hc := dualBondConfig_wiredKST_lower_connector m ω x hx (by omega) (by omega)
    rw [Sym2.eq_swap, he, hc] at hop
    contradiction
  · ext i
    fin_cases i <;> simp <;> omega
  · omega

/-- An open edge from the central upper row and staying below it points downward. -/
theorem wiredKST_dual_upper_central_neighbor (m : ℕ) (ω : Sym2 (Site 2) → Bool)
    {x y : Site 2} (hxy : (lattice 2).Adj x y)
    (hx : x 1 = m) (hy : y 1 ≤ m)
    (hl : -((m / 12 : ℕ) : ℤ) ≤ x 0) (hu : x 0 < m / 12)
    (hop : dualBondConfig (wiredKSTConfig m ω) s(x, y) = true) :
    y = x - Pi.single 1 1 := by
  obtain h | h | h | h := lattice_two_adj_cases hxy
  · have he : x = y - Pi.single 0 1 := by
      ext i
      fin_cases i <;> simp <;> omega
    have hc := dualBondConfig_wiredKST_upper_connector m ω y (by omega) (by omega) (by omega)
    rw [he, hc] at hop
    contradiction
  · have he : y = x - Pi.single 0 1 := by
      ext i
      fin_cases i <;> simp <;> omega
    have hc := dualBondConfig_wiredKST_upper_connector m ω x hx (by omega) (by omega)
    rw [Sym2.eq_swap, he, hc] at hop
    contradiction
  · omega
  · ext i
    fin_cases i <;> simp <;> omega

end Sandpile.External.RSW
