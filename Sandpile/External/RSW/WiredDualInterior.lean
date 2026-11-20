import Sandpile.External.RSW.WiredArmDual
import Sandpile.External.RSW.SiteBondCrossing
import Sandpile.Support.WalkRay

/-!
# Interior dual bonds of the wired arm configuration

Nearest-neighbor dual bonds strictly below the upper face row and above the
lower exterior row retain their states after wiring the primal arm boundary.
-/

namespace Sandpile.External.RSW

/-- Wiring preserves a dual bond whose endpoints lie strictly below the upper face row. -/
theorem dualBondConfig_wiredArm_eq_of_adjacent_interior (m : ℕ)
    (ω : Sym2 (Site 2) → Bool) {x y : Site 2} (hxy : (lattice 2).Adj x y)
    (hx : -(m : ℤ) ≤ x 1 ∧ x 1 < m)
    (hy : -(m : ℤ) ≤ y 1 ∧ y 1 < m) :
    dualBondConfig (wiredArmConfig m ω) s(x, y) = dualBondConfig ω s(x, y) := by
  obtain h | h | h | h := lattice_two_adj_cases hxy
  · have he : x = y - Pi.single 0 1 := by
      ext i
      fin_cases i <;> simp <;> omega
    rw [he]
    exact dualBondConfig_wiredArm_vertical_interior m ω y (by omega) (by omega)
  · have he : y = x - Pi.single 0 1 := by
      ext i
      fin_cases i <;> simp <;> omega
    rw [Sym2.eq_swap, he]
    exact dualBondConfig_wiredArm_vertical_interior m ω x (by omega) (by omega)
  · have he : x = y - Pi.single 1 1 := by
      ext i
      fin_cases i <;> simp <;> omega
    rw [he]
    exact dualBondConfig_wiredArm_horizontal_interior m ω y (by omega) (by omega)
  · have he : y = x - Pi.single 1 1 := by
      ext i
      fin_cases i <;> simp <;> omega
    rw [Sym2.eq_swap, he]
    exact dualBondConfig_wiredArm_horizontal_interior m ω x (by omega) (by omega)

/-- A wired dual walk confined to the interior strip is open in the original dual. -/
theorem IsBondOpenWalk.of_wired_dual_interior (m : ℕ)
    (ω : Sym2 (Site 2) → Bool) {Q : Finset (Site 2)} {a b : Q}
    (p : (rectangleGraph Q).Walk a b)
    (hp : IsBondOpenWalk (dualBondConfig (wiredArmConfig m ω)) p)
    (hs : ∀ z ∈ p.support, -(m : ℤ) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 < m) :
    IsBondOpenWalk (dualBondConfig ω) p := by
  induction p with
  | nil => trivial
  | @cons a b c hab p ih =>
    have ha := hs a (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons, true_or])
    have htail : ∀ z ∈ p.support, -(m : ℤ) ≤ (z : Site 2) 1 ∧ (z : Site 2) 1 < m :=
      fun z hz => hs z (by simp only [SimpleGraph.Walk.support_cons, List.mem_cons, hz, or_true])
    have hb := htail b p.start_mem_support
    refine ⟨?_, ih hp.2 htail⟩
    have hadj : (lattice 2).Adj (a : Site 2) (b : Site 2) := hab
    rw [← dualBondConfig_wiredArm_eq_of_adjacent_interior m ω hadj ha hb]
    exact hp.1

end Sandpile.External.RSW
