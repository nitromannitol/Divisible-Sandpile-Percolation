import Sandpile.External.RSW.WiredArmConfiguration
import Sandpile.External.RSW.DualLaw

/-!
# Dual bonds of a wired arm configuration

Dual bonds crossing the interior retain their original states, and the bonds
crossing the wired target connectors are closed.
-/

open Percolation.Literature

namespace Sandpile.External.RSW

/-- The dual of a vertical primal bond has the complementary state. -/
theorem dualBondConfig_vertical (ω : Sym2 (Site 2) → Bool) (z : Site 2) :
    dualBondConfig ω s(z - Pi.single 0 1, z) =
      !(ω s(z, z + Pi.single 1 1)) := by
  rw [← dualEdge_vertical z, ← dualEdgeEquiv_apply]
  simp only [dualBondConfig, Equiv.symm_apply_apply]

/-- The dual of a horizontal primal bond has the complementary state. -/
theorem dualBondConfig_horizontal (ω : Sym2 (Site 2) → Bool) (z : Site 2) :
    dualBondConfig ω s(z - Pi.single 1 1, z) =
      !(ω s(z, z + Pi.single 0 1)) := by
  rw [← dualEdge_horizontal z, ← dualEdgeEquiv_apply]
  simp only [dualBondConfig, Equiv.symm_apply_apply]

/-- The dual of a vertical interior bond is unchanged by wiring the arm boundary. -/
theorem dualBondConfig_wiredArm_vertical_interior (m : ℕ)
    (ω : Sym2 (Site 2) → Bool) (z : Site 2)
    (hl : -(m : ℤ) ≤ z 1) (hu : z 1 + 1 ≤ m) :
    dualBondConfig (wiredArmConfig m ω) s(z - Pi.single 0 1, z) =
      dualBondConfig ω s(z - Pi.single 0 1, z) := by
  rw [dualBondConfig_vertical, dualBondConfig_vertical]
  congr 1
  apply wiredArmConfig_eq_of_interior
  intro x hx
  simp only [Sym2.mem_iff] at hx
  rcases hx with rfl | rfl
  · exact ⟨hl, by omega⟩
  · simp only [Pi.add_apply, Pi.single_eq_same]
    omega

/-- The dual of a horizontal interior bond is unchanged by wiring the arm boundary. -/
theorem dualBondConfig_wiredArm_horizontal_interior (m : ℕ)
    (ω : Sym2 (Site 2) → Bool) (z : Site 2)
    (hl : -(m : ℤ) ≤ z 1) (hu : z 1 ≤ m) :
    dualBondConfig (wiredArmConfig m ω) s(z - Pi.single 1 1, z) =
      dualBondConfig ω s(z - Pi.single 1 1, z) := by
  rw [dualBondConfig_horizontal, dualBondConfig_horizontal]
  congr 1
  apply wiredArmConfig_eq_of_interior
  intro x hx
  simp only [Sym2.mem_iff] at hx
  rcases hx with rfl | rfl
  · exact ⟨hl, hu⟩
  · simpa only [Pi.add_apply, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
      add_zero] using And.intro hl hu

/-- Every dual bond crossing the upper wired row is closed. -/
theorem dualBondConfig_wiredArm_upper_row (m : ℕ)
    (ω : Sym2 (Site 2) → Bool) (z : Site 2) (hz : z 1 = (m : ℤ) + 1) :
    dualBondConfig (wiredArmConfig m ω) s(z - Pi.single 1 1, z) = false := by
  rw [dualBondConfig_horizontal, wiredArmConfig_upper_row m ω z (z + Pi.single 0 1) hz]
  · rfl
  · simpa only [Pi.add_apply, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
      add_zero] using hz

/-- Every dual bond crossing the lower wired row is closed. -/
theorem dualBondConfig_wiredArm_lower_row (m : ℕ)
    (ω : Sym2 (Site 2) → Bool) (z : Site 2) (hz : z 1 = -((m : ℤ) + 1)) :
    dualBondConfig (wiredArmConfig m ω) s(z - Pi.single 1 1, z) = false := by
  rw [dualBondConfig_horizontal, wiredArmConfig_lower_row m ω z (z + Pi.single 0 1) hz]
  · rfl
  · simpa only [Pi.add_apply, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
      add_zero] using hz

/-- Every dual bond crossing an upper target connector is closed. -/
theorem dualBondConfig_wiredArm_upper_connector (m : ℕ)
    (ω : Sym2 (Site 2) → Bool) (z : Site 2)
    (hz : z 1 = m) (hl : -((m / 64 : ℕ) : ℤ) ≤ z 0) (hu : z 0 ≤ m / 64) :
    dualBondConfig (wiredArmConfig m ω) s(z - Pi.single 0 1, z) = false := by
  rw [dualBondConfig_vertical]
  have h := wiredArmConfig_upper_connector m ω (z + Pi.single 1 1) z
    (by simp only [Pi.add_apply, Pi.single_eq_same]; omega) hz hl hu
  rw [Sym2.eq_swap] at h
  rw [h]
  rfl

/-- Every dual bond crossing a lower target connector is closed. -/
theorem dualBondConfig_wiredArm_lower_connector (m : ℕ)
    (ω : Sym2 (Site 2) → Bool) (z : Site 2)
    (hz : z 1 = -((m : ℤ) + 1)) (hl : -((m / 64 : ℕ) : ℤ) ≤ z 0)
    (hu : z 0 ≤ m / 64) :
    dualBondConfig (wiredArmConfig m ω) s(z - Pi.single 0 1, z) = false := by
  rw [dualBondConfig_vertical]
  have h := wiredArmConfig_lower_connector m ω (z + Pi.single 1 1) z hz
    (by simp only [Pi.add_apply, Pi.single_eq_same]; omega)
    (by simpa only [Pi.add_apply, Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), add_zero] using hl)
    (by simpa only [Pi.add_apply, Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), add_zero] using hu)
  rw [Sym2.eq_swap] at h
  rw [h]
  rfl

end Sandpile.External.RSW
