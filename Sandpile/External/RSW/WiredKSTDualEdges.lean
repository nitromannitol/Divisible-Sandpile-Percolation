import Sandpile.External.RSW.WiredKSTDualCrossing

/-!
# Dual edges of a wired path configuration

An open dual edge crossing an interior bond cannot cross an edge of the
original path. Dual edges crossing the wired boundary rows and target
connectors are closed.
-/

namespace Sandpile.External.RSW

/-- An open horizontal dual edge avoids the vertical path edge it crosses. -/
theorem not_mem_path_edges_of_wired_dual_horizontal (k : ℕ)
    {Q : Finset (Site 2)} {a b : Q} (p : (rectangleGraph Q).Walk a b) (z : Site 2)
    (hl : -(k : ℤ) ≤ z 1) (hu : z 1 + 1 ≤ k)
    (he : dualBondConfig (wiredKSTConfig k (pathBondConfig p))
      s(z - Pi.single 0 1, z) = true) :
    s(z, z + Pi.single 1 1) ∉ p.edges.map (Sym2.map Subtype.val) := by
  rw [dualBondConfig_vertical, wiredKSTConfig_eq_of_interior] at he
  · classical
    have he' := Bool.eq_false_of_not_eq_true' he
    simpa only [pathBondConfig, decide_eq_false_iff_not] using he'
  · intro x hx
    simp only [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨hl, by omega⟩
    · simp only [Pi.add_apply, Pi.single_eq_same]
      omega

/-- An open vertical dual edge avoids the horizontal path edge it crosses. -/
theorem not_mem_path_edges_of_wired_dual_vertical (k : ℕ)
    {Q : Finset (Site 2)} {a b : Q} (p : (rectangleGraph Q).Walk a b) (z : Site 2)
    (hl : -(k : ℤ) ≤ z 1) (hu : z 1 ≤ k)
    (he : dualBondConfig (wiredKSTConfig k (pathBondConfig p))
      s(z - Pi.single 1 1, z) = true) :
    s(z, z + Pi.single 0 1) ∉ p.edges.map (Sym2.map Subtype.val) := by
  rw [dualBondConfig_horizontal, wiredKSTConfig_eq_of_interior] at he
  · classical
    have he' := Bool.eq_false_of_not_eq_true' he
    simpa only [pathBondConfig, decide_eq_false_iff_not] using he'
  · intro x hx
    simp only [Sym2.mem_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨hl, hu⟩
    · simpa only [Pi.add_apply, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
        add_zero] using And.intro hl hu

/-- Every dual edge crossing the upper wired row is closed. -/
theorem dualBondConfig_wiredKST_upper_row (k : ℕ)
    (ω : Sym2 (Site 2) → Bool) (z : Site 2) (hz : z 1 = (k : ℤ) + 1) :
    dualBondConfig (wiredKSTConfig k ω) s(z - Pi.single 1 1, z) = false := by
  rw [dualBondConfig_horizontal, wiredKSTConfig_upper_row k ω z (z + Pi.single 0 1) hz]
  · rfl
  · simpa only [Pi.add_apply, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
      add_zero] using hz

/-- Every dual edge crossing the lower wired row is closed. -/
theorem dualBondConfig_wiredKST_lower_row (k : ℕ)
    (ω : Sym2 (Site 2) → Bool) (z : Site 2) (hz : z 1 = -((k : ℤ) + 1)) :
    dualBondConfig (wiredKSTConfig k ω) s(z - Pi.single 1 1, z) = false := by
  rw [dualBondConfig_horizontal, wiredKSTConfig_lower_row k ω z (z + Pi.single 0 1) hz]
  · rfl
  · simpa only [Pi.add_apply, Pi.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
      add_zero] using hz

/-- Every dual edge crossing an upper target connector is closed. -/
theorem dualBondConfig_wiredKST_upper_connector (k : ℕ)
    (ω : Sym2 (Site 2) → Bool) (z : Site 2)
    (hz : z 1 = k) (hl : -((k / 12 : ℕ) : ℤ) ≤ z 0) (hu : z 0 ≤ k / 12) :
    dualBondConfig (wiredKSTConfig k ω) s(z - Pi.single 0 1, z) = false := by
  rw [dualBondConfig_vertical]
  have h := wiredKSTConfig_upper_connector k ω (z + Pi.single 1 1) z
    (by simp only [Pi.add_apply, Pi.single_eq_same]; omega) hz hl hu
  rw [Sym2.eq_swap] at h
  rw [h]
  rfl

/-- Every dual edge crossing a lower target connector is closed. -/
theorem dualBondConfig_wiredKST_lower_connector (k : ℕ)
    (ω : Sym2 (Site 2) → Bool) (z : Site 2)
    (hz : z 1 = -((k : ℤ) + 1)) (hl : -((k / 12 : ℕ) : ℤ) ≤ z 0)
    (hu : z 0 ≤ k / 12) :
    dualBondConfig (wiredKSTConfig k ω) s(z - Pi.single 0 1, z) = false := by
  rw [dualBondConfig_vertical]
  have h := wiredKSTConfig_lower_connector k ω (z + Pi.single 1 1) z hz
    (by simp only [Pi.add_apply, Pi.single_eq_same]; omega)
    (by simpa only [Pi.add_apply, Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), add_zero] using hl)
    (by simpa only [Pi.add_apply, Pi.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), add_zero] using hu)
  rw [Sym2.eq_swap] at h
  rw [h]
  rfl

end Sandpile.External.RSW
