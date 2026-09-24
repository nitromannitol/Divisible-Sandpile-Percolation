/-
The parabolic lattice mesh approaches every space-time point uniformly in the
spatial point and the nonnegative horizon. The errors are bounded by the mesh
width in time and by the spatial mesh width times the square root of dimension.
-/
import Sandpile.Support.ContMeshPoint
import Mathlib

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal NNReal

theorem Sandpile.exists_parabolic_mesh_threshold (d : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ T : ℝ, 0 ≤ T →
      ∀ u : Sandpile.Continuum.Space d,
        dist (((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) / R ^ 2, Sandpile.Support.meshPoint R u) (T, u) < η := by
  let c : ℝ := max 1 (Real.sqrt d)
  refine ⟨max 1 (c / η + 1), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro R hR T hT u
  have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
  have hRp : 0 < R := lt_of_lt_of_le one_pos hR1
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hRp
  have hcR : c < R * η := by
    have hc : c / η + 1 ≤ R := (le_max_right _ _).trans hR
    have hdiv : c / η < R := by linarith
    exact (div_lt_iff₀ hη).1 hdiv
  have hi : 1 / R < η := (div_lt_iff₀ hRp).2 (by
    have hc : 1 ≤ c := le_max_left _ _
    nlinarith)
  have hs : Real.sqrt d / R < η := (div_lt_iff₀ hRp).2 (by
    have hc : Real.sqrt d ≤ c := le_max_right _ _
    nlinarith)
  rw [Prod.dist_eq, max_lt_iff]
  constructor
  · have hfl : ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) ≤ R ^ 2 * T :=
      Nat.floor_le (mul_nonneg (sq_nonneg R) hT)
    have ht : ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) / R ^ 2 ≤ T :=
      (div_le_iff₀ hR2).2 (by nlinarith)
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht)]
    calc
      -(((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) / R ^ 2 - T) =
          (R ^ 2 * T - ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ)) / R ^ 2 := by
        field_simp
        ring
      _ < 1 / R ^ 2 := (div_lt_div_iff_of_pos_right hR2).2 (by
        have := Nat.lt_floor_add_one (R ^ 2 * T)
        linarith)
      _ ≤ 1 / R := div_le_div_of_nonneg_left zero_le_one hRp (by nlinarith)
      _ < η := hi
  · rw [dist_eq_norm]
    exact (Sandpile.Support.norm_meshPoint_sub_le hRp u).trans_lt hs
