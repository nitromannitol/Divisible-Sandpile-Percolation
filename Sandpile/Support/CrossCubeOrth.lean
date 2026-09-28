import Sandpile.Support.LimNoiseCoordinates
import Sandpile.Support.ContCell

/-! # Orthonormal cube indicators

The orthonormality of the white-noise coordinates of the exploration: the
indicators of the disjoint unit cubes the exploration reveals are orthonormal in
`L²`, so the coordinates are independent standard Gaussians
(`sandpile.tex:2262-2270`).
-/

open MeasureTheory ProbabilityTheory
open Sandpile.Continuum

namespace Sandpile.Support

/-- Disjoint cubes of volume one give orthonormal indicators in `L²`. -/
theorem orthonormal_cubeIndicators {d n : ℕ} (c : Fin n → Set (Space d))
    (hmeas : ∀ i, MeasurableSet (c i)) (hvol : ∀ i, volume (c i) = 1)
    (hdisj : ∀ i j, i ≠ j → Disjoint (c i) (c j)) :
    Orthonormal ℝ (fun i : Fin n =>
      (indicatorConstLp 2 (hmeas i) (by rw [hvol i]; exact ENNReal.one_ne_top) (1 : ℝ))) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [L2.inner_indicatorConstLp_indicatorConstLp (hmeas i) (hmeas j)
    (by rw [hvol i]; exact ENNReal.one_ne_top) (by rw [hvol j]; exact ENNReal.one_ne_top)]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    simp [Measure.real, hvol i]
  · rw [if_neg hij]
    simp [Measure.real, Set.disjoint_iff_inter_eq_empty.mp (hdisj i j hij)]

end Sandpile.Support
