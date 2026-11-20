import Sandpile.External.RSW.WiredKSTClipped
import Sandpile.External.RSW.BaseScaleArithmetic

/-!
# Scale inclusion for wired duality

A smaller scale and its wired boundary fit in the ambient corridor rectangle.
-/

namespace Sandpile.External.RSW

/-- A strictly smaller scale and its wired boundary fit in the corridor. -/
theorem wiredKST_rectangle_subset_corridor {m k : ℕ} (hkm : k < m) :
    centeredPlaneRectangle (k + k / 12) (k + 1) ⊆
      centeredPlaneRectangle (m + 3 * (m / 12)) m := by
  intro z hz
  have hz' := (mem_centeredPlaneRectangle _ _ z).mp hz
  have hdiv : k / 12 ≤ m / 12 := Nat.div_le_div_right (Nat.le_of_lt hkm)
  apply (mem_centeredPlaneRectangle _ _ z).mpr
  push_cast at *
  omega

/-- A base scale is strictly increasing with its index. -/
theorem kstBaseScale_lt {i j : ℕ} (hij : j < i) : kstBaseScale j < kstBaseScale i := by
  unfold kstBaseScale
  exact Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by decide) hij) (by decide)

/-- A wired base-scale rectangle fits in every larger base-scale corridor. -/
theorem wiredKST_base_rectangle_subset_corridor {i j : ℕ} (hij : j < i) :
    centeredPlaneRectangle (kstBaseScale j + kstBaseScale j / 12) (kstBaseScale j + 1) ⊆
      centeredPlaneRectangle (kstBaseScale i + 3 * (kstBaseScale i / 12)) (kstBaseScale i) :=
  wiredKST_rectangle_subset_corridor (kstBaseScale_lt hij)

end Sandpile.External.RSW
