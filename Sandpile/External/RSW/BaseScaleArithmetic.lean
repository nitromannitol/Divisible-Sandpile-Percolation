import Sandpile.External.RSW.BaseScaleReduction

/-!
# Integer offsets at geometric scales

The base `1536` makes the arm and bridge offsets integral at the geometric scales and
at the two intermediate scales used in the quasi-crossing construction.
-/

namespace Sandpile.External.RSW

/-- The divisible geometric scales used for the quasi-crossing induction. -/
def kstBaseScale (j : ℕ) : ℕ := 1536 * 4 ^ j

/-- The base-scale arm and bridge offsets are exact. -/
theorem kstBaseScale_offsets (j : ℕ) :
    kstBaseScale j / 64 = 24 * 4 ^ j ∧
    kstBaseScale j / 12 = 128 * 4 ^ j := by
  dsimp only [kstBaseScale]
  omega

/-- The intermediate scales in the arm construction are integral. -/
theorem kstBaseScale_intermediate (j : ℕ) :
    5 * kstBaseScale j / 2 = 3840 * 4 ^ j ∧
    3 * kstBaseScale j / 2 = 2304 * 4 ^ j ∧
    31 * kstBaseScale j / 8 = 5952 * 4 ^ j := by
  dsimp only [kstBaseScale]
  omega

/-- The arm and bridge offsets at both intermediate scales are integral. -/
theorem kstBaseScale_intermediate_offsets (j : ℕ) :
    (5 * kstBaseScale j / 2) / 64 = 60 * 4 ^ j ∧
    (5 * kstBaseScale j / 2) / 12 = 320 * 4 ^ j ∧
    (31 * kstBaseScale j / 8) / 64 = 93 * 4 ^ j ∧
    (31 * kstBaseScale j / 8) / 12 = 496 * 4 ^ j := by
  rcases kstBaseScale_intermediate j with ⟨h₁, _, h₂⟩
  rw [h₁, h₂]
  omega

/-- Every base scale and the next base scale differ by a factor of four. -/
theorem kstBaseScale_succ (j : ℕ) : kstBaseScale (j + 1) = 4 * kstBaseScale j := by
  simp only [kstBaseScale, pow_succ]
  ring

end Sandpile.External.RSW
