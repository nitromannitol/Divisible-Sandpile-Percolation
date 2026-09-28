import Sandpile.Support.ExplBallFinal
import Sandpile.Support.GrowExternalDischarge

/-!
# Samplewise polynomial growth for the ball-localization argument

This file derives the samplewise polynomial growth hypothesis that `lem:brownian-ball-localization`
(`sandpile.tex:1647-1658`) consumes, from the growth of the continuous version of the Gaussian
heat potential of `sandpile.tex:1019-1021`. The version's polynomial growth on each time strip,
`Sandpile.Support.continuousVersionGrowth`, is rewritten with a nonnegative amplitude and a
natural-number exponent, the shape the localization argument uses.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum

/-- The growth residual of the ball localization follows from the polynomial growth of the
continuous version of the Gaussian heat potential. -/
theorem ballGrowthResidual_of_external (d : ℕ) (hd : 1 ≤ d) (hd3 : d ≤ 3) :
    BallGrowthResidual d := by
  intro ΩW _ PW _ W hW ν2 hν2 Z hmod hcont T hT
  filter_upwards [Sandpile.Support.continuousVersionGrowth d hd hd3 ν2 hν2 ΩW PW W hW Z hmod
    hcont T hT] with ω hω
  obtain ⟨C, k, hCk⟩ := hω
  refine ⟨max C 0, le_max_right _ _, ⌈k⌉₊, ?_⟩
  intro v hv y
  have h1 : |Z v y ω| ≤ C * (1 + ‖y‖) ^ k := hCk (v, y) ⟨⟨NNReal.coe_nonneg v, hv⟩, trivial⟩
  rw [Real.norm_eq_abs]
  have h2 : (1 + ‖y‖) ^ k ≤ (1 + ‖y‖) ^ (⌈k⌉₊ : ℕ) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg y]) (Nat.le_ceil k)
  have ha : 0 ≤ (1 + ‖y‖) ^ k := Real.rpow_nonneg (by linarith [norm_nonneg y]) k
  have hm : 0 ≤ max C 0 := le_max_right C 0
  have h3 : C * (1 + ‖y‖) ^ k ≤ max C 0 * (1 + ‖y‖) ^ (⌈k⌉₊ : ℕ) :=
    calc C * (1 + ‖y‖) ^ k ≤ max C 0 * (1 + ‖y‖) ^ k :=
          mul_le_mul_of_nonneg_right (le_max_left C 0) ha
      _ ≤ max C 0 * (1 + ‖y‖) ^ (⌈k⌉₊ : ℕ) := mul_le_mul_of_nonneg_left h2 hm
  linarith [h1, h3]

end Sandpile.Continuum
