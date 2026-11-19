import Sandpile.Continuum.Stopping

/-!
# Polynomially bounded rewards for Brownian stopping

The finite-horizon stopping theorem of Peskir and Shiryaev, *Optimal Stopping and
Free-Boundary Problems*, Chapter I, Section 2, uses an integrable reward envelope.
A real growth exponent can be increased to a natural exponent, suitable for moment bounds.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Snell

/-- A real polynomial-growth exponent can be replaced by a natural-number exponent. -/
theorem exists_nat_growth_bound {d : ℕ} (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (T : ℝ)
    (hg : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ p : ℕ,
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ y, ‖G t y‖ ≤ C * (1 + ‖y‖) ^ p := by
  obtain ⟨C, k, hg⟩ := hg
  obtain ⟨p, hp⟩ := exists_nat_gt k
  refine ⟨max C 0, le_max_right _ _, p, ?_⟩
  intro t ht y
  have hbase : (1 : ℝ) ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
  have hpow : (1 + ‖y‖) ^ k ≤ (1 + ‖y‖) ^ p := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hbase hp.le
  have hpnonneg : 0 ≤ (1 + ‖y‖) ^ k := Real.rpow_nonneg (by positivity) _
  calc
    ‖G t y‖ = |G t y| := Real.norm_eq_abs _
    _ ≤ C * (1 + ‖y‖) ^ k := hg t ht y
    _ ≤ max C 0 * (1 + ‖y‖) ^ k := mul_le_mul_of_nonneg_right (le_max_left _ _) hpnonneg
    _ ≤ max C 0 * (1 + ‖y‖) ^ p := mul_le_mul_of_nonneg_left hpow (le_max_right _ _)

end Sandpile.External.Snell
