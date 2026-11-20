import Sandpile.Continuum.Membrane
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Negative Sobolev boundedness from an energy estimate

A uniform first-moment bound for a nonnegative energy controls the probability
that a functional's negative Sobolev norm exceeds a threshold when that norm is
bounded by the square root of the energy. This is the Markov step in the
four-dimensional membrane norm estimate.
-/

open MeasureTheory
open scoped ENNReal

namespace Sandpile.Support

/-- A uniform expected energy bound gives boundedness in probability for
negative Sobolev norms controlled by the square root of that energy. -/
theorem negSobolevNorm_bounded_in_probability_of_energy
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (d : ℕ) (s : ℝ)
    (D : Set (Sandpile.Continuum.Space d))
    (F : ℝ → Ω → (Sandpile.Continuum.Space d → ℝ) → ℝ)
    (E : ℝ → Ω → ℝ≥0∞) (C : ℝ) (hC : 0 ≤ C)
    (hmeas : ∀ R, 1 ≤ R → AEMeasurable (E R) P)
    (hbound : ∀ R, 1 ≤ R → (∫⁻ ω, E R ω ∂P) ≤ ENNReal.ofReal C)
    (hcontrol : ∀ R, 1 ≤ R → ∀ ω,
      Sandpile.Continuum.negSobolevNorm d s D (F R ω) ≤ (E R ω) ^ (1 / 2 : ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ R : ℝ, 1 ≤ R →
      P {ω | M < Sandpile.Continuum.negSobolevNorm d s D (F R ω)} ≤ ENNReal.ofReal ε := by
  intro ε hε
  let b : ℝ := (C + 1) / ε
  have hb : 0 < b := by dsimp [b]; positivity
  let B : ℝ≥0∞ := ENNReal.ofReal b
  have hB0 : B ≠ 0 := (ENNReal.ofReal_pos.mpr hb).ne'
  have hBtop : B ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨B ^ (1 / 2 : ℝ), ENNReal.rpow_ne_top_of_nonneg (by norm_num) hBtop, ?_⟩
  intro R hR
  have hsubset : {ω | B ^ (1 / 2 : ℝ) < Sandpile.Continuum.negSobolevNorm d s D (F R ω)}
      ⊆ {ω | B ≤ E R ω} := by
    intro ω hω
    have hroot : B ^ (1 / 2 : ℝ) < (E R ω) ^ (1 / 2 : ℝ) :=
      lt_of_lt_of_le hω (hcontrol R hR ω)
    exact le_of_lt ((ENNReal.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) < 1 / 2)).mp hroot)
  calc
    _ ≤ P {ω | B ≤ E R ω} := measure_mono hsubset
    _ ≤ (∫⁻ ω, E R ω ∂P) / B := meas_ge_le_lintegral_div (hmeas R hR) hB0 hBtop
    _ ≤ ENNReal.ofReal C / B := by
      gcongr
      exact hbound R hR
    _ = ENNReal.ofReal (C / b) := by
      rw [show B = ENNReal.ofReal b from rfl, ENNReal.ofReal_div_of_pos hb]
    _ ≤ ENNReal.ofReal ε := by
      apply ENNReal.ofReal_le_ofReal
      rw [div_le_iff₀ hb]
      dsimp [b]
      field_simp
      nlinarith

end Sandpile.Support
