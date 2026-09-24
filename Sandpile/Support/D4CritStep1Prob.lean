/-
Step 1 of the dimension-four percolation proof in probability
(`sandpile.tex:4001-4026`): once the mean of the localized exit value is at
least `2 b₀ log r`, the concentration of `lem:d4-exit-average-concentration`
makes the event that `Y_r(z)` falls below `b₀ log r` exponentially unlikely,
uniformly in the site.
-/
import Sandpile.Frozen.D4ExitAverageConcentration
import Sandpile.Frozen.D4FiniteRangeLowerBound
import Sandpile.Support.D4CritCube

open MeasureTheory

noncomputable section
namespace Sandpile

/-- The exit value of `lem:d4-exit-average-concentration` and the exit value of
`lem:d4-finite-range-lower-bound` are the same function. -/
theorem eaExitValue_eq_frExitValue (Aex : ℕ) (Aloc : ℝ) (r : ℕ) (ζ : Site 4 → ℝ)
    (z : Site 4) : eaExitValue Aex Aloc r ζ z = frExitValue Aex Aloc r ζ z := rfl

/-- Step 1: a mean at least `2b` makes the event `Y_r(z) < b` exponentially
unlikely, uniformly in the site. -/
theorem measure_exit_value_low_le (hBallGreen : Sandpile.External.BallGreenBounds)
    (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ Aloc : ℝ, 1 ≤ Aloc → ∀ Aex : ℕ, 1 ≤ Aex →
      ∀ ν : Measure ℝ, IsProbabilityMeasure ν → ∫ z, z ∂ν = 0 →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ r : ℕ, 2 ≤ r → ∀ b : ℝ, 0 ≤ b →
        (∀ x : Site 4, 2 * b ≤ ∫ ζ, eaExitValue Aex Aloc r ζ x ∂(LatticeProb.iidLaw 4 ν)) →
        ∀ x : Site 4,
          LatticeProb.iidLaw 4 ν {ζ : Site 4 → ℝ | frExitValue Aex Aloc r ζ x < b}
            ≤ ENNReal.ofReal (C * Real.exp (-(c * min (b ^ 2) (b * (r : ℝ) ^ 2)))) := by
  obtain ⟨c, C, hc, hC, hconc⟩ :=
    Sandpile.Frozen.d4_exit_average_concentration hBallGreen θ₀ K₀ hθ₀
  refine ⟨c, C, hc, hC, ?_⟩
  intro Aloc hAloc Aex hAex ν hν hmean hint hK r hr b hb hEY x
  have hsub : {ζ : Site 4 → ℝ | frExitValue Aex Aloc r ζ x < b} ⊆
      {ζ : Site 4 → ℝ | b < |Sandpile.eaExitValue Aex Aloc r ζ x -
        ∫ η, Sandpile.eaExitValue Aex Aloc r η x ∂(LatticeProb.iidLaw 4 ν)|} := by
    intro ζ hζ
    have h1 : eaExitValue Aex Aloc r ζ x < b := hζ
    have h2 := hEY x
    have h3 : b < (∫ η, Sandpile.eaExitValue Aex Aloc r η x ∂(LatticeProb.iidLaw 4 ν))
        - eaExitValue Aex Aloc r ζ x := by linarith
    show b < |_|
    rw [abs_sub_comm]
    exact lt_of_lt_of_le h3 (le_abs_self _)
  refine (measure_mono hsub).trans ?_
  exact hconc Aloc hAloc Aex hAex ν hν hmean hint hK r hr b hb x

end Sandpile
