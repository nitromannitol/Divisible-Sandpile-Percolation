import Sandpile.Frozen.D4ExitAverageConcentration
import Sandpile.Support.Localization
import Sandpile.Support.StoppedOdometer
import Sandpile.Support.Stationary
import Sandpile.Support.ExitAverage
import Sandpile.Support.OriginKilled
import Sandpile.Support.ExitPayoffMeas
import Sandpile.Support.ExitPayoffInt

/-!
# Fubini swap for the localized exit-value expectation

The localized exit average `localizedExitAverage D N E m ζ x` is a `ζ`-average of the localized
odometer evaluated at the site where a walk from `x`, stopped on exiting `D` within `N` steps,
lands. This file swaps the order of the two integrals, the mass-configuration average over `ζ`
and the walk average over `X`, showing the `ζ`-average of the exit average equals the walk
average of the `ζ`-average of the exit payoff. The swap rests on the measurability and
integrability of the uncurried exit payoff on the product measure.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace Sandpile

variable {d : ℕ}

/-- Fubini swap, given measurability and integrability of the uncurried
payoff. -/
theorem localizedExitAverage_expectation_swap_aux (hd : 1 ≤ d) (D : Set (Site d)) (N : ℕ)
    (E : Site d → Set (Site d)) (m : ℕ) (x : Site d) (ν : Measure ℝ)
    (hprob : IsProbabilityMeasure ν) (_hpos : Integrable (fun z => max z 0) ν)
    (_hmeas : AEStronglyMeasurable (Function.uncurry
      (fun (ζ : Site d → ℝ) (X : ℕ → Site d) =>
        if X (stopBeforeExit D N (fun _ => N) X) ∈ D then 0
          else localizedOdometer (E (X (stopBeforeExit D N (fun _ => N) X))) ζ m
            (X (stopBeforeExit D N (fun _ => N) X))))
      ((LatticeProb.iidLaw d ν).prod (walkLaw d x)))
    (hint : Integrable (Function.uncurry
      (fun (ζ : Site d → ℝ) (X : ℕ → Site d) =>
        if X (stopBeforeExit D N (fun _ => N) X) ∈ D then 0
          else localizedOdometer (E (X (stopBeforeExit D N (fun _ => N) X))) ζ m
            (X (stopBeforeExit D N (fun _ => N) X))))
      ((LatticeProb.iidLaw d ν).prod (walkLaw d x))) :
    ∫ ζ, localizedExitAverage D N E m ζ x ∂(LatticeProb.iidLaw d ν) =
      ∫ X, (if X (stopBeforeExit D N (fun _ => N) X) ∈ D then 0
          else ∫ ζ, localizedOdometer (E (X (stopBeforeExit D N (fun _ => N) X))) ζ m
              (X (stopBeforeExit D N (fun _ => N) X)) ∂(LatticeProb.iidLaw d ν))
        ∂(walkLaw d x) := by
  classical
  haveI : NeZero d := ⟨by omega⟩
  haveI : IsProbabilityMeasure (walkLaw d x) := walkLaw_isProbabilityMeasure d x
  show ∫ ζ : Site d → ℝ, ∫ X : ℕ → Site d,
      (if X (stopBeforeExit D N (fun _ => N) X) ∈ D then 0
        else localizedOdometer (E (X (stopBeforeExit D N (fun _ => N) X))) ζ m
          (X (stopBeforeExit D N (fun _ => N) X))) ∂walkLaw d x
    ∂(LatticeProb.iidLaw d ν) = _
  rw [MeasureTheory.integral_integral_swap (f := fun (ζ : Site d → ℝ) (X : ℕ → Site d) =>
    if X (stopBeforeExit D N (fun _ => N) X) ∈ D then 0
      else localizedOdometer (E (X (stopBeforeExit D N (fun _ => N) X))) ζ m
        (X (stopBeforeExit D N (fun _ => N) X))) hint]
  refine integral_congr_ae (ae_of_all _ fun X => ?_)
  by_cases hmem : X (stopBeforeExit D N (fun _ => N) X) ∈ D
  · simp only [if_pos hmem, integral_zero]
  · simp only [if_neg hmem]

/-- Fubini swap for the exit-value expectation: the ζ-average of the walk
exit average equals the walk average of the ζ-average of the payoff. -/
theorem localizedExitAverage_expectation_swap (hd : 1 ≤ d) (D : Set (Site d)) (N : ℕ)
    (E : Site d → Set (Site d)) (m : ℕ) (x : Site d) (ν : Measure ℝ)
    (hprob : IsProbabilityMeasure ν) (hpos : Integrable (fun z => max z 0) ν) :
    ∫ ζ, localizedExitAverage D N E m ζ x ∂(LatticeProb.iidLaw d ν) =
      ∫ X, (if X (stopBeforeExit D N (fun _ => N) X) ∈ D then 0
          else ∫ ζ, localizedOdometer (E (X (stopBeforeExit D N (fun _ => N) X))) ζ m
              (X (stopBeforeExit D N (fun _ => N) X)) ∂(LatticeProb.iidLaw d ν))
        ∂(walkLaw d x) := by
  classical
  set τ := stopBeforeExit D N (fun _ => N) with hτdef
  have h4 : IsWalkStopping τ := isWalkStopping_stopBeforeExit (D := D)
    (isWalkStopping_const N) (fun _ => le_rfl)
  have hτN : ∀ X, τ X ≤ N := stopBeforeExit_le (fun _ : ℕ → Site d => le_refl N)
  have hτt : ∀ X, τ X ≤ N + m := fun X => (hτN X).trans (Nat.le_add_right _ _)
  -- measurability of the uncurried integrand
  have hmeas : AEStronglyMeasurable (Function.uncurry
      (fun (ζ : Site d → ℝ) (X : ℕ → Site d) =>
        if X (τ X) ∈ D then 0
          else localizedOdometer (E (X (τ X))) ζ m (X (τ X))))
      ((LatticeProb.iidLaw d ν).prod (walkLaw d x)) :=
    (measurable_uncurry_exit_payoff hd D N E m).aestronglyMeasurable
  -- integrability
  have hint : Integrable (Function.uncurry
      (fun (ζ : Site d → ℝ) (X : ℕ → Site d) =>
        if X (τ X) ∈ D then 0
          else localizedOdometer (E (X (τ X))) ζ m (X (τ X))))
      ((LatticeProb.iidLaw d ν).prod (walkLaw d x)) :=
    integrable_uncurry_exit_payoff hd D N E m x ν hprob hpos
  exact localizedExitAverage_expectation_swap_aux hd D N E m x ν hprob hpos hmeas hint

end Sandpile
