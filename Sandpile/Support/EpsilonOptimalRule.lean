/-
ε-optimal localized stopping rules: for every starting point in the domain
and every ε > 0 there is a stopping rule bounded by the horizon whose
expected localized payoff is within ε of the localized value.  This is the
selection step for the finite-range lower bound of the dimension-four
critical-level percolation argument (`sandpile.tex:3882-3895`).
-/
import Mathlib
import Sandpile.Walk
import Sandpile.Support.Localization

open MeasureTheory
namespace Sandpile

theorem exists_epsilon_optimal_rule {d : ℕ} (hd : 1 ≤ d) (D : Set (Site d)) (ζ : Site d → ℝ)
    (t : ℕ) (y : Site d) (hy : y ∈ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : (ℕ → Site d) → ℕ, IsWalkStopping ρ ∧ (∀ X, ρ X ≤ t) ∧
      localizedOdometer D ζ t y - ε ≤
        ∫ X, (∑ j ∈ Finset.range (ρ X),
          Set.indicator {j : ℕ | ∀ i ≤ j, X i ∈ D} (fun j => ζ (X j)) j)
          ∂(walkLaw d y) := by
  unfold localizedOdometer
  rw [Set.indicator_of_mem hy]
  unfold stoppingSup
  set S : Set ℝ := {a | ∃ ρ : (ℕ → Site d) → ℕ, IsWalkStopping ρ ∧ (∀ X, ρ X ≤ t) ∧
    a = ∫ X, (∑ j ∈ Finset.range (ρ X),
      Set.indicator {j : ℕ | ∀ i ≤ j, X i ∈ D} (fun j => ζ (X j)) j) ∂(walkLaw d y)} with hS
  have hne : S.Nonempty := by
    refine ⟨(0:ℝ), fun _ => 0, isWalkStopping_zero, fun _ => Nat.zero_le t, ?_⟩
    simp [Finset.range_zero]
  have hbdd : BddAbove S := by
    refine ⟨t * sceneryBound y t ζ, fun a ha => ?_⟩
    obtain ⟨ρ, hρ, hρt, rfl⟩ := ha
    have hconv : (∫ X, (∑ j ∈ Finset.range (ρ X),
        Set.indicator {j : ℕ | ∀ i ≤ j, X i ∈ D} (fun j => ζ (X j)) j) ∂(walkLaw d y))
        = ∫ X, sceneryPartialSum ζ (stopBeforeExit D t ρ X) X ∂(walkLaw d y) :=
      integral_congr_ae (Filter.Eventually.of_forall fun X => localizedSum_eq D t ζ hρt X)
    rw [hconv]
    exact le_trans (le_abs_self _) (abs_integral_stoppedScenery_le hd y ζ t
      (isWalkStopping_stopBeforeExit hρ hρt) (stopBeforeExit_le hρt))
  obtain ⟨a, ⟨ρ, hρ, hρt, rfl⟩, hlt⟩ : ∃ a ∈ S, sSup S - ε < a := by
    by_contra hcon
    push Not at hcon
    have h1 : sSup S ≤ sSup S - ε := csSup_le hne hcon
    have h3 : sSup S - ε < sSup S := by linarith
    linarith
  exact ⟨ρ, hρ, hρt, le_of_lt hlt⟩

end Sandpile
