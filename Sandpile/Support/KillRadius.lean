import Sandpile.Support.KillCutoff
import Sandpile.Support.ContLcltPoint

/-!
# Cutoff radius and side conditions for the killed problem

The radius at which the cutoff of the proof of Theorem 1.3(i)(b) is one on the whole
killed problem, and the two side conditions the killed walk value needs.

`Sandpile/Support/KillCutoff.lean` shows that a cutoff equal to one at every site a
killed walk can occupy does not change the killed value. `cutoff_one_of_killed_site`
says which radius that is: a walk killed on exiting `Q(⌊Ru⌋,R)` is within `⌊R⌋+1` of
`⌊Ru⌋` in every coordinate, so its rescaling is within `2√d` of `⌊Ru⌋/R`, which is
itself within `√d` of `u`; a radius `‖u‖+3√d` therefore covers the whole killed
problem for every scale `R ≥ 1`.

The two side conditions are measurability and integrability of the rescaled reward read
along a bounded walk stopping time. Both hold for a BOUNDED reward and for no further
reason: the reward at a stopping time bounded by `n` reads only the positions up to `n`,
so it is measurable, and a bounded measurable function on a probability space is
integrable. This is the walk half of the side conditions of
`Sandpile.killed_stability_gap_of_close`.
-/

open MeasureTheory
open scoped NNReal

namespace Sandpile

variable {d : ℕ}

/-- **The cutoff is one on the whole killed problem** at radius `‖u‖+3√d`: every site a
walk killed on exiting `Q(⌊Ru⌋,R)` can occupy rescales into the ball of that radius. -/
theorem cutoff_one_of_killed_site (hd : 1 ≤ d) {R ρ A : ℝ} (hR : 1 ≤ R)
    (u : Sandpile.Continuum.Space d) (hu : ‖u‖ ≤ ρ) (hA : ρ + 3 * Real.sqrt d ≤ A)
    (y : Site d) (hy : ∀ i, |y i - ⌊R * u i⌋| ≤ ⌊R⌋ + 1) :
    Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R y) = 1 := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  have hdpos : (0 : ℝ) < Real.sqrt d := by
    have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hd
    positivity
  have hρ : 0 ≤ ρ := le_trans (norm_nonneg u) hu
  have hApos : 0 < A := by nlinarith
  have hfl1 : (1 : ℤ) ≤ ⌊R⌋ := Int.le_floor.mpr (by exact_mod_cast hR)
  have hm : (0 : ℝ) ≤ ((⌊R⌋ : ℝ) + 1) := by
    have : (0 : ℝ) ≤ (⌊R⌋ : ℝ) := by exact_mod_cast le_trans zero_le_one hfl1
    linarith
  have hcoord : ∀ i, |((y i : ℤ) : ℝ) - (((fun i => ⌊R * u i⌋) i : ℤ) : ℝ)| ≤ (⌊R⌋ : ℝ) + 1 := by
    intro i
    have hi := hy i
    have hcast : |((y i - ⌊R * u i⌋ : ℤ) : ℝ)| ≤ ((⌊R⌋ + 1 : ℤ) : ℝ) := by exact_mod_cast hi
    push_cast at hcast ⊢
    exact hcast
  have h1 := norm_scaledSite_sub_le hR0 y (fun i => ⌊R * u i⌋) hm hcoord
  have h2 : ‖Sandpile.External.Lclt.scaledSite R (fun i => ⌊R * u i⌋)‖
      ≤ ρ + Real.sqrt d / R := by
    rw [Sandpile.Support.scaledSite_floor_eq_meshPoint]
    have hmp := Sandpile.Support.norm_meshPoint_sub_le hR0 u
    calc ‖Sandpile.Support.meshPoint R u‖
        ≤ ‖Sandpile.Support.meshPoint R u - u‖ + ‖u‖ := by
          simpa using norm_add_le (Sandpile.Support.meshPoint R u - u) u
      _ ≤ Real.sqrt d / R + ρ := by linarith
      _ = ρ + Real.sqrt d / R := by ring
  refine Sandpile.Continuum.cutoff_eq_one_of_norm_le A hApos _ ?_
  have h3 : ‖Sandpile.External.Lclt.scaledSite R y‖
      ≤ ‖Sandpile.External.Lclt.scaledSite R y
          - Sandpile.External.Lclt.scaledSite R (fun i => ⌊R * u i⌋)‖
        + ‖Sandpile.External.Lclt.scaledSite R (fun i => ⌊R * u i⌋)‖ := by
    simpa using norm_add_le (Sandpile.External.Lclt.scaledSite R y
      - Sandpile.External.Lclt.scaledSite R (fun i => ⌊R * u i⌋))
      (Sandpile.External.Lclt.scaledSite R (fun i => ⌊R * u i⌋))
  have hfl : (⌊R⌋ : ℝ) ≤ R := Int.floor_le R
  have hdiv1 : Real.sqrt d / R ≤ Real.sqrt d := by
    rw [div_le_iff₀ hR0]
    nlinarith
  have hdiv2 : Real.sqrt d * ((⌊R⌋ : ℝ) + 1) / R ≤ 2 * Real.sqrt d := by
    rw [div_le_iff₀ hR0]
    nlinarith
  linarith

/-- The rescaled reward read along a bounded walk stopping time is measurable: it depends
only on the positions up to the bound. -/
theorem measurable_stopped_scaledReward (n : ℕ) (R : ℝ)
    (F : ℝ → Sandpile.Continuum.Space d → ℝ)
    {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) (hτn : ∀ X, τ X ≤ n) :
    Measurable fun X : ℕ → Site d =>
      F (((n : ℕ) - ((τ X : ℕ) : ℝ)) / R ^ 2)
        (Sandpile.External.Lclt.scaledSite R (X (τ X))) := by
  refine measurable_of_dependsOn n _ fun X Y h => ?_
  have hxy : τ X = τ Y := isWalkStopping_dependsOn hτ hτn X Y h
  rw [hxy, h (τ Y) (hτn Y)]

/-- A bounded rescaled reward read along a bounded walk stopping time is integrable. -/
theorem integrable_stopped_scaledReward (hd : 1 ≤ d) (x : Site d) (n : ℕ) (R : ℝ)
    (F : ℝ → Sandpile.Continuum.Space d → ℝ) (M : ℝ)
    (hM : ∀ (s : ℝ) (y : Sandpile.Continuum.Space d), |F s y| ≤ M)
    {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) (hτn : ∀ X, τ X ≤ n) :
    Integrable (fun X : ℕ → Site d =>
      F (((n : ℕ) - ((τ X : ℕ) : ℝ)) / R ^ 2)
        (Sandpile.External.Lclt.scaledSite R (X (τ X)))) (walkLaw d x) := by
  haveI : NeZero d := ⟨by omega⟩
  haveI : IsProbabilityMeasure (walkLaw d x) := walkLaw_isProbabilityMeasure d x
  refine (integrable_const M).mono'
    (measurable_stopped_scaledReward n R F hτ hτn).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun X => ?_
  simpa [Real.norm_eq_abs] using hM _ _

/-- A bounded rescaled reward has a bounded set of attainable killed payoffs. -/
theorem bddAbove_killedSet_of_bound (hd : 1 ≤ d) (D : Set (Site d)) (x : Site d) (n : ℕ)
    (R : ℝ) (F : ℝ → Sandpile.Continuum.Space d → ℝ) (M : ℝ)
    (hM : ∀ (s : ℝ) (y : Sandpile.Continuum.Space d), |F s y| ≤ M) :
    BddAbove (killedSet D n x (fun (k : ℕ) (X : ℕ → Site d) =>
      F (((n : ℕ) - (k : ℝ)) / R ^ 2)
        (Sandpile.External.Lclt.scaledSite R (X k)))) := by
  refine bddAbove_killedSet D n x _ (bddAbove_walkPayoffs_of_bound hd x n
    (fun (k : ℕ) (X : ℕ → Site d) => F (((n : ℕ) - (k : ℝ)) / R ^ 2)
      (Sandpile.External.Lclt.scaledSite R (X k))) M ?_ ?_)
  · intro k X
    exact le_trans (le_abs_self _) (hM _ _)
  · intro τ hτ hτn
    exact integrable_stopped_scaledReward hd x n R F M hM hτ hτn

end Sandpile
