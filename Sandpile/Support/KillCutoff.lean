/-
The cutoff of the proof of Theorem 1.3(i)(b) is free in the killed problem.

The proof of Theorem 1.3(i)(b) inserts a continuous cutoff `χ_A` on both sides so
that the cited stability input, which needs BOUNDED rewards, applies, and then pays
the two cutoff errors of `sandpile.tex:1908-1922`.  In the killed problem of
`rem:dlt4-killed-scaling` there is nothing to pay: the killed walk is within one
step of `Q(⌊Ru⌋,R)` when it stops and the killed motion is in the closed cube
`u+[-1,1]^d` when it stops, so as soon as `χ_A` is one on a fixed neighbourhood of
the cube both killed values are UNCHANGED by the cutoff, not merely close to the
uncut ones.  That is what this module proves: the two payoff sets are equal,
because their integrands agree almost surely.
-/
import Sandpile.Support.KillBox
import Sandpile.Support.KillLip
import Sandpile.Support.ExplCutoff

open MeasureTheory
open scoped NNReal

namespace Sandpile

variable {d : ℕ}

/-- A point whose coordinates are within `L` of those of `u` has norm at most
`‖u‖ + √d·L`. -/
theorem Continuum.norm_le_of_cube {u y : Sandpile.Continuum.Space d} {L : ℝ} (hL : 0 ≤ L)
    (h : ∀ i, |y i - u i| ≤ L) : ‖y‖ ≤ ‖u‖ + Real.sqrt d * L := by
  have hsub : ‖y - u‖ ≤ Real.sqrt d * L :=
    Continuum.norm_le_of_coord_le hL (fun i => by simpa using h i)
  calc ‖y‖ = ‖(y - u) + u‖ := by rw [sub_add_cancel]
    _ ≤ ‖y - u‖ + ‖u‖ := norm_add_le _ _
    _ ≤ Real.sqrt d * L + ‖u‖ := by linarith
    _ = ‖u‖ + Real.sqrt d * L := by ring

/-- **The cutoff does not change the killed walk value** when it is one at every site the
killed walk can occupy. -/
theorem killedSet_cutoff_eq (hd : 1 ≤ d) (R A : ℝ) (x₀ : Site d) (L : ℝ) (hL : 0 ≤ ⌊L⌋)
    (n : ℕ) (F : ℕ → (ℕ → Site d) → ℝ)
    (hone : ∀ y : Site d, (∀ i, |y i - x₀ i| ≤ ⌊L⌋ + 1) →
      Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R y) = 1) :
    killedSet (supBox x₀ L) n x₀
        (fun k X => Sandpile.Continuum.cutoff A
          (Sandpile.External.Lclt.scaledSite R (X k)) * F k X)
      = killedSet (supBox x₀ L) n x₀ F := by
  have key : ∀ (τ : (ℕ → Site d) → ℕ), (∀ X, ∀ j < τ X, X j ∈ supBox x₀ L) →
      (∫ X, Sandpile.Continuum.cutoff A
          (Sandpile.External.Lclt.scaledSite R (X (τ X))) * F (τ X) X ∂(walkLaw d x₀))
        = ∫ X, F (τ X) X ∂(walkLaw d x₀) := by
    intro τ hkill
    refine integral_congr_ae ?_
    filter_upwards [ae_walk_start x₀, ae_step_walk hd x₀] with X h0 hstep
    rw [hone _ (killed_position_box hL h0 hstep (τ X) (hkill X)), one_mul]
  ext a
  constructor
  · rintro ⟨τ, hτ, hτn, hkill, rfl⟩
    exact ⟨τ, hτ, hτn, hkill, key τ hkill⟩
  · rintro ⟨τ, hτ, hτn, hkill, rfl⟩
    exact ⟨τ, hτ, hτn, hkill, (key τ hkill).symm⟩

/-- **The cutoff does not change the killed walk value.** -/
theorem killedStoppingSup_cutoff_eq (hd : 1 ≤ d) (R A : ℝ) (x₀ : Site d) (L : ℝ)
    (hL : 0 ≤ ⌊L⌋) (n : ℕ) (F : ℕ → (ℕ → Site d) → ℝ)
    (hone : ∀ y : Site d, (∀ i, |y i - x₀ i| ≤ ⌊L⌋ + 1) →
      Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R y) = 1) :
    killedStoppingSup (supBox x₀ L) n x₀
        (fun k X => Sandpile.Continuum.cutoff A
          (Sandpile.External.Lclt.scaledSite R (X k)) * F k X)
      = killedStoppingSup (supBox x₀ L) n x₀ F := by
  unfold killedStoppingSup
  rw [killedSet_cutoff_eq hd R A x₀ L hL n F hone]

namespace Continuum

variable {ΩB : Type*} [MeasurableSpace ΩB]

/-- **The cutoff does not change the cube-killed Brownian value** when it is one on the
closed cube. -/
theorem cubeStoppingPayoffs_cutoff_eq (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T L A : ℝ) (hL : 0 ≤ L) (u : Space d)
    (hcont : ∀ᵐ ω ∂P, Continuous fun s : ℝ≥0 => B s ω) (hstart : ∀ᵐ ω ∂P, B 0 ω = u)
    (hone : ∀ y : Space d, (∀ i, |y i - u i| ≤ L) → cutoff A y = 1) :
    cubeStoppingPayoffs B P (fun s y => cutoff A y * h s y) T L u
      = cubeStoppingPayoffs B P h T L u := by
  have key : ∀ τ : ΩB → ℝ≥0, (∀ᵐ ω ∂P, ∀ s : ℝ≥0, s < τ ω → ∀ i, |B s ω i - u i| ≤ L) →
      (∫ ω, -(cutoff A (B (τ ω) ω) * h (T - τ ω) (B (τ ω) ω)) ∂P)
        = ∫ ω, -h (T - τ ω) (B (τ ω) ω) ∂P := by
    intro τ hkill
    refine integral_congr_ae ?_
    filter_upwards [ae_cube_at_stop B P u L hL hcont hstart τ hkill] with ω hω
    rw [hone _ hω, one_mul]
  ext a
  constructor
  · rintro ⟨τ, hτ, hτT, hkill, rfl⟩
    exact ⟨τ, hτ, hτT, hkill, key τ hkill⟩
  · rintro ⟨τ, hτ, hτT, hkill, rfl⟩
    exact ⟨τ, hτ, hτT, hkill, (key τ hkill).symm⟩

/-- **The cutoff does not change the cube-killed Brownian discount.** -/
theorem brownianDiscountCube_cutoff_eq (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T L A : ℝ) (hL : 0 ≤ L) (u : Space d)
    (hcont : ∀ᵐ ω ∂P, Continuous fun s : ℝ≥0 => B s ω) (hstart : ∀ᵐ ω ∂P, B 0 ω = u)
    (hone : ∀ y : Space d, (∀ i, |y i - u i| ≤ L) → cutoff A y = 1) :
    brownianDiscountCube B P (fun s y => cutoff A y * h s y) T L u
      = brownianDiscountCube B P h T L u := by
  unfold brownianDiscountCube
  rw [cubeStoppingPayoffs_cutoff_eq B P h T L A hL u hcont hstart hone]

end Continuum

end Sandpile
