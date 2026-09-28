import Sandpile.Support.KillStability
import Sandpile.Support.ExplValueGap
import Sandpile.Support.ExplCutoffError

/-!
# Assembling the killed two-term bound

The assembly of `rem:dlt4-killed-scaling`, in the shape of the four-term bound of the
proof of Theorem 1.3(i)(b) (`Sandpile.abs_rescaled_odometer_sub_brownianValue_le`) with
its two cutoff errors removed.

The proof of Theorem 1.3(i)(b) bounds the gap between the rescaled odometer and the
Brownian value by `E₀+E₁+E₂+E₃`: the error of the field at the mesh point, the discrete
cutoff error, the stability gap at the cut-off rewards, and the Brownian cutoff error.
In the killed problem `E₁` and `E₃` are ZERO, by `Sandpile/Support/KillCutoff.lean`, so
the killed bound has two terms:

  `|R^{d/2-2} u^{Q(y,L)}_t(y) - 𝒰_{h,□}(T,u)| ≤ E₀ + E₂`,

with `E₀` the error of the field at the mesh point and `E₂` the killed stability gap.
`killedStoppingSup_meshReward_eq` is what lets `E₂` be read in the vocabulary of the
cited stability input: at a lattice point the rescaled position is a mesh point, so the
interpolated field returns the mesh field there, and the cutoff is one at every site the
killed walk can occupy.
-/

open MeasureTheory
open scoped NNReal

namespace Sandpile

variable {d : ℕ}

/-- The killed payoff set depends on the reward only through its values at the times the
killed problem can stop. -/
theorem killedSet_congr (D : Set (Site d)) (n : ℕ) (x : Site d) (F G : ℕ → (ℕ → Site d) → ℝ)
    (h : ∀ k ≤ n, ∀ X : ℕ → Site d, F k X = G k X) :
    killedSet D n x F = killedSet D n x G := by
  have key : ∀ τ : (ℕ → Site d) → ℕ, (∀ X, τ X ≤ n) →
      (∫ X, F (τ X) X ∂(walkLaw d x)) = ∫ X, G (τ X) X ∂(walkLaw d x) := by
    intro τ hτn
    exact integral_congr_ae (Filter.Eventually.of_forall fun X => h (τ X) (hτn X) X)
  ext a
  constructor
  · rintro ⟨τ, hτ, hτn, hkill, rfl⟩
    exact ⟨τ, hτ, hτn, hkill, key τ hτn⟩
  · rintro ⟨τ, hτ, hτn, hkill, rfl⟩
    exact ⟨τ, hτ, hτn, hkill, (key τ hτn).symm⟩

/-- The killed value depends on the reward only through its values at the times the killed
problem can stop. -/
theorem killedStoppingSup_congr (D : Set (Site d)) (n : ℕ) (x : Site d)
    (F G : ℕ → (ℕ → Site d) → ℝ) (h : ∀ k ≤ n, ∀ X : ℕ → Site d, F k X = G k X) :
    killedStoppingSup D n x F = killedStoppingSup D n x G := by
  unfold killedStoppingSup
  rw [killedSet_congr D n x F G h]

/-- **The killed reward of the cited stability input is the mesh reward of the exact
identity.**  At a lattice point the rescaled position is a mesh point, so the interpolated
field returns the mesh field there, and the cutoff is one at every site a killed walk can
occupy, so neither the interpolation nor the cutoff changes the killed value. -/
theorem killedStoppingSup_meshReward_eq (hd : 1 ≤ d) (R : ℝ) (hR : R ≠ 0) (A : ℝ)
    (x₀ : Site d) (L : ℝ) (hL : 0 ≤ ⌊L⌋) (ζ : Site d → ℝ) (t : ℕ)
    (hone : ∀ y : Site d, (∀ i, |y i - x₀ i| ≤ ⌊L⌋ + 1) →
      Sandpile.Continuum.cutoff A (Sandpile.External.Lclt.scaledSite R y) = 1) :
    killedStoppingSup (supBox x₀ L) t x₀
        (fun k X => -(Sandpile.Continuum.cutoff A
            (Sandpile.External.Lclt.scaledSite R (X k)) *
          Frozen.HeatPotentialInvariance.linInterp d R ζ (((t : ℝ) - (k : ℝ)) / R ^ 2)
            (Sandpile.External.Lclt.scaledSite R (X k))))
      = killedStoppingSup (supBox x₀ L) t x₀
        (fun k X => -Frozen.HeatPotentialInvariance.meshValue d R ζ (t - k) (X k)) := by
  have h1 : (fun (k : ℕ) (X : ℕ → Site d) => -(Sandpile.Continuum.cutoff A
        (Sandpile.External.Lclt.scaledSite R (X k)) *
        Frozen.HeatPotentialInvariance.linInterp d R ζ (((t : ℝ) - (k : ℝ)) / R ^ 2)
          (Sandpile.External.Lclt.scaledSite R (X k))))
      = fun (k : ℕ) (X : ℕ → Site d) => Sandpile.Continuum.cutoff A
        (Sandpile.External.Lclt.scaledSite R (X k)) *
        -(Frozen.HeatPotentialInvariance.linInterp d R ζ (((t : ℝ) - (k : ℝ)) / R ^ 2)
          (Sandpile.External.Lclt.scaledSite R (X k))) := by
    funext k X
    ring
  rw [h1, killedStoppingSup_cutoff_eq hd R A x₀ L hL t _ hone]
  refine killedStoppingSup_congr _ _ _ _ _ ?_
  intro k hk X
  rw [linInterp_scaledSite R hR ζ t k hk]

/-- **The killed two-term bound**, the killed form of the four-term bound of the proof of
Theorem 1.3(i)(b) with the two cutoff errors gone: the gap between the rescaled localized
value at a lattice point and the cube-killed Brownian value at a point of `ℝ^d` is at most
the error of the field at the mesh point plus the killed stability gap. -/
theorem abs_rescaled_localizedOdometer_sub_brownianValueCube_le {ΩB : Type*}
    [MeasurableSpace ΩB] (hd : 1 ≤ d) (R : ℝ) (hR : 0 < R) (D : Set (Site d))
    (ζ : Site d → ℝ) (t : ℕ) (y : Site d) (hy : y ∈ D)
    (B : ℝ≥0 → ΩB → Sandpile.Continuum.Space d) (PB : Measure ΩB)
    (h : ℝ → Sandpile.Continuum.Space d → ℝ) (T L : ℝ)
    (u : Sandpile.Continuum.Space d) (E₀ E₂ : ℝ)
    (hfield : |Frozen.HeatPotentialInvariance.meshValue d R ζ t y - h T u| ≤ E₀)
    (hstab : |killedStoppingSup D t y
        (fun k X => -Frozen.HeatPotentialInvariance.meshValue d R ζ (t - k) (X k))
        - Sandpile.Continuum.brownianDiscountCube B PB h T L u| ≤ E₂) :
    |R ^ ((d : ℝ) / 2 - 2) * localizedOdometer D ζ t y
        - Sandpile.Continuum.brownianValueCube B PB h T L u| ≤ E₀ + E₂ := by
  rw [rescaled_killed_difference_representation hd R hR D ζ t y hy]
  have hsplit : Frozen.HeatPotentialInvariance.meshValue d R ζ t y
        + killedStoppingSup D t y
            (fun k X => -Frozen.HeatPotentialInvariance.meshValue d R ζ (t - k) (X k))
        - Sandpile.Continuum.brownianValueCube B PB h T L u
      = (Frozen.HeatPotentialInvariance.meshValue d R ζ t y - h T u)
        + (killedStoppingSup D t y
            (fun k X => -Frozen.HeatPotentialInvariance.meshValue d R ζ (t - k) (X k))
          - Sandpile.Continuum.brownianDiscountCube B PB h T L u) := by
    unfold Sandpile.Continuum.brownianValueCube
    ring
  rw [hsplit]
  exact le_trans (abs_add_le _ _) (add_le_add hfield hstab)

namespace Continuum

variable {ΩB : Type*} [MeasurableSpace ΩB]

/-- A bounded reward has a bounded set of attainable cube-killed payoffs: the cube-killed
payoffs are a subset of the unkilled ones.  This is the Brownian side condition of
`Sandpile.killed_stability_gap_of_close`. -/
theorem bddAbove_cubeStoppingPayoffs_of_bound (B : ℝ≥0 → ΩB → Sandpile.Continuum.Space d)
    (P : Measure ΩB) [IsProbabilityMeasure P] (h : ℝ → Sandpile.Continuum.Space d → ℝ)
    (T L M : ℝ) (u : Sandpile.Continuum.Space d)
    (hb : ∀ (s : ℝ) (y : Sandpile.Continuum.Space d), |h s y| ≤ M)
    (hint : ∀ τ : ΩB → ℝ≥0, Sandpile.Continuum.IsBrownianStopping B τ →
      (∀ ω, (τ ω : ℝ) ≤ T) →
      Integrable (fun ω => -h (T - τ ω) (B (τ ω) ω)) P) :
    BddAbove (Sandpile.Continuum.cubeStoppingPayoffs B P h T L u) :=
  (Sandpile.Continuum.bddAbove_stoppingPayoffs_of_bound B P h T M hb hint).mono
    (Sandpile.Continuum.cubeStoppingPayoffs_subset B P h T L u)

end Continuum

end Sandpile
