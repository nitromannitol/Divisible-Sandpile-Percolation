import Sandpile.Support.ExplScalingId
import Sandpile.Support.ExplHorizon
import Sandpile.Support.ExplCutoff
import Sandpile.External.LocalCLT

/-!
# The four-term error decomposition of the odometer-Brownian gap

`abs_rescaled_odometer_sub_brownianValue_le` bounds the gap between the rescaled odometer at a
lattice point and the Brownian value at the corresponding point of `ℝ^d` by the sum of four
named errors: the error of the interpolated field at the mesh point, the discrete cutoff
error, the stability gap of optimal-stopping values under uniform convergence of the cut-off
rewards, and the Brownian cutoff error. The two cutoff errors,
`abs_stoppingSup_sub_cutoffSup_le` on the walk side and
`abs_brownianDiscount_sub_cutoffDiscount_le` on the Brownian side, both reduce to a single
bound on how much the cutoff removes from the integral of the reward. `linInterp_scaledSite`
and `cutoff_linInterp_scaledSite` identify the interpolated field of the stability input with
the mesh field of the exact identity at a lattice point, where the rescaled position is
already a mesh point.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace Sandpile

variable {d : ℕ}

/-- At a lattice site the rescaled position is a mesh point of `R^{-1}ℤ^d`, and an elapsed
time of a whole number of steps is a mesh time, so the interpolated field of
`prop:dlt4-heat-potential-invariance` returns the mesh field there. -/
theorem linInterp_scaledSite (R : ℝ) (hR : R ≠ 0) (ζ : Site d → ℝ) (t k : ℕ) (hk : k ≤ t)
    (z : Site d) :
    Frozen.HeatPotentialInvariance.linInterp d R ζ (((t : ℝ) - (k : ℝ)) / R ^ 2)
        (External.Lclt.scaledSite R z)
      = Frozen.HeatPotentialInvariance.meshValue d R ζ (t - k) z := by
  refine linInterp_of_mesh R ζ _ _ (t - k) z ?_ ?_
  · rw [Nat.cast_sub hk]
    field_simp
  · intro i
    show R * ((z i : ℝ) / R) = (z i : ℝ)
    field_simp

/-- The cut-off reward of the stability input is the cutoff times the mesh reward of the
exact identity. -/
theorem cutoff_linInterp_scaledSite (R : ℝ) (hR : R ≠ 0) (ζ : Site d → ℝ) (A : ℝ)
    (t k : ℕ) (hk : k ≤ t) (z : Site d) :
    -(Continuum.cutoff A (External.Lclt.scaledSite R z) *
        Frozen.HeatPotentialInvariance.linInterp d R ζ (((t : ℝ) - (k : ℝ)) / R ^ 2)
          (External.Lclt.scaledSite R z))
      = Continuum.cutoff A (External.Lclt.scaledSite R z) *
          -Frozen.HeatPotentialInvariance.meshValue d R ζ (t - k) z := by
  rw [linInterp_scaledSite R hR ζ t k hk]
  ring

/-- **The four-term bound of the proof of Theorem 1.3(i)(b)**: the gap between the rescaled
odometer at a lattice point and the Brownian value at a point of `ℝ^d` is at most the error
of the field at the mesh point, plus the discrete cutoff error, plus the stability gap at
the cut-off rewards, plus the Brownian cutoff error. -/
theorem abs_rescaled_odometer_sub_brownianValue_le {ΩB : Type*} [MeasurableSpace ΩB]
    (hd : 1 ≤ d) (R : ℝ) (hR : 0 < R) (ζ : Site d → ℝ) (t : ℕ) (y : Site d)
    (B : ℝ≥0 → ΩB → Sandpile.Continuum.Space d) (PB : Measure ΩB)
    (h hχ : ℝ → Sandpile.Continuum.Space d → ℝ) (T : ℝ) (x : Sandpile.Continuum.Space d)
    (Fχ : ℕ → (ℕ → Site d) → ℝ) (E₀ E₁ E₂ E₃ : ℝ)
    (hfield : |Frozen.HeatPotentialInvariance.meshValue d R ζ t y - h T x| ≤ E₀)
    (hcut : |stoppingSup t y
        (fun k X => -Frozen.HeatPotentialInvariance.meshValue d R ζ (t - k) (X k))
        - stoppingSup t y Fχ| ≤ E₁)
    (hstab : |stoppingSup t y Fχ - Sandpile.Continuum.brownianDiscount B PB hχ T| ≤ E₂)
    (hcutB : |Sandpile.Continuum.brownianDiscount B PB hχ T
        - Sandpile.Continuum.brownianDiscount B PB h T| ≤ E₃) :
    |R ^ ((d : ℝ) / 2 - 2) * odometerOf ζ t y
        - Sandpile.Continuum.brownianValue B PB h T x| ≤ E₀ + E₁ + E₂ + E₃ := by
  rw [rescaled_difference_representation hd R hR ζ t y]
  have hb : |stoppingSup t y
        (fun k X => -Frozen.HeatPotentialInvariance.meshValue d R ζ (t - k) (X k))
      - Sandpile.Continuum.brownianDiscount B PB h T| ≤ E₁ + E₂ + E₃ := by
    have h12 := abs_sub_le
      (stoppingSup t y (fun k X => -Frozen.HeatPotentialInvariance.meshValue d R ζ (t - k) (X k)))
      (stoppingSup t y Fχ) (Sandpile.Continuum.brownianDiscount B PB h T)
    have h23 := abs_sub_le (stoppingSup t y Fχ)
      (Sandpile.Continuum.brownianDiscount B PB hχ T)
      (Sandpile.Continuum.brownianDiscount B PB h T)
    linarith
  have hsplit : Frozen.HeatPotentialInvariance.meshValue d R ζ t y
        + stoppingSup t y
            (fun k X => -Frozen.HeatPotentialInvariance.meshValue d R ζ (t - k) (X k))
        - Sandpile.Continuum.brownianValue B PB h T x
      = (Frozen.HeatPotentialInvariance.meshValue d R ζ t y - h T x)
        + (stoppingSup t y
            (fun k X => -Frozen.HeatPotentialInvariance.meshValue d R ζ (t - k) (X k))
          - Sandpile.Continuum.brownianDiscount B PB h T) := by
    unfold Sandpile.Continuum.brownianValue
    ring
  rw [hsplit]
  calc |(Frozen.HeatPotentialInvariance.meshValue d R ζ t y - h T x)
        + (stoppingSup t y
            (fun k X => -Frozen.HeatPotentialInvariance.meshValue d R ζ (t - k) (X k))
          - Sandpile.Continuum.brownianDiscount B PB h T)|
      ≤ |Frozen.HeatPotentialInvariance.meshValue d R ζ t y - h T x|
        + |stoppingSup t y
            (fun k X => -Frozen.HeatPotentialInvariance.meshValue d R ζ (t - k) (X k))
          - Sandpile.Continuum.brownianDiscount B PB h T| := abs_add_le _ _
    _ ≤ E₀ + (E₁ + E₂ + E₃) := add_le_add hfield hb
    _ = E₀ + E₁ + E₂ + E₃ := by ring

/-- **The discrete cutoff error pays the gap between the value and the value of the cut-off
reward**: the bound of the display at `sandpile.tex:1908-1921`, uniform over stopping times,
bounds the gap between the two suprema. -/
theorem abs_stoppingSup_sub_cutoffSup_le (x : Site d) (n : ℕ) (R A : ℝ)
    (F : ℕ → (ℕ → Site d) → ℝ) (E : ℝ)
    (hbddF : BddAbove {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
      a = ∫ X, F (τ X) X ∂(walkLaw d x)})
    (hbddG : BddAbove {a : ℝ | ∃ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ ∧ (∀ X, τ X ≤ n) ∧
      a = ∫ X, Sandpile.Continuum.cutoff A (External.Lclt.scaledSite R (X (τ X))) * F (τ X) X
        ∂(walkLaw d x)})
    (hF : ∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ n) →
      Integrable (fun X => F (τ X) X) (walkLaw d x))
    (hχF : ∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ n) →
      Integrable (fun X => Sandpile.Continuum.cutoff A (External.Lclt.scaledSite R (X (τ X)))
        * F (τ X) X) (walkLaw d x))
    (hE : ∀ τ : (ℕ → Site d) → ℕ, IsWalkStopping τ → (∀ X, τ X ≤ n) →
      (∫ X, (1 - Sandpile.Continuum.cutoff A (External.Lclt.scaledSite R (X (τ X))))
        * |F (τ X) X| ∂(walkLaw d x)) ≤ E) :
    |stoppingSup n x F - stoppingSup n x
        (fun k X => Sandpile.Continuum.cutoff A (External.Lclt.scaledSite R (X k)) * F k X)|
      ≤ E := by
  refine abs_stoppingSup_sub_le n x F _ E hbddF hbddG ?_
  intro τ hτ hτn
  exact abs_integral_sub_cutoff_le x τ F
    (fun k X => Sandpile.Continuum.cutoff A (External.Lclt.scaledSite R (X k))) E
    (fun k X => Sandpile.Continuum.cutoff_le_one A _) (hF τ hτ hτn) (hχF τ hτ hτn) (hE τ hτ hτn)

namespace Continuum

variable {ΩB : Type*} [MeasurableSpace ΩB]

/-- **The Brownian cutoff error pays the gap between the discount and the discount of the
cut-off field**, which is the sentence "the analogous Brownian estimate holds" at
`sandpile.tex:1922`. -/
theorem abs_brownianDiscount_sub_cutoffDiscount_le (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (h : ℝ → Space d → ℝ) (T A E : ℝ) (hT : 0 ≤ T)
    (hbdd : BddAbove (stoppingPayoffs B P h T))
    (hbdd' : BddAbove (stoppingPayoffs B P (fun s y => cutoff A y * h s y) T))
    (hf : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      Integrable (fun ω => -h (T - τ ω) (B (τ ω) ω)) P)
    (hχf : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      Integrable (fun ω => -(cutoff A (B (τ ω) ω) * h (T - τ ω) (B (τ ω) ω))) P)
    (hE : ∀ τ : ΩB → ℝ≥0, IsBrownianStopping B τ → (∀ ω, (τ ω : ℝ) ≤ T) →
      (∫ ω, (1 - cutoff A (B (τ ω) ω)) * |h (T - τ ω) (B (τ ω) ω)| ∂P) ≤ E) :
    |brownianDiscount B P h T
      - brownianDiscount B P (fun s y => cutoff A y * h s y) T| ≤ E := by
  refine abs_brownianDiscount_sub_le B P h _ T E hT hbdd hbdd' ?_
  intro τ hτ hτT
  exact abs_integral_sub_cutoff_le B P h T E τ (cutoff A) (fun y => cutoff_le_one A y)
    (hf τ hτ hτT) (hχf τ hτ hτT) (hE τ hτ hτT)

end Continuum

end Sandpile
