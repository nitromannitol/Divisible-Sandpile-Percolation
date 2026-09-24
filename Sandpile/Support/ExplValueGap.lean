/-
The skeleton of the proof of Theorem 1.3(i)(b) (`sandpile.tex:1874-1935`): the gap
between the rescaled odometer at a lattice point and the Brownian value at the
corresponding point of `ℝ^d`, in four named errors.

The paper's proof runs: the exact identity for `u_t - V_t` at the parabolic scale
turns the rescaled odometer into the field plus an optimal-stopping value; the
field converges (`prop:dlt4-heat-potential-invariance`); and the two
optimal-stopping values are compared by inserting the cutoff `χ_A` on both sides,
so that the standard stability of optimal-stopping values under uniform
convergence of BOUNDED rewards applies (`ext-continuum-stopping-stability`), and
the two cutoff errors are paid separately (`sandpile.tex:1908-1922`).

`abs_rescaled_odometer_sub_brownianValue_le` is exactly that: the gap is at most
`E₀ + E₁ + E₂ + E₃`, where `E₀` is the error of the field at the mesh point, `E₁`
the discrete cutoff error, `E₂` the stability gap at the cut-off rewards, and `E₃`
the Brownian cutoff error.  Nothing about the four errors is assumed here beyond
their own statements; each is supplied by a named result of the paper, and the
two cutoff errors are reduced to the paper's display by
`Sandpile.abs_stoppingSup_sub_le` with `Sandpile.abs_integral_sub_cutoff_le` and
by their Brownian counterparts in `Sandpile/Support/ExplHorizon.lean`.

`linInterp_scaledSite` and `cutoff_linInterp_scaledSite` are what let the two
vocabularies meet.  The external stability input states the discrete value with the
INTERPOLATED field `Z_R^{lin}` evaluated at the rescaled walk position, while the
exact identity produces the MESH field `Z_R` at the lattice position; at a lattice
point the rescaled position is a mesh point and the two agree, which is
`linInterp_of_mesh`.
-/
import Sandpile.Support.ExplScalingId
import Sandpile.Support.ExplHorizon
import Sandpile.Support.ExplCutoff
import Sandpile.External.LocalCLT

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
