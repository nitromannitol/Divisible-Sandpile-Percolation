import Sandpile.External.Stopping.WalkInterpolation

/-!
# Small increments of the interpolated walk

The rounded stopping-time estimate and the nearest-neighbor step bound imply a
small-increment estimate for the linearly interpolated walk. This is a step
in verifying the tightness condition used by Coquet and Toldo, *Convergence of
values in optimal stopping and convergence of optimal stopping times*, Section 2.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- The interpolated walk has small increments in probability over short
intervals following bounded stopping times. Time is measured in lattice steps. -/
theorem linearWalk_increment_small (d : ℕ) (hd : 1 ≤ d) (ε η : ℝ)
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ R₀ : ℝ, 0 < δ ∧ 0 < R₀ ∧
      ∀ (R : ℝ), R₀ ≤ R → ∀ (H : ℝ≥0) (x : Site d)
        (τ σ : (ℕ → Site d) → ℝ≥0),
        Continuum.IsBrownianStopping (linearWalk R) τ →
        (∀ X, τ X ≤ H) →
        (∀ X, τ X ≤ σ X ∧ (σ X : ℝ) ≤ (τ X : ℝ) + δ * R ^ 2) →
        walkLaw d x {X | ε ≤ ‖linearWalk R (σ X) X - linearWalk R (τ X) X‖} ≤
          ENNReal.ofReal η := by
  obtain ⟨δ, R₁, hδ, hR₁, hsmall⟩ :=
    rounded_increment_small d hd (ε / 2) η (by positivity) hη
  refine ⟨δ, max R₁ (4 / ε), hδ, lt_of_lt_of_le hR₁ (le_max_left _ _), ?_⟩
  intro R hR H x τ σ hτ hτH hτσ
  have hR₁' : R₁ ≤ R := (le_max_left _ _).trans hR
  have hRpos : 0 < R := hR₁.trans_le hR₁'
  have hRlarge : 4 / ε ≤ R := (le_max_right _ _).trans hR
  have herror : 2 / R ≤ ε / 2 := by
    have hprod : 4 ≤ R * ε := (div_le_iff₀ hε).mp hRlarge
    apply (div_le_iff₀ hRpos).2
    nlinarith
  have herror' : 1 / R + 1 / R ≤ ε / 2 := by
    convert herror using 1 <;> ring
  have hbound := hsmall R hR₁' H x (linearWalk R) τ σ hτ
    (linearWalk_grid_causal R) hτH hτσ
  apply le_trans (measure_mono_ae ?_) hbound
  filter_upwards [ae_norm_linearWalk_sub_next_le hd x R hRpos] with X hX hbig
  have h₁ := hX (σ X)
  have h₂ := hX (τ X)
  let a := Lclt.scaledSite R (X (⌊(σ X : ℝ)⌋₊ + 1))
  let b := Lclt.scaledSite R (X (⌊(τ X : ℝ)⌋₊ + 1))
  have htri : ‖linearWalk R (σ X) X - linearWalk R (τ X) X‖ ≤
      ‖linearWalk R (σ X) X - a‖ + ‖a - b‖ +
        ‖linearWalk R (τ X) X - b‖ := by
    have hfirst := norm_sub_le_norm_sub_add_norm_sub
      (linearWalk R (σ X) X) a (linearWalk R (τ X) X)
    have hsecond := norm_sub_le_norm_sub_add_norm_sub a b (linearWalk R (τ X) X)
    rw [norm_sub_rev b (linearWalk R (τ X) X)] at hsecond
    linarith
  have hnorm := norm_scaledSite_sub_le_graphNorm R hRpos
    (X (⌊(σ X : ℝ)⌋₊ + 1)) (X (⌊(τ X : ℝ)⌋₊ + 1))
  change (ε / 2) * R ≤ ((LatticeProb.graphNorm
    (X (⌊(σ X : ℝ)⌋₊ + 1) - X (⌊(τ X : ℝ)⌋₊ + 1)) : ℕ) : ℝ)
  have hmiddle : ε / 2 ≤ ‖a - b‖ := by
    change ε ≤ ‖linearWalk R (σ X) X - linearWalk R (τ X) X‖ at hbig
    change ‖linearWalk R (σ X) X - a‖ ≤ 1 / R at h₁
    change ‖linearWalk R (τ X) X - b‖ ≤ 1 / R at h₂
    linarith
  exact (le_div_iff₀ hRpos).mp (hmiddle.trans hnorm)

end Sandpile.External.Stopping
