import Sandpile.External.Stopping.WalkInterpolatedIncrement

/-!
# Gaussian increments of the interpolated walk

The Gaussian maximal-displacement estimate transfers through grid rounding and
linear interpolation. Keeping the rate gives the quantitative input for a
finite-grid modulus-of-continuity bound.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Interpolated walk increments after a bounded stopping time satisfy a
Gaussian bound, uniformly in the starting site and the terminal time. -/
theorem exists_linearWalk_increment_gaussian (d : ℕ) (hd : 1 ≤ d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (R ε δ : ℝ), 0 < R → 4 ≤ R * ε →
        ∀ (H : ℝ≥0) (x : Site d) (τ σ : (ℕ → Site d) → ℝ≥0),
          Continuum.IsBrownianStopping (linearWalk R) τ →
          (∀ X, τ X ≤ H) →
          (∀ X, τ X ≤ σ X ∧ (σ X : ℝ) ≤ (τ X : ℝ) + δ * R ^ 2) →
          walkLaw d x {X | ε ≤ ‖linearWalk R (σ X) X - linearWalk R (τ X) X‖} ≤
            ENNReal.ofReal (C * Real.exp (-c * ((ε / 2) * R) ^ 2 /
              ((⌊δ * R ^ 2⌋₊ + 1 : ℕ) : ℝ))) := by
  obtain ⟨C, c, hC, hc, hmax⟩ := exists_stopped_maxDisplacement_bound d hd
  refine ⟨C, c, hC, hc, ?_⟩
  intro R ε δ hR hRε H x τ σ hτ hτH hτσ
  let n : ℕ := ⌊δ * R ^ 2⌋₊ + 1
  let ρ : (ℕ → Site d) → ℕ := fun X => ⌊(τ X : ℝ)⌋₊ + 1
  let κ : (ℕ → Site d) → ℕ := fun X => ⌊(σ X : ℝ)⌋₊ + 1
  have ha : 1 ≤ (ε / 2) * R := by nlinarith
  have herror : 1 / R + 1 / R ≤ ε / 2 := by
    have h : 2 / R ≤ ε / 2 := (div_le_iff₀ hR).2 (by nlinarith)
    convert h using 1; ring
  have hindex : ∀ X, ρ X ≤ κ X ∧ κ X ≤ ρ X + n := by
    intro X
    constructor
    · exact Nat.add_le_add_right (Nat.floor_mono (by exact_mod_cast (hτσ X).1)) 1
    · have ht := Nat.lt_floor_add_one (τ X : ℝ)
      have hz := Nat.lt_floor_add_one (δ * R ^ 2)
      have hs := (hτσ X).2
      have hs' : (σ X : ℝ) <
          ((⌊(τ X : ℝ)⌋₊ + (⌊δ * R ^ 2⌋₊ + 2) : ℕ) : ℝ) := by
        push_cast
        linarith
      have hf := (Nat.floor_lt (show (0 : ℝ) ≤ σ X from (σ X).property)).2 hs'
      dsimp [ρ, κ, n]
      omega
  have hbig := hmax (⌊(H : ℝ)⌋₊ + 1) n ((ε / 2) * R)
    (by dsimp [n]; omega) ha x ρ
    (isWalkStopping_floor_add_one_of_grid_causal (linearWalk R) τ hτ
      (linearWalk_grid_causal R))
    (floor_add_one_le_of_le τ H hτH)
  apply le_trans (measure_mono_ae ?_) hbig
  filter_upwards [ae_norm_linearWalk_sub_next_le hd x R hR] with X hX hlarge
  have h₁ := hX (σ X)
  have h₂ := hX (τ X)
  let a := Lclt.scaledSite R (X (κ X))
  let b := Lclt.scaledSite R (X (ρ X))
  have htri : ‖linearWalk R (σ X) X - linearWalk R (τ X) X‖ ≤
      ‖linearWalk R (σ X) X - a‖ + ‖a - b‖ +
        ‖linearWalk R (τ X) X - b‖ := by
    have hfirst := norm_sub_le_norm_sub_add_norm_sub
      (linearWalk R (σ X) X) a (linearWalk R (τ X) X)
    have hsecond := norm_sub_le_norm_sub_add_norm_sub a b (linearWalk R (τ X) X)
    rw [norm_sub_rev b (linearWalk R (τ X) X)] at hsecond
    linarith
  have hnorm := norm_scaledSite_sub_le_graphNorm R hR (X (κ X)) (X (ρ X))
  have hmiddle : ε / 2 ≤ ‖a - b‖ := by
    change ε ≤ ‖linearWalk R (σ X) X - linearWalk R (τ X) X‖ at hlarge
    change ‖linearWalk R (σ X) X - a‖ ≤ 1 / R at h₁
    change ‖linearWalk R (τ X) X - b‖ ≤ 1 / R at h₂
    linarith
  have hdispl : (ε / 2) * R ≤
      ((LatticeProb.graphNorm (X (κ X) - X (ρ X)) : ℕ) : ℝ) :=
    (le_div_iff₀ hR).mp (hmiddle.trans hnorm)
  refine ⟨κ X - ρ X, ?_, ?_⟩
  · have hi := hindex X
    omega
  · simpa only [Nat.add_sub_of_le (hindex X).1] using hdispl

end Sandpile.External.Stopping
