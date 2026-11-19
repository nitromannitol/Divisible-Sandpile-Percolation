import Sandpile.External.Stopping.TimeChange
import Sandpile.External.Stopping.WalkGaussianIncrement

/-!
# Gaussian interval bounds in diffusive time

The stopped interpolated walk has a Gaussian maximal-displacement bound over a
short interval in diffusive time. This quantitative estimate is used to control
continuous-path moduli on bounded time windows.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- The Gaussian increment bound after a bounded stopping time, in diffusive
time and with an arbitrary path-dependent terminal time. -/
theorem exists_diffusiveWalk_increment_gaussian (d : ℕ) (hd : 1 ≤ d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (R ε δ : ℝ), 0 < R → 4 ≤ R * ε →
        ∀ (H : ℝ≥0) (x : Site d) (τ σ : (ℕ → Site d) → ℝ≥0),
          Continuum.IsBrownianStopping (diffusiveWalk R) τ →
          (∀ X, τ X ≤ H) →
          (∀ X, τ X ≤ σ X ∧ (σ X : ℝ) ≤ (τ X : ℝ) + δ) →
          walkLaw d x {X | ε ≤ ‖diffusiveWalk R (σ X) X - diffusiveWalk R (τ X) X‖} ≤
            ENNReal.ofReal (C * Real.exp (-c * ((ε / 2) * R) ^ 2 /
              ((⌊δ * R ^ 2⌋₊ + 1 : ℕ) : ℝ))) := by
  obtain ⟨C, c, hC, hc, hgauss⟩ := exists_linearWalk_increment_gaussian d hd
  refine ⟨C, c, hC, hc, ?_⟩
  intro R ε δ hR hRε H x τ σ hτ hτH hτσ
  let q : ℝ≥0 := ⟨R ^ 2, sq_nonneg R⟩
  have hq : 0 < q := by
    change (0 : ℝ) < R ^ 2
    positivity
  have hstop : Continuum.IsBrownianStopping (linearWalk R) (fun X => q * τ X) :=
    isBrownianStopping_mul_timeChange (linearWalk R) q hq τ hτ
  have hbound : ∀ X, q * τ X ≤ q * H := fun X => mul_le_mul_of_nonneg_left (hτH X) hq.le
  have hshort : ∀ X, q * τ X ≤ q * σ X ∧
      ((q * σ X : ℝ≥0) : ℝ) ≤ ((q * τ X : ℝ≥0) : ℝ) + δ * R ^ 2 := by
    intro X
    refine ⟨mul_le_mul_of_nonneg_left (hτσ X).1 hq.le, ?_⟩
    have hm := mul_le_mul_of_nonneg_left (hτσ X).2 (sq_nonneg R)
    change R ^ 2 * (σ X : ℝ) ≤ R ^ 2 * (τ X : ℝ) + δ * R ^ 2
    nlinarith
  simpa [diffusiveWalk, q] using hgauss R ε δ hR hRε (q * H) x
    (fun X => q * τ X) (fun X => q * σ X) hstop hbound hshort

/-- The same Gaussian bound holds for the maximal displacement over the entire
short interval following a bounded stopping time. -/
theorem exists_diffusiveWalk_interval_gaussian (d : ℕ) (hd : 1 ≤ d) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (R ε δ : ℝ), 0 < R → 0 ≤ δ → 4 ≤ R * ε →
        ∀ (H : ℝ≥0) (x : Site d) (τ : (ℕ → Site d) → ℝ≥0),
          Continuum.IsBrownianStopping (diffusiveWalk R) τ →
          (∀ X, τ X ≤ H) →
          walkLaw d x {X | ∃ t : ℝ≥0, τ X ≤ t ∧ (t : ℝ) ≤ (τ X : ℝ) + δ ∧
            ε ≤ ‖diffusiveWalk R t X - diffusiveWalk R (τ X) X‖} ≤
            ENNReal.ofReal (C * Real.exp (-c * ((ε / 2) * R) ^ 2 /
              ((⌊δ * R ^ 2⌋₊ + 1 : ℕ) : ℝ))) := by
  classical
  obtain ⟨C, c, hC, hc, hgauss⟩ := exists_diffusiveWalk_increment_gaussian d hd
  refine ⟨C, c, hC, hc, ?_⟩
  intro R ε δ hR hδ hRε H x τ hτ hτH
  let P : (ℕ → Site d) → ℝ≥0 → Prop := fun X t =>
    τ X ≤ t ∧ (t : ℝ) ≤ (τ X : ℝ) + δ ∧
      ε ≤ ‖diffusiveWalk R t X - diffusiveWalk R (τ X) X‖
  let σ : (ℕ → Site d) → ℝ≥0 := fun X =>
    if h : ∃ t, P X t then Classical.choose h else τ X
  have hσ : ∀ X, τ X ≤ σ X ∧ (σ X : ℝ) ≤ (τ X : ℝ) + δ := by
    intro X
    by_cases h : ∃ t, P X t
    · have hw := Classical.choose_spec h
      simpa only [σ, dite_eq_left h] using And.intro hw.1 hw.2.1
    · simp only [σ, dite_eq_right h, le_refl, true_and]
      linarith
  have hsub : {X | ∃ t : ℝ≥0, P X t} ⊆
      {X | ε ≤ ‖diffusiveWalk R (σ X) X - diffusiveWalk R (τ X) X‖} := by
    intro X hX
    have hX' : ∃ t, P X t := hX
    have hw := Classical.choose_spec hX'
    change ε ≤ ‖diffusiveWalk R (σ X) X - diffusiveWalk R (τ X) X‖
    simpa only [σ, dite_eq_left hX'] using hw.2.2
  exact (measure_mono hsub).trans (hgauss R ε δ hR hRε H x τ σ hτ hτH hσ)

end Sandpile.External.Stopping
