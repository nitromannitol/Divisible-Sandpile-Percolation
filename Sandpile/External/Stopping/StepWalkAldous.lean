import Sandpile.External.Stopping.StepWalkFiltration

/-!
# Small increments of the diffusive step walk

The diffusive step walk satisfies a uniform small-increment estimate after
bounded stopping times in its natural filtration. The proof compares its
increments with those of the linearly interpolated walk.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- The step walk has uniformly small increments in probability over short
intervals after bounded natural-filtration stopping times. -/
theorem diffusiveStepWalk_increment_small (d : ℕ) (hd : 1 ≤ d) (ε η : ℝ)
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ R₀ : ℝ, 0 < δ ∧ 0 < R₀ ∧
      ∀ (R : ℝ), R₀ ≤ R → ∀ (H : ℝ≥0) (x : Site d)
        (τ σ : (ℕ → Site d) → ℝ≥0),
        Continuum.IsBrownianStopping (diffusiveStepWalk R) τ →
        (∀ X, τ X ≤ H) →
        (∀ X, τ X ≤ σ X ∧ (σ X : ℝ) ≤ (τ X : ℝ) + δ) →
        walkLaw d x {X | ε ≤ ‖diffusiveStepWalk R (σ X) X - diffusiveStepWalk R (τ X) X‖} ≤
          ENNReal.ofReal η := by
  obtain ⟨δ, R₁, hδ, hR₁, hsmall⟩ :=
    diffusiveWalk_increment_small d hd (ε / 2) η (by positivity) hη
  refine ⟨δ, max R₁ (4 / ε), hδ, lt_of_lt_of_le hR₁ (le_max_left _ _), ?_⟩
  intro R hR H x τ σ hτ hτH hτσ
  have hR₁' : R₁ ≤ R := (le_max_left _ _).trans hR
  have hRpos : 0 < R := hR₁.trans_le hR₁'
  have hRlarge : 4 / ε ≤ R := (le_max_right _ _).trans hR
  have herror : 1 / R + 1 / R ≤ ε / 2 := by
    have hprod : 4 ≤ R * ε := (div_le_iff₀ hε).mp hRlarge
    have hbound : 2 / R ≤ ε / 2 := by
      apply (div_le_iff₀ hRpos).2
      nlinarith
    convert hbound using 1; ring
  have hbound := hsmall R hR₁' H x τ σ
    (isBrownianStopping_diffusiveWalk_of_stepWalk hRpos τ hτ) hτH hτσ
  apply le_trans (measure_mono_ae ?_) hbound
  filter_upwards [ae_norm_diffusiveWalk_sub_stepWalk_le hd x R hRpos] with X hX hbig
  have h₁ := hX (σ X)
  have h₂ := hX (τ X)
  have htri : ‖diffusiveStepWalk R (σ X) X - diffusiveStepWalk R (τ X) X‖ ≤
      ‖diffusiveWalk R (σ X) X - diffusiveStepWalk R (σ X) X‖ +
        ‖diffusiveWalk R (σ X) X - diffusiveWalk R (τ X) X‖ +
        ‖diffusiveWalk R (τ X) X - diffusiveStepWalk R (τ X) X‖ := by
    have ha := norm_sub_le_norm_sub_add_norm_sub
      (diffusiveStepWalk R (σ X) X) (diffusiveWalk R (σ X) X) (diffusiveStepWalk R (τ X) X)
    have hb := norm_sub_le_norm_sub_add_norm_sub
      (diffusiveWalk R (σ X) X) (diffusiveWalk R (τ X) X) (diffusiveStepWalk R (τ X) X)
    rw [norm_sub_rev (diffusiveStepWalk R (σ X) X) (diffusiveWalk R (σ X) X)] at ha
    linarith
  change ε ≤ ‖diffusiveStepWalk R (σ X) X - diffusiveStepWalk R (τ X) X‖ at hbig
  change ε / 2 ≤ ‖diffusiveWalk R (σ X) X - diffusiveWalk R (τ X) X‖
  linarith

end Sandpile.External.Stopping
