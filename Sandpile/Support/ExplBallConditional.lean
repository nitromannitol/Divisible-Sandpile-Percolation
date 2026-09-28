import Sandpile.Support.ExplBallFinal
import Sandpile.Support.ExplBallStepEnvelope
import Sandpile.Support.ExplBallGaussian
import Sandpile.Support.ExplBrownianEnvelope
import Sandpile.Support.ExplBallFarUniform
import Sandpile.Support.ExplBallBound

/-! # Ball Step Residual from Growth and the Conditional Bound

The strong Markov step of `lem:brownian-ball-localization` (`sandpile.tex:1647-1658`)
from samplewise polynomial growth of the field and the conditional bound at the
exit event of the ball.

The conditional bound is the estimate the strong Markov property at the exit time
supplies: on the event where the capped time differs from the time, the difference
of the two payoffs is at most the exit probability times the far supremum.  The
growth supplies the integrability of the two stopped rewards through the envelope
of the field, and the step follows.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum

variable {d : ℕ}

/-- The strong Markov step residual from samplewise polynomial growth and the conditional
bound at the exit event. -/
theorem ballStepResidual_of_growth_and_conditional (d : ℕ)
    (hgrowth : BallGrowthResidual d)
    (hcond : ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
      (W : (Space d → ℝ) → ΩW → ℝ), IsWhiteNoise d W PW →
      ∀ ν2 : ℝ, 0 ≤ ν2 → ∀ (Z : ℝ → Space d → ΩW → ℝ),
      (∀ (t : ℝ) (x : Space d), Z t x =ᵐ[PW] fun ω => gaussianPotential d ν2 W t x ω) →
      (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
        ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω) (Set.Icc 0 T ×ˢ Set.univ)) →
      ∀ T : ℝ, 0 < T → ∀ A : ℝ, 1 ≤ A → ∀ K : Set (Space d), IsCompact K →
      ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : Space d → ℝ≥0 → ΩB → Space d),
        (∀ y : Space d, IsBrownian d y (B y) PB) →
        (∀ (y : Space d) (ω : ΩB), Continuous fun s => B y s ω) →
        (∀ (y : Space d) (t : ℝ≥0), StronglyMeasurable (B y t)) →
      ∀ᵐ ω ∂PW, ∀ u ∈ K,
        (∀ τ : ΩB → ℝ≥0, IsBrownianStopping (B u) τ → (∀ b, (τ b : ℝ) ≤ T) →
          (∫ b in {b : ΩB | ballExitTime (B u) u A T b < τ b},
            ((fun t z => Z t z ω) (T - ((min (τ b) (ballExitTime (B u) u A T b) : ℝ≥0) : ℝ))
                (B u (min (τ b) (ballExitTime (B u) u A T b)) b) -
              (fun t z => Z t z ω) (T - (τ b : ℝ)) (B u (τ b) b)) ∂PB)
            ≤ PB.real {b : ΩB | ballExitTime (B u) u A T b < τ b} *
              sSup (farValues B PB (fun t z => Z t z ω) T A K))) :
    BallStepResidual d := by
  intro ΩW mΩW PW hPW W hW ν2 hν2 Z hmod hc T hT A hA K hK ΩB mΩB PB hPB B hBrown hcont hmeas
  filter_upwards [hgrowth ΩW PW W hW ν2 hν2 Z hmod hc T hT,
      hcond ΩW PW W hW ν2 hν2 Z hmod hc T hT A hA K hK ΩB PB B hBrown hcont hmeas,
      hc T hT] with ω hg hω hcω
  intro u hu
  obtain ⟨C, hC, p, hp⟩ := hg
  have hCu : 0 ≤ C * (1 + ‖u‖) ^ p := mul_nonneg hC (by positivity)
  have hpu : ∀ v : ℝ≥0, (v : ℝ) ≤ T → ∀ y : Space d,
      ‖Z v y ω‖ ≤ C * (1 + ‖u‖) ^ p * (1 + ‖y - u‖) ^ p := by
    intro v hv y
    refine (hp v hv y).trans ?_
    have h1 : (1 : ℝ) + ‖y‖ ≤ (1 + ‖u‖) * (1 + ‖y - u‖) := by
      have h2 : ‖y‖ ≤ ‖u‖ + ‖y - u‖ := by
        calc ‖y‖ = ‖(y - u) + u‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - u‖ + ‖u‖ := norm_add_le _ _
          _ = ‖u‖ + ‖y - u‖ := by ring
      have h5 : (0:ℝ) ≤ ‖u‖ * ‖y - u‖ := mul_nonneg (norm_nonneg u) (norm_nonneg (y - u))
      nlinarith [h2, h5]
    have h4 : (0 : ℝ) ≤ 1 + ‖y - u‖ := by positivity
    calc C * (1 + ‖y‖) ^ p ≤ C * ((1 + ‖u‖) * (1 + ‖y - u‖)) ^ p :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 p) hC
      _ = C * (1 + ‖u‖) ^ p * (1 + ‖y - u‖) ^ p := by rw [mul_pow]; ring
  have hcoe : (T.toNNReal : ℝ) = T := Real.coe_toNNReal T hT.le
  obtain ⟨D, hD, hdom⟩ :=
    Sandpile.Support.exists_brownian_envelope_of_polynomial_growth (hBrown u)
      (fun s => (hmeas u s).measurable) (hcont u) (fun t z => Z t z ω) T.toNNReal
      (C * (1 + ‖u‖) ^ p) hCu p (fun v hv y => hpu v (by
        have h : (v:ℝ) ≤ (T.toNNReal:ℝ) := by exact_mod_cast hv
        rwa [hcoe] at h) y)
  have hbddFull : BddAbove (stoppingPayoffs (B u) PB (fun t z => Z t z ω) T) :=
    bddAbove_stoppingPayoffs_of_samplewise_growth (P := PB) (B := B u) (x := u) (hBrown u)
      (fun s => (hmeas u s).measurable) (hcont u) (fun t z => Z t z ω) T hT.le hcω
      (fun _ => C * (1 + ‖u‖) ^ p) (C * (1 + ‖u‖) ^ p)
      (Filter.Eventually.of_forall fun _ => le_rfl) p
      (Filter.Eventually.of_forall fun ω' v hv y => hpu v hv y)
  exact ballExcessStep_of_conditional_of_envelope (B u) PB (fun t z => Z t z ω) T A u
    (sSup (farValues B PB (fun t z => Z t z ω) T A K)) hT
    (le_trans (brownianValue_nonneg_ae (B u) PB (fun t z => Z t z ω) T hT.le u
        (hBrown u).start hbddFull)
      (le_csSup (bddAbove_farValues_of_growth_pointwise (PW := PW) (PB := PB) hBrown hcont
          (fun y t => (hmeas y t).measurable) Z T A hT.le K hK p C hC ω hp hcω)
        ⟨u, ⟨⟨u, hu, by rw [sub_self, norm_zero]; linarith [hA]⟩, rfl⟩⟩))
    (hcont u) (fun t => (hmeas u t).aemeasurable) (Filter.Eventually.of_forall (hcont u)) hcω
    D hD (Filter.Eventually.of_forall (fun b r hr => by
      have h1 : ((T - (r:ℝ)).toNNReal : ℝ) = T - r := Real.coe_toNNReal _ (by linarith)
      have h2 : (T - (r:ℝ)).toNNReal ≤ T.toNNReal := by
        rw [← NNReal.coe_le_coe, h1, hcoe]; linarith
      have h3 := hdom b (T - (r:ℝ)).toNNReal h2 r (by rw [← NNReal.coe_le_coe, hcoe]; exact hr)
      rwa [h1] at h3))
    (hω u hu)

end Sandpile.Continuum
