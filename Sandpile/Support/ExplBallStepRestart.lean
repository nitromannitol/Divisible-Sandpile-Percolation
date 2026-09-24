/-
The strong Markov step of `lem:brownian-ball-localization` (`sandpile.tex:1647-1658`)
from samplewise polynomial growth of the field and the pointwise restart bound at
the exit event of the ball.

The restart bound is the estimate the strong Markov property at the exit time
supplies: on the event where the capped time differs from the time, the difference
of the two payoffs is at most the far supremum.  The growth supplies the
integrability of the two stopped rewards through the envelope of the field, and
the step follows.
-/
import Sandpile.Support.ExplBallRestartStep
import Sandpile.Support.ExplBallConditional
import Sandpile.Support.ExplBallFinal
import Sandpile.Support.ExplBallStepEnvelope
import Sandpile.Support.ExplBallGaussian
import Sandpile.Support.ExplBrownianEnvelope
import Sandpile.Support.ExplBallFarUniform
import Sandpile.Support.ExplBallBound

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum

variable {d : ℕ}

/-- The strong Markov restart bound at the exit time of the ball, for the actual continuous
Gaussian heat potential, in the form the strong Markov property supplies it: the increment of
the two payoffs, integrated over the event where the capped time differs from the time, is at
most the probability of that event times the far supremum.  The increment itself is not
bounded pointwise; only its conditional expectation given the exit time is. -/
def BallRestartResidual (d : ℕ) : Prop :=
  ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
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
            sSup (farValues B PB (fun t z => Z t z ω) T A K))

/-- The strong Markov property at the exit time of the ball, in the form it is actually
supplied: the conditional expectation of the increment of the two payoffs, given the past at
the exit time, is at most the far supremum on the event where the capped time differs from the
time.  The increment itself is not bounded pointwise; only its conditional expectation is. -/
def BallCondExpResidual (d : ℕ) : Prop :=
  ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (W : (Space d → ℝ) → ΩW → ℝ), IsWhiteNoise d W PW →
  ∀ ν2 : ℝ, 0 ≤ ν2 → ∀ (Z : ℝ → Space d → ΩW → ℝ),
    (∀ (t : ℝ) (x : Space d), Z t x =ᵐ[PW] fun ω => gaussianPotential d ν2 W t x ω) →
    (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω) (Set.Icc 0 T ×ˢ Set.univ)) →
    ∀ T : ℝ, 0 < T → ∀ A : ℝ, 1 ≤ A → ∀ K : Set (Space d), IsCompact K →
    ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
      (B : Space d → ℝ≥0 → ΩB → Space d),
      (∀ y : Space d, IsBrownian d y (B y) PB) →
      (hcont : ∀ (y : Space d) (ω : ΩB), Continuous fun s => B y s ω) →
      (∀ (y : Space d) (t : ℝ≥0), StronglyMeasurable (B y t)) →
    ∀ᵐ ω ∂PW, ∀ u ∈ K,
      ∀ (τ : ΩB → ℝ≥0) (hτ : IsBrownianStopping (B u) τ), (∀ b, (τ b : ℝ) ≤ T) →
        Integrable (fun b' => (fun t z => Z t z ω)
              (T - ((min (τ b') (ballExitTime (B u) u A T b') : ℝ≥0) : ℝ))
              (B u (min (τ b') (ballExitTime (B u) u A T b')) b') -
            (fun t z => Z t z ω) (T - (τ b' : ℝ)) (B u (τ b') b')) PB ∧
        ∀ᵐ b ∂PB, ballExitTime (B u) u A T b < τ b →
          PB[fun b' => (fun t z => Z t z ω)
                (T - ((min (τ b') (ballExitTime (B u) u A T b') : ℝ≥0) : ℝ))
                (B u (min (τ b') (ballExitTime (B u) u A T b')) b') -
              (fun t z => Z t z ω) (T - (τ b' : ℝ)) (B u (τ b') b') |
              hτ.measurableSpace] b
            ≤ sSup (farValues B PB (fun t z => Z t z ω) T A K)

/-- The set-integral restart bound from the conditional-expectation form of the strong Markov
property at the exit time. -/
theorem ballRestartResidual_of_condExp (d : ℕ) (h : BallCondExpResidual d) :
    BallRestartResidual d := by
  intro ΩW mΩW PW hPW W hW ν2 hν2 Z hmod hc T hT A hA K hK ΩB mΩB PB hPB B hBrown hcont hmeas
  filter_upwards [h ΩW PW W hW ν2 hν2 Z hmod hc T hT A hA K hK ΩB PB B hBrown hcont hmeas,
    hc T hT] with ω hω hcω
  intro u hu τ hτ hbound
  have hle_m : hτ.measurableSpace ≤ (inferInstance : MeasurableSpace ΩB) :=
    hτ.measurableSpace_le.trans
      (measurable_iff_comap_le.mp (measurable_pi_iff.mpr fun t => (hmeas u t).measurable))
  have hE : MeasurableSet {b : ΩB | ballExitTime (B u) u A T b < τ b} :=
    measurableSet_ballExitTime_lt (B u) u A T (fun t => hmeas u t) (hcont u) τ hτ
  have hEτ : MeasurableSet[hτ.measurableSpace] {b : ΩB | ballExitTime (B u) u A T b < τ b} := by
    have hτA : IsBrownianStopping (B u) (ballExitTime (B u) u A T) :=
      isBrownianStopping_exitTimeTrunc (hcont u) u A T.toNNReal
    have h1 : MeasurableSet[hτ.measurableSpace]
        {b : ΩB | (ballExitTime (B u) u A T b : WithTop ℝ≥0) ≤ (τ b : WithTop ℝ≥0)} :=
      IsStoppingTime.measurableSet_stopping_time_le hτA hτ
    have h2 : MeasurableSet[hτ.measurableSpace]
        {b : ΩB | (τ b : WithTop ℝ≥0) = (ballExitTime (B u) u A T b : WithTop ℝ≥0)} :=
      IsStoppingTime.measurableSet_eq_stopping_time hτ hτA
    have h2' : MeasurableSet[hτ.measurableSpace]
        {b : ΩB | (ballExitTime (B u) u A T b : WithTop ℝ≥0) = (τ b : WithTop ℝ≥0)} := by
      convert h2 using 2
      ext b; exact eq_comm
    have he : {b : ΩB | ballExitTime (B u) u A T b < τ b} =
        {b : ΩB | (ballExitTime (B u) u A T b : WithTop ℝ≥0) ≤ (τ b : WithTop ℝ≥0)} \
          {b : ΩB | (ballExitTime (B u) u A T b : WithTop ℝ≥0) = (τ b : WithTop ℝ≥0)} := by
      ext b
      simp only [Set.mem_setOf_eq, Set.mem_sdiff, WithTop.coe_le_coe, WithTop.coe_eq_coe]
      exact lt_iff_le_and_ne
    rw [he]; exact h1.diff h2'
  obtain ⟨hg, hle⟩ := hω u hu τ hτ hbound
  calc ∫ b in {b : ΩB | ballExitTime (B u) u A T b < τ b},
        ((fun t z => Z t z ω) (T - ((min (τ b) (ballExitTime (B u) u A T b) : ℝ≥0) : ℝ))
            (B u (min (τ b) (ballExitTime (B u) u A T b)) b) -
          (fun t z => Z t z ω) (T - (τ b : ℝ)) (B u (τ b) b)) ∂PB
      = ∫ b in {b : ΩB | ballExitTime (B u) u A T b < τ b},
          PB[fun b' => (fun t z => Z t z ω)
                (T - ((min (τ b') (ballExitTime (B u) u A T b') : ℝ≥0) : ℝ))
                (B u (min (τ b') (ballExitTime (B u) u A T b')) b') -
              (fun t z => Z t z ω) (T - (τ b' : ℝ)) (B u (τ b') b') | hτ.measurableSpace] b ∂PB := by
        rw [MeasureTheory.setIntegral_condExp hle_m hg hEτ]
    _ ≤ ∫ _b in {b : ΩB | ballExitTime (B u) u A T b < τ b},
          sSup (farValues B PB (fun t z => Z t z ω) T A K) ∂PB := by
        refine MeasureTheory.setIntegral_mono_on_ae
          ((MeasureTheory.integrable_condExp (μ := PB) (m := hτ.measurableSpace) (f := fun b' => (fun t z => Z t z ω)
                (T - ((min (τ b') (ballExitTime (B u) u A T b') : ℝ≥0) : ℝ))
                (B u (min (τ b') (ballExitTime (B u) u A T b')) b') -
              (fun t z => Z t z ω) (T - (τ b' : ℝ)) (B u (τ b') b'))).integrableOn)
          integrableOn_const hE ?_
        filter_upwards [hle] with b hb
        exact hb
    _ = PB.real {b : ΩB | ballExitTime (B u) u A T b < τ b} *
          sSup (farValues B PB (fun t z => Z t z ω) T A K) := by
        rw [MeasureTheory.setIntegral_const]; ring

/-- The strong Markov step residual from samplewise polynomial growth and the pointwise
restart bound at the exit event. -/
theorem ballStepResidual_of_growth_and_restart (d : ℕ)
    (hgrowth : BallGrowthResidual d)
    (hrestart : ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
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
          ∀ᵐ b ∂PB, ballExitTime (B u) u A T b < τ b →
            (fun t z => Z t z ω) (T - ((min (τ b) (ballExitTime (B u) u A T b) : ℝ≥0) : ℝ))
                (B u (min (τ b) (ballExitTime (B u) u A T b)) b) -
              (fun t z => Z t z ω) (T - (τ b : ℝ)) (B u (τ b) b)
              ≤ sSup (farValues B PB (fun t z => Z t z ω) T A K))) :
    BallStepResidual d := by
  intro ΩW mΩW PW hPW W hW ν2 hν2 Z hmod hc T hT A hA K hK ΩB mΩB PB hPB B hBrown hcont hmeas
  filter_upwards [hgrowth ΩW PW W hW ν2 hν2 Z hmod hc T hT, hrestart ΩW PW W hW ν2 hν2 Z hmod hc T hT A hA K hK ΩB PB B hBrown hcont hmeas, hc T hT] with ω hg hω hcω
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
  obtain ⟨D, hD, hdom⟩ := Sandpile.Support.exists_brownian_envelope_of_polynomial_growth (hBrown u) (fun s => (hmeas u s).measurable) (hcont u) (fun t z => Z t z ω) T.toNNReal (C * (1 + ‖u‖) ^ p) hCu p (fun v hv y => hpu v (by
      have h : (v:ℝ) ≤ (T.toNNReal:ℝ) := by exact_mod_cast hv
      rwa [hcoe] at h) y)
  have hbddFull : BddAbove (stoppingPayoffs (B u) PB (fun t z => Z t z ω) T) :=
    bddAbove_stoppingPayoffs_of_samplewise_growth (P := PB) (B := B u) (x := u) (hBrown u)
      (fun s => (hmeas u s).measurable) (hcont u) (fun t z => Z t z ω) T hT.le hcω
      (fun _ => C * (1 + ‖u‖) ^ p) (C * (1 + ‖u‖) ^ p)
      (Filter.Eventually.of_forall fun _ => le_rfl) p
      (Filter.Eventually.of_forall fun ω' v hv y => hpu v hv y)
  exact ballExcessStep_of_restart_of_envelope (B u) PB (fun t z => Z t z ω) T A u
    (sSup (farValues B PB (fun t z => Z t z ω) T A K)) hT
    (le_trans (brownianValue_nonneg_ae (B u) PB (fun t z => Z t z ω) T hT.le u (hBrown u).start hbddFull)
      (le_csSup (bddAbove_farValues_of_growth_pointwise (PW := PW) (PB := PB) hBrown hcont (fun y t => (hmeas y t).measurable) Z T A hT.le K hK p C hC ω hp hcω) ⟨u, ⟨⟨u, hu, by rw [sub_self, norm_zero]; linarith [hA]⟩, rfl⟩⟩))
    (hcont u) (fun t => (hmeas u t).aemeasurable) hcω
    D hD (Filter.Eventually.of_forall (fun b r hr => by
      have h1 : ((T - (r:ℝ)).toNNReal : ℝ) = T - r := Real.coe_toNNReal _ (by linarith)
      have h2 : (T - (r:ℝ)).toNNReal ≤ T.toNNReal := by
        rw [← NNReal.coe_le_coe, h1, hcoe]; linarith
      have h3 := hdom b (T - (r:ℝ)).toNNReal h2 r (by rw [← NNReal.coe_le_coe, hcoe]; exact hr)
      rwa [h1] at h3))
    (hω u hu)
    (fun τ hτ => measurableSet_ballExitTime_lt (B u) u A T (fun t => hmeas u t) (hcont u) τ hτ)

/-- The strong Markov step residual from samplewise polynomial growth and the named restart
residual. -/
theorem ballStepResidual_of_growth_and_restartResidual (d : ℕ)
    (hgrowth : BallGrowthResidual d) (hrestart : BallRestartResidual d) :
    BallStepResidual d :=
  ballStepResidual_of_growth_and_conditional d hgrowth hrestart

end Sandpile.Continuum
