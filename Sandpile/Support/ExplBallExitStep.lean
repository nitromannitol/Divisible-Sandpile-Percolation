/-
The strong Markov step of `lem:brownian-ball-localization` (`sandpile.tex:1647-1658`)
from the strong Markov property at the exit time of the ball and the polynomial
growth of the field.

The strong Markov property at the exit time is the External
`Sandpile.External.BrownianExitStep`, version 3: it needs an integrable envelope of
the field along the motions started near `K`, and its conclusion bounds the excess
by the supremum of the value over every remaining horizon `s ∈ [0, T]`, not only
`s = T`.  The envelope is built here from the samplewise polynomial growth of the
field and the uniform moment bound of the compact-time Brownian maximum
(`exists_uniform_pathRadius_moment`), recentred at each starting point exactly as
the growth is recentred at `u` elsewhere in this development; the bound on its
integral does not depend on the starting point because the growth amplitude is
bounded on the compact `A`-neighbourhood of `K`.  Passing from the supremum over
every remaining horizon to the supremum at `T` alone uses the monotonicity of the
Brownian value of the Gaussian heat potential in the horizon,
`Sandpile.Frozen.brownian_value_mono_horizon`, the one dependency of this file that
is still a registered `sorry`.  That dependency is isolated to the thin wrapper
`ballStepResidual_of_exitStep`: the bulk of the argument,
`ballStepResidual_of_exitStep_of_mono`, takes the monotonicity fact as an explicit
hypothesis and is sorry-free.
-/
import Sandpile.Support.ExplBallConditional
import Sandpile.Support.ExplBallFarUniform
import Sandpile.Support.ExplBrownianEnvelope
import Sandpile.Support.ExplBallMoment
import Sandpile.External.BrownianExitStep
import Sandpile.Frozen.BrownianValueMonotone

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.Continuum
open Sandpile.Support

/-- The integrable envelope `Sandpile.External.BrownianExitStep` needs for a field with
samplewise polynomial growth: an integrable `D` for every motion started within `A` of `K`,
with a bound on `∫ D` that does not depend on the starting point.  Built from the growth bound
recentred at the starting point and the moment bound of `exists_uniform_pathRadius_moment`,
which is uniform in the starting point; the amplitude `(1 + ‖z‖) ^ p` is bounded on the compact
`A`-neighbourhood of `K` by `exists_bound_on_neighbourhood`. -/
theorem exitStep_envelope_of_growth {ΩB : Type*} [MeasurableSpace ΩB] {d : ℕ}
    (PB : Measure ΩB) [IsProbabilityMeasure PB] (B : Space d → ℝ≥0 → ΩB → Space d)
    (hBrown : ∀ y : Space d, IsBrownian d y (B y) PB)
    (hcont : ∀ (y : Space d) (ω : ΩB), Continuous fun s => B y s ω)
    (hmeas : ∀ (y : Space d) (t : ℝ≥0), StronglyMeasurable (B y t))
    (h : ℝ → Space d → ℝ) (T A : ℝ) (hT : 0 < T)
    (K : Set (Space d)) (hK : IsCompact K)
    (C : ℝ) (hC : 0 ≤ C) (p : ℕ)
    (hp : ∀ v : ℝ≥0, (v : ℝ) ≤ T → ∀ y : Space d, ‖h v y‖ ≤ C * (1 + ‖y‖) ^ p) :
    ∃ M : ℝ, ∀ z : Space d, (∃ y ∈ K, ‖z - y‖ ≤ A) →
      ∃ D : ΩB → ℝ, Integrable D PB ∧ ∫ b, D b ∂PB ≤ M ∧
        ∀ᵐ b ∂PB, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ r : ℝ≥0, (r : ℝ) ≤ T →
          ‖h t (B z r b)‖ ≤ D b := by
  obtain ⟨M₀, hM₀⟩ := exists_uniform_pathRadius_moment d T.toNNReal p
  obtain ⟨R, hR⟩ := exists_bound_on_neighbourhood (fun _ z => (1 + ‖z‖) ^ p) T A hT.le
    K hK (Continuous.continuousOn (by fun_prop))
  refine ⟨C * R * M₀, fun z hz => ?_⟩
  have hRz : (1 + ‖z‖) ^ p ≤ R := hR z hz
  have hM0z := hM₀ ΩB PB inferInstance z (B z) (hBrown z) (fun s => (hmeas z s).measurable)
    (hcont z)
  have hM0nn : 0 ≤ M₀ := by
    have h1 : (0 : ℝ) ≤ ∫ b, (1 + brownianPathRadius (B z) z T.toNNReal b) ^ p ∂PB :=
      integral_nonneg fun b => pow_nonneg (add_nonneg zero_le_one
        (le_trans (norm_nonneg _) (norm_le_pathRadius (B z) (hcont z) z T.toNNReal b le_rfl))) p
    linarith [hM0z]
  have hpoly : ∀ v : ℝ≥0, (v : ℝ) ≤ T → ∀ y : Space d,
      ‖h v y‖ ≤ C * (1 + ‖z‖) ^ p * (1 + ‖y - z‖) ^ p := by
    intro v hv y
    refine (hp v hv y).trans ?_
    have h1 : (1 : ℝ) + ‖y‖ ≤ (1 + ‖z‖) * (1 + ‖y - z‖) := by
      have h2 : ‖y‖ ≤ ‖z‖ + ‖y - z‖ := by
        calc ‖y‖ = ‖(y - z) + z‖ := by rw [sub_add_cancel]
          _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
          _ = ‖z‖ + ‖y - z‖ := by ring
      have h5 : (0 : ℝ) ≤ ‖z‖ * ‖y - z‖ := mul_nonneg (norm_nonneg z) (norm_nonneg (y - z))
      nlinarith [h2, h5]
    calc C * (1 + ‖y‖) ^ p ≤ C * ((1 + ‖z‖) * (1 + ‖y - z‖)) ^ p :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 p) hC
      _ = C * (1 + ‖z‖) ^ p * (1 + ‖y - z‖) ^ p := by rw [mul_pow]; ring
  refine ⟨fun b => C * (1 + ‖z‖) ^ p * (1 + brownianPathRadius (B z) z T.toNNReal b) ^ p,
    (integrable_brownian_pathRadius_pow (hBrown z) (fun s => (hmeas z s).measurable)
      (hcont z) T.toNNReal p).const_mul (C * (1 + ‖z‖) ^ p), ?_, ?_⟩
  · rw [integral_const_mul]
    calc C * (1 + ‖z‖) ^ p * ∫ b, (1 + brownianPathRadius (B z) z T.toNNReal b) ^ p ∂PB
        ≤ C * (1 + ‖z‖) ^ p * M₀ :=
          mul_le_mul_of_nonneg_left hM0z (mul_nonneg hC (by positivity))
      _ ≤ C * R * M₀ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRz hC) hM0nn
  · refine Filter.Eventually.of_forall (fun b t ht r hr => ?_)
    have hcoe : (T.toNNReal : ℝ) = T := Real.coe_toNNReal T hT.le
    have hr' : r ≤ T.toNNReal := by rw [← NNReal.coe_le_coe, hcoe]; exact hr
    have h1 := hpoly t.toNNReal (by rw [Real.coe_toNNReal t ht.1]; exact ht.2) (B z r b)
    rw [Real.coe_toNNReal t ht.1] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity)
        (by linarith [norm_le_pathRadius (B z) (hcont z) z T.toNNReal b hr']) p)
      (mul_nonneg hC (by positivity)))

/-- The strong Markov step residual of `lem:brownian-ball-localization` from the strong Markov
property at the exit time of the ball, with its integrable envelope built from the polynomial
growth of the field, and the monotonicity of the Brownian value in the horizon, taken as an
explicit hypothesis.  Sorry-free: every proof obligation beyond `hExit`, `hgrowth` and `hmono`
is discharged here. -/
theorem ballStepResidual_of_exitStep_of_mono (d : ℕ)
    (hExit : Sandpile.External.BrownianExitStep) (hgrowth : BallGrowthResidual d)
    (hmono : ∀ (ΩW : Type) [MeasurableSpace ΩW] (PW : Measure ΩW) [IsProbabilityMeasure PW]
        (W : (Space d → ℝ) → ΩW → ℝ), IsWhiteNoise d W PW →
      ∀ ν2 : ℝ, 0 ≤ ν2 →
      ∀ (ΩB : Type) [MeasurableSpace ΩB] (PB : Measure ΩB) [IsProbabilityMeasure PB]
        (B : Space d → ℝ≥0 → ΩB → Space d),
        (∀ y : Space d, IsBrownian d y (B y) PB) →
        (∀ (y : Space d) (ω : ΩB), Continuous fun s => B y s ω) →
        (∀ (y : Space d) (t : ℝ≥0), StronglyMeasurable (B y t)) →
      ∀ (Z : ℝ → Space d → ΩW → ℝ),
        (∀ (t : ℝ) (x : Space d), Z t x =ᵐ[PW] fun ω => gaussianPotential d ν2 W t x ω) →
        (∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
          ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω) (Set.Icc (0 : ℝ) T ×ˢ Set.univ)) →
      ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW, ∀ z : Space d, ∀ s ∈ Set.Icc (0 : ℝ) T,
        brownianValue (B z) PB (fun t x => Z t x ω) s z ≤
          brownianValue (B z) PB (fun t x => Z t x ω) T z) :
    BallStepResidual d := by
  refine ballStepResidual_of_growth_and_conditional d hgrowth ?_
  intro ΩW mΩW PW hPW W hW ν2 hν2 Z hmod hc T hT A hA K hK ΩB mΩB PB hPB B hBrown hcont hmeas
  filter_upwards [hgrowth ΩW PW W hW ν2 hν2 Z hmod hc T hT, hc T hT,
    hmono ΩW PW W hW ν2 hν2 ΩB PB B hBrown hcont hmeas Z hmod hc T hT] with ω hg hcω hmonoω
  intro u hu τ hτ hbound
  obtain ⟨C, hC, p, hp⟩ := hg
  have henv := exitStep_envelope_of_growth PB B hBrown hcont hmeas (fun t z => Z t z ω) T A hT
    K hK C hC p hp
  have hres := hExit d ΩB PB B hBrown hcont hmeas T hT (fun t z => Z t z ω) hcω A hA K hK
    henv u hu τ hτ hbound
  have hfar : BddAbove (farValues B PB (fun t z => Z t z ω) T A K) :=
    bddAbove_farValues_of_growth_pointwise (PW := PW) (PB := PB) hBrown hcont
      (fun y t => (hmeas y t).measurable) Z T A hT.le K hK p C hC ω hp hcω
  have hSup_le : sSup {v : ℝ | ∃ w : Space d, (∃ y ∈ K, ‖w - y‖ ≤ A) ∧
      ∃ s ∈ Set.Icc (0 : ℝ) T, v = brownianValue (B w) PB (fun t z => Z t z ω) s w} ≤
      sSup (farValues B PB (fun t z => Z t z ω) T A K) := by
    refine csSup_le ⟨brownianValue (B u) PB (fun t z => Z t z ω) T u,
      ⟨u, ⟨u, hu, by simpa using le_trans zero_le_one hA⟩, T, ⟨hT.le, le_refl T⟩, rfl⟩⟩ ?_
    rintro v ⟨w, hw, s, hs, rfl⟩
    exact (hmonoω w s hs).trans (le_csSup hfar ⟨w, hw, rfl⟩)
  exact hres.trans (mul_le_mul_of_nonneg_left hSup_le measureReal_nonneg)

/-- The strong Markov step residual of `lem:brownian-ball-localization` from the strong Markov
property at the exit time of the ball and the polynomial growth of the field, supplying the
monotonicity of the Brownian value in the horizon from
`Sandpile.Frozen.brownian_value_mono_horizon`, which is still a registered `sorry`. -/
theorem ballStepResidual_of_exitStep (d : ℕ) (hd : d < 4)
    (hExit : Sandpile.External.BrownianExitStep) (hgrowth : BallGrowthResidual d) :
    BallStepResidual d :=
  ballStepResidual_of_exitStep_of_mono d hExit hgrowth
    (Sandpile.Frozen.brownian_value_mono_horizon d hd)

end Sandpile.Continuum
