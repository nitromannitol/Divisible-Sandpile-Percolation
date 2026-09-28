import Sandpile.Support.Dgt4AConcContract
import Sandpile.External.GaussianLipschitzConcentration

/-!
# Gaussian concentration for the residual field after conditioning

Conditioning the Gaussian scenery on the linear functional `-V_∞(0)` replaces its covariance
by a rank-one reduction, so the same concentration bound holds conditionally. The law of the
residual field `residField d hd` is the image of the standard Gaussian product under that
reduction, and since the reduction (`projUnit`) is a contraction for the `ℓ²` distance at
every configuration, a functional that is Lipschitz for that distance under the residual law
lifts to one with the same constant under the product, where the cited Gaussian-Lipschitz
concentration inequality applies. The image of the reduction agrees with the `L²`
representative `residField` almost everywhere, so the two descriptions coincide as measures.
-/

open MeasureTheory ProbabilityTheory Filter Topology

open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The residual law is the image of the standard Gaussian product under the
everywhere-defined reduction. -/
theorem map_projUnit_eq_map_residField (hd : 5 ≤ d) :
    (LatticeProb.gaussLaw (Site d)).map (projUnit d hd)
      = (LatticeProb.gaussLaw (Site d)).map (residField d hd) :=
  Measure.map_congr (ae_projUnit_eq_residField hd)

/-- **The concentration bound under the conditioning** (`sandpile.tex:5265-5266`): a
functional of the residual field that is `Λ`-Lipschitz for the `\ell^2` distance exceeds
its conditional mean by `t` with probability at most `exp(-t²/(2Λ²))`. -/
theorem measure_resid_ge_integral_le
    (hGaussConc : Sandpile.External.GaussianLipschitzConcentration) (hd : 5 ≤ d)
    (Φ : (Site d → ℝ) → ℝ) (Λ : ℝ) (hΛ : 0 < Λ) (hmeas : Measurable Φ)
    (hint : Integrable Φ ((LatticeProb.gaussLaw (Site d)).map (residField d hd)))
    (hlip : ∀ (r r' : Site d → ℝ) (M : ℝ), HasSum (fun z => (r z - r' z) ^ 2) M →
      |Φ r - Φ r'| ≤ Λ * Real.sqrt M)
    (t : ℝ) (ht : 0 ≤ t) :
    ((LatticeProb.gaussLaw (Site d)).map (residField d hd))
        {r | (∫ r', Φ r' ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd))) + t ≤ Φ r}
      ≤ ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * Λ ^ 2))) := by
  set μ : Measure (Site d → ℝ) := LatticeProb.gaussLaw (Site d) with hμ
  set ρ : Measure (Site d → ℝ) := μ.map (residField d hd) with hρ
  set F : (Site d → ℝ) → ℝ := fun ω => Φ (projUnit d hd ω) with hF
  have hmap : μ.map (projUnit d hd) = ρ := map_projUnit_eq_map_residField hd
  have hFmeas : Measurable F := hmeas.comp (measurable_projUnit hd)
  have hintF : Integrable F μ := by
    rw [← hmap] at hint
    exact (integrable_map_measure hmeas.aestronglyMeasurable
      (measurable_projUnit hd).aemeasurable).mp hint
  have hmean : ∫ ω, F ω ∂μ = ∫ r, Φ r ∂ρ := by
    rw [← hmap, integral_map (measurable_projUnit hd).aemeasurable hmeas.aestronglyMeasurable]
  have hlipF : ∀ (ω η : Site d → ℝ) (M : ℝ), HasSum (fun z => (ω z - η z) ^ 2) M →
      |F ω - F η| ≤ Λ * Real.sqrt M := by
    intro ω η M hM
    obtain ⟨M', hM', hle⟩ := hasSum_sq_projUnit_sub_le hd ω η M hM
    refine (hlip _ _ M' hM').trans ?_
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) hΛ.le
  have hconc := hGaussConc (Site d) F Λ hΛ hFmeas hintF hlipF t ht
  have hmeasset : MeasurableSet {r : Site d → ℝ | (∫ r', Φ r' ∂ρ) + t ≤ Φ r} :=
    measurableSet_le measurable_const hmeas
  have hpull : ρ {r : Site d → ℝ | (∫ r', Φ r' ∂ρ) + t ≤ Φ r}
      = μ {ω : Site d → ℝ | (∫ ω', F ω' ∂μ) + t ≤ F ω} := by
    have h1 : ρ {r : Site d → ℝ | (∫ r', Φ r' ∂ρ) + t ≤ Φ r}
        = (μ.map (projUnit d hd)) {r : Site d → ℝ | (∫ r', Φ r' ∂ρ) + t ≤ Φ r} := by
      rw [hmap]
    rw [h1, Measure.map_apply (measurable_projUnit hd) hmeasset, ← hmean]
    rfl
  rw [hpull]
  exact hconc

end Sandpile
