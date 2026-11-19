import Sandpile.External.Stopping.WalkBrownianPathLimit
import LatticeProb.Prob.BrownianPathCoords

/-!
# Walk invariance principle

The diffusively rescaled interpolated simple walk converges weakly on continuous
path space to Brownian motion, for any convergent sequence of rescaled starts.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- The interpolated walk laws converge to the law of a measurable continuous
version of Brownian motion started at the limiting point. -/
theorem exists_brownian_path_limit
    (d : ℕ) [NeZero d] (R : ℕ → ℝ) (x : ℕ → Site d) (hR : Tendsto R atTop atTop)
    (y : Continuum.Space d)
    (hx : Tendsto (fun n => Lclt.scaledSite (R n) (x n)) atTop (𝓝 y))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hB : LatticeProb.IsBrownianSpace d 0 B P) :
    ∃ (F : Ω → C(ℝ≥0, Continuum.Space d)) (hFm : Measurable F),
      (∀ᵐ ω ∂P, ∀ t, F ω t = y + B t ω) ∧
      Tendsto (fun n => diffusiveWalkPathLaw d (R n) (x n)) atTop
        (𝓝 (⟨P.map F, (Measure.isProbabilityMeasure_map_iff hFm.aemeasurable).2 inferInstance⟩ :
          ProbabilityMeasure C(ℝ≥0, Continuum.Space d))) := by
  obtain ⟨C, hCm, hCc, _, hCae, _, _⟩ := hB.exists_continuousVersion
  have hd : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d))
  let D : ℝ≥0 → Ω → Continuum.Space d := fun t ω => y + (Real.sqrt d)⁻¹ • C t ω
  have hDm (t : ℝ≥0) : Measurable (D t) := by
    change Measurable (fun ω => y + (Real.sqrt (d : ℝ))⁻¹ • C t ω)
    exact measurable_const.add ((measurable_const : Measurable (fun _ : Ω => (Real.sqrt (d : ℝ))⁻¹)).smul (hCm t))
  have hDc (ω : Ω) : Continuous (fun t => D t ω) := by
    change Continuous (fun t => y + (Real.sqrt (d : ℝ))⁻¹ • C t ω)
    exact continuous_const.add ((continuous_const : Continuous (fun _ : ℝ≥0 => (Real.sqrt (d : ℝ))⁻¹)).smul (hCc ω))
  let F := LatticeProb.pathMap D hDc
  have hFm : Measurable F := LatticeProb.measurable_pathMap D hDm hDc
  have hFae : ∀ᵐ ω ∂P, ∀ t, F ω t = y + B t ω := by
    filter_upwards [hCae] with ω hω t
    change y + (Real.sqrt d)⁻¹ • C t ω = y + B t ω
    rw [hω t, sub_zero, smul_smul, inv_mul_cancel₀ hd.ne', one_smul]
  obtain ⟨M, hM⟩ := (Metric.isBounded_iff_subset_ball 0).mp
    (Metric.isBounded_range_of_tendsto _ hx)
  have hMb (n : ℕ) : dist (Lclt.scaledSite (R n) (x n)) 0 ≤ M :=
    (hM ⟨n, rfl⟩).le
  exact ⟨F, hFm, hFae, tendsto_diffusiveWalkPathLaw_brownian d R x hR y hx M hMb
    P B hB F hFm.aemeasurable hFae⟩

end Sandpile.External.Stopping
