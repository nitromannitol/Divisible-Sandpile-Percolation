import Sandpile.External.Stopping.WalkFiniteTimesStart
import Sandpile.External.Stopping.WalkContinuity

/-!
# Finite-dimensional limits of lattice walk positions

The position-path law is the image of the independent increment law under
cumulative summation. This identifies the finite-dimensional limits of the
walk at the grid points immediately preceding the observation times.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Rescaled grid positions converge jointly at any finite family of times when
rescaled initial positions converge. -/
theorem tendstoInDistribution_walk_grid_finite_times
    {d : ℕ} [NeZero d] {ι : Type*} [Fintype ι]
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (u : ι → ℝ≥0)
    (x : ℕ → Site d) (y : Continuum.Space d)
    (hx : Tendsto (fun n => Lclt.scaledSite (R n) (x n)) atTop (𝓝 y))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hB : LatticeProb.IsBrownianSpace d 0 B P) :
    TendstoInDistribution
      (fun n (X : ℕ → Site d) (p : ι × Fin d) =>
        Lclt.scaledSite (R n) (X ⌊(u p.1 : ℝ) * (R n) ^ 2⌋₊) p.2)
      atTop (fun ω (p : ι × Fin d) => y p.2 + B (u p.1) ω p.2)
      (fun n => LatticeProb.siteWalkLaw d (x n)) P := by
  let a : ℕ → Fin d → ℝ := fun n i => Lclt.scaledSite (R n) (x n) i
  let a₀ : Fin d → ℝ := fun i => y i
  have ha : Tendsto a atTop (𝓝 a₀) := by
    apply tendsto_pi_nhds.mpr
    intro i
    exact ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i).tendsto y).comp hx
  have h := tendstoInDistribution_walk_brownian_finite_times_add_start R hR u a a₀ ha P B hB
  let Z : ℕ → (ℕ → Site d) → (ι × Fin d → ℝ) := fun n X p =>
    Lclt.scaledSite (R n) (X ⌊(u p.1 : ℝ) * (R n) ^ 2⌋₊) p.2
  have hZ (n : ℕ) : Measurable (Z n) := by
    apply Measurable.of_eval
    intro p
    exact (measurable_of_countable (fun z : Site d => Lclt.scaledSite (R n) z p.2)).comp
      (measurable_pi_apply _)
  have heq (n : ℕ) (ξ : ℕ → Site d) : Z n (LatticeProb.sitePath (x n) ξ) =
      (fun p : ι × Fin d => a n p.2 + (R n)⁻¹ *
        ∑ k ∈ Finset.range (⌊(u p.1 : ℝ) * (R n) ^ 2⌋₊), ((ξ k p.2 : ℤ) : ℝ)) := by
    funext p
    simp only [Z, LatticeProb.sitePath, Lclt.scaledSite, WithLp.ofLp_toLp,
      Pi.add_apply, Finset.sum_apply, a]
    push_cast
    simp only [div_eq_mul_inv]
    ring
  have hmaps (n : ℕ) : (LatticeProb.siteWalkLaw d (x n)).map (Z n) =
      (LatticeProb.incPathLaw d).map (fun ξ p => a n p.2 + (R n)⁻¹ *
        ∑ k ∈ Finset.range (⌊(u p.1 : ℝ) * (R n) ^ 2⌋₊), ((ξ k p.2 : ℤ) : ℝ)) := by
    rw [LatticeProb.siteWalkLaw_eq,
      Measure.map_map (hZ n) (LatticeProb.measurable_sitePath (x n))]
    congr 1
    funext ξ
    exact heq n ξ
  refine ⟨fun n => (hZ n).aemeasurable, h.aemeasurable_limit, ?_⟩
  have hfun : (fun n => (⟨(LatticeProb.siteWalkLaw d (x n)).map (Z n),
      inferInstance⟩ : ProbabilityMeasure (ι × Fin d → ℝ))) =
      (fun n => ⟨(LatticeProb.incPathLaw d).map (fun ξ p => a n p.2 + (R n)⁻¹ *
        ∑ k ∈ Finset.range (⌊(u p.1 : ℝ) * (R n) ^ 2⌋₊), ((ξ k p.2 : ℤ) : ℝ)),
        inferInstance⟩) := by
    funext n
    exact ProbabilityMeasure.toMeasure_injective (hmaps n)
  change Tendsto (fun n => (⟨(LatticeProb.siteWalkLaw d (x n)).map (Z n),
    inferInstance⟩ : ProbabilityMeasure (ι × Fin d → ℝ))) atTop _
  rw [hfun]
  exact h.tendsto

end Sandpile.External.Stopping
