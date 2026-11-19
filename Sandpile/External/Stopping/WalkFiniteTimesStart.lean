import Sandpile.External.Stopping.WalkFiniteTimes

/-!
# Finite-dimensional limits with changing starts

A convergent sequence of deterministic starting positions can be added to the
centered walk without changing the limiting fluctuations.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- Joint convergence at finite times with convergent deterministic starting
positions and Brownian fluctuations started at zero. -/
theorem tendstoInDistribution_walk_brownian_finite_times_add_start
    {d : ℕ} [NeZero d] {ι : Type*} [Fintype ι]
    (R : ℕ → ℝ) (hR : Tendsto R atTop atTop) (u : ι → ℝ≥0)
    (a : ℕ → Fin d → ℝ) (a₀ : Fin d → ℝ) (ha : Tendsto a atTop (𝓝 a₀))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)) (hB : LatticeProb.IsBrownianSpace d 0 B P) :
    TendstoInDistribution
      (fun n (ξ : ℕ → LatticeProb.Site d) (p : ι × Fin d) =>
        a n p.2 + (R n)⁻¹ * ∑ k ∈ Finset.range (⌊(u p.1 : ℝ) * (R n) ^ 2⌋₊),
          ((ξ k p.2 : ℤ) : ℝ))
      atTop (fun ω (p : ι × Fin d) => a₀ p.2 + B (u p.1) ω p.2)
      (fun _ => LatticeProb.incPathLaw d) P := by
  let c : ℕ → (ι × Fin d → ℝ) := fun n p => a n p.2
  let c₀ : ι × Fin d → ℝ := fun p => a₀ p.2
  have hc : Tendsto c atTop (𝓝 c₀) := by
    apply tendsto_pi_nhds.mpr
    intro p
    exact (continuous_apply p.2).tendsto a₀ |>.comp ha
  have hcmeasure : TendstoInMeasure (LatticeProb.incPathLaw d)
      (fun n (_ : ℕ → LatticeProb.Site d) => c n) atTop (fun _ => c₀) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact stronglyMeasurable_const.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun _ => hc
  have h := (tendstoInDistribution_walk_brownian_finite_times R hR u P B hB)
    |>.add_of_tendstoInMeasure_const hcmeasure (fun _ => measurable_const.aemeasurable)
  refine h.congr (fun n => Filter.Eventually.of_forall fun ξ => ?_) ?_
  · funext p
    dsimp only [Pi.add_apply, c]
    exact add_comm _ _
  · filter_upwards [hB.start] with ω hω
    funext p
    simp only [Pi.add_apply, c₀, hω, PiLp.zero_apply, sub_zero, add_comm]

end Sandpile.External.Stopping
