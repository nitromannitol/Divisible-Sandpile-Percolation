import LatticeProb.Topology.OrderedClockConvergence
import LatticeProb.Prob.ContinuousStoppedPath

/-!
# Stopped paths at regular exits

At a regular exit, convergence of paths and of their boundary and exit clocks
implies convergence of the paths stopped at either clock, including when the
finite horizon varies. This is a pathwise ingredient for the killed-walk
invariance principle cited in Coquet and Toldo, *Convergence of values in
optimal stopping and convergence of optimal stopping times* (2007).
-/

open Filter Metric Set Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Convergent paths stopped at their boundary and exit clocks converge to the
limiting path stopped at its regular exit, after truncation by a varying horizon. -/
theorem tendsto_stoppedPaths_of_regular_exit
    {E α : Type*} [MetricSpace E] {l : Filter α}
    {F : α → C(ℝ≥0, E)} {f : C(ℝ≥0, E)} {a b H : α → ℝ≥0}
    {δ : α → ℝ} {K C : Set E} {τ h : ℝ≥0}
    (hK : IsClosed K) (hKne : K.Nonempty) (hC : IsClosed C) (hCne : C.Nonempty)
    (hF : Tendsto F l (𝓝 f)) (hH : Tendsto H l (𝓝 h))
    (ha : Tendsto (fun i => infDist (F i (a i)) K) l (𝓝 0))
    (hδ : Tendsto δ l (𝓝 0))
    (hbound : ∀ᶠ i in l, ∀ s < b i, infDist (F i s) C ≤ δ i)
    (horder : ∀ᶠ i in l, a i ≤ b i)
    (hbefore : ∀ s < τ, f s ∉ K)
    (hafter : ∀ t > τ, ∃ s < t, f s ∉ C) :
    Tendsto (fun i => LatticeProb.stoppedPath ((min (a i) (H i) : ℝ≥0) : ℝ≥0∞) (F i)) l
        (𝓝 (LatticeProb.stoppedPath ((min τ h : ℝ≥0) : ℝ≥0∞) f)) ∧
      Tendsto (fun i => LatticeProb.stoppedPath ((min (b i) (H i) : ℝ≥0) : ℝ≥0∞) (F i)) l
        (𝓝 (LatticeProb.stoppedPath ((min τ h : ℝ≥0) : ℝ≥0∞) f)) := by
  obtain ⟨ha', hb'⟩ := LatticeProb.tendsto_ordered_clocks_of_regular_exit
    hK hKne hC hCne hF ha hδ hbound horder hbefore hafter
  constructor
  · exact (LatticeProb.continuous_stoppedPath.tendsto _).comp
      (((ENNReal.continuous_coe.tendsto _).comp (ha'.min hH)).prodMk_nhds hF)
  · exact (LatticeProb.continuous_stoppedPath.tendsto _).comp
      (((ENNReal.continuous_coe.tendsto _).comp (hb'.min hH)).prodMk_nhds hF)

end Sandpile.External.Stopping
