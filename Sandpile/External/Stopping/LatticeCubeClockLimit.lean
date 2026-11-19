import Sandpile.External.Stopping.LatticeCubeBoundary
import Sandpile.External.Stopping.CubeStoppedPathLimit
import LatticeProb.Walk.GraphClockConvergence

/-!
# Lattice cube clocks and stopped paths

For convergent centered interpolated lattice paths, the first inner-boundary
clock and the cube exit clock both converge to a regular limiting cube exit.
Stopping at either clock and at a varying finite horizon preserves convergence.
-/

open Filter Metric Set Topology MatedCRTHarmonic.Markov
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- If centered interpolated lattice paths converge to a path with a regular
unit-cube exit, both the inner-boundary and exit clocks and their stopped paths
converge to the corresponding limiting objects. -/
theorem tendsto_latticeCube_clocks_and_stoppedPaths
    {d : ℕ} [NeZero d] {α : Type*} {l : Filter α}
    (R : α → ℝ) (q : α → Site d) (X : α → ℕ → Site d)
    (m : α → ℝ≥0) (N : α → ℕ) (F : α → C(ℝ≥0, Continuum.Space d))
    (f : C(ℝ≥0, Continuum.Space d)) (τ h : ℝ≥0) (H : α → ℝ≥0)
    (hRpos : ∀ i, 0 < R i) (hR : Tendsto R l atTop)
    (hm : ∀ i, 0 < m i)
    (hexit : ∀ i, hitTime (supBox (q i) (R i))ᶜ (X i) = N i)
    (hstart : ∀ i, X i 0 ∈ supBox (q i) (R i))
    (hstep : ∀ i n, X i (n + 1) = X i n ∨ (LatticeProb.lattice d).Adj (X i n) (X i (n + 1)))
    (hpath : ∀ i t, F i t = LatticeProb.ConstantStepInterpolation.path (m i)
      (centeredScaledSite (R i) (q i) ∘ X i) t)
    (hF : Tendsto F l (𝓝 f)) (hH : Tendsto H l (𝓝 h))
    (hbefore : ∀ s < τ, ∀ j, |f s j| < 1)
    (hafter : ∀ t > τ, ∃ s < t, ∃ j, 1 < |f s j|) :
    let a := fun i => LatticeProb.ConstantStepInterpolation.knot (m i)
      (hitTime (LatticeProb.Graph.innerBoundary (LatticeProb.lattice d)
        (supBox (q i) (R i))) (X i)).toNat
    let b := fun i => LatticeProb.ConstantStepInterpolation.knot (m i) (N i)
    Tendsto a l (𝓝 τ) ∧ Tendsto b l (𝓝 τ) ∧
      Tendsto (fun i => LatticeProb.stoppedPath ((min (a i) (H i) : ℝ≥0) : ℝ≥0∞) (F i)) l
        (𝓝 (LatticeProb.stoppedPath ((min τ h : ℝ≥0) : ℝ≥0∞) f)) ∧
      Tendsto (fun i => LatticeProb.stoppedPath ((min (b i) (H i) : ℝ≥0) : ℝ≥0∞) (F i)) l
        (𝓝 (LatticeProb.stoppedPath ((min τ h : ℝ≥0) : ℝ≥0∞) f)) := by
  let K := (openUnitCube (0 : Continuum.Space d))ᶜ
  let C := closedUnitCube (0 : Continuum.Space d)
  let A : α → Set (Site d) := fun i => supBox (q i) (R i)
  let p : α → Site d → Continuum.Space d := fun i => centeredScaledSite (R i) (q i)
  let δ : α → ℝ := fun i => 1 / R i
  have hδ : Tendsto δ l (𝓝 0) := by
    simpa only [δ, one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hR
  have hins (i : α) (v : Site d) (hv : v ∈ A i) : p i v ∈ C :=
    centeredScaledSite_mem_closedUnitCube (hRpos i) hv
  have hedge (i : α) (j : ℕ) (_hj : j < N i) : dist (p i (X i j)) (p i (X i (j + 1))) ≤ δ i := by
    rcases hstep i j with heq | hadj
    · simp only [heq, dist_self, δ]
      exact (one_div_pos.mpr (hRpos i)).le
    · exact dist_centeredScaledSite_le_of_adj (hRpos i) (q i) hadj
  have hboundary : Tendsto (fun i => infDist
      (p i (X i (hitTime (LatticeProb.Graph.innerBoundary (LatticeProb.lattice d) (A i)) (X i)).toNat)) K)
      l (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hδ
    · exact fun i => infDist_nonneg
    · intro i
      have hg := LatticeProb.ConstantStepInterpolation.graph_boundary_and_exit_clocks
        (LatticeProb.lattice d) (A i) C (X i) (p i) (hm i) (hexit i) (hstart i)
        (hstep i) (hins i) (hedge i)
      exact infDist_centeredScaledSite_innerBoundary_le (hRpos i) hg.2.2.1
  have hb : ∀ s < τ, f s ∉ K := by
    intro s hs hn
    apply hn
    intro j
    simpa using hbefore s hs j
  have ha : ∀ t > τ, ∃ s < t, f s ∉ C := by
    intro t ht
    obtain ⟨s, hs, j, hj⟩ := hafter t ht
    refine ⟨s, hs, fun hz => ?_⟩
    have hz' := hz j
    simp at hz'
    exact (not_lt_of_ge hz') hj
  obtain ⟨hca, hcb, _⟩ := LatticeProb.ConstantStepInterpolation.tendsto_graph_clocks_of_regular_exit
    (fun _ => LatticeProb.lattice d) A X p m N F f δ K C τ
    (isOpen_openUnitCube 0).isClosed_compl (openUnitCube_compl_nonempty 0)
    (isClosed_closedUnitCube 0) (closedUnitCube_nonempty 0)
    hm hexit hstart hstep hins hedge hpath hF hboundary hδ hb ha
  refine ⟨hca, hcb, ?_, ?_⟩
  · exact (LatticeProb.continuous_stoppedPath.tendsto _).comp
      (((ENNReal.continuous_coe.tendsto _).comp (hca.min hH)).prodMk_nhds hF)
  · exact (LatticeProb.continuous_stoppedPath.tendsto _).comp
      (((ENNReal.continuous_coe.tendsto _).comp (hcb.min hH)).prodMk_nhds hF)

end Sandpile.External.Stopping
