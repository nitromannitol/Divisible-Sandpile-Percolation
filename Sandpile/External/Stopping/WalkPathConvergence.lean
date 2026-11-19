import Sandpile.External.Stopping.WalkTightness
import LatticeProb.Bonanno.ReflectedGMS.Limit.PathLawFiniteDimensionalConvergence

/-!
# Reduction of rescaled walk path convergence

Tightness of the interpolated walks reduces weak convergence on continuous path
space to convergence of their finite-dimensional distributions.
-/

open MeasureTheory Filter Topology
open scoped NNReal

namespace Sandpile.External.Stopping

/-- The law on continuous path space of a diffusively rescaled walk. -/
noncomputable def diffusiveWalkPathLaw (d : ℕ) [NeZero d] (R : ℝ) (x : Site d) :
    ProbabilityMeasure C(ℝ≥0, Continuum.Space d) :=
  ⟨Measure.map (diffusiveWalkPath R) (walkLaw d x),
    (Measure.isProbabilityMeasure_map_iff (measurable_diffusiveWalkPath R).aemeasurable).2
      (by change IsProbabilityMeasure (LatticeProb.siteWalkLaw d x); infer_instance)⟩

/-- For diverging scales and bounded scaled starts, finite-dimensional
convergence implies convergence of the rescaled walk laws on path space. -/
theorem tendsto_diffusiveWalkPathLaw_of_finiteDimensional
    (d : ℕ) [NeZero d] (R : ℕ → ℝ) (x : ℕ → Site d) (hR : Tendsto R atTop atTop)
    (M : ℝ) (hM : ∀ n, dist (Lclt.scaledSite (R n) (x n)) 0 ≤ M)
    (μ : ProbabilityMeasure C(ℝ≥0, Continuum.Space d))
    (hfdd : ∀ I : Finset ℝ≥0,
      Tendsto (fun n => (diffusiveWalkPathLaw d (R n) (x n)).map
        (fun f => I.restrict (ReflectedGMS.MartingaleLimit.pathCoordinates f))) atTop
        (𝓝 (μ.map (fun f => I.restrict (ReflectedGMS.MartingaleLimit.pathCoordinates f))))) :
    Tendsto (fun n => diffusiveWalkPathLaw d (R n) (x n)) atTop (𝓝 μ) := by
  apply ReflectedGMS.MartingaleLimit.tendsto_of_isTightMeasureSet_of_tendsto_map_finsetRestrict
    _ μ (Set.range fun n => diffusiveWalkPathLaw d (R n) (x n))
  · exact Filter.Eventually.of_forall fun n => ⟨n, rfl⟩
  · have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
    convert isTightMeasureSet_range_diffusiveWalkPath d hd R x hR M hM using 1
    ext ν
    simp only [Set.mem_ofPred_eq, Set.mem_range, exists_exists_eq_and]
    rfl
  · exact hfdd

end Sandpile.External.Stopping
