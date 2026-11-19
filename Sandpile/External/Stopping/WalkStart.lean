import Sandpile.External.Stopping.WalkContinuity

/-!
# Starting points of diffusively rescaled walks

The path law starts at the scaled lattice starting point. Consequently,
bounded scaled starting points satisfy the initial-position estimate used in
continuous-path tightness criteria.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- A walk started at `x` has interpolated initial position `x / R` almost surely. -/
theorem ae_diffusiveWalkPath_zero {d : ℕ} (hd : 1 ≤ d) (x : Site d) (R : ℝ) :
    ∀ᵐ X ∂(walkLaw d x), diffusiveWalkPath R X 0 = Lclt.scaledSite R x := by
  let : NeZero d := ⟨by omega⟩
  have hstart : ∀ᵐ X ∂(walkLaw d x), X 0 = x := by
    have hm : MeasurableSet {X : ℕ → Site d | X 0 = x} := by
      change MeasurableSet ((fun X : ℕ → Site d => X 0) ⁻¹' {x})
      exact (measurable_pi_apply 0) (Set.to_countable _).measurableSet
    rw [show walkLaw d x = LatticeProb.siteWalkLaw d x from rfl,
      LatticeProb.siteWalkLaw_eq, ae_map_iff (LatticeProb.measurable_sitePath x).aemeasurable hm]
    exact Filter.Eventually.of_forall fun ξ => LatticeProb.sitePath_zero x ξ
  filter_upwards [hstart] with X hX
  let c : ℝ≥0 := ⟨R ^ 2, sq_nonneg R⟩
  change linearWalk R (c * 0) X = Lclt.scaledSite R x
  rw [mul_zero]
  simpa using (linearWalk_nat R 0 X).trans (congrArg (Lclt.scaledSite R) hX)

/-- If the scaled starting point lies within distance `M` of `z`, the path
law assigns zero mass to paths starting farther than `M` from `z`. -/
theorem measure_diffusiveWalkPath_start_far {d : ℕ} (hd : 1 ≤ d) (x : Site d) (R M : ℝ)
    (z : Continuum.Space d) (hM : dist (Lclt.scaledSite R x) z ≤ M) :
    (Measure.map (diffusiveWalkPath R) (walkLaw d x))
      {f : C(ℝ≥0, Continuum.Space d) | M < dist (f 0) z} = 0 := by
  have hm : MeasurableSet {f : C(ℝ≥0, Continuum.Space d) | M < dist (f 0) z} :=
    measurableSet_lt measurable_const
      ((ContinuousMap.measurable_eval 0).dist measurable_const)
  rw [Measure.map_apply (measurable_diffusiveWalkPath R) hm]
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_diffusiveWalkPath_zero hd x R] with X hX
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, not_lt]
  simpa only [hX] using hM

end Sandpile.External.Stopping
