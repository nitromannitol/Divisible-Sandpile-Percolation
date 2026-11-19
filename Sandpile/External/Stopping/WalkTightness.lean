import Sandpile.External.Stopping.WalkModulusSmall
import Sandpile.External.Stopping.WalkStart
import LatticeProb.Prob.PathModulusContinuity

/-!
# Tightness of rescaled walk laws

Diffusive walk path laws are tight when the scales tend to infinity and the
scaled starting sites remain bounded. The modulus estimate controls the tail
of the sequence, and continuity controls the finitely many earlier path laws.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- Rescaled walk laws with bounded starting points form a tight family. -/
theorem isTightMeasureSet_range_diffusiveWalkPath (d : ℕ) (hd : 1 ≤ d)
    (R : ℕ → ℝ) (x : ℕ → Site d) (hR : Tendsto R atTop atTop)
    (M : ℝ) (hM : ∀ n, dist (Lclt.scaledSite (R n) (x n)) 0 ≤ M) :
    IsTightMeasureSet (Set.range fun n =>
      Measure.map (diffusiveWalkPath (R n)) (walkLaw d (x n))) := by
  classical
  let : NeZero d := ⟨by omega⟩
  let μ : ℕ → Measure C(ℝ≥0, Continuum.Space d) := fun n =>
    Measure.map (diffusiveWalkPath (R n)) (walkLaw d (x n))
  let : ∀ n, IsProbabilityMeasure (μ n) := fun n => by
    change IsProbabilityMeasure (Measure.map (diffusiveWalkPath (R n)) (walkLaw d (x n)))
    exact (Measure.isProbabilityMeasure_map_iff (measurable_diffusiveWalkPath (R n)).aemeasurable).2
      (by change IsProbabilityMeasure (LatticeProb.siteWalkLaw d (x n)); infer_instance)
  change IsTightMeasureSet (Set.range μ)
  apply LatticeProb.isTightMeasureSet_of_pathModuli (Set.range μ) (0 : Continuum.Space d)
  · intro ζ hζ
    refine ⟨M, ?_⟩
    rintro ν ⟨n, rfl⟩
    change (Measure.map (diffusiveWalkPath (R n)) (walkLaw d (x n))) _ ≤ _
    rw [measure_diffusiveWalkPath_start_far hd (x n) (R n) M 0 (hM n)]
    exact bot_le
  · intro L hL
    obtain ⟨δ₀, R₀, hδ₀, hR₀, hsmall⟩ :=
      diffusiveWalk_modulus_small d hd L (1 / L) (1 / L) hL (by positivity) (by positivity)
    obtain ⟨N, hN⟩ := (eventually_atTop.1 (hR.eventually_ge_atTop R₀))
    have hprefix : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ n ∈ Finset.range N,
        μ n (LatticeProb.pathModulusFailure L δ.toNNReal) < ENNReal.ofReal (1 / L) := by
      apply (Filter.eventually_all_finset (Finset.range N)).2
      intro n _
      have hlimit := LatticeProb.tendsto_measure_pathModulusFailure (μ n) hL
      exact hlimit.eventually (Iio_mem_nhds (ENNReal.ofReal_pos.mpr (by positivity)))
    have hlt : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < (δ₀ : ℝ) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by exact_mod_cast hδ₀))
    have hpos : ∀ᶠ z : ℝ in 𝓝[>] 0, 0 < z := self_mem_nhdsWithin
    obtain ⟨z, hzpos, hzlt, hz⟩ := (hpos.and (hlt.and hprefix)).exists
    refine ⟨z.toNNReal, Real.toNNReal_pos.mpr hzpos, ?_⟩
    rintro ν ⟨n, rfl⟩
    by_cases hn : n < N
    · exact (hz n (Finset.mem_range.mpr hn)).le
    · have hδle : z.toNNReal ≤ δ₀ := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal z hzpos.le]
        exact hzlt.le
      calc
        μ n (LatticeProb.pathModulusFailure L z.toNNReal) ≤
            μ n (LatticeProb.pathModulusFailure L δ₀) :=
          measure_mono (LatticeProb.pathModulusFailure_mono_scale L hδle)
        _ ≤ ENNReal.ofReal (1 / L) := by
          change (Measure.map (diffusiveWalkPath (R n)) (walkLaw d (x n))) _ ≤ _
          rw [Measure.map_apply (measurable_diffusiveWalkPath (R n))
            (LatticeProb.isOpen_pathModulusFailure L δ₀).measurableSet]
          exact hsmall (R n) (hN n (by omega)) (x n)

end Sandpile.External.Stopping
