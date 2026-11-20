import Sandpile.External.Stopping.AdaptedThresholdClock
import Mathlib.Probability.Kernel.Representation
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Adapted quantiles of probability kernels

The inverse distribution construction represents a probability kernel on a
bounded interval by a uniform random parameter. If its distribution functions
are adapted, the resulting random clock is adapted as well. This is the
randomization step in Coquet and Toldo, Section 2.3.1.
-/

open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped NNReal ENNReal Topology

namespace Sandpile.External.Stopping

/-- A decreasing quantile of a probability measure on the unit interval. -/
noncomputable def clockQuantile (μ : Measure I) (u : I) : I :=
  sSup {t | μ.real (Icc 0 t) < u}

/-- The quantile event is the corresponding distribution-function threshold. -/
theorem clockQuantile_le_iff (μ : Measure I) [IsProbabilityMeasure μ] (u t : I) :
    clockQuantile μ u ≤ t ↔ (u : ℝ) ≤ μ.real (Icc 0 t) := by
  have hmono : Monotone (fun x : I => μ.real (Icc 0 x)) :=
    fun x y hxy => measureReal_mono (by gcongr)
  constructor
  · intro h
    by_cases ht : t = 1
    · simp [ht, ← univ_eq_Icc, u.2.2]
    let g := fun y : I => μ.real (Icc 0 y)
    let nebot : NeBot (𝓝[>] t) := by
      refine nhdsGT_neBot_of_exists_gt ?_
      exact ⟨1, lt_of_le_of_ne t.2.2 ht⟩
    refine le_of_tendsto_of_tendsto (b := 𝓝[>] t) (g := g)
      continuousWithinAt_const ?_ ?_
    · let H := cdf (μ.map Subtype.val)
      have hH := continuousWithinAt_Ioi_iff_Ici.mpr (H.right_continuous t)
      simp_rw [g, ← unitInterval.cdf_eq_real μ]
      exact hH.comp (Continuous.continuousWithinAt (by fun_prop)) (fun y hy => hy)
    · refine eventually_nhdsWithin_of_forall fun y hy => ?_
      by_contra! hyu
      simp only [clockQuantile, sSup_le_iff] at h
      specialize h y hyu
      exact (not_lt_of_ge h) hy
  · intro h
    simp only [clockQuantile, sSup_le_iff]
    intro y hy
    by_contra! hty
    exact (not_le_of_gt (lt_of_lt_of_le hy h)) (hmono hty.le)

/-- The quantile of a probability kernel is jointly measurable and has the
specified conditional law for every parameter. -/
theorem clockQuantile_kernel
    {Ω : Type*} [MeasurableSpace Ω] (κ : Kernel Ω I) [IsMarkovKernel κ] :
    Measurable (fun p : Ω × I => clockQuantile (κ p.1) p.2) ∧
      ∀ ω, volume.map (clockQuantile (κ ω)) = κ ω := by
  have hmeas : Measurable (fun p : Ω × I => clockQuantile (κ p.1) p.2) := by
    refine measurable_of_Iic fun t => ?_
    have heq : {p : Ω × I | clockQuantile (κ p.1) p.2 ≤ t} =
        {p : Ω × I | (p.2 : ℝ) ≤ (κ p.1).real (Icc 0 t)} := by
      ext p
      exact clockQuantile_le_iff _ _ _
    change MeasurableSet {p : Ω × I | clockQuantile (κ p.1) p.2 ≤ t}
    rw [heq]
    refine measurableSet_le measurable_snd.subtype_val ?_
    simp_rw [measureReal_def]
    exact ((κ.measurable_coe measurableSet_Icc).comp measurable_fst).ennreal_toReal
  refine ⟨hmeas, fun ω => ?_⟩
  apply Measure.ext_of_Iic
  intro t
  have ht : ((κ ω).real (Icc 0 t)) ∈ I := ⟨measureReal_nonneg, measureReal_le_one⟩
  have hsection : Measurable (clockQuantile (κ ω)) :=
    hmeas.comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hsection measurableSet_Iic]
  have heq : clockQuantile (κ ω) ⁻¹' Iic t = Iic ⟨_, ht⟩ := by
    ext u
    exact clockQuantile_le_iff _ _ _
  rw [heq, unitInterval.volume_Iic, ofReal_measureReal (measure_ne_top (κ ω) _)]
  congr 1
  ext u
  simp

/-- Sampling the quantile with an independent uniform parameter realizes the
joint law given by the composition of a marginal and a kernel. -/
theorem map_clockQuantile_prod
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (κ : Kernel Ω I) [IsMarkovKernel κ] :
    (P.prod volume).map (fun p : Ω × I => (p.1, clockQuantile (κ p.1) p.2)) =
      P ⊗ₘ κ := by
  have hquant := (clockQuantile_kernel κ).1
  have hmap : Measurable (fun p : Ω × I => (p.1, clockQuantile (κ p.1) p.2)) :=
    measurable_fst.prodMk hquant
  ext s hs
  rw [Measure.map_apply hmap hs, Measure.prod_apply (hs.preimage hmap),
    Measure.compProd_apply hs]
  apply lintegral_congr
  intro ω
  have hsection : Measurable (clockQuantile (κ ω)) :=
    hquant.comp (measurable_const.prodMk measurable_id)
  have hset : MeasurableSet (Prod.mk ω ⁻¹' s) := hs.preimage measurable_prodMk_left
  have h := congrArg (fun μ : Measure I => μ (Prod.mk ω ⁻¹' s))
    ((clockQuantile_kernel κ).2 ω)
  rw [Measure.map_apply hsection hset] at h
  exact h

/-- Adapted distribution functions produce stopping-clock events in the
product of the parameter and observation sigma-algebras. -/
theorem clockQuantile_adapted
    {Ω : Type*} {m : MeasurableSpace Ω} (F : Filtration I m)
    (κ : @Kernel Ω I m inferInstance) [IsMarkovKernel κ]
    (hκ : ∀ t, @Measurable Ω ℝ (F t) inferInstance
      (fun ω => (κ ω).real (Icc 0 t))) :
    ∀ t, MeasurableSet[(F t).prod inferInstance]
      {p : Ω × I | clockQuantile (κ p.1) p.2 ≤ t} := by
  intro t
  have heq : {p : Ω × I | clockQuantile (κ p.1) p.2 ≤ t} =
      {p : Ω × I | (p.2 : ℝ) ≤ (κ p.1).real (Icc 0 t)} := by
    ext p
    exact clockQuantile_le_iff _ _ _
  rw [heq]
  exact measurableSet_le measurable_snd.subtype_val ((hκ t).comp measurable_fst)

end Sandpile.External.Stopping
