/-
From a coupling at every scale to convergence in distribution.

The parabolic scaling limit of `thm:main-explosion`(i)(b) is produced by
`Sandpile.dlt4_scaling_of_inputs` in COUPLING form: for every accuracy and every
probability there is a threshold beyond which the rescaled odometer and the
Brownian value can be realized on one space so that they differ by more than the
accuracy with probability at most the one prescribed.  The frozen statement asks
for weak convergence.  This module is the bridge, and it is the quantitative half
of the Portmanteau theorem read in the easy direction.

For a closed set `F`, a coupling with error `(ε, δ)` gives
`μ_R(F) ≤ ν(F^ε) + δ`, because on the event that the two are within `ε` the first
lying in `F` forces the second into the closed `ε`-thickening.  Letting `δ → 0`
and then `ε → 0`, and using that the measure of the closed thickening of a closed
set tends to the measure of the set, gives `limsup_R μ_R(F) ≤ ν(F)`, which is one
of the equivalent formulations of weak convergence.

This is the converse of `Sandpile.Continuum.exists_coupling_close_of_tendstoInDistribution`,
which the repository already has and which the killed route used in the other
direction.
-/
import Sandpile.Support.StopWeakCoupling

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace Sandpile.Continuum

variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
  {ΩA ΩB : Type*} [MeasurableSpace ΩA] [MeasurableSpace ΩB]

/-- **A coupling bounds the law of a set by the law of its closed thickening.**  If the
two variables differ by more than `ε` with probability at most `δ` under a coupling of
`μ` and `ν`, then the `μ`-law of any set is at most the `ν`-law of its closed
`ε`-thickening plus `δ`. -/
theorem map_le_map_cthickening_of_coupling
    (μ : Measure ΩA) (ν : Measure ΩB)
    (X : ΩA → E) (Y : ΩB → E) (hX : AEMeasurable X μ) (hY : AEMeasurable Y ν)
    (P : Measure (ΩA × ΩB)) (hf : P.map Prod.fst = μ) (hs : P.map Prod.snd = ν)
    (ε δ : ℝ) (hbad : P {p | ε < dist (X p.1) (Y p.2)} ≤ ENNReal.ofReal δ)
    (F : Set E) (hF : MeasurableSet F) :
    μ.map X F ≤ ν.map Y (Metric.cthickening ε F) + ENNReal.ofReal δ := by
  classical
  have hthick : MeasurableSet (Metric.cthickening ε F) :=
    (Metric.isClosed_cthickening (δ := ε) (E := F)).measurableSet
  have hsub : (Prod.fst ⁻¹' (X ⁻¹' F) : Set (ΩA × ΩB)) ⊆
      (Prod.snd ⁻¹' (Y ⁻¹' Metric.cthickening ε F)) ∪ {p | ε < dist (X p.1) (Y p.2)} := by
    intro p hp
    by_cases hd : ε < dist (X p.1) (Y p.2)
    · exact Or.inr hd
    · refine Or.inl ?_
      have hle : dist (Y p.2) (X p.1) ≤ ε := by
        rw [dist_comm]
        exact not_lt.mp hd
      have : Y p.2 ∈ Metric.cthickening ε F :=
        Metric.mem_cthickening_of_dist_le _ _ ε F hp hle
      exact this
  calc μ.map X F = P (Prod.fst ⁻¹' (X ⁻¹' F)) := by
        rw [Measure.map_apply_of_aemeasurable hX hF, ← hf,
          Measure.map_apply₀ measurable_fst.aemeasurable
            (by simpa only [hf] using hX.nullMeasurableSet_preimage hF)]
    _ ≤ P ((Prod.snd ⁻¹' (Y ⁻¹' Metric.cthickening ε F)) ∪
          {p | ε < dist (X p.1) (Y p.2)}) := measure_mono hsub
    _ ≤ P (Prod.snd ⁻¹' (Y ⁻¹' Metric.cthickening ε F)) +
          P {p | ε < dist (X p.1) (Y p.2)} := measure_union_le _ _
    _ ≤ ν.map Y (Metric.cthickening ε F) + ENNReal.ofReal δ := by
        refine add_le_add (le_of_eq ?_) hbad
        rw [Measure.map_apply_of_aemeasurable hY hthick, ← hs,
          Measure.map_apply₀ measurable_snd.aemeasurable
            (by simpa only [hs] using hY.nullMeasurableSet_preimage hthick)]

/-- **Convergence in distribution from a coupling at every scale.**  If for every
accuracy and every probability there is a threshold beyond which `X R` and `Y` can be
coupled so that they differ by more than the accuracy with probability at most the
prescribed one, then `X R` converges to `Y` in distribution. -/
theorem tendstoInDistribution_of_coupling [BorelSpace E]
    (μ : Measure ΩA) [IsProbabilityMeasure μ] (ν : Measure ΩB) [IsProbabilityMeasure ν]
    (X : ℝ → ΩA → E) (Y : ΩB → E) (hX : ∀ R : ℝ, AEMeasurable (X R) μ) (hY : AEMeasurable Y ν)
    (h : ∀ ε δ : ℝ, 0 < ε → 0 < δ → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
      ∃ P : Measure (ΩA × ΩB), IsProbabilityMeasure P ∧
        P.map Prod.fst = μ ∧ P.map Prod.snd = ν ∧
        P {p | ε < dist (X R p.1) (Y p.2)} ≤ ENNReal.ofReal δ) :
    TendstoInDistribution X atTop Y (fun _ => μ) ν := by
  classical
  refine ⟨hX, hY, ?_⟩
  refine MeasureTheory.tendsto_of_forall_isClosed_limsup_le' ?_
  intro F hF
  have hstep : ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      limsup (fun R : ℝ => (μ.map (X R)) F) atTop
        ≤ (ν.map Y) (Metric.cthickening ε F) + ENNReal.ofReal δ := by
    intro ε δ hε hδ
    obtain ⟨R₀, hR₀⟩ := h ε δ hε hδ
    refine limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [eventually_ge_atTop R₀] with R hR
    obtain ⟨P, hP, hf, hs, hbad⟩ := hR₀ R hR
    exact map_le_map_cthickening_of_coupling μ ν (X R) Y (hX R) hY P hf hs ε δ hbad F
      hF.measurableSet
  have hthin : ∀ ε : ℝ, 0 < ε →
      limsup (fun R : ℝ => (μ.map (X R)) F) atTop ≤ (ν.map Y) (Metric.cthickening ε F) := by
    intro ε hε
    refine ENNReal.le_of_forall_pos_le_add ?_
    intro δ hδ _
    exact le_trans (hstep ε δ hε (by exact_mod_cast hδ))
      (by gcongr; exact le_of_eq (by simp [ENNReal.ofReal_coe_nnreal]))
  haveI : IsProbabilityMeasure (ν.map Y) :=
    MeasureTheory.Measure.isProbabilityMeasure_map hY
  have hlim : Filter.Tendsto (fun ε : ℝ => (ν.map Y) (Metric.cthickening ε F)) (𝓝[>] 0)
      (𝓝 ((ν.map Y) F)) :=
    (_root_.tendsto_measure_cthickening_of_isClosed
      ⟨1, by norm_num, measure_ne_top _ _⟩ hF).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hthin ε hε

end Sandpile.Continuum
