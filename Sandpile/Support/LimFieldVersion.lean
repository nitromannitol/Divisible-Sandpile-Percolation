/-
A measurable version of an almost surely continuous field.

The chaining bound on a box asks for a field that is measurable in the sample point at
every parameter and continuous in the parameter at *every* sample point.  The fields of
the crossing argument are the other way round: they are almost surely continuous in the
parameter, because they are built from the heat potential, but at a fixed parameter they
are only almost surely equal to a measurable function, because `ContinuousHeatPotential`
carries no measurability.  A modification fixes this without assuming anything new: on
the almost sure event where the field is continuous and agrees, at every point of a fixed
countable dense set, with the measurable field it is a modification of, the value at an
arbitrary parameter is the limit along that dense set, hence a countable `limsup` of
measurable functions; off that event the modification is set to zero, which is continuous
too.
-/
import Mathlib

open MeasureTheory Filter Topology

namespace Sandpile.Support

/-- **A field that is almost surely continuous, and at each parameter almost surely equal
to a measurable one, has a modification which is measurable at every parameter and
continuous at every sample point.** -/
theorem exists_measurable_continuous_version {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {E : Type*} [MetricSpace E] [TopologicalSpace.SeparableSpace E]
    (F X : E → Ω → ℝ) (hX : ∀ u, Measurable (X u))
    (hae : ∀ u, F u =ᵐ[P] X u)
    (hcont : ∀ᵐ ω ∂P, Continuous fun u => F u ω) :
    ∃ Y : E → Ω → ℝ, (∀ u, Measurable (Y u)) ∧ (∀ ω, Continuous fun u => Y u ω) ∧
      ∀ᵐ ω ∂P, ∀ u, Y u ω = F u ω := by
  classical
  obtain ⟨S, hScount, hSdense⟩ := TopologicalSpace.exists_countable_dense E
  -- the exceptional sets
  have hnull : ∀ v : E, ∃ N : Set Ω, {ω | ¬ F v ω = X v ω} ⊆ N ∧ MeasurableSet N ∧ P N = 0 :=
    fun v => exists_measurable_superset_of_null (hae v)
  choose N hNsub hNmeas hNnull using hnull
  obtain ⟨Nc, hNcsub, hNcmeas, hNcnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hcont)
  set Bad : Set Ω := (⋃ v ∈ S, N v) ∪ Nc with hBaddef
  have hBadmeas : MeasurableSet Bad :=
    (MeasurableSet.biUnion hScount fun v _ => hNmeas v).union hNcmeas
  have hBadnull : P Bad = 0 := by
    refine measure_union_null ?_ hNcnull
    exact (measure_biUnion_null_iff hScount).mpr fun v _ => hNnull v
  -- a sequence in the dense set converging to each parameter
  have hseq : ∀ (u : E) (n : ℕ), ∃ w ∈ S, dist u w < 1 / ((n : ℝ) + 1) := by
    intro u n
    exact hSdense.exists_dist_lt u (by positivity)
  choose v hvS hvdist using hseq
  have hvtend : ∀ u : E, Tendsto (fun n => v u n) atTop (𝓝 u) := by
    intro u
    refine Metric.tendsto_atTop.2 fun ε hε => ?_
    obtain ⟨n₀, hn₀⟩ := exists_nat_gt (1 / ε)
    refine ⟨n₀, fun n hn => ?_⟩
    have h1 : dist u (v u n) < 1 / ((n : ℝ) + 1) := hvdist u n
    have h2 : 1 / ((n : ℝ) + 1) ≤ 1 / ((n₀ : ℝ) + 1) := by
      have hn' : (n₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hpos : (0 : ℝ) < (n₀ : ℝ) + 1 := by positivity
      exact one_div_le_one_div_of_le hpos (by linarith)
    have h3 : 1 / ((n₀ : ℝ) + 1) < ε := by
      have hpos : (0 : ℝ) < (n₀ : ℝ) + 1 := by positivity
      rw [div_lt_iff₀ hpos]
      have h4 : 1 / ε < (n₀ : ℝ) := hn₀
      rw [div_lt_iff₀ hε] at h4
      nlinarith
    rw [dist_comm]
    linarith
  -- the key identification on the good event
  have hkey : ∀ ω ∈ Badᶜ, ∀ u : E, limsup (fun n => X (v u n) ω) atTop = F u ω := by
    intro ω hω u
    have hcontω : Continuous fun u => F u ω := by
      by_contra hc
      exact hω (Or.inr (hNcsub hc))
    have hXF : ∀ n, X (v u n) ω = F (v u n) ω := by
      intro n
      by_contra hne
      refine hω (Or.inl ?_)
      refine Set.mem_biUnion (hvS u n) (hNsub (v u n) ?_)
      exact fun h => hne h.symm
    have htend : Tendsto (fun n => X (v u n) ω) atTop (𝓝 (F u ω)) := by
      have h1 : Tendsto (fun n => F (v u n) ω) atTop (𝓝 (F u ω)) :=
        (hcontω.tendsto u).comp (hvtend u)
      refine h1.congr fun n => (hXF n).symm
    exact htend.limsup_eq
  refine ⟨fun u => Set.indicator Badᶜ (fun ω => limsup (fun n => X (v u n) ω) atTop), ?_, ?_, ?_⟩
  · intro u
    exact (Measurable.limsup fun n => hX (v u n)).indicator hBadmeas.compl
  · intro ω
    by_cases hω : ω ∈ Badᶜ
    · have hcontω : Continuous fun u => F u ω := by
        by_contra hc
        exact hω (Or.inr (hNcsub hc))
      refine hcontω.congr fun u => ?_
      show F u ω = Set.indicator Badᶜ (fun ω => limsup (fun n => X (v u n) ω) atTop) ω
      rw [Set.indicator_of_mem hω]
      exact (hkey ω hω u).symm
    · have hzero : ∀ u : E,
          Set.indicator Badᶜ (fun ω => limsup (fun n => X (v u n) ω) atTop) ω = 0 := by
        intro u
        exact Set.indicator_of_notMem hω _
      simpa only [hzero] using continuous_const
  · have hfull : ∀ᵐ ω ∂P, ω ∈ Badᶜ := by
      rw [ae_iff]
      simpa using hBadnull
    filter_upwards [hfull] with ω hω u
    rw [Set.indicator_of_mem hω]
    exact hkey ω hω u

end Sandpile.Support
