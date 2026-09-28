import Sandpile.Support.ExplHeatPrimitive

/-!
# Almost-Everywhere Space-Time Envelopes for the Gaussian Potential

This module upgrades a pointwise-in-space integrable envelope of a continuous
field into a joint space-time envelope valid for almost every point and almost
every noise sample. It first shows that a bound holding almost surely at each
fixed space-index `u`, for a field with continuous, jointly measurable time
sections, in fact holds for almost every pair `(u, ω)` and every time `t`
simultaneously (`ae_space_time_bound_of_continuous_sections`), by testing the
bound along a countable dense set of times and using continuity to pass to all
times. It then applies this to the Gaussian potential field to produce, for
almost every noise sample, a single spatially integrable function dominating
the field over any compact time interval
(`gaussianPotential_integrable_space_time_envelope`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace Sandpile.Support
open Sandpile.Continuum

/-- A bound `‖Z t u ω‖ ≤ D u ω` holding for almost every `ω` at each fixed `u` extends to a bound
holding simultaneously for almost every `(ω, u)` and every time `t`, provided `Z` has continuous
time-sections a.e. and is jointly measurable in `t`: the bound is first pushed through a countable
dense set of times via `Measure.ae_prod_iff_ae_ae`, then extended to all `t` by continuity. -/
theorem ae_space_time_bound_of_continuous_sections {E U Ω : Type*}
    [Nonempty E] [TopologicalSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace U] [MeasurableSpace Ω]
    (μ : Measure U) [SigmaFinite μ] (P : Measure Ω) [SigmaFinite P]
    (Z : E → U → Ω → ℝ) (D : U → Ω → ℝ)
    (hm : ∀ t, Measurable (fun p : U × Ω => Z t p.1 p.2))
    (hD : Measurable (Function.uncurry D))
    (hc : ∀ᵐ ω ∂P, ∀ u, Continuous (fun t => Z t u ω))
    (hb : ∀ u, ∀ᵐ ω ∂P, ∀ t, ‖Z t u ω‖ ≤ D u ω) :
    ∀ᵐ ω ∂P, ∀ᵐ u ∂μ, ∀ t, ‖Z t u ω‖ ≤ D u ω := by
  have hn (n : ℕ) : ∀ᵐ p : U × Ω ∂μ.prod P,
      ‖Z (TopologicalSpace.denseSeq E n) p.1 p.2‖ ≤ D p.1 p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le (hm _).norm hD)).mpr
    exact Eventually.of_forall fun u => (hb u).mono fun ω hω => hω _
  have hall : ∀ᵐ p : U × Ω ∂μ.prod P, ∀ n : ℕ,
      ‖Z (TopologicalSpace.denseSeq E n) p.1 p.2‖ ≤ D p.1 p.2 := ae_all_iff.mpr hn
  have hfull : ∀ᵐ p : U × Ω ∂μ.prod P, ∀ t, ‖Z t p.1 p.2‖ ≤ D p.1 p.2 := by
    filter_upwards [hall, Measure.quasiMeasurePreserving_snd.ae hc] with p hp hpc
    have he := (TopologicalSpace.denseRange_denseSeq E).equalizer
      ((hpc p.1).norm.min continuous_const) (hpc p.1).norm
      (funext fun n => min_eq_left (hp n))
    exact fun t => min_eq_left_iff.mp (congrFun he t)
  exact Measure.ae_ae_of_ae_prod
    ((Measure.measurePreserving_swap (μ := P) (ν := μ)).quasiMeasurePreserving.ae hfull)
/-- For any finite spatial measure, an integrable envelope bounds the continuous field at all
compact times. -/
theorem gaussianPotential_integrable_space_time_envelope {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (ν2 : ℝ) (Z : ℝ → Space d → Ω → ℝ)
    (hmod : ∀ t : ℝ, 0 ≤ t → ∀ x, Z t x =ᵐ[P] gaussianPotential d ν2 W t x)
    (hc : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P,
      ContinuousOn (fun q : ℝ × Space d => Z q.1 q.2 ω) (Set.Icc 0 T ×ˢ Set.univ))
    (μ : Measure (Space d)) [IsFiniteMeasure μ] {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∃ D : Space d → ℝ, Integrable D μ ∧
      ∀ᵐ x ∂μ, ∀ t ∈ Set.Icc 0 T, ‖Z t x ω‖ ≤ D x := by
  obtain ⟨Y, hY, hv, hYi⟩ := exists_joint_integrable_heat_noise hd hd3 hW
  let μt : Measure ℝ := volume.restrict (Set.Ioo 0 T)
  let F (p : ℝ × (Space d × Ω)) := Y (p.1, p.2.1) p.2.2
  have hF : StronglyMeasurable F := hY.comp_measurable
    (show Measurable (fun p : ℝ × (Space d × Ω) => ((p.1, p.2.1), p.2.2)) by fun_prop)
  have hFi : Integrable F (μt.prod (μ.prod P)) := by
    apply ((measurePreserving_prodAssoc μt μ P).integrable_comp hF.aestronglyMeasurable).mp
    exact hYi μ inferInstance T
  let D (x : Space d) (ω : Ω) := Real.sqrt ν2 * ∫ s in Set.Ioo 0 T, ‖Y (s, x) ω‖
  have hDi : Integrable (Function.uncurry D) (μ.prod P) :=
    hFi.integral_norm_prod_right.const_mul (Real.sqrt ν2)
  have hDm : Measurable (Function.uncurry D) :=
    measurable_const.mul hF.norm.integral_prod_left.measurable
  let E := Set.Icc (0 : ℝ) T
  letI : Nonempty E := ⟨⟨0, le_rfl, hT.le⟩⟩
  let ZK (q : E × Space d) (ω : Ω) := Z q.1 q.2 ω
  have hKm (q : E × Space d) : AEMeasurable (ZK q) P := by
    have hh : Measurable (gaussianPotential d ν2 W q.1 q.2) :=
      measurable_const.mul (hW.meas _ (memLp_greenTimeBM hd hd3 q.1.property.1 q.2))
    exact hh.aemeasurable.congr (hmod q.1 q.1.property.1 q.2).symm
  have hKc : ∀ᵐ ω ∂P, Continuous (fun q : E × Space d => ZK q ω) := by
    filter_upwards [hc T hT] with ω hω
    exact hω.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun q => ⟨q.1.property, Set.mem_univ _⟩)
  obtain ⟨X, hX, hXe⟩ := exists_joint_version_of_ae_continuous P ZK hKm hKc
  have hXm (t : E) : Measurable (fun p : Space d × Ω => X (t, p.1) p.2) :=
    hX.measurable.comp (show Measurable (fun p : Space d × Ω => ((t, p.1), p.2)) by fun_prop)
  have hXc : ∀ᵐ ω ∂P, ∀ x, Continuous (fun t : E => X (t, x) ω) := by
    filter_upwards [hXe, hKc] with ω he hω
    intro x
    have hh := hω.comp (show Continuous (fun t : E => (t, x)) by fun_prop)
    convert hh using 1
    funext t
    exact he (t, x)
  have hb (x : Space d) : ∀ᵐ ω ∂P, ∀ t : E, ‖X (t, x) ω‖ ≤ D x ω := by
    filter_upwards [hXe, (gaussianPotential_time_envelope hd hd3 hW Y hY hv ν2 Z hmod hc hT x).2]
      with ω he hω
    intro t
    rw [he (t, x)]
    exact hω t t.property
  have hall := ae_space_time_bound_of_continuous_sections μ P (fun t x ω => X (t, x) ω)
    D hXm hDm hXc hb
  filter_upwards [hDi.prod_left_ae, hall, hXe] with ω hi hb he
  refine ⟨fun x => D x ω, hi, ?_⟩
  filter_upwards [hb] with x hx
  intro t ht
  have hh := hx (⟨t, ht⟩ : E)
  rwa [he (⟨t, ht⟩, x)] at hh
end Sandpile.Support
