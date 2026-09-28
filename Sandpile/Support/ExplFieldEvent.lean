import Sandpile.Support.ExplFieldSemigroup

/-!
# Continuity lemmas and the common heat-semigroup event

Elementary continuity lemmas used to promote the heat-semigroup identity for the Gaussian
potential `gaussianPotential` from a fixed-parameter almost-everywhere statement to a single
event valid for all times and points: continuity under the integral sign from local dominated
envelopes, gluing strip-wise continuity to nonnegative times, and joint continuity of the
Brownian heat kernel `heatKernelBM` away from time `0`. Combining these with separability of
the parameter space and `ae_forall_eq_of_continuous_modifications` produces
`gaussianPotential_heat_semigroup_common_of_local_envelopes`, a single almost-sure event on
which the semigroup identity holds for every positive time and point, and
`gaussianPotential_increment_semigroup` derives from it the corresponding identity for
increments of the potential.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace Sandpile.Support
open Sandpile.Continuum

/-- Continuous modifications agree on one event over a separable parameter space. -/
theorem ae_forall_eq_of_continuous_modifications {E Ω : Type*}
    [Nonempty E] [TopologicalSpace E] [TopologicalSpace.SeparableSpace E] [MeasurableSpace Ω]
    (P : Measure Ω) (F G : E → Ω → ℝ)
    (hF : ∀ᵐ ω ∂P, Continuous fun x => F x ω)
    (hG : ∀ᵐ ω ∂P, Continuous fun x => G x ω)
    (hmod : ∀ x, F x =ᵐ[P] G x) :
    ∀ᵐ ω ∂P, ∀ x, F x ω = G x ω := by
  have he : ∀ᵐ ω ∂P, ∀ n : ℕ,
      F (TopologicalSpace.denseSeq E n) ω = G (TopologicalSpace.denseSeq E n) ω :=
    ae_all_iff.mpr fun n => hmod (TopologicalSpace.denseSeq E n)
  filter_upwards [hF, hG, he] with ω hFω hGω heω
  have hfg := (TopologicalSpace.denseRange_denseSeq E).equalizer hFω hGω (funext heω)
  exact fun x => congrFun hfg x

/-- If `F x` is a.e. strongly measurable for each `x`, `u ↦ F x u` is a.e. jointly continuous
in `x`, and every `x` has a neighborhood on which `F` is dominated by a fixed integrable
envelope `D`, then `x ↦ ∫ u, F x u ∂μ` is continuous. -/
theorem continuous_integral_of_local_envelopes {E U : Type*}
    [TopologicalSpace E] [FirstCountableTopology E] [MeasurableSpace U]
    (μ : Measure U) (F : E → U → ℝ)
    (hm : ∀ x, AEStronglyMeasurable (F x) μ)
    (hc : ∀ᵐ u ∂μ, Continuous fun x => F x u)
    (hdom : ∀ x : E, ∃ D : U → ℝ, Integrable D μ ∧
      ∀ᶠ y in 𝓝 x, ∀ᵐ u ∂μ, ‖F y u‖ ≤ D u) :
    Continuous fun x => ∫ u, F x u ∂μ := by
  apply continuous_iff_continuousAt.mpr
  intro x
  obtain ⟨D, hD, hb⟩ := hdom x
  exact continuousAt_of_dominated (Eventually.of_forall hm) hb hD
    (hc.mono fun u hu => hu.continuousAt)

/-- If `Z` is jointly continuous on every strip `[0, n+1] × Space d`, then its restriction to
nonnegative times `ℝ≥0 × Space d` is continuous, by patching the strips at each point using
the one strip that contains it. -/
theorem continuous_nonnegative_time_of_bounded_strips {d : ℕ}
    (Z : ℝ → Space d → ℝ)
    (hc : ∀ n : ℕ, ContinuousOn (fun q : ℝ × Space d => Z q.1 q.2)
      (Set.Icc 0 ((n : ℝ) + 1) ×ˢ Set.univ)) :
    Continuous (fun q : ℝ≥0 × Space d => Z q.1 q.2) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨n, hn⟩ := exists_nat_gt (q.1 : ℝ)
  have ht : Continuous (fun p : ℝ≥0 × Space d => (p.1 : ℝ)) := by fun_prop
  have hf : Continuous (fun p : ℝ≥0 × Space d => ((p.1 : ℝ), p.2)) := by fun_prop
  have hp : ContinuousOn (fun p : ℝ≥0 × Space d => Z p.1 p.2)
      {p | ((p.1 : ℝ), p.2) ∈ Set.Icc 0 ((n : ℝ) + 1) ×ˢ Set.univ} :=
    (hc n).comp hf.continuousOn (fun _ hp => hp)
  apply hp.continuousAt
  have hq : (q.1 : ℝ) < (n : ℝ) + 1 := by linarith
  have he := (isOpen_lt ht (continuous_const (y := (n : ℝ) + 1))).mem_nhds hq
  exact Filter.mem_of_superset he (fun p hp => ⟨⟨p.1.property, hp.le⟩, Set.mem_univ _⟩)

/-- For fixed `y`, the Brownian heat kernel `heatKernelBM d r x y` is jointly continuous in
`(r, x)` on `{r : ℝ // 0 < r} × Space d`, as it is built from continuous power, exponential,
and norm operations while `r` stays positive. -/
theorem continuous_heatKernelBM_positive {d : ℕ} (hd : 1 ≤ d) (y : Space d) :
    Continuous (fun q : {r : ℝ // 0 < r} × Space d => heatKernelBM d q.1.1 q.2 y) := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpi := Real.pi_pos
  have ht : Continuous (fun q : {r : ℝ // 0 < r} × Space d => q.1.1) :=
    continuous_subtype_val.comp continuous_fst
  have hb : Continuous (fun q : {r : ℝ // 0 < r} × Space d =>
      4 * Real.pi * q.1.1 / (2 * (d : ℝ))) := (continuous_const.mul ht).div_const _
  have h1 : Continuous (fun q : {r : ℝ // 0 < r} × Space d =>
      (4 * Real.pi * q.1.1 / (2 * (d : ℝ))) ^ (-(d : ℝ) / 2)) := by
    refine hb.rpow_const fun q => Or.inl ?_
    have := q.1.property
    exact ne_of_gt (by positivity)
  have hn : Continuous (fun q : {r : ℝ // 0 < r} × Space d =>
      -(d : ℝ) * ‖q.2 - y‖ ^ 2) := continuous_const.mul
        ((continuous_snd.sub continuous_const).norm.pow 2)
  have h2 : Continuous (fun q : {r : ℝ // 0 < r} × Space d =>
      Real.exp (-(d : ℝ) * ‖q.2 - y‖ ^ 2 / (2 * q.1.1))) := by
    refine Real.continuous_exp.comp (hn.div (continuous_const.mul ht) ?_)
    intro q
    have := q.1.property
    positivity
  exact h1.mul h2

/-- One noise event for every positive heat time, under local integrable envelopes. -/
theorem gaussianPotential_heat_semigroup_common_of_local_envelopes
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {P : Measure Ω} [IsProbabilityMeasure P] {W : (Space d → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise d W P) (ν2 : ℝ) (Z : ℝ → Space d → Ω → ℝ)
    (hmod : ∀ t : ℝ, 0 ≤ t → ∀ x, Z t x =ᵐ[P] gaussianPotential d ν2 W t x)
    (hc : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P,
      ContinuousOn (fun q : ℝ × Space d => Z q.1 q.2 ω) (Set.Icc 0 T ×ˢ Set.univ))
    (hdom : ∀ᵐ ω ∂P, ∀ q : {r : ℝ // 0 < r} × (ℝ≥0 × Space d),
      ∃ D : Space d → ℝ, Integrable D volume ∧
        ∀ᶠ p in 𝓝 q, ∀ᵐ y ∂volume,
          ‖heatKernelBM d p.1.1 p.2.2 y * Z p.2.1 y ω‖ ≤ D y) :
    ∀ᵐ ω ∂P, ∀ (r s : ℝ), 0 < r → 0 ≤ s → ∀ x : Space d,
      Integrable (fun y => heatKernelBM d r x y * Z s y ω) volume ∧
        (∫ y, heatKernelBM d r x y * Z s y ω) = Z (r + s) x ω - Z r x ω := by
  let E := {r : ℝ // 0 < r} × (ℝ≥0 × Space d)
  letI : Nonempty E := ⟨⟨⟨1, zero_lt_one⟩, 0, 0⟩⟩
  let F (q : E) (ω : Ω) := ∫ y, heatKernelBM d q.1.1 q.2.2 y * Z q.2.1 y ω
  let G (q : E) (ω : Ω) := Z (q.1.1 + q.2.1) q.2.2 ω - Z q.1.1 q.2.2 ω
  have hZ : ∀ᵐ ω ∂P, Continuous (fun q : ℝ≥0 × Space d => Z q.1 q.2 ω) := by
    have hn : ∀ᵐ ω ∂P, ∀ n : ℕ, ContinuousOn (fun q : ℝ × Space d => Z q.1 q.2 ω)
        (Set.Icc 0 ((n : ℝ) + 1) ×ˢ Set.univ) := ae_all_iff.mpr fun n => hc _ (by positivity)
    exact hn.mono fun ω hω => continuous_nonnegative_time_of_bounded_strips (fun t x => Z t x ω) hω
  have hmeas (ω : Ω) (hω : Continuous (fun q : ℝ≥0 × Space d => Z q.1 q.2 ω)) (q : E) :
      AEStronglyMeasurable (fun y => heatKernelBM d q.1.1 q.2.2 y * Z q.2.1 y ω) volume := by
    have hm : Measurable (heatKernelBM d q.1.1 q.2.2) := by unfold heatKernelBM; fun_prop
    exact (hm.mul (hω.comp (show Continuous (fun y : Space d => (q.2.1, y)) by
      fun_prop)).measurable).aestronglyMeasurable
  have hF : ∀ᵐ ω ∂P, Continuous (fun q => F q ω) := by
    filter_upwards [hZ, hdom] with ω hω hD
    apply continuous_integral_of_local_envelopes volume _ (hmeas ω hω) _ hD
    apply Eventually.of_forall
    intro y
    have hk := (continuous_heatKernelBM_positive hd y).comp
      (show Continuous (fun q : E => (q.1, q.2.2)) by fun_prop)
    have hz := hω.comp (show Continuous (fun q : E => (q.2.1, y)) by fun_prop)
    exact hk.mul hz
  have hG : ∀ᵐ ω ∂P, Continuous (fun q => G q ω) := by
    filter_upwards [hZ] with ω hω
    have h1 := hω.comp (show Continuous (fun q : E => (Real.toNNReal q.1.1 + q.2.1, q.2.2)) by
      dsimp [E]; fun_prop)
    have h2 := hω.comp (show Continuous (fun q : E => (Real.toNNReal q.1.1, q.2.2)) by
      dsimp [E]; fun_prop)
    convert h1.sub h2 using 1
    funext q
    simp only [G, Pi.sub_apply, Function.comp_apply, NNReal.coe_add,
      Real.coe_toNNReal _ q.1.property.le]
  have he : ∀ q : E, F q =ᵐ[P] G q := by
    intro q
    exact (gaussianPotential_heat_semigroup hd hd3 hW ν2 Z hmod hc
      q.1.property q.2.1.property q.2.2).mono
      fun ω hω => hω.2
  have hall := ae_forall_eq_of_continuous_modifications P F G hF hG he
  filter_upwards [hall, hZ, hdom] with ω hω hzc hD
  intro r s hr hs x
  let q : E := ⟨⟨r, hr⟩, ⟨s, hs⟩, x⟩
  obtain ⟨D, hi, hb⟩ := hD q
  exact ⟨hi.mono' (hmeas ω hzc q) hb.self_of_nhds, hω q⟩

/-- The heat semigroup identity for an increment of the Gaussian potential: almost surely, the
convolution of `heatKernelBM d r x` against `Z (s + δ) - Z s` is integrable and equals
`Z (r + s + δ) x - Z (r + s) x`, obtained by subtracting the semigroup identity at `s + δ` from
the one at `s`. -/
theorem gaussianPotential_increment_semigroup {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (ν2 : ℝ) (Z : ℝ → Space d → Ω → ℝ)
    (hmod : ∀ t : ℝ, 0 ≤ t → ∀ x, Z t x =ᵐ[P] gaussianPotential d ν2 W t x)
    (hc : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P,
      ContinuousOn (fun q : ℝ × Space d => Z q.1 q.2 ω) (Set.Icc 0 T ×ˢ Set.univ))
    {r s δ : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (hδ : 0 ≤ δ) (x : Space d) :
    ∀ᵐ ω ∂P, Integrable (fun y => heatKernelBM d r x y * (Z (s + δ) y ω - Z s y ω)) volume ∧
      (∫ y, heatKernelBM d r x y * (Z (s + δ) y ω - Z s y ω)) =
        Z (r + s + δ) x ω - Z (r + s) x ω := by
  filter_upwards [gaussianPotential_heat_semigroup hd hd3 hW ν2 Z hmod hc hr (add_nonneg hs hδ) x,
    gaussianPotential_heat_semigroup hd hd3 hW ν2 Z hmod hc hr hs x] with ω h1 h2
  simp_rw [mul_sub]
  refine ⟨h1.1.sub h2.1, ?_⟩
  rw [integral_sub h1.1 h2.1, h1.2, h2.2]
  rw [add_assoc]
  ring

end Sandpile.Support
