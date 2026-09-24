import Sandpile.Support.ExplHeatNoise
import Sandpile.Support.ExplFieldEvent
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace Sandpile.Support
open Sandpile.Continuum

theorem integrable_positive_heat_time_space {d : ℕ} (hd : 1 ≤ d)
    (T : ℝ) (x : Space d) :
    Integrable (fun q : ℝ × Space d => if 0 < q.1 then heatKernelBM d q.1 x q.2 else 0)
      ((volume.restrict (Set.Ioo 0 T)).prod volume) := by
  rcases le_or_gt T 0 with hT | hT
  · simp only [Set.Ioo_eq_empty (not_lt.mpr hT), Measure.restrict_empty, Measure.zero_prod, integrable_zero_measure]
  have hm : Measurable (fun q : ℝ × Space d => if 0 < q.1 then heatKernelBM d q.1 x q.2 else 0) := by
    apply Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    · unfold heatKernelBM
      fun_prop
    · exact measurable_const
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    simpa only [if_pos hs.1] using integrable_heatKernelBM_space hd hs.1 x
  · apply (integrable_const (1 : ℝ)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    simp only [if_pos hs.1, Real.norm_eq_abs,
      abs_of_nonneg (heatKernelBM_nonneg d hs.1.le x _), integral_heatKernelBM_eq_one hd hs.1 x]
/-- The time primitive of a joint heat-noise version is white noise applied to the Green kernel. -/
theorem whiteNoise_heat_primitive_eq {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (Y : (ℝ × Space d) → Ω → ℝ) (hY : StronglyMeasurable (Function.uncurry Y))
    (hv : ∀ q, Y q =ᵐ[P] W (fun y => if 0 < q.1 then heatKernelBM d q.1 q.2 y else 0))
    (T : ℝ) (hT : 0 ≤ T) (x : Space d) :
    Integrable (fun p : ℝ × Ω => Y (p.1, x) p.2) ((volume.restrict (Set.Ioo 0 T)).prod P) ∧
      W (greenTimeBM d T x) =ᵐ[P] fun ω => ∫ s in Set.Ioo 0 T, Y (s, x) ω := by
  obtain ⟨hf, hS, hI⟩ := positiveHeatKernel_family hd hd3
  let μ : Measure ℝ := volume.restrict (Set.Ioo 0 T)
  have hF : Integrable (fun s => (hf (s, x)).toLp
      (fun y => if 0 < s then heatKernelBM d s x y else 0)) μ := by
    have hh := (hI (Measure.dirac x) inferInstance T).prod_left_ae
    simpa only [ae_dirac_eq, Filter.eventually_pure] using hh
  have hYs : StronglyMeasurable (fun p : ℝ × Ω => Y (p.1, x) p.2) :=
    hY.comp_measurable (show Measurable (fun p : ℝ × Ω => ((p.1, x), p.2)) by fun_prop)
  have hmain := whiteNoise_integral_comm_of_version hW μ
    (fun s y => if 0 < s then heatKernelBM d s x y else 0) (fun s => hf (s, x)) hF
    (fun s ω => Y (s, x) ω) hYs (fun s => hv (s, x))
  have hrep := coe_integral_L2_eq_integral_of_integrable μ volume
    (fun s => (hf (s, x)).toLp (fun y => if 0 < s then heatKernelBM d s x y else 0)) hF
    (fun s y => if 0 < s then heatKernelBM d s x y else 0)
    (integrable_positive_heat_time_space hd T x) (fun s => (hf (s, x)).coeFn_toLp.symm)
  have he (y : Space d) : (∫ s, (if 0 < s then heatKernelBM d s x y else 0) ∂μ) = greenTimeBM d T x y := by
    calc (∫ s, (if 0 < s then heatKernelBM d s x y else 0) ∂μ)
        = ∫ s in Set.Ioo 0 T, heatKernelBM d s x y := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
          exact if_pos hs.1
      _ = greenTimeBM d T x y := by
          rw [greenTimeBM, intervalIntegral.integral_of_le hT, integral_Ioc_eq_integral_Ioo]
  have hidx := whiteNoise_index_congr hW (Lp.memLp _) (hrep.trans (Eventually.of_forall he))
  exact ⟨hmain.1, hidx.symm.trans hmain.2⟩
/-- At each spatial point, one integrable envelope bounds the continuous potential on a compact time interval. -/
theorem gaussianPotential_time_envelope {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (Y : (ℝ × Space d) → Ω → ℝ) (hY : StronglyMeasurable (Function.uncurry Y))
    (hv : ∀ q, Y q =ᵐ[P] W (fun y => if 0 < q.1 then heatKernelBM d q.1 q.2 y else 0))
    (ν2 : ℝ) (Z : ℝ → Space d → Ω → ℝ)
    (hmod : ∀ t : ℝ, 0 ≤ t → ∀ x, Z t x =ᵐ[P] gaussianPotential d ν2 W t x)
    (hc : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂P,
      ContinuousOn (fun q : ℝ × Space d => Z q.1 q.2 ω) (Set.Icc 0 T ×ˢ Set.univ))
    {T : ℝ} (hT : 0 < T) (x : Space d) :
    Integrable (fun ω => Real.sqrt ν2 * ∫ s in Set.Ioo 0 T, ‖Y (s, x) ω‖) P ∧
      ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc 0 T,
        ‖Z t x ω‖ ≤ Real.sqrt ν2 * ∫ s in Set.Ioo 0 T, ‖Y (s, x) ω‖ := by
  have hmain := whiteNoise_heat_primitive_eq hd hd3 hW Y hY hv T hT.le x
  let D (ω : Ω) := Real.sqrt ν2 * ∫ s in Set.Ioo 0 T, ‖Y (s, x) ω‖
  refine ⟨hmain.1.integral_norm_prod_right.const_mul (Real.sqrt ν2), ?_⟩
  let E := Set.Icc (0 : ℝ) T
  letI : Nonempty E := ⟨⟨0, le_rfl, hT.le⟩⟩
  have hbound (t : E) : ∀ᵐ ω ∂P, ‖Z t x ω‖ ≤ D ω := by
    filter_upwards [hmod t t.property.1 x,
      (whiteNoise_heat_primitive_eq hd hd3 hW Y hY hv t t.property.1 x).2,
      hmain.1.prod_left_ae] with ω hz hy hi
    rw [hz]
    unfold gaussianPotential
    rw [hy, norm_mul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg ν2)
    apply (norm_integral_le_integral_norm _).trans
    apply setIntegral_mono_set hi.norm (Eventually.of_forall fun _ => norm_nonneg _) _
    exact Eventually.of_forall fun s hs => ⟨hs.1, hs.2.trans_le t.property.2⟩
  have hzc : ∀ᵐ ω ∂P, Continuous (fun t : E => Z t x ω) := by
    filter_upwards [hc T hT] with ω hω
    exact hω.comp_continuous (show Continuous (fun t : E => ((t : ℝ), x)) by dsimp [E]; fun_prop)
      (fun t => ⟨t.property, Set.mem_univ _⟩)
  have he := ae_forall_eq_of_continuous_modifications P
    (fun t : E => fun ω => min ‖Z t x ω‖ (D ω)) (fun t : E => fun ω => ‖Z t x ω‖)
    (hzc.mono fun ω hω => hω.norm.min continuous_const) (hzc.mono fun ω hω => hω.norm)
    (fun t => (hbound t).mono fun ω hω => min_eq_left hω)
  filter_upwards [he] with ω hω
  intro t ht
  exact min_eq_left_iff.mp (hω ⟨t, ht⟩)
end Sandpile.Support
