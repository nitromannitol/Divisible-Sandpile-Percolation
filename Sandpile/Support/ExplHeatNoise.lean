import Sandpile.Support.ExplFieldSemigroup

/-!
# `L²` bounds for the heat kernel and a single joint heat-noise version

`memLp_heatKernelBM` records that the spatial heat kernel `heatKernelBM d s x` lies in
`L²(ℝ^d)` for every positive time `s`, since its square is integrable by the semigroup
identity `integrable_heatKernelBM_mul_space`. `exists_norm_heatKernelBM_toLp_le` bounds the
`L²` norm of that kernel by a constant times `s^{-d/4}`, using the diagonal semigroup value
`heatKernelBM d (s+s) x x` and the bound `heatKernelBM_diag_add_le`. `positiveHeatKernel_family`
packages the kernel as a strongly measurable, jointly integrable family indexed by `(t,x)` for
dimension at most three, so that `IsWhiteNoise.jointMeas_univ` can be applied to it; this is
what `exists_joint_integrable_heat_noise` does, producing a single strongly measurable version
`Y` of the white noise integrated against the heat kernel that is jointly integrable in time,
space and the probability variable over every bounded time window and finite spatial measure.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace
namespace Sandpile.Support
open Sandpile.Continuum

/-- The spatial heat kernel `heatKernelBM d s x` lies in `L²(ℝ^d)` for every `s > 0`: its
square is integrable by the heat-semigroup identity at the doubled time `s+s`. -/
theorem memLp_heatKernelBM {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s)
    (x : Space d) : MemLp (heatKernelBM d s x) 2 (volume : Measure (Space d)) := by
  have hm : AEStronglyMeasurable (heatKernelBM d s x) (volume : Measure (Space d)) := by
    have h : Measurable (heatKernelBM d s x) := by unfold heatKernelBM; fun_prop
    exact h.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hm]
  simpa only [pow_two] using integrable_heatKernelBM_mul_space hd hs hs x

/-- The `L²` norm of the heat kernel `heatKernelBM d s x`, viewed as an `Lp` element, is
bounded by a constant multiple of `s^{-d/4}`, uniformly in `s > 0` and the centre `x`; the
constant comes from the diagonal semigroup bound `heatKernelBM_diag_add_le` on
`heatKernelBM d (s+s) x x`, which computes the squared norm exactly. -/
theorem exists_norm_heatKernelBM_toLp_le {d : ℕ} (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℝ) (hs : 0 < s) (x : Space d),
      ‖(memLp_heatKernelBM hd hs x).toLp (heatKernelBM d s x)‖ ≤
        C * s ^ (-(d : ℝ) / 4) := by
  let K : ℝ := (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) * 2 ^ (-(d : ℝ) / 2)
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpi := Real.pi_pos
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨Real.sqrt K, Real.sqrt_pos.mpr hK, ?_⟩
  intro s hs x
  let f := (memLp_heatKernelBM hd hs x).toLp (heatKernelBM d s x)
  have he : ‖f‖ ^ 2 = heatKernelBM d (s + s) x x := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    calc (∫ y, inner ℝ (f y) (f y)) = ∫ y, heatKernelBM d s x y * heatKernelBM d s x y := by
          apply integral_congr_ae
          filter_upwards [(memLp_heatKernelBM hd hs x).coeFn_toLp] with y hy
          simp only [RCLike.inner_apply, conj_trivial, f, hy]
      _ = heatKernelBM d (s + s) x x := integral_heatKernelBM_mul hd hs hs x
  have hb := heatKernelBM_diag_add_le hd hs hs x
  change heatKernelBM d (s + s) x x ≤ K * (s ^ (-(d : ℝ) / 4) * s ^ (-(d : ℝ) / 4)) at hb
  have hsq : (Real.sqrt K * s ^ (-(d : ℝ) / 4)) ^ 2 =
      K * (s ^ (-(d : ℝ) / 4) * s ^ (-(d : ℝ) / 4)) := by
    rw [mul_pow, Real.sq_sqrt hK.le, pow_two]
  have hn : 0 ≤ Real.sqrt K * s ^ (-(d : ℝ) / 4) := by positivity
  change ‖f‖ ≤ _
  nlinarith [norm_nonneg f]
/-- The positive-time heat kernel is an integrable family of spatial `L²` indices below
dimension four. -/
theorem positiveHeatKernel_family {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) :
    ∃ hf : ∀ q : ℝ × Space d,
        MemLp (fun y => if 0 < q.1 then heatKernelBM d q.1 q.2 y else 0) 2 volume,
      StronglyMeasurable (fun q => (hf q).toLp
        (fun y => if 0 < q.1 then heatKernelBM d q.1 q.2 y else 0)) ∧
      ∀ (μ : Measure (Space d)), IsFiniteMeasure μ → ∀ T : ℝ,
        Integrable (fun q => (hf q).toLp (fun y => if 0 < q.1 then heatKernelBM d q.1 q.2 y else 0))
          ((volume.restrict (Set.Ioo 0 T)).prod μ) := by
  classical
  have hf (q : ℝ × Space d) :
      MemLp (fun y => if 0 < q.1 then heatKernelBM d q.1 q.2 y else 0) 2 volume := by
    by_cases h : 0 < q.1
    · simpa only [if_pos h] using memLp_heatKernelBM hd h q.2
    · simp only [if_neg h]
      exact MemLp.zero'
  have hm : Measurable (fun q : (ℝ × Space d) × Space d =>
      if 0 < q.1.1 then heatKernelBM d q.1.1 q.1.2 q.2 else 0) := by
    apply Measurable.ite (measurableSet_lt measurable_const (measurable_fst.comp measurable_fst))
    · unfold heatKernelBM
      fun_prop
    · exact measurable_const
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  have hS := stronglyMeasurable_toLp_of_uncurry volume
    (fun q : ℝ × Space d => fun y => if 0 < q.1 then heatKernelBM d q.1 q.2 y else 0) hf hm
  refine ⟨hf, hS, ?_⟩
  intro μ hμ T
  letI := hμ
  rcases le_or_gt T 0 with hT | hT
  · simp only [Set.Ioo_eq_empty (not_lt.mpr hT), Measure.restrict_empty, Measure.zero_prod,
      integrable_zero_measure]
  obtain ⟨C, hC, hbound⟩ := exists_norm_heatKernelBM_toLp_le hd
  have hp : (-1 : ℝ) < -(d : ℝ) / 4 := by
    have : (d : ℝ) ≤ 3 := by exact_mod_cast hd3
    linarith
  have hI : IntegrableOn (fun s : ℝ => s ^ (-(d : ℝ) / 4)) (Set.Ioo 0 T) volume := by
    have h := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := T) hp
    rwa [intervalIntegrable_iff_integrableOn_Ioo_of_le hT.le] at h
  have hD : Integrable (fun q : ℝ × Space d => C * q.1 ^ (-(d : ℝ) / 4))
      ((volume.restrict (Set.Ioo 0 T)).prod μ) := by
    simpa only [mul_one] using (hI.const_mul C).mul_prod (integrable_const (1 : ℝ) (μ := μ))
  apply hD.mono' hS.aestronglyMeasurable
  have hpos : ∀ᵐ q : ℝ × Space d ∂((volume.restrict (Set.Ioo 0 T)).prod μ), 0 < q.1 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const measurable_fst)).mpr
    exact (ae_restrict_mem measurableSet_Ioo).mono fun s hs => Eventually.of_forall fun _ => hs.1
  filter_upwards [hpos] with q hq
  have he : (hf q).toLp (fun y => if 0 < q.1 then heatKernelBM d q.1 q.2 y else 0) =
      (memLp_heatKernelBM hd hq q.2).toLp (heatKernelBM d q.1 q.2) := by
    apply Lp.ext
    filter_upwards [(hf q).coeFn_toLp, (memLp_heatKernelBM hd hq q.2).coeFn_toLp] with y h1 h2
    rw [h1, h2, if_pos hq]
  rw [he]
  exact hbound q.1 hq q.2
/-- A single joint heat-noise version, integrable over bounded positive times and any finite
measure of centres. -/
theorem exists_joint_integrable_heat_noise {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P) :
    ∃ Y : (ℝ × Space d) → Ω → ℝ, StronglyMeasurable (Function.uncurry Y) ∧
      (∀ q, Y q =ᵐ[P] W (fun y => if 0 < q.1 then heatKernelBM d q.1 q.2 y else 0)) ∧
      ∀ (μ : Measure (Space d)), IsFiniteMeasure μ → ∀ T : ℝ,
        Integrable (Function.uncurry Y) (((volume.restrict (Set.Ioo 0 T)).prod μ).prod P) := by
  obtain ⟨hf, hS, hI⟩ := positiveHeatKernel_family hd hd3
  obtain ⟨Y, hY, hv⟩ := hW.jointMeas_univ (volume : Measure (ℝ × Space d))
    (fun q : ℝ × Space d => fun y => if 0 < q.1 then heatKernelBM d q.1 q.2 y else 0) hf hS
  refine ⟨Y, hY, hv, ?_⟩
  intro μ hμ T
  letI := hμ
  exact (whiteNoise_integral_comm_of_version hW ((volume.restrict (Set.Ioo 0 T)).prod μ)
    _ hf (hI μ hμ T) Y hY hv).1
end Sandpile.Support
