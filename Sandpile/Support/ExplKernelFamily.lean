import Sandpile.Support.ContBMGreenIdentity
import Mathlib

/-!
# Measurable L2 Families of Brownian Green Kernels

Measurable L2 families of Brownian Green kernels.

Jointly measurable scalar kernels with L2 sections give strongly measurable L2
classes. For the finite-time Brownian Green kernel in dimensions one through
three, its L2 norm is independent of the spatial centre and increases with the
horizon. Thus evaluating its L2 class along any measurable family of bounded
times is Bochner integrable under a finite measure.
-/

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace NNReal ENNReal

namespace Sandpile.Support

/-- A map into a nonempty, second-countable metric space is measurable as soon as its distance
to every fixed point is measurable, proved by approximating `f` pointwise via a dense sequence
`s` and the measurable selector `Measurable.find` choosing the first index within `(1/2)^n`. -/
theorem measurable_of_measurable_dist {U E : Type*} [MeasurableSpace U]
    [Nonempty E] [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (f : U → E)
    (hm : ∀ x : E, Measurable fun u => dist (f u) x) : Measurable f := by
  classical
  let s := TopologicalSpace.denseSeq E
  have hex (n : ℕ) (u : U) : ∃ k, dist (f u) (s k) < (1 / 2 : ℝ) ^ n :=
    Metric.denseRange_iff.mp (TopologicalSpace.denseRange_denseSeq E) (f u)
      ((1 / 2 : ℝ) ^ n) (pow_pos (by norm_num) n)
  let a (n : ℕ) (u : U) := s (Nat.find (hex n u))
  have ha (n : ℕ) : Measurable (a n) := by
    exact Measurable.find (fun _ => measurable_const)
      (fun k => measurableSet_lt (hm (s k)) measurable_const) (hex n)
  refine measurable_of_tendsto_metrizable ha (tendsto_pi_nhds.mpr (fun u => ?_))
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1 / 2 : ℝ)) (by norm_num))
  simpa only [dist_comm] using (Nat.find_spec (hex n u)).le

open scoped RealInnerProductSpace

/-- If `f : U → X → ℝ` is jointly measurable and each section `f u` lies in `MemLp _ 2 μ`, then
`u ↦ (hf u).toLp (f u)` is strongly measurable, proved by reducing to
`measurable_of_measurable_dist` and computing the squared distance to any `v` as the measurable
integral `∫ x, (f u x - v x)^2 ∂μ`. -/
theorem stronglyMeasurable_toLp_of_uncurry {U X : Type*}
    [MeasurableSpace U] [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    [SecondCountableTopology (Lp ℝ 2 μ)]
    (f : U → X → ℝ) (hf : ∀ u, MemLp (f u) 2 μ)
    (hm : Measurable (Function.uncurry f)) :
    StronglyMeasurable (fun u => (hf u).toLp (f u)) := by
  letI : MeasurableSpace (Lp ℝ 2 μ) := borel (Lp ℝ 2 μ)
  letI : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  apply Measurable.stronglyMeasurable
  apply measurable_of_measurable_dist
  intro v
  have he (u : U) : ‖(hf u).toLp (f u) - v‖ ^ 2 = ∫ x, (f u x - v x) ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub ((hf u).toLp (f u)) v, (hf u).coeFn_toLp] with x hx hfx
    simp only [RCLike.inner_apply, conj_trivial, hx, Pi.sub_apply, hfx, sq]
  have hsq : Measurable (fun p : U × X => (f p.1 p.2 - v p.2) ^ 2) := by
    exact (hm.sub ((Lp.stronglyMeasurable v).measurable.comp measurable_snd)).pow_const 2
  have hi : Measurable (fun u => ∫ x, (f u x - v x) ^ 2 ∂μ) :=
    hsq.stronglyMeasurable.integral_prod_right.measurable
  have hid : (fun u => dist ((hf u).toLp (f u)) v) =
      fun u => Real.sqrt (∫ x, (f u x - v x) ^ 2 ∂μ) := by
    funext u
    rw [← he u, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), dist_eq_norm]
  rw [hid]
  exact Real.continuous_sqrt.measurable.comp hi


open Sandpile.Continuum Sandpile.Support
open scoped NNReal ENNReal

/-- The uncurried Brownian Green kernel `(t, x, y) ↦ greenTimeBM d t x y` is jointly measurable,
proved by rewriting it as the integral over `s` of an indicator-cut heat kernel `F` and applying
Fubini-type measurability for the integral over the last coordinate. -/
theorem measurable_uncurry_greenTimeBM (d : ℕ) :
    Measurable (fun p : (ℝ≥0 × Space d) × Space d => greenTimeBM d p.1.1 p.1.2 p.2) := by
  let F (p : ((ℝ≥0 × Space d) × Space d) × ℝ) : ℝ :=
    if p.2 ∈ Set.Ioo (0 : ℝ) p.1.1.1 then heatKernelBM d p.2 p.1.1.2 p.1.2 else 0
  have hm : Measurable F := by
    apply Measurable.ite
    · exact (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_lt measurable_snd (by fun_prop))
    · unfold heatKernelBM
      fun_prop
    · exact measurable_const
  have he (p : (ℝ≥0 × Space d) × Space d) :
      greenTimeBM d p.1.1 p.1.2 p.2 = ∫ s, F (p, s) := by
    rw [greenTimeBM,
      intervalIntegral.integral_of_le (show (0 : ℝ) ≤ (p.1.1 : ℝ) from p.1.1.property),
      integral_Ioc_eq_integral_Ioo]
    simpa only [F, Set.indicator] using (integral_indicator (μ := (volume : Measure ℝ))
      (s := Set.Ioo (0 : ℝ) (p.1.1 : ℝ))
      (f := fun s => heatKernelBM d s p.1.2 p.2) measurableSet_Ioo).symm
  simp_rw [he]
  exact hm.stronglyMeasurable.integral_prod_right.measurable

/-- The map `p ↦ (greenTimeBM d p.1 p.2).toLp` sending a time-space pair to the `L²` class of the
Brownian Green kernel is strongly measurable, an instance of `stronglyMeasurable_toLp_of_uncurry`
via the joint measurability from `measurable_uncurry_greenTimeBM`. -/
theorem stronglyMeasurable_greenTimeBM_toLp {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) :
    StronglyMeasurable (fun p : ℝ≥0 × Space d =>
      (memLp_greenTimeBM hd hd3 p.1.property p.2).toLp (greenTimeBM d p.1 p.2)) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  exact stronglyMeasurable_toLp_of_uncurry (volume : Measure (Space d))
    (fun p : ℝ≥0 × Space d => greenTimeBM d p.1 p.2)
    (fun p : ℝ≥0 × Space d => memLp_greenTimeBM hd hd3 p.1.property p.2)
    (measurable_uncurry_greenTimeBM d)

/-- The `L²` norm of the Green kernel class at time `t ≤ T` and any spatial point `x` is bounded by
its value at the later time `T` centred at `0`: the norm is spatially constant at each fixed time
(by translation of `volume`) and increasing in time (`greenTimeBM_mono`), so the claim reduces to
comparing pointwise via `Lp.norm_le_norm_of_ae_le`. -/
theorem norm_greenTimeBM_toLp_le {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) (x : Space d) :
    ‖(memLp_greenTimeBM hd hd3 ht x).toLp (greenTimeBM d t x)‖ ≤
      ‖(memLp_greenTimeBM hd hd3 (ht.trans htT) 0).toLp (greenTimeBM d T 0)‖ := by
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have he (s : ℝ) (hs : 0 ≤ s) (z : Space d) :
      ‖(memLp_greenTimeBM hd hd3 hs z).toLp (greenTimeBM d s z)‖ ^ 2 =
        ∫ y, greenTimeBM d s z y * greenTimeBM d s z y := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(memLp_greenTimeBM hd hd3 hs z).coeFn_toLp] with y hy
    simp only [RCLike.inner_apply, conj_trivial, hy]
  have hx : ‖(memLp_greenTimeBM hd hd3 (ht.trans htT) x).toLp (greenTimeBM d T x)‖ =
      ‖(memLp_greenTimeBM hd hd3 (ht.trans htT) 0).toLp (greenTimeBM d T 0)‖ := by
    have hs : ‖(memLp_greenTimeBM hd hd3 (ht.trans htT) x).toLp (greenTimeBM d T x)‖ ^ 2 =
        ‖(memLp_greenTimeBM hd hd3 (ht.trans htT) 0).toLp (greenTimeBM d T 0)‖ ^ 2 := by
      rw [he T (ht.trans htT) x, he T (ht.trans htT) 0,
        integral_greenTimeBM_mul_two_interval hd hd3 (ht.trans htT) (ht.trans htT),
        integral_greenTimeBM_mul_two_interval hd hd3 (ht.trans htT) (ht.trans htT)]
      simp only [heatKernelBM, sub_self, norm_zero]
    nlinarith [norm_nonneg ((memLp_greenTimeBM hd hd3 (ht.trans htT) x).toLp (greenTimeBM d T x)),
      norm_nonneg ((memLp_greenTimeBM hd hd3 (ht.trans htT) 0).toLp (greenTimeBM d T 0))]
  rw [← hx]
  apply Lp.norm_le_norm_of_ae_le
  have hne : ∀ᵐ y : Space d, y ≠ x := by
    rw [ae_iff]
    simp
  filter_upwards [hne, (memLp_greenTimeBM hd hd3 ht x).coeFn_toLp,
    (memLp_greenTimeBM hd hd3 (ht.trans htT) x).coeFn_toLp] with y hy ht' hT'
  rw [ht', hT', Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (greenTimeBM_nonneg d ht x y),
    abs_of_nonneg (greenTimeBM_nonneg d (ht.trans htT) x y)]
  exact greenTimeBM_mono hd ht htT hy.symm

/-- Along any measurable family of time-space pairs `q` whose time coordinate is bounded by `T`,
the resulting `L²` Green-kernel classes are Bochner integrable under a finite measure `μ`: they are
strongly measurable (composing `stronglyMeasurable_greenTimeBM_toLp` with `q`) and dominated by the
constant `‖(greenTimeBM d T 0).toLp‖` via `norm_greenTimeBM_toLp_le`. -/
theorem integrable_greenTimeBM_toLp_of_bounded_time {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsFiniteMeasure μ] {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    (q : U → ℝ≥0 × Space d) (hq : Measurable q) (T : ℝ≥0)
    (hT : ∀ u, (q u).1 ≤ T) :
    Integrable (fun u => (memLp_greenTimeBM hd hd3 (q u).1.property (q u).2).toLp
      (greenTimeBM d (q u).1 (q u).2)) μ := by
  have hs := (stronglyMeasurable_greenTimeBM_toLp hd hd3).comp_measurable hq
  apply (integrable_const ‖(memLp_greenTimeBM hd hd3 T.property 0).toLp
    (greenTimeBM d T 0)‖).mono' hs.aestronglyMeasurable
  exact Eventually.of_forall fun u =>
    norm_greenTimeBM_toLp_le hd hd3 (q u).1.property (hT u) (q u).2

end Sandpile.Support
