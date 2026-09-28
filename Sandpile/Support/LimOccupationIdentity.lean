import Sandpile.Support.LimStoppedKernel
import Sandpile.Support.LimRestart
import Sandpile.Support.ExplBrownianDensity
import Sandpile.Support.LimOccupationLimit

/-!
# The ball-stopped occupation identity

The optional-stopping identity behind `sandpile.tex:2499-2513`: the kernel the
ball-stopped field averages the white noise against IS the expected occupation
density of the stopped motion.

Write `τ` for the exit time of the ball of radius `s` about the starting point,
truncated at the horizon `T`.  The kernel produced by the increment of the heat
potential is

  `k(y) = g_T(x,y) - E[g_{T-τ}(B_τ, y)]`,

and the claim is that for every bounded measurable `φ`

  `∫ φ(y) k(y) dy = E[∫_0^τ φ(B_r) dr]`.

The proof is the one the paper's sentence takes for granted.  Testing a finite-time
Green kernel against `φ` gives the time integral of the transition averages
(`integral_mul_greenTimeBM`), and each transition average is an expectation of `φ`
along the motion (`brownian_transition_integral`), so the first term is
`E[∫_0^T φ(B_r) dr]`.  For the second term the strong Markov property at `τ`
(`integral_brownian_after_stopping`) turns the expected Green kernel from the
stopped position into `E[∫_τ^T φ(B_r) dr]`, one time `r` at a time, and the two
Fubini exchanges that assemble the times are legitimate because `φ` is bounded and
the Green kernels have spatial mass their own time.  Subtracting leaves
`E[∫_0^τ φ(B_r) dr]`.  The final assembly, `integral_mul_ballStoppedKernel`, specializes
this to the exit time of a ball, and `integral_mul_stoppedOccupation` is the general
bounded-stopping-rule version from which it is derived.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open Sandpile.Continuum Sandpile.Frozen.FixedScaleCrossings
open scoped ENNReal NNReal

namespace Sandpile.Support

variable {ΩB : Type*}

/-- The transition average `∫ φ(y) p_r(z,y) dy` of `sandpile.tex:1069-1071`. -/
noncomputable def transAvg (d : ℕ) (φ : Space d → ℝ) (r : ℝ) (z : Space d) : ℝ :=
  ∫ y, φ y * heatKernelBM d r z y

/-- The heat kernel `heatKernelBM d r z` is measurable as a function of its target
argument `y`. -/
theorem measurable_heatKernelBM_right (d : ℕ) (r : ℝ) (z : Space d) :
    Measurable (fun y => heatKernelBM d r z y) := by
  unfold heatKernelBM
  fun_prop

/-- A pointwise bound `M * heatKernelBM d r z y` on `φ y * heatKernelBM d r z y`, from a
bound `|φ y| ≤ M` and the nonnegativity of the heat kernel (`heatKernelBM_nonneg`). -/
theorem norm_mul_heatKernelBM_le {d : ℕ} {r : ℝ} (hr : 0 ≤ r) (z : Space d)
    (φ : Space d → ℝ) {M : ℝ} (hM : ∀ y, |φ y| ≤ M) (y : Space d) :
    ‖φ y * heatKernelBM d r z y‖ ≤ M * heatKernelBM d r z y := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernelBM_nonneg d hr z y)]
  exact mul_le_mul_of_nonneg_right (hM y) (heatKernelBM_nonneg d hr z y)

/-- Integrability of `y ↦ φ y * heatKernelBM d r z y`, by dominating it (via
`norm_mul_heatKernelBM_le`) with the constant multiple `M * heatKernelBM d r z y` of the
integrable heat kernel `integrable_heatKernelBM_space`. -/
theorem integrable_mul_heatKernelBM {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (z : Space d)
    (φ : Space d → ℝ) (hφ : Measurable φ) {M : ℝ} (hM : ∀ y, |φ y| ≤ M) :
    Integrable (fun y => φ y * heatKernelBM d r z y) (volume : Measure (Space d)) :=
  Integrable.mono' ((integrable_heatKernelBM_space hd hr z).const_mul M)
    ((hφ.mul (measurable_heatKernelBM_right d r z)).aestronglyMeasurable)
    (Eventually.of_forall (norm_mul_heatKernelBM_le hr.le z φ hM))

/-- The transition average `transAvg d φ r z` is bounded by `M` whenever `|φ| ≤ M`, since the
heat kernel integrates to one (`integral_heatKernelBM_eq_one`). -/
theorem abs_transAvg_le {d : ℕ} (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (z : Space d)
    (φ : Space d → ℝ) (hφ : Measurable φ) {M : ℝ} (hM : ∀ y, |φ y| ≤ M) :
    |transAvg d φ r z| ≤ M := by
  have hint := integrable_mul_heatKernelBM hd hr z φ hφ hM
  calc |transAvg d φ r z| ≤ ∫ y, ‖φ y * heatKernelBM d r z y‖ := by
        rw [transAvg]
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (f := fun y => φ y * heatKernelBM d r z y)
    _ ≤ ∫ y, M * heatKernelBM d r z y :=
        integral_mono hint.norm ((integrable_heatKernelBM_space hd hr z).const_mul M)
          (norm_mul_heatKernelBM_le hr.le z φ hM)
    _ = M := by rw [integral_const_mul, integral_heatKernelBM_eq_one hd hr z, mul_one]

/-- **Testing a finite-time Green kernel against a bounded function.**  The pairing is
the time integral of the transition averages. -/
theorem integral_mul_greenTimeBM {d : ℕ} (hd : 1 ≤ d) {t : ℝ} (ht : 0 ≤ t) (z : Space d)
    (φ : Space d → ℝ) (hφ : Measurable φ) {M : ℝ} (hM : ∀ y, |φ y| ≤ M) :
    (∫ y, φ y * greenTimeBM d t z y) = ∫ r in Set.Ioo (0 : ℝ) t, transAvg d φ r z := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (φ z)) (hM z)
  set μ : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) t) with hμ
  haveI : IsFiniteMeasure μ := ⟨by rw [hμ, Measure.restrict_apply_univ]; exact measure_Ioo_lt_top⟩
  set F : ℝ × Space d → ℝ := fun p => φ p.2 * heatKernelBM d p.1 z p.2 with hF
  have hmF : Measurable F :=
    (hφ.comp measurable_snd).mul (by unfold heatKernelBM; fun_prop)
  have hsections : ∀ᵐ r ∂μ, Integrable (fun y => F (r, y)) (volume : Measure (Space d)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact integrable_mul_heatKernelBM hd hr.1 z φ hφ hM
  have hnorm : Integrable (fun r => ∫ y : Space d, ‖F (r, y)‖) μ := by
    refine Integrable.mono' (integrable_const M)
      (hmF.norm.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hb : (∫ y : Space d, ‖F (r, y)‖) ≤ M := by
      calc (∫ y : Space d, ‖F (r, y)‖) ≤ ∫ y : Space d, M * heatKernelBM d r z y :=
            integral_mono (integrable_mul_heatKernelBM hd hr.1 z φ hφ hM).norm
              ((integrable_heatKernelBM_space hd hr.1 z).const_mul M)
              (norm_mul_heatKernelBM_le hr.1.le z φ hM)
        _ = M := by rw [integral_const_mul, integral_heatKernelBM_eq_one hd hr.1 z, mul_one]
    rw [Real.norm_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
    exact hb
  have hi : Integrable F (μ.prod (volume : Measure (Space d))) :=
    (integrable_prod_iff hmF.aestronglyMeasurable).mpr ⟨hsections, hnorm⟩
  calc (∫ y, φ y * greenTimeBM d t z y) = ∫ y : Space d, ∫ r, F (r, y) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        show φ y * greenTimeBM d t z y = ∫ r, φ y * heatKernelBM d r z y ∂μ
        rw [integral_const_mul, hμ, integral_restrict_eq_greenTimeBM ht z y]
    _ = ∫ r, (∫ y : Space d, F (r, y)) ∂μ := (integral_integral_swap hi).symm
    _ = ∫ r in Set.Ioo (0 : ℝ) t, transAvg d φ r z := rfl


/-- Fubini for a bounded measurable function of two finite measure spaces. -/
theorem integral_integral_swap_bdd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [SFinite ν] [IsFiniteMeasure ν]
    (f : α × β → ℝ) (hf : Measurable f) {M : ℝ} (hM : ∀ p, |f p| ≤ M) :
    (∫ a, ∫ b, f (a, b) ∂ν ∂μ) = ∫ b, ∫ a, f (a, b) ∂μ ∂ν := by
  have hi : Integrable f (μ.prod ν) :=
    Integrable.mono' (integrable_const M) hf.aestronglyMeasurable
      (Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hM p)
  exact integral_integral_swap hi

/-- The transition average is the expectation of the reward along the motion. -/
theorem transAvg_eq_integral {d : ℕ} (hd : 1 ≤ d) [MeasurableSpace ΩB] {PB : Measure ΩB}
    [IsProbabilityMeasure PB] {x : Space d} {X : ℝ≥0 → ΩB → Space d}
    (hX : IsBrownian d x X PB) {r : ℝ} (hr : 0 < r) (z : Space d)
    (φ : Space d → ℝ) (hφ : Measurable φ) {M : ℝ} (hM : ∀ y, |φ y| ≤ M) :
    transAvg d φ r z = ∫ b, φ (z + (X r.toNNReal b - X 0 b)) ∂PB := by
  have hrc : ((Real.toNNReal r : ℝ≥0) : ℝ) = r := Real.coe_toNNReal r hr.le
  have hrpos : (0 : ℝ≥0) < Real.toNNReal r := by
    rw [← NNReal.coe_lt_coe, hrc]
    exact_mod_cast hr
  have hi : Integrable (fun y => heatKernelBM d (Real.toNNReal r : ℝ) z y * φ y)
      (volume : Measure (Space d)) := by
    rw [hrc]
    exact (integrable_mul_heatKernelBM hd hr z φ hφ hM).congr
      (Eventually.of_forall fun y => mul_comm _ _)
  have h := (brownian_transition_integral hd hX (Real.toNNReal r) hrpos z φ hφ hi).2
  rw [transAvg, h]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  rw [hrc]
  exact mul_comm _ _


/-- Joint measurability of a bounded reward along the motion. -/
theorem measurable_reward_uncurry [MeasurableSpace ΩB] {d : ℕ} {X : ℝ≥0 → ΩB → Space d}
    (hXc : ∀ ω, Continuous fun t => X t ω) (hXm : ∀ t, StronglyMeasurable (X t))
    (φ : Space d → ℝ) (hφ : Measurable φ) :
    Measurable (fun p : ℝ × ΩB => φ (X p.1.toNNReal p.2)) := by
  have hXj : StronglyMeasurable (Function.uncurry X) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hXc hXm
  exact hφ.comp (hXj.measurable.comp
    ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd))

/-- **The free term.**  The finite-time Green kernel tested against a bounded reward is the
expected accumulated reward up to the horizon. -/
theorem integral_mul_greenTimeBM_motion [MeasurableSpace ΩB] {d : ℕ} (hd : 1 ≤ d)
    {PB : Measure ΩB} [IsProbabilityMeasure PB] {x : Space d} {X : ℝ≥0 → ΩB → Space d}
    (hX : IsBrownian d x X PB) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hXm : ∀ t, StronglyMeasurable (X t)) {T : ℝ} (hT : 0 ≤ T)
    (φ : Space d → ℝ) (hφ : Measurable φ) {M : ℝ} (hM : ∀ y, |φ y| ≤ M) :
    (∫ y, φ y * greenTimeBM d T x y)
      = ∫ b, (∫ r in (0 : ℝ)..T, φ (X r.toNNReal b)) ∂PB := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (φ x)) (hM x)
  set μ : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) T) with hμ
  haveI : IsFiniteMeasure μ := ⟨by rw [hμ, Measure.restrict_apply_univ]; exact measure_Ioo_lt_top⟩
  have hstep : ∀ r ∈ Set.Ioo (0 : ℝ) T,
      transAvg d φ r x = ∫ b, φ (X r.toNNReal b) ∂PB := by
    intro r hr
    rw [transAvg_eq_integral hd hX hr.1 x φ hφ hM]
    refine integral_congr_ae ?_
    filter_upwards [hX.start] with b hb
    rw [hb]
    congr 1
    abel
  have hswap := integral_integral_swap_bdd μ PB (fun p : ℝ × ΩB => φ (X p.1.toNNReal p.2))
    (measurable_reward_uncurry hXc hXm φ hφ) (M := M) (fun p => hM _)
  calc (∫ y, φ y * greenTimeBM d T x y) = ∫ r in Set.Ioo (0 : ℝ) T, transAvg d φ r x :=
        integral_mul_greenTimeBM hd hT x φ hφ hM
    _ = ∫ r, (∫ b, φ (X r.toNNReal b) ∂PB) ∂μ := by
        rw [hμ]
        exact setIntegral_congr_fun measurableSet_Ioo hstep
    _ = ∫ b, (∫ r, φ (X r.toNNReal b) ∂μ) ∂PB := hswap
    _ = ∫ b, (∫ r in (0 : ℝ)..T, φ (X r.toNNReal b)) ∂PB := by
        refine integral_congr_ae (Eventually.of_forall fun b => ?_)
        show (∫ r, φ (X r.toNNReal b) ∂μ) = ∫ r in (0 : ℝ)..T, φ (X r.toNNReal b)
        rw [intervalIntegral.integral_of_le hT, hμ, ← integral_Ioc_eq_integral_Ioo]


/-- Joint measurability of `transAvg d φ` in the time-space pair `(r, z)`, obtained from
`StronglyMeasurable.integral_prod_right'` applied to the jointly measurable integrand. -/
theorem measurable_transAvg {d : ℕ} (φ : Space d → ℝ) (hφ : Measurable φ) :
    Measurable (fun p : ℝ × Space d => transAvg d φ p.1 p.2) := by
  have hmeas : Measurable (fun q : (ℝ × Space d) × Space d =>
      φ q.2 * heatKernelBM d q.1.1 q.1.2 q.2) := by
    refine (hφ.comp measurable_snd).mul ?_
    unfold heatKernelBM
    fun_prop
  exact (hmeas.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-- For `c : ℝ≥0` and `r ≥ 0`, taking `toNNReal` of the sum `(c : ℝ) + r` recovers
`c + r.toNNReal`. -/
theorem toNNReal_add_coe {c : ℝ≥0} {r : ℝ} (hr : 0 ≤ r) :
    Real.toNNReal ((c : ℝ) + r) = c + Real.toNNReal r := by
  refine NNReal.coe_injective ?_
  rw [NNReal.coe_add, Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal r hr]



/-- The stopped time-space parameter of a bounded stopping rule, as a measurable map into the
time-space cylinder the Green kernels are indexed by. -/
theorem exists_stopped_spaceTime [MeasurableSpace ΩB] {d : ℕ} {X : ℝ≥0 → ΩB → Space d}
    (hXc : ∀ ω, Continuous fun t => X t ω) (hXm : ∀ t, StronglyMeasurable (X t))
    (τ : ΩB → ℝ≥0) (hτm : Measurable τ) {T : ℝ} (hT : 0 < T) (hτT : ∀ b, (τ b : ℝ) ≤ T) :
    ∃ q : ΩB → ℝ≥0 × Space d, Measurable q ∧ (∀ b, (q b).1 ≤ T.toNNReal) ∧
      (∀ b, ((q b).1 : ℝ) = T - (τ b : ℝ)) ∧ (∀ b, (q b).2 = X (τ b) b) := by
  have hτT' : ∀ b, τ b ≤ T.toNNReal := by
    intro b
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal T hT.le]
    exact hτT b
  refine ⟨fun b => (⟨((T.toNNReal : ℝ≥0) : ℝ) - τ b, sub_nonneg.mpr (by
    exact_mod_cast hτT' b)⟩, X (τ b) b),
    measurable_stopped_spaceTime X hXc hXm τ hτm T.toNNReal hτT', fun b => ?_, fun b => ?_,
    fun b => rfl⟩
  · exact show ((T.toNNReal : ℝ≥0) : ℝ) - τ b ≤ ((T.toNNReal : ℝ≥0) : ℝ) from
      sub_le_self _ (τ b).property
  · show ((T.toNNReal : ℝ≥0) : ℝ) - (τ b : ℝ) = T - (τ b : ℝ)
    rw [Real.coe_toNNReal T hT.le]

/-- The Green kernels from the stopped position are integrable on the product of the sample
space and the space. -/
theorem integrable_greenTimeBM_stopped [MeasurableSpace ΩB] {d : ℕ} (hd : 1 ≤ d)
    (PB : Measure ΩB) [IsProbabilityMeasure PB] {X : ℝ≥0 → ΩB → Space d}
    (hXc : ∀ ω, Continuous fun t => X t ω) (hXm : ∀ t, StronglyMeasurable (X t))
    (τ : ΩB → ℝ≥0) (hτm : Measurable τ) {T : ℝ} (hT : 0 < T) (hτT : ∀ b, (τ b : ℝ) ≤ T) :
    Integrable (fun p : ΩB × Space d =>
        greenTimeBM d (T - (τ p.1 : ℝ)) (X (τ p.1) p.1) p.2)
      (PB.prod (volume : Measure (Space d))) := by
  obtain ⟨q, hq, hqT, hqc, hqs⟩ := exists_stopped_spaceTime hXc hXm τ hτm hT hτT
  refine (integrable_greenTimeBM_product PB hd q hq T.toNNReal hqT).congr
    (Eventually.of_forall fun p => ?_)
  dsimp only
  rw [hqc p.1, hqs p.1]

/-- **The stopped term, for an arbitrary bounded stopping rule.**  The expected Green kernel
from the stopped position, tested against a bounded reward, is the expected reward accumulated
between the stopping time and the horizon.  This is the strong Markov property at the stopping
rule, applied one time at a time. -/
theorem integral_mul_expectedGreen [MeasurableSpace ΩB] {d : ℕ} (hd : 1 ≤ d)
    {PB : Measure ΩB} [IsProbabilityMeasure PB] {x : Space d} {X : ℝ≥0 → ΩB → Space d}
    (hX : IsBrownian d x X PB) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hXm : ∀ t, StronglyMeasurable (X t)) (τ : ΩB → ℝ≥0) (hτm : Measurable τ)
    (hstop : Sandpile.Continuum.IsBrownianStopping X τ)
    {T : ℝ} (hT : 0 < T) (hτT : ∀ b, (τ b : ℝ) ≤ T)
    (φ : Space d → ℝ) (hφ : Measurable φ) {M : ℝ} (hM : ∀ y, |φ y| ≤ M) :
    (∫ y, φ y * (∫ b, greenTimeBM d (T - (τ b : ℝ)) (X (τ b) b) y ∂PB))
      = ∫ b, (∫ r in ((τ b : ℝ))..T, φ (X r.toNNReal b)) ∂PB := by
  classical
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (φ x)) (hM x)
  have hτ0 : ∀ b, (0 : ℝ) ≤ (τ b : ℝ) := fun b => (τ b).property
  set μ : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) T) with hμ
  haveI : IsFiniteMeasure μ := ⟨by rw [hμ, Measure.restrict_apply_univ]; exact measure_Ioo_lt_top⟩
  have hXj : StronglyMeasurable (Function.uncurry X) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hXc hXm
  have hstate : Measurable (fun b => X (τ b) b) :=
    hXj.measurable.comp (hτm.prodMk measurable_id)
  -- the good set of time-sample pairs
  set S : Set (ℝ × ΩB) := {p | 0 < p.1 ∧ p.1 < T - (τ p.2 : ℝ)} with hS
  have hSmeas : MeasurableSet S := by
    refine (measurableSet_lt measurable_const measurable_fst).inter ?_
    exact measurableSet_lt measurable_fst
      (measurable_const.sub (hτm.comp measurable_snd).coe_nnreal_real)
  have hSslice : ∀ b : ΩB, ∀ r : ℝ, ((r, b) ∈ S ↔ r ∈ Set.Ioo (0 : ℝ) (T - (τ b : ℝ))) := by
    intro b r
    simp only [hS, Set.mem_setOf_eq, Set.mem_Ioo]
  -- the two integrands
  set G : ℝ × ΩB → ℝ :=
    S.indicator (fun p => transAvg d φ p.1 (X (τ p.2) p.2)) with hG
  set H : ℝ × ΩB → ℝ :=
    S.indicator (fun p => φ (X (τ p.2 + p.1.toNNReal) p.2)) with hH
  have hGmeas : Measurable G := by
    have hinner : Measurable (fun p : ℝ × ΩB => transAvg d φ p.1 (X (τ p.2) p.2)) :=
      (measurable_transAvg φ hφ).comp (measurable_fst.prodMk (hstate.comp measurable_snd))
    exact hinner.indicator hSmeas
  have hHmeas : Measurable H := by
    have hinner : Measurable (fun p : ℝ × ΩB => φ (X (τ p.2 + p.1.toNNReal) p.2)) :=
      hφ.comp (hXj.measurable.comp
        (((hτm.comp measurable_snd).add
          (measurable_real_toNNReal.comp measurable_fst)).prodMk measurable_snd))
    exact hinner.indicator hSmeas
  have hGbdd : ∀ p, |G p| ≤ M := by
    intro p
    by_cases hp : p ∈ S
    · rw [hG, Set.indicator_of_mem hp]
      exact abs_transAvg_le hd hp.1 _ φ hφ hM
    · rw [hG, Set.indicator_of_notMem hp, abs_zero]
      exact hM0
  have hHbdd : ∀ p, |H p| ≤ M := by
    intro p
    by_cases hp : p ∈ S
    · rw [hH, Set.indicator_of_mem hp]
      exact hM _
    · rw [hH, Set.indicator_of_notMem hp, abs_zero]
      exact hM0
  -- Step 1: the spatial Fubini
  obtain ⟨q, hq, hqT, hqc, hqs⟩ := exists_stopped_spaceTime hXc hXm τ hτm hT hτT
  have hq' : Measurable (fun p : ΩB × Space d => (q p.1, p.2)) :=
    (hq.comp measurable_fst).prodMk measurable_snd
  have hmg := (measurable_uncurry_greenTimeBM d).comp hq'
  have hgprod : Integrable (fun p : ΩB × Space d => φ p.2 * greenTimeBM d (q p.1).1 (q p.1).2 p.2)
      (PB.prod (volume : Measure (Space d))) := by
    refine Integrable.mono' ((integrable_greenTimeBM_product PB hd q hq T.toNNReal hqT).const_mul M)
      ((hφ.comp measurable_snd).mul hmg).aestronglyMeasurable ?_
    filter_upwards with p
    have hg0 : 0 ≤ greenTimeBM d ((q p.1).1 : ℝ) (q p.1).2 p.2 :=
      greenTimeBM_nonneg d (NNReal.coe_nonneg _) (q p.1).2 p.2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hg0]
    exact mul_le_mul_of_nonneg_right (hM p.2) hg0
  have hstep1 : (∫ y, φ y * (∫ b, greenTimeBM d (T - (τ b : ℝ)) (X (τ b) b) y ∂PB))
      = ∫ b, (∫ y, φ y * greenTimeBM d (T - (τ b : ℝ)) (X (τ b) b) y) ∂PB := by
    have hswap := integral_integral_swap
      (f := fun (b : ΩB) (y : Space d) => φ y * greenTimeBM d (q b).1 (q b).2 y) hgprod
    calc (∫ y, φ y * (∫ b, greenTimeBM d (T - (τ b : ℝ)) (X (τ b) b) y ∂PB))
        = ∫ y : Space d, ∫ b, φ y * greenTimeBM d (q b).1 (q b).2 y ∂PB := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          show φ y * (∫ b, greenTimeBM d (T - (τ b : ℝ)) (X (τ b) b) y ∂PB)
              = ∫ b, φ y * greenTimeBM d ((q b).1 : ℝ) (q b).2 y ∂PB
          rw [integral_const_mul]
          congr 1
          refine integral_congr_ae (Eventually.of_forall fun b => ?_)
          dsimp only
          rw [hqc b, hqs b]
      _ = ∫ b, (∫ y : Space d, φ y * greenTimeBM d (q b).1 (q b).2 y) ∂PB := hswap.symm
      _ = ∫ b, (∫ y, φ y * greenTimeBM d (T - (τ b : ℝ)) (X (τ b) b) y) ∂PB := by
          refine integral_congr_ae (Eventually.of_forall fun b => ?_)
          dsimp only
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          dsimp only
          rw [hqc b, hqs b]
  -- Step 2: the time integral, per sample
  have hstep2 : ∀ b : ΩB, (∫ y, φ y * greenTimeBM d (T - (τ b : ℝ)) (X (τ b) b) y)
      = ∫ r, G (r, b) ∂μ := by
    intro b
    rw [integral_mul_greenTimeBM hd (by linarith [hτT b]) (X (τ b) b) φ hφ hM, hμ]
    have hind : (fun r : ℝ => G (r, b))
        = (Set.Ioo (0 : ℝ) (T - (τ b : ℝ))).indicator
            (fun r => transAvg d φ r (X (τ b) b)) := by
      funext r
      by_cases hr : (r, b) ∈ S
      · rw [hG, Set.indicator_of_mem hr, Set.indicator_of_mem ((hSslice b r).mp hr)]
      · rw [hG, Set.indicator_of_notMem hr,
          Set.indicator_of_notMem (fun h => hr ((hSslice b r).mpr h))]
    rw [hind, setIntegral_indicator measurableSet_Ioo, Set.Ioo_inter_Ioo, max_self,
      min_eq_right (by linarith [hτ0 b])]
  -- Step 6: the time integral of the reward, per sample
  have hstep6 : ∀ b : ΩB, (∫ r, H (r, b) ∂μ)
      = ∫ r in ((τ b : ℝ))..T, φ (X r.toNNReal b) := by
    intro b
    have hind : (fun r : ℝ => H (r, b))
        = (Set.Ioo (0 : ℝ) (T - (τ b : ℝ))).indicator
            (fun r => φ (X (τ b + r.toNNReal) b)) := by
      funext r
      by_cases hr : (r, b) ∈ S
      · rw [hH, Set.indicator_of_mem hr, Set.indicator_of_mem ((hSslice b r).mp hr)]
      · rw [hH, Set.indicator_of_notMem hr,
          Set.indicator_of_notMem (fun h => hr ((hSslice b r).mpr h))]
    rw [hμ, hind, setIntegral_indicator measurableSet_Ioo, Set.Ioo_inter_Ioo, max_self,
      min_eq_right (by linarith [hτ0 b]), ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by linarith [hτT b])]
    have hshift := intervalIntegral.integral_comp_add_left
      (a := (0 : ℝ)) (b := T - (τ b : ℝ)) (f := fun v : ℝ => φ (X v.toNNReal b)) ((τ b : ℝ))
    rw [add_zero, show (τ b : ℝ) + (T - (τ b : ℝ)) = T by ring] at hshift
    rw [← hshift]
    refine intervalIntegral.integral_congr fun r hr => ?_
    have hr0 : (0 : ℝ) ≤ r := by
      have hle : (0 : ℝ) ≤ T - (τ b : ℝ) := by linarith [hτT b]
      rw [Set.uIcc_of_le hle] at hr
      exact hr.1
    show φ (X (τ b + r.toNNReal) b) = φ (X ((τ b : ℝ) + r).toNNReal b)
    rw [toNNReal_add_coe hr0]
  -- Steps 3 and 5: the two time-sample Fubini exchanges
  have hfub1 : (∫ b, (∫ r, G (r, b) ∂μ) ∂PB) = ∫ r, (∫ b, G (r, b) ∂PB) ∂μ :=
    (integral_integral_swap_bdd μ PB G hGmeas hGbdd).symm
  have hfub2 : (∫ r, (∫ b, H (r, b) ∂PB) ∂μ) = ∫ b, (∫ r, H (r, b) ∂μ) ∂PB :=
    integral_integral_swap_bdd μ PB H hHmeas hHbdd
  -- Step 4: the strong Markov property, at each time
  have hrestart : ∀ r ∈ Set.Ioo (0 : ℝ) T, (∫ b, G (r, b) ∂PB) = ∫ b, H (r, b) ∂PB := by
    intro r hr
    set F : (ℝ≥0 × Space d) × Space d → ℝ := fun p =>
      (if r < T - ((p.1.1 : ℝ≥0) : ℝ) then (1 : ℝ) else 0) * φ p.2 with hF
    have hFm : Measurable F := by
      refine Measurable.mul ?_ (hφ.comp measurable_snd)
      refine Measurable.ite ?_ measurable_const measurable_const
      exact measurableSet_lt measurable_const
        (measurable_const.sub (measurable_fst.fst.coe_nnreal_real))
    have hFb : ∀ p, ‖F p‖ ≤ M := by
      intro p
      rw [hF, Real.norm_eq_abs, abs_mul]
      by_cases h : r < T - ((p.1.1 : ℝ≥0) : ℝ)
      · rw [if_pos h, abs_one, one_mul]
        exact hM _
      · rw [if_neg h, abs_zero, zero_mul]
        exact hM0
    have hmain := integral_brownian_after_stopping hX hXm hXc τ hstop r.toNNReal F hFm M hFb
    have hGval : ∀ b : ΩB, G (r, b)
        = ∫ η, F ((τ b, X (τ b) b), X (τ b) b + (X r.toNNReal η - X 0 η)) ∂PB := by
      intro b
      have hinner : (∫ η, F ((τ b, X (τ b) b), X (τ b) b + (X r.toNNReal η - X 0 η)) ∂PB)
          = (if r < T - (τ b : ℝ) then (1 : ℝ) else 0) *
            ∫ η, φ (X (τ b) b + (X r.toNNReal η - X 0 η)) ∂PB := by
        rw [← integral_const_mul]
      rw [hinner]
      by_cases hc : r < T - (τ b : ℝ)
      · rw [if_pos hc, one_mul, hG, Set.indicator_of_mem ((hSslice b r).mpr ⟨hr.1, hc⟩)]
        exact transAvg_eq_integral hd hX hr.1 (X (τ b) b) φ hφ hM
      · rw [if_neg hc, zero_mul, hG,
          Set.indicator_of_notMem (fun h => hc ((hSslice b r).mp h).2)]
    have hHval : ∀ b : ΩB, H (r, b) = F ((τ b, X (τ b) b), X (τ b + r.toNNReal) b) := by
      intro b
      by_cases hc : r < T - (τ b : ℝ)
      · rw [hH, Set.indicator_of_mem ((hSslice b r).mpr ⟨hr.1, hc⟩), hF]
        simp only [if_pos hc, one_mul]
      · rw [hH, Set.indicator_of_notMem (fun h => hc ((hSslice b r).mp h).2), hF]
        simp only [if_neg hc, zero_mul]
    calc (∫ b, G (r, b) ∂PB)
        = ∫ b, (∫ η, F ((τ b, X (τ b) b), X (τ b) b + (X r.toNNReal η - X 0 η)) ∂PB) ∂PB :=
          integral_congr_ae (Eventually.of_forall hGval)
      _ = ∫ b, F ((τ b, X (τ b) b), X (τ b + r.toNNReal) b) ∂PB := hmain.symm
      _ = ∫ b, H (r, b) ∂PB := (integral_congr_ae (Eventually.of_forall hHval)).symm
  -- assembly
  calc (∫ y, φ y * (∫ b, greenTimeBM d (T - (τ b : ℝ)) (X (τ b) b) y ∂PB))
      = ∫ b, (∫ y, φ y * greenTimeBM d (T - (τ b : ℝ)) (X (τ b) b) y) ∂PB := hstep1
    _ = ∫ b, (∫ r, G (r, b) ∂μ) ∂PB :=
        integral_congr_ae (Eventually.of_forall hstep2)
    _ = ∫ r, (∫ b, G (r, b) ∂PB) ∂μ := hfub1
    _ = ∫ r, (∫ b, H (r, b) ∂PB) ∂μ := by
        rw [hμ]
        exact setIntegral_congr_fun measurableSet_Ioo hrestart
    _ = ∫ b, (∫ r, H (r, b) ∂μ) ∂PB := hfub2
    _ = ∫ b, (∫ r in ((τ b : ℝ))..T, φ (X r.toNNReal b)) ∂PB :=
        integral_congr_ae (Eventually.of_forall hstep6)


/-! ### The accumulated reward as a random variable -/

/-- The reward accumulated up to a measurable nonnegative time is a random variable. -/
theorem stronglyMeasurable_reward_upTo [MeasurableSpace ΩB] {d : ℕ} {X : ℝ≥0 → ΩB → Space d}
    (hXc : ∀ ω, Continuous fun t => X t ω) (hXm : ∀ t, StronglyMeasurable (X t))
    (φ : Space d → ℝ) (hφ : Measurable φ) (c : ΩB → ℝ) (hc : Measurable c)
    (hc0 : ∀ b, 0 ≤ c b) :
    StronglyMeasurable (fun b => ∫ r in (0 : ℝ)..(c b), φ (X r.toNNReal b)) := by
  have hXj : StronglyMeasurable (Function.uncurry X) :=
    stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hXc hXm
  have hF : Measurable (fun p : ΩB × ℝ => φ (X p.2.toNNReal p.1)) :=
    hφ.comp (hXj.measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst))
  set A : Set (ΩB × ℝ) := {p | 0 < p.2 ∧ p.2 ≤ c p.1} with hA
  have hAm : MeasurableSet A :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (hc.comp measurable_fst))
  have h := (hF.indicator hAm).stronglyMeasurable.integral_prod_right' (ν := volume)
  convert h using 1
  funext b
  rw [intervalIntegral.integral_of_le (hc0 b)]
  show (∫ r in Set.Ioc (0 : ℝ) (c b), φ (X r.toNNReal b)) = _
  rw [← integral_indicator measurableSet_Ioc]
  rfl

/-- The reward accumulated up to a measurable time bounded by the horizon is integrable. -/
theorem integrable_reward_upTo [MeasurableSpace ΩB] {d : ℕ} (PB : Measure ΩB)
    [IsFiniteMeasure PB] {X : ℝ≥0 → ΩB → Space d}
    (hXc : ∀ ω, Continuous fun t => X t ω) (hXm : ∀ t, StronglyMeasurable (X t))
    (φ : Space d → ℝ) (hφ : Measurable φ) {M : ℝ} (hM : ∀ y, |φ y| ≤ M)
    (c : ΩB → ℝ) (hc : Measurable c) (hc0 : ∀ b, 0 ≤ c b) {T : ℝ} (hcT : ∀ b, c b ≤ T) :
    Integrable (fun b => ∫ r in (0 : ℝ)..(c b), φ (X r.toNNReal b)) PB := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (φ 0)) (hM 0)
  refine Integrable.of_bound
    (stronglyMeasurable_reward_upTo hXc hXm φ hφ c hc hc0).aestronglyMeasurable (M * T)
    (Eventually.of_forall fun b => ?_)
  have hbnd := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := c b) (C := M)
    (fun r _ => show ‖φ (X r.toNNReal b)‖ ≤ M by
      simpa only [Real.norm_eq_abs] using hM (X r.toNNReal b))
  rw [sub_zero, abs_of_nonneg (hc0 b)] at hbnd
  exact hbnd.trans (mul_le_mul_of_nonneg_left (hcT b) hM0)


/-- **The occupation identity, for an arbitrary bounded stopping rule.**  The kernel produced by
the increment of the heat potential along a bounded stopping rule is the expected occupation
density of the stopped motion, tested against any bounded measurable reward. -/
theorem integral_mul_stoppedOccupation [MeasurableSpace ΩB] {d : ℕ} (hd : 1 ≤ d)
    {PB : Measure ΩB} [IsProbabilityMeasure PB] {x : Space d} {X : ℝ≥0 → ΩB → Space d}
    (hX : IsBrownian d x X PB) (hXc : ∀ ω, Continuous fun t => X t ω)
    (hXm : ∀ t, StronglyMeasurable (X t)) (τ : ΩB → ℝ≥0) (hτm : Measurable τ)
    (hstop : Sandpile.Continuum.IsBrownianStopping X τ)
    {T : ℝ} (hT : 0 < T) (hτT : ∀ b, (τ b : ℝ) ≤ T)
    (φ : Space d → ℝ) (hφ : Measurable φ) {M : ℝ} (hM : ∀ y, |φ y| ≤ M) :
    (∫ y, φ y * (greenTimeBM d T x y - ∫ b, greenTimeBM d (T - (τ b : ℝ)) (X (τ b) b) y ∂PB))
      = ∫ b, (∫ r in (0 : ℝ)..((τ b : ℝ)), φ (X r.toNNReal b)) ∂PB := by
  have hτ0 : ∀ b, (0 : ℝ) ≤ (τ b : ℝ) := fun b => (τ b).coe_nonneg
  have hnorm : ∀ᵐ y ∂(volume : Measure (Space d)), ‖φ y‖ ≤ M :=
    Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hM y
  have hKint : Integrable
      (fun y => ∫ b, greenTimeBM d (T - (τ b : ℝ)) (X (τ b) b) y ∂PB)
      (volume : Measure (Space d)) :=
    (integrable_greenTimeBM_stopped hd PB hXc hXm τ hτm hT hτT).integral_prod_right
  have hGint : Integrable (fun y => greenTimeBM d T x y) (volume : Measure (Space d)) :=
    (integrable_greenTimeBM_and_integral_eq hd hT.le x).1
  have h1 : Integrable (fun y => φ y * greenTimeBM d T x y) (volume : Measure (Space d)) :=
    hGint.bdd_mul hφ.aestronglyMeasurable hnorm
  have h2 : Integrable
      (fun y => φ y * ∫ b, greenTimeBM d (T - (τ b : ℝ)) (X (τ b) b) y ∂PB)
      (volume : Measure (Space d)) := hKint.bdd_mul hφ.aestronglyMeasurable hnorm
  -- the reward integrals along the motion
  have hrewT : Integrable (fun b => ∫ r in (0 : ℝ)..T, φ (X r.toNNReal b)) PB :=
    integrable_reward_upTo PB hXc hXm φ hφ hM (fun _ => T) measurable_const
      (fun _ => hT.le) (fun _ => le_rfl)
  have hrewτ : Integrable (fun b => ∫ r in (0 : ℝ)..((τ b : ℝ)), φ (X r.toNNReal b)) PB :=
    integrable_reward_upTo PB hXc hXm φ hφ hM (fun b => (τ b : ℝ)) hτm.coe_nnreal_real
      hτ0 hτT
  have hsplit : ∀ b : ΩB, (∫ r in ((τ b : ℝ))..T, φ (X r.toNNReal b))
      = (∫ r in (0 : ℝ)..T, φ (X r.toNNReal b))
        - ∫ r in (0 : ℝ)..((τ b : ℝ)), φ (X r.toNNReal b) := by
    intro b
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (a := (0 : ℝ)) (b := ((τ b : ℝ))) (c := T)
      (intervalIntegrable_brownian_bounded_reward X hXc φ hφ M hM b 0 ((τ b : ℝ)))
      (intervalIntegrable_brownian_bounded_reward X hXc φ hφ M hM b ((τ b : ℝ)) T)
    linarith [hadd]
  calc (∫ y, φ y * (greenTimeBM d T x y - ∫ b, greenTimeBM d (T - (τ b : ℝ)) (X (τ b) b) y ∂PB))
      = (∫ y, φ y * greenTimeBM d T x y)
        - ∫ y, φ y * (∫ b, greenTimeBM d (T - (τ b : ℝ)) (X (τ b) b) y ∂PB) := by
        rw [← integral_sub h1 h2]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        dsimp only
        ring
    _ = (∫ b, (∫ r in (0 : ℝ)..T, φ (X r.toNNReal b)) ∂PB)
        - ∫ b, (∫ r in ((τ b : ℝ))..T, φ (X r.toNNReal b)) ∂PB := by
        rw [integral_mul_greenTimeBM_motion hd hX hXc hXm hT.le φ hφ hM,
          integral_mul_expectedGreen hd hX hXc hXm τ hτm hstop hT hτT φ hφ hM]
    _ = ∫ b, (∫ r in (0 : ℝ)..((τ b : ℝ)), φ (X r.toNNReal b)) ∂PB := by
        have hcongr : (∫ b, (∫ r in ((τ b : ℝ))..T, φ (X r.toNNReal b)) ∂PB)
            = (∫ b, (∫ r in (0 : ℝ)..T, φ (X r.toNNReal b)) ∂PB)
              - ∫ b, (∫ r in (0 : ℝ)..((τ b : ℝ)), φ (X r.toNNReal b)) ∂PB := by
          rw [← integral_sub hrewT hrewτ]
          exact integral_congr_ae (Eventually.of_forall hsplit)
        rw [hcongr]
        ring

/-- **The occupation identity for the ball-stopped kernel** (`sandpile.tex:2499-2503`).  The
kernel the ball-stopped field averages the white noise against is the expected occupation
density of the motion stopped on leaving the ball of radius `s`, or at the horizon `T`. -/
theorem integral_mul_ballStoppedKernel [MeasurableSpace ΩB] {d : ℕ} (hd : 1 ≤ d)
    (PB : Measure ΩB) [IsProbabilityMeasure PB] {B : Space d → ℝ≥0 → ΩB → Space d}
    (hB : ∀ y, IsBrownian d y (B y) PB) (hBc : ∀ y ω, Continuous fun t => B y t ω)
    (hBm : ∀ y t, StronglyMeasurable (B y t)) {s T : ℝ} (hT : 0 < T) (u : Space 2)
    (φ : Space d → ℝ) (hφ : Measurable φ) {M : ℝ} (hM : ∀ y, |φ y| ≤ M) :
    (∫ y, φ y * ballStoppedKernel d PB B s T u y)
      = ∫ b, (∫ r in (0 : ℝ)..((ballStopTime d B s T u b : ℝ)),
          φ (B (planePoint u) r.toNNReal b)) ∂PB := by
  have hstop : Sandpile.Continuum.IsBrownianStopping (B (planePoint u))
      (ballStopTime d B s T u) := by
    rw [Sandpile.Continuum.isBrownianStopping_iff_natFiltration (B (planePoint u)) (hBm _)]
    exact LatticeProb.isStoppingTime_exitTimeTrunc (hBm _) (hBc _) (planePoint u) s T.toNNReal
  exact integral_mul_stoppedOccupation hd (hB (planePoint u)) (hBc _) (hBm _)
    (ballStopTime d B s T u) (measurable_ballStopTime hBc hBm s T u) hstop hT
    (ballStopTime_le_real B hT.le u) φ hφ hM

end Sandpile.Support
