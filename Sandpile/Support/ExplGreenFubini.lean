import Sandpile.Support.ExplHeatVersion

/-!
# Pointwise spatial kernels in stochastic Fubini for the continuous heat potential

An integrable joint scalar representative identifies a Bochner L2 integral on a sigma-finite
spatial measure (`coe_integral_L2_eq_integral_of_integrable`). The proof tests against indicators
of finite-measure sets. Brownian Green kernels have spatial L1 mass equal to their horizon
(`integrable_greenTimeBM_and_integral_eq`), so a bounded measurable family of Green kernels is
integrable on the full product (`integrable_greenTimeBM_product`).

Consequently the white-noise index in the stopped continuous-field identity can be written as the
literal spatial function `y ↦ ∫ b, √ν² * g_{T-τ}(B_τ b, y) dP_B`
(`gaussianPotential_stopped_integral_comm_pointwise`). The equality remains almost sure for each
fixed stopping time; it does not assert an event simultaneous over all admissible stopping times.
-/

open LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace InnerProductSpace

namespace Sandpile.Support

/-- **A jointly integrable scalar representative identifies the Bochner integral pointwise.**
Given an integrable `F : U → Lp ℝ 2 P` and a jointly integrable `g` with `g u =ᵐ[P] F u` for
every `u`, the coercion of `∫ u, F u ∂μ` to a function agrees almost everywhere with
`ω ↦ ∫ u, g u ω ∂μ`. Proved by testing against indicators of finite-measure sets via
`ae_eq_of_forall_setIntegral_eq_of_sigmaFinite` and swapping the iterated integral. -/
theorem coe_integral_L2_eq_integral_of_integrable {U Ω : Type*} [MeasurableSpace U]
    [MeasurableSpace Ω]
    (μ : Measure U) [SigmaFinite μ] (P : Measure Ω) [SigmaFinite P]
    (F : U → Lp ℝ 2 P) (hF : Integrable F μ)
    (g : U → Ω → ℝ) (hg : Integrable (Function.uncurry g) (μ.prod P))
    (hgeq : ∀ u, g u =ᵐ[P] F u) :
    (fun ω => (∫ u, F u ∂μ) ω) =ᵐ[P] fun ω => ∫ u, g u ω ∂μ := by
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun s hs hPs => ?_) (fun _ _ _ => hg.integral_prod_right.integrableOn) ?_
  · haveI : IsFiniteMeasure (P.restrict s) := ⟨by simpa using hPs⟩
    exact ((Lp.memLp (∫ u, F u ∂μ)).mono_measure Measure.restrict_le_self).integrable (by norm_num)
  intro s hs hPs
  let L : Lp ℝ 2 P →L[ℝ] ℝ := innerSL ℝ (indicatorConstLp 2 hs hPs.ne (1 : ℝ))
  rw [← L2.inner_indicatorConstLp_one hs hPs.ne]
  change L (∫ u, F u ∂μ) = _
  rw [← L.integral_comp_comm hF]
  calc (∫ u, L (F u) ∂μ) = ∫ u, ∫ ω in s, g u ω ∂P ∂μ := by
        apply integral_congr_ae
        filter_upwards with u
        change inner ℝ (indicatorConstLp 2 hs hPs.ne (1 : ℝ)) (F u) = _
        rw [L2.inner_indicatorConstLp_one hs hPs.ne]
        apply setIntegral_congr_ae hs
        filter_upwards [hgeq u] with ω hω _
        exact hω.symm
    _ = ∫ ω in s, ∫ u, g u ω ∂μ ∂P :=
      integral_integral_swap (hg.mono_measure
        (Measure.prod_mono le_rfl Measure.restrict_le_self))

open Sandpile.Support Sandpile.Continuum

/-- **A Brownian Green kernel has spatial L1 mass equal to its horizon.** For `t ≥ 0`,
`greenTimeBM d t x`, the time-integrated Brownian heat kernel from `x` run up to time `t`, is
integrable in space and its spatial integral is exactly `t`. Proved by Fubini, using that
`heatKernelBM` integrates to `1` in space at every intermediate time. -/
theorem integrable_greenTimeBM_and_integral_eq {d : ℕ} (hd : 1 ≤ d) {t : ℝ} (ht : 0 ≤ t)
    (x : Space d) :
    Integrable (greenTimeBM d t x) volume ∧ (∫ y, greenTimeBM d t x y) = t := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) t)
  haveI : IsFiniteMeasure μ := ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioo_lt_top⟩
  let F (p : ℝ × Space d) := heatKernelBM d p.1 x p.2
  have hm : Measurable F := by unfold F heatKernelBM; fun_prop
  have hn (u : ℝ) (hu : 0 < u) : (∫ y : Space d, ‖F (u, y)‖) = 1 := by
    calc (∫ y : Space d, ‖F (u, y)‖) = ∫ y : Space d, F (u, y) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun y => Real.norm_of_nonneg (heatKernelBM_nonneg d hu.le x y)
      _ = 1 := integral_heatKernelBM_eq_one hd hu x
  have hi : Integrable F (μ.prod (volume : Measure (Space d))) := by
    refine (integrable_prod_iff hm.aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      exact integrable_heatKernelBM_space hd hu.1 x
    · refine (integrable_const (1 : ℝ)).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      exact (hn u hu.1).symm
  have he (y : Space d) : (∫ u, F (u, y) ∂μ) = greenTimeBM d t x y :=
    integral_restrict_eq_greenTimeBM ht x y
  refine ⟨hi.integral_prod_right.congr (Eventually.of_forall he), ?_⟩
  calc (∫ y, greenTimeBM d t x y) = ∫ y, ∫ u, F (u, y) ∂μ := by simp_rw [he]
    _ = ∫ u, (∫ y : Space d, F (u, y)) ∂μ := (integral_integral_swap hi).symm
    _ = ∫ _ : ℝ, (1 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
        exact integral_heatKernelBM_eq_one hd hu.1 x
    _ = t := by simp [μ, ht]

/-- **A measurable family of Green kernels bounded in time is integrable on the full product.**
Given a measurable `q : U → ℝ≥0 × Space d` with `(q u).1 ≤ T` for every `u`, the map
`(u, y) ↦ greenTimeBM d (q u).1 (q u).2 y` is integrable on `μ.prod volume`. Proved via
`integrable_prod_iff`, with the sections integrable by
`integrable_greenTimeBM_and_integral_eq` and their L1 norms dominated by the integrable constant
`T`. -/
theorem integrable_greenTimeBM_product {U : Type*} [MeasurableSpace U]
    (μ : Measure U) [IsFiniteMeasure μ] {d : ℕ} (hd : 1 ≤ d)
    (q : U → ℝ≥0 × Space d) (hq : Measurable q) (T : ℝ≥0)
    (hT : ∀ u, (q u).1 ≤ T) :
    Integrable (fun p : U × Space d => greenTimeBM d (q p.1).1 (q p.1).2 p.2)
      (μ.prod (volume : Measure (Space d))) := by
  have hq' : Measurable (fun p : U × Space d => (q p.1, p.2)) :=
    (hq.comp measurable_fst).prodMk measurable_snd
  have hm := (measurable_uncurry_greenTimeBM d).comp hq'
  have hsections : ∀ᵐ u ∂μ, Integrable (fun y => greenTimeBM d (q u).1 (q u).2 y) volume :=
    Eventually.of_forall fun u =>
      (integrable_greenTimeBM_and_integral_eq hd (t := ((q u).1 : ℝ)) (q u).1.property
        (q u).2).1
  have he (u : U) : (∫ y : Space d, ‖greenTimeBM d (q u).1 (q u).2 y‖) = ((q u).1 : ℝ) := by
    calc (∫ y : Space d, ‖greenTimeBM d (q u).1 (q u).2 y‖)
        = ∫ y : Space d, greenTimeBM d (q u).1 (q u).2 y := by
          apply integral_congr_ae
          exact Eventually.of_forall fun y => Real.norm_of_nonneg
            (greenTimeBM_nonneg d (q u).1.property (q u).2 y)
      _ = ((q u).1 : ℝ) :=
          (integrable_greenTimeBM_and_integral_eq hd (t := ((q u).1 : ℝ)) (q u).1.property
            (q u).2).2
  have htint : Integrable (fun u => ((q u).1 : ℝ)) μ := by
    apply (integrable_const (μ := μ) (T : ℝ)).mono' (hq.fst.subtype_val.aestronglyMeasurable)
    exact Eventually.of_forall fun u => by
      rw [Real.norm_of_nonneg (q u).1.property]
      exact_mod_cast hT u
  have hn : Integrable (fun u => ∫ y : Space d, ‖greenTimeBM d (q u).1 (q u).2 y‖) μ := by
    simpa only [he] using htint
  exact (integrable_prod_iff hm.aestronglyMeasurable).mpr ⟨hsections, hn⟩

end Sandpile.Support

namespace Sandpile.Continuum

open Sandpile.Support

/-- **The white-noise index of the stopped Gaussian potential is the literal spatial Green
kernel, pointwise.** At a fixed bounded stopping time `τ`, the stopped reward
`ω ↦ ∫ b, Z (T - τ b) (B (τ b) b) ω ∂PB` is a.e. equal to `W` evaluated at
`y ↦ ∫ b, √ν² · greenTimeBM d (T - τ b) (B (τ b) b) y ∂PB`, and the stopped reward is a.e.
integrable. Obtained from `gaussianPotential_stopped_integral_comm` by identifying its L2
representative `F` with the pointwise Green-kernel average `f` via
`coe_integral_L2_eq_integral_of_integrable`. -/
theorem gaussianPotential_stopped_integral_comm_pointwise {ΩW ΩB : Type*}
    [MeasurableSpace ΩW] [MeasurableSpace ΩB] {d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3)
    {PW : Measure ΩW} [IsProbabilityMeasure PW] {W : (Space d → ℝ) → ΩW → ℝ}
    (hW : IsWhiteNoise d W PW) (ν2 : ℝ) (Z : ℝ → Space d → ΩW → ℝ)
    (hmod : ∀ t : ℝ, 0 ≤ t → ∀ x, Z t x =ᵐ[PW] gaussianPotential d ν2 W t x)
    (hc : ∀ T : ℝ, 0 < T → ∀ᵐ ω ∂PW,
      ContinuousOn (fun p : ℝ × Space d => Z p.1 p.2 ω) (Set.Icc 0 T ×ˢ Set.univ))
    (PB : Measure ΩB) [IsProbabilityMeasure PB] (B : ℝ≥0 → ΩB → Space d)
    (hBc : ∀ ω, Continuous fun t => B t ω) (hBm : ∀ t, StronglyMeasurable (B t))
    (τ : ΩB → ℝ≥0) (hτm : Measurable τ) (T : ℝ≥0) (hτT : ∀ ω, τ ω ≤ T) :
    (∀ᵐ ω ∂PW, Integrable (fun b => Z ((T : ℝ) - τ b) (B (τ b) b) ω) PB) ∧
      W (fun y => ∫ b, Real.sqrt ν2 *
        greenTimeBM d ((T : ℝ) - τ b) (B (τ b) b) y ∂PB) =ᵐ[PW]
        fun ω => ∫ b, Z ((T : ℝ) - τ b) (B (τ b) b) ω ∂PB := by
  let q (b : ΩB) : ℝ≥0 × Space d :=
    (⟨(T : ℝ) - τ b, sub_nonneg.mpr (hτT b)⟩, B (τ b) b)
  have hq : Measurable q := measurable_stopped_spaceTime B hBc hBm τ hτm T hτT
  have hqT (b : ΩB) : (q b).1 ≤ T := show (T : ℝ) - τ b ≤ T from sub_le_self _ (τ b).property
  let F (b : ΩB) : Lp ℝ 2 (volume : Measure (Space d)) := Real.sqrt ν2 •
    (memLp_greenTimeBM hd hd3 (q b).1.property (q b).2).toLp (greenTimeBM d (q b).1 (q b).2)
  let f (b : ΩB) (y : Space d) := Real.sqrt ν2 * greenTimeBM d (q b).1 (q b).2 y
  have hF : Integrable F PB :=
    (integrable_greenTimeBM_toLp_of_bounded_time PB hd hd3 q hq T hqT).smul (Real.sqrt ν2)
  have hf : Integrable (Function.uncurry f) (PB.prod (volume : Measure (Space d))) :=
    (integrable_greenTimeBM_product PB hd q hq T hqT).const_mul (Real.sqrt ν2)
  have he (b : ΩB) : f b =ᵐ[volume] (fun y => F b y) := by
    filter_upwards [Lp.coeFn_smul (Real.sqrt ν2)
      ((memLp_greenTimeBM hd hd3 (q b).1.property (q b).2).toLp (greenTimeBM d (q b).1 (q b).2)),
      (memLp_greenTimeBM hd hd3 (q b).1.property (q b).2).coeFn_toLp] with y h1 h2
    change f b y = (Real.sqrt ν2 •
      (memLp_greenTimeBM hd hd3 (q b).1.property (q b).2).toLp (greenTimeBM d (q b).1 (q b).2)) y
    exact (congrArg (fun a : ℝ => Real.sqrt ν2 * a) h2).symm.trans h1.symm
  have hrep := coe_integral_L2_eq_integral_of_integrable PB volume F hF f hf he
  have hmem : MemLp (fun y => ∫ b, f b y ∂PB) 2 volume := MemLp.ae_eq hrep (Lp.memLp (∫ b, F b ∂PB))
  have hnoise : W (fun y => (∫ b, F b ∂PB) y) =ᵐ[PW] W (fun y => ∫ b, f b y ∂PB) := by
    apply ((hW.gaussian.hasGaussianLaw_eval _).memLp_two.toLp_eq_toLp_iff
      (hW.gaussian.hasGaussianLaw_eval _).memLp_two).mp
    exact toLp_eq_of_covariance_of_ae_eq volume PW W
      (fun a => (hW.gaussian.hasGaussianLaw_eval a).memLp_two) hW.cov _ _ (Lp.memLp _) hmem hrep
  have hmain := gaussianPotential_stopped_integral_comm hd hd3 hW ν2 Z hmod hc PB B hBc hBm
    τ hτm T hτT
  exact ⟨hmain.1, hnoise.symm.trans hmain.2⟩

end Sandpile.Continuum
