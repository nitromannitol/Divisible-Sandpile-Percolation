/-
Stochastic Fubini for white noise along Bochner-integrable spatial L2 families.

The white-noise linear isometry commutes with the Bochner integral. Its proof
uses finite simple families and linearity, then continuity in the L1 norm of the
parameter measure with values in L2. On a probability space Cauchy--Schwarz gives
L1 <= L2, so any joint version is integrable on the product. Testing the L2
integral against indicators identifies it with the scalar iterated integral.

The weak jointMeas clause supplies a version equal almost surely at each
parameter. Replacing that version by the actual evaluations requires actual
joint measurability; the final corollary states this hypothesis explicitly.
-/
import LatticeProb.Prob.L2JointVersion
import Sandpile.Support.LimNoiseCoordinates

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace InnerProductSpace

namespace Sandpile.Support

/-- On a probability space, the L1 norm is bounded by the L2 norm. -/
theorem integral_norm_L2_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (F : Lp ℝ 2 P) :
    (∫ ω, ‖F ω‖ ∂P) ≤ ‖F‖ := by
  rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable F),
    ← eLpNorm_one_eq_lintegral_enorm, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top F)
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (Lp.aestronglyMeasurable F))

/-- A joint version of an integrable L2 family is integrable on the product. -/
theorem integrable_joint_L2_version {U Ω : Type*} [MeasurableSpace U] [MeasurableSpace Ω]
    (μ : Measure U) (P : Measure Ω) [IsProbabilityMeasure P]
    (F : U → Lp ℝ 2 P) (hF : Integrable F μ)
    (g : U → Ω → ℝ) (hg : StronglyMeasurable (Function.uncurry g))
    (hgeq : ∀ u, g u =ᵐ[P] F u) :
    Integrable (Function.uncurry g) (μ.prod P) := by
  have hgi (u : U) : Integrable (g u) P :=
    ((Lp.memLp (F u)).integrable (by norm_num)).congr (hgeq u).symm
  refine (integrable_prod_iff hg.aestronglyMeasurable).2
    ⟨Eventually.of_forall hgi, ?_⟩
  refine hF.norm.mono' hg.norm.integral_prod_right.aestronglyMeasurable ?_
  filter_upwards with u
  change ‖∫ ω, ‖g u ω‖ ∂P‖ ≤ ‖F u‖
  rw [Real.norm_of_nonneg (integral_nonneg (fun ω => norm_nonneg (g u ω)))]
  calc (∫ ω, ‖g u ω‖ ∂P) = ∫ ω, ‖F u ω‖ ∂P := integral_congr_ae ((hgeq u).fun_comp norm)
    _ ≤ ‖F u‖ := integral_norm_L2_le P (F u)

/-- A Bochner L2 integral is represented by the integral of any integrable joint version. -/
theorem coe_integral_L2_eq_integral_version {U Ω : Type*} [MeasurableSpace U] [MeasurableSpace Ω]
    (μ : Measure U) [SigmaFinite μ] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : U → Lp ℝ 2 P) (hF : Integrable F μ)
    (g : U → Ω → ℝ) (hg : Integrable (Function.uncurry g) (μ.prod P))
    (hgeq : ∀ u, g u =ᵐ[P] F u) :
    (fun ω => (∫ u, F u ∂μ) ω) =ᵐ[P] fun ω => ∫ u, g u ω ∂μ := by
  refine Integrable.ae_eq_of_forall_setIntegral_eq _ _
    ((Lp.memLp (∫ u, F u ∂μ)).integrable (by norm_num)) hg.integral_prod_right ?_
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

/-- The second moment of a scalar integral is bounded by the square of the integral of L2 norms. -/
theorem integral_sq_integral_L2_version_le {U Ω : Type*} [MeasurableSpace U] [MeasurableSpace Ω]
    (μ : Measure U) [SigmaFinite μ] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : U → Lp ℝ 2 P) (hF : Integrable F μ)
    (g : U → Ω → ℝ) (hg : StronglyMeasurable (Function.uncurry g))
    (hgeq : ∀ u, g u =ᵐ[P] F u) :
    (∫ ω, (∫ u, g u ω ∂μ) ^ 2 ∂P) ≤ (∫ u, ‖F u‖ ∂μ) ^ 2 := by
  have hi := integrable_joint_L2_version μ P F hF g hg hgeq
  have he := coe_integral_L2_eq_integral_version μ P F hF g hi hgeq
  have hsq : (∫ ω, (∫ u, g u ω ∂μ) ^ 2 ∂P) = ‖∫ u, F u ∂μ‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [RCLike.inner_apply, conj_trivial]
    apply integral_congr_ae
    filter_upwards [he] with ω hω
    rw [hω]
    ring
  rw [hsq]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm _) 2

open Sandpile.Continuum

/-- The L2 noise isometry agrees with the original coordinate of an L2 test function. -/
theorem whiteNoiseLinearIsometry_toLp_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {P : Measure Ω} {W : (Space d → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise d W P) (f : Space d → ℝ) (hf : MemLp f 2 volume) :
    (fun ω => Sandpile.Support.whiteNoiseLinearIsometry hW (hf.toLp f) ω) =ᵐ[P] W f := by
  have he := LatticeProb.toLp_eq_of_covariance_of_ae_eq volume P W
    (fun q => (hW.gaussian.hasGaussianLaw_eval q).memLp_two) hW.cov
    (fun x => hf.toLp f x) f (Lp.memLp _) hf hf.coeFn_toLp
  change (fun ω => (hW.gaussian.hasGaussianLaw_eval
    (fun x => hf.toLp f x)).memLp_two.toLp (W (fun x => hf.toLp f x)) ω) =ᵐ[P] W f
  rw [he]
  exact (hW.gaussian.hasGaussianLaw_eval f).memLp_two.coeFn_toLp

end Sandpile.Support

namespace Sandpile.Continuum

open Sandpile.Support

/-- Stochastic Fubini for any jointly measurable version of a white-noise family. -/
theorem whiteNoise_integral_comm_of_version {Ω U : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
    {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (μ : Measure U) [SigmaFinite μ] (f : U → Space d → ℝ)
    (hf : ∀ u, MemLp (f u) 2 volume)
    (hF : Integrable (fun u => (hf u).toLp (f u)) μ)
    (g : U → Ω → ℝ) (hg : StronglyMeasurable (Function.uncurry g))
    (hgeq : ∀ u, g u =ᵐ[P] W (f u)) :
    Integrable (Function.uncurry g) (μ.prod P) ∧
      W (fun x => (∫ u, (hf u).toLp (f u) ∂μ) x) =ᵐ[P]
        fun ω => ∫ u, g u ω ∂μ := by
  let L := Sandpile.Support.whiteNoiseLinearIsometry hW
  let F (u : U) : Lp ℝ 2 (volume : Measure (Space d)) := (hf u).toLp (f u)
  have hLF : Integrable (fun u => L (F u)) μ :=
    L.toContinuousLinearMap.integrable_comp hF
  have he (u : U) : g u =ᵐ[P] (fun ω => L (F u) ω) :=
    (hgeq u).trans (whiteNoiseLinearIsometry_toLp_ae_eq hW (f u) (hf u)).symm
  have hi := Sandpile.Support.integrable_joint_L2_version μ P _ hLF g hg he
  refine ⟨hi, ?_⟩
  have hc := Sandpile.Support.coe_integral_L2_eq_integral_version μ P _ hLF g hi he
  have hl : (∫ u, L (F u) ∂μ) = L (∫ u, F u ∂μ) :=
    L.toContinuousLinearMap.integral_comp_comm hF
  rw [hl] at hc
  have hw : (fun ω => L (∫ u, F u ∂μ) ω) =ᵐ[P]
      W (fun x => (∫ u, F u ∂μ) x) :=
    (hW.gaussian.hasGaussianLaw_eval (fun x => (∫ u, F u ∂μ) x)).memLp_two.coeFn_toLp
  exact hw.symm.trans hc

universe vΩ vU

/-- White noise commutes with the integral of an L1 family of spatial L2 functions, using a joint version. -/
theorem whiteNoise_integral_comm {Ω : Type vΩ} {U : Type vU}
    [MeasurableSpace Ω] [MeasurableSpace U] {d : ℕ}
    {P : Measure Ω} [IsProbabilityMeasure P] {W : (Space d → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise.{vΩ} d W P) (μ : Measure U) [SigmaFinite μ]
    (f : U → Space d → ℝ) (hf : ∀ u, MemLp (f u) 2 volume)
    (hs : StronglyMeasurable (fun u => (hf u).toLp (f u)))
    (hF : Integrable (fun u => (hf u).toLp (f u)) μ) :
    ∃ g : U → Ω → ℝ, StronglyMeasurable (Function.uncurry g) ∧
      (∀ u, g u =ᵐ[P] W (f u)) ∧ Integrable (Function.uncurry g) (μ.prod P) ∧
        W (fun x => (∫ u, (hf u).toLp (f u) ∂μ) x) =ᵐ[P]
          fun ω => ∫ u, g u ω ∂μ := by
  obtain ⟨g, hg, hgeq⟩ := hW.jointMeas_univ μ f hf hs
  have hi := whiteNoise_integral_comm_of_version hW μ f hf hF g hg hgeq
  exact ⟨g, hg, hgeq, hi.1, hi.2⟩

theorem whiteNoise_integral_comm_of_jointMeasurable {Ω U : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
    {d : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (Space d → ℝ) → Ω → ℝ} (hW : IsWhiteNoise d W P)
    (μ : Measure U) [SigmaFinite μ] (f : U → Space d → ℝ)
    (hf : ∀ u, MemLp (f u) 2 volume)
    (hF : Integrable (fun u => (hf u).toLp (f u)) μ)
    (hg : StronglyMeasurable (fun p : U × Ω => W (f p.1) p.2)) :
    Integrable (fun p : U × Ω => W (f p.1) p.2) (μ.prod P) ∧
      W (fun x => (∫ u, (hf u).toLp (f u) ∂μ) x) =ᵐ[P]
        fun ω => ∫ u, W (f u) ω ∂μ := by
  exact whiteNoise_integral_comm_of_version hW μ f hf hF (fun u ω => W (f u) ω) hg
    (fun _ => Filter.EventuallyEq.rfl)

end Sandpile.Continuum
