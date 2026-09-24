/-
Exact exponential moments of finite Gaussian linear combinations
and their transport to the iid scenery law.
-/
import Sandpile.Support.GaussianScale
import Sandpile.Support.FiniteKernelTail

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

noncomputable section
namespace Sandpile

lemma hasSubgaussianMGF_mono {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {c C : ℝ≥0} (hX : HasSubgaussianMGF X c μ) (hc : c ≤ C) :
    HasSubgaussianMGF X C μ where
  integrable_exp_mul := hX.integrable_exp_mul
  mgf_le a := (hX.mgf_le a).trans (Real.exp_le_exp.mpr (by gcongr))

lemma gaussian_linear_exp_eq_prod {I : Type*} [Fintype I] (b : I → ℝ) (a : ℝ) (x : I → ℝ) :
    Real.exp (a * ∑ i, b i * x i) = ∏ i, Real.exp ((a * b i) * x i) := by
  rw [← Real.exp_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma integrable_exp_gaussian_linear {I : Type*} [Fintype I] (b : I → ℝ) (v : ℝ≥0) (a : ℝ) :
    Integrable (fun x : I → ℝ => Real.exp (a * ∑ i, b i * x i)) (Measure.pi (fun _ : I => gaussianReal 0 v)) := by
  simp_rw [gaussian_linear_exp_eq_prod]
  exact Integrable.fintype_prod (fun i => integrable_exp_mul_gaussianReal (a * b i))

lemma integral_exp_gaussian_linear {I : Type*} [Fintype I] (b : I → ℝ) (v : ℝ≥0) (a : ℝ) :
    (∫ x : I → ℝ, Real.exp (a * ∑ i, b i * x i) ∂Measure.pi (fun _ : I => gaussianReal 0 v)) =
      Real.exp ((v : ℝ) * (∑ i, b i ^ 2) * a ^ 2 / 2) := by
  simp_rw [gaussian_linear_exp_eq_prod]
  rw [integral_fintype_prod_eq_prod (fun i x => Real.exp ((a * b i) * x))]
  have he (i : I) : (∫ x : ℝ, Real.exp ((a * b i) * x) ∂gaussianReal 0 v) =
      Real.exp ((v : ℝ) * (a * b i) ^ 2 / 2) := by
    simpa only [mgf, id_eq, zero_mul, zero_add] using congrFun (mgf_id_gaussianReal (μ := 0) (v := v)) (a * b i)
  simp_rw [he]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma hasSubgaussianMGF_gaussian_linear {I : Type*} [Fintype I] (b : I → ℝ) (v : ℝ≥0) :
    HasSubgaussianMGF (fun x : I → ℝ => ∑ i, b i * x i)
      ⟨(v : ℝ) * ∑ i, b i ^ 2, mul_nonneg v.coe_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg (b i)))⟩
      (Measure.pi (fun _ : I => gaussianReal 0 v)) where
  integrable_exp_mul := integrable_exp_gaussian_linear b v
  mgf_le a := by
    change (∫ x : I → ℝ, Real.exp (a * ∑ i, b i * x i) ∂Measure.pi (fun _ : I => gaussianReal 0 v)) ≤ _
    rw [integral_exp_gaussian_linear]
    rfl

lemma hasSubgaussianMGF_iid_finite_sum {d : ℕ} (s : Finset (Site d)) (b : Site d → ℝ)
    (v C : ℝ≥0) (hC : (v : ℝ) * (∑ y ∈ s, b y ^ 2) ≤ C) :
    HasSubgaussianMGF (fun ζ : Site d → ℝ => ∑ y ∈ s, b y * ζ y) C
      (LatticeProb.iidLaw d (gaussianReal 0 v)) := by
  have hg := hasSubgaussianMGF_gaussian_linear (fun y : s => b y) v
  have hc : (⟨(v : ℝ) * ∑ y : s, b y ^ 2, by positivity⟩ : ℝ≥0) ≤ C := by
    change (v : ℝ) * (∑ y : s, b y ^ 2) ≤ C
    rw [Finset.sum_coe_sort s (fun y => b y ^ 2)]
    exact hC
  have hh := hasSubgaussianMGF_mono hg hc
  have hm := measurePreserving_finite_restrict (gaussianReal 0 v) s
  rw [← hm.map_eq] at hh
  have hp := hh.of_map hm.aemeasurable
  change HasSubgaussianMGF (fun ζ : Site d → ℝ => ∑ y : s, b y * ζ y) C
    (LatticeProb.iidLaw d (gaussianReal 0 v)) at hp
  have he : (fun ζ : Site d → ℝ => ∑ y : s, b y * ζ y) = (fun ζ => ∑ y ∈ s, b y * ζ y) := by
    funext ζ
    exact Finset.sum_coe_sort s (fun y => b y * ζ y)
  rw [he] at hp
  exact hp

end Sandpile
