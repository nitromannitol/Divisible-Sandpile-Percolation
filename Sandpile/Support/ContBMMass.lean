/-
The total mass of the Brownian heat kernel of `eq:brownian-heat-green-kernels`
(`sandpile.tex:963-968`): `∫ p^{BM}_t(x,y) dy = 1` for every positive time.

The kernel `p^{BM}_t(x,y) = (4\pi t/(2d))^{-d/2}e^{-d|x-y|^2/(2t)}` is the
density of the Gaussian of variance `t/d` in each coordinate, so it factors as a
product of one-dimensional Gaussian densities and its integral is the product of
their integrals.  This is what bounds a double space integral against the kernel
by the product of the sup-norm and the `L¹` norm of the test function,
`∫∫|φ(u)||φ(v)|p^{BM}_t(u,v) ≤ ‖φ‖_∞‖φ‖_1`, uniformly in `t`, which is the
estimate that removes the small times from the double time integral of
`prop:weighted-membrane-limit`.
-/
import Sandpile.Support.ContBMKernel
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory Filter Topology
open scoped NNReal

namespace Sandpile.Support

open Sandpile.Continuum

/-! ### The kernel as a product of one-dimensional Gaussian densities -/

/-- The squared Euclidean norm of a difference is the sum of the squared
coordinate differences. -/
theorem norm_sq_sub_eq_sum {d : ℕ} (x y : Space d) :
    ‖x - y‖ ^ 2 = ∑ i : Fin d, (y i - x i) ^ 2 := by
  rw [← dist_eq_norm, EuclideanSpace.dist_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.dist_eq, sq_abs]
  ring

/-- The inverse square root raised to a natural power is the negative half
power. -/
theorem inv_sqrt_pow_eq_rpow {A : ℝ} (hA : 0 < A) (d : ℕ) :
    (Real.sqrt A)⁻¹ ^ d = A ^ (-(d : ℝ) / 2) := by
  have h1 : (Real.sqrt A)⁻¹ = A ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hA.le]
  rw [h1, ← Real.rpow_natCast (A ^ (-(1 / 2 : ℝ))) d, ← Real.rpow_mul hA.le]
  congr 1
  ring

/-- The product of the one-dimensional Gaussian densities whose means are the
coordinates of `x`. -/
theorem prod_gaussianPDFReal_at {d : ℕ} (v : ℝ≥0) (x y : Space d) :
    ∏ i : Fin d, ProbabilityTheory.gaussianPDFReal (x i) v (y i)
      = (Real.sqrt (2 * Real.pi * v))⁻¹ ^ d *
        Real.exp (-(∑ i : Fin d, (y i - x i) ^ 2) / (2 * v)) := by
  simp only [ProbabilityTheory.gaussianPDFReal]
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum, Finset.card_univ,
    Fintype.card_fin]
  congr 1
  rw [← Finset.sum_div]
  congr 1
  rw [← Finset.sum_neg_distrib]

/-- **The Brownian heat kernel is the product of the one-dimensional Gaussian
densities of variance `t/d`.** -/
theorem heatKernelBM_eq_prod {d : ℕ} (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) (x y : Space d) :
    heatKernelBM d t x y
      = ∏ i : Fin d, ProbabilityTheory.gaussianPDFReal (x i) (Real.toNNReal (t / d)) (y i) := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpos : (0 : ℝ) < t / d := by positivity
  have hv : ((Real.toNNReal (t / d) : ℝ≥0) : ℝ) = t / d := Real.coe_toNNReal _ hpos.le
  have hA : (0 : ℝ) < 4 * Real.pi * t / (2 * d) := by
    have := Real.pi_pos
    positivity
  have hAv : 2 * Real.pi * ((Real.toNNReal (t / d) : ℝ≥0) : ℝ) = 4 * Real.pi * t / (2 * d) := by
    rw [hv]
    field_simp
    ring
  have hpre : (Real.sqrt (2 * Real.pi * ((Real.toNNReal (t / d) : ℝ≥0) : ℝ)))⁻¹ ^ d
      = (4 * Real.pi * t / (2 * d)) ^ (-(d : ℝ) / 2) := by
    rw [hAv]
    exact inv_sqrt_pow_eq_rpow hA d
  rw [heatKernelBM, prod_gaussianPDFReal_at, hpre]
  congr 1
  rw [← norm_sq_sub_eq_sum, hv]
  field_simp

/-! ### The total mass -/

/-- The integral over Euclidean space of a product of one-dimensional factors is
the product of the one-dimensional integrals. -/
theorem integral_euclidean_prod (d : ℕ) (f : Fin d → ℝ → ℝ) :
    ∫ y : Space d, ∏ i, f i (y i) = ∏ i, ∫ z : ℝ, f i z := by
  rw [← MeasureTheory.integral_fintype_prod_volume_eq_prod (fun i : Fin d => f i)]
  exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp'
    (fun w : Fin d → ℝ => ∏ i, f i (w i))

/-- **The Brownian heat kernel has total mass one at every positive time.** -/
theorem integral_heatKernelBM_eq_one {d : ℕ} (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) (x : Space d) :
    ∫ y : Space d, heatKernelBM d t x y = 1 := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpos : (0 : ℝ) < t / d := by positivity
  have hne : Real.toNNReal (t / d) ≠ 0 := by
    simpa using hpos
  calc ∫ y : Space d, heatKernelBM d t x y
      = ∫ y : Space d,
          ∏ i : Fin d, ProbabilityTheory.gaussianPDFReal (x i) (Real.toNNReal (t / d)) (y i) := by
        exact integral_congr_ae (Filter.Eventually.of_forall
          fun y => heatKernelBM_eq_prod hd ht x y)
    _ = ∏ i : Fin d, ∫ z : ℝ, ProbabilityTheory.gaussianPDFReal (x i) (Real.toNNReal (t / d)) z :=
        integral_euclidean_prod d
          (fun i z => ProbabilityTheory.gaussianPDFReal (x i) (Real.toNNReal (t / d)) z)
    _ = 1 := by
        rw [Finset.prod_congr rfl fun i _ =>
          ProbabilityTheory.integral_gaussianPDFReal_eq_one (x i) hne]
        simp

end Sandpile.Support
