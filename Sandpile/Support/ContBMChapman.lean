import Sandpile.Support.ContBMMass

/-!
# Chapman-Kolmogorov for the Brownian heat kernel

Chapman-Kolmogorov for the Brownian heat kernel of `eq:brownian-heat-green-kernels`
(`sandpile.tex:963-968`):

  `∫ p^{BM}_s(x,y) p^{BM}_{s'}(x,y) dy = p^{BM}_{s+s'}(x,x)`.

The kernel factors as a product of one-dimensional Gaussian densities (`heatKernelBM_eq_prod`),
so the identity reduces to the one-dimensional statement that the integral of the product of two
Gaussian densities with a common mean and variances `v` and `v'` is the value at the mean of the
density of variance `v+v'`. That in turn is the translated Gaussian integral.

This is what turns the `L²` norm of the finite-time Green kernel `g^{BM}_t(x,·)` into the double
time integral of `p^{BM}_{s+s'}(x,x)`, which is finite exactly when `d < 4`; it is the identity
behind the square-integrability the white noise asks of its index in the dimension one-to-three
chain.
-/

open MeasureTheory
open scoped NNReal Real

namespace Sandpile.Support

open Sandpile.Continuum

/-- The translated Gaussian integral. -/
theorem integral_exp_neg_mul_sq_sub (m : ℝ) (b : ℝ) :
    ∫ u : ℝ, Real.exp (-b * (u - m) ^ 2) = Real.sqrt (Real.pi / b) := by
  rw [integral_sub_right_eq_self (fun u : ℝ => Real.exp (-b * u ^ 2)) m]
  exact integral_gaussian b

/-- The integral of the product of two Gaussian densities with the same mean. -/
theorem integral_gaussianPDFReal_mul (m : ℝ) {v v' : ℝ≥0} (hv : (0:ℝ) < v) (hv' : (0:ℝ) < v') :
    ∫ u : ℝ, ProbabilityTheory.gaussianPDFReal m v u * ProbabilityTheory.gaussianPDFReal m v' u
      = (Real.sqrt (2 * Real.pi * ((v : ℝ) + (v' : ℝ))))⁻¹ := by
  have hpi := Real.pi_pos
  set b : ℝ := (1 : ℝ) / (2 * (v : ℝ)) + (1 : ℝ) / (2 * (v' : ℝ)) with hb
  have hb0 : 0 < b := by positivity
  have hint : ∀ u : ℝ,
      ProbabilityTheory.gaussianPDFReal m v u * ProbabilityTheory.gaussianPDFReal m v' u
        = ((Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ * (Real.sqrt (2 * Real.pi * (v' : ℝ)))⁻¹) *
            Real.exp (-b * (u - m) ^ 2) := by
    intro u
    rw [ProbabilityTheory.gaussianPDFReal, ProbabilityTheory.gaussianPDFReal,
      mul_mul_mul_comm, ← Real.exp_add]
    congr 1
    rw [hb]
    field_simp
    ring_nf
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hint),
    MeasureTheory.integral_const_mul, integral_exp_neg_mul_sq_sub m b]
  rw [show Real.pi / b = 2 * Real.pi * (v : ℝ) * (2 * Real.pi * (v' : ℝ)) /
      (2 * Real.pi * ((v : ℝ) + (v' : ℝ))) by rw [hb]; field_simp; ring_nf]
  rw [← Real.sqrt_inv, ← Real.sqrt_inv, ← Real.sqrt_mul (by positivity),
    ← Real.sqrt_mul (by positivity), ← Real.sqrt_inv]
  congr 1
  field_simp

/-- **Chapman-Kolmogorov for the Brownian heat kernel.**  The space integral of
the product of two kernels based at the same point is the kernel at the sum of
the two times, on the diagonal. -/
theorem integral_heatKernelBM_mul {d : ℕ} (hd : 1 ≤ d) {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (x : Space d) :
    ∫ y : Space d, heatKernelBM d s x y * heatKernelBM d s' x y
      = heatKernelBM d (s + s') x x := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hv : (0 : ℝ) < s / d := by positivity
  have hv' : (0 : ℝ) < s' / d := by positivity
  have hcast : ((Real.toNNReal (s / d) : ℝ≥0) : ℝ) = s / d := Real.coe_toNNReal _ hv.le
  have hcast' : ((Real.toNNReal (s' / d) : ℝ≥0) : ℝ) = s' / d := Real.coe_toNNReal _ hv'.le
  have hprod : ∀ y : Space d, heatKernelBM d s x y * heatKernelBM d s' x y
      = ∏ i : Fin d, (ProbabilityTheory.gaussianPDFReal (x i) (Real.toNNReal (s / d)) (y i) *
          ProbabilityTheory.gaussianPDFReal (x i) (Real.toNNReal (s' / d)) (y i)) := by
    intro y
    rw [heatKernelBM_eq_prod hd hs x y, heatKernelBM_eq_prod hd hs' x y, ← Finset.prod_mul_distrib]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hprod),
    integral_euclidean_prod d (fun i u =>
      ProbabilityTheory.gaussianPDFReal (x i) (Real.toNNReal (s / d)) u *
        ProbabilityTheory.gaussianPDFReal (x i) (Real.toNNReal (s' / d)) u)]
  have hone : ∀ i : Fin d,
      (∫ u : ℝ, ProbabilityTheory.gaussianPDFReal (x i) (Real.toNNReal (s / d)) u *
        ProbabilityTheory.gaussianPDFReal (x i) (Real.toNNReal (s' / d)) u)
      = (Real.sqrt (2 * Real.pi * ((s + s') / d)))⁻¹ := by
    intro i
    rw [integral_gaussianPDFReal_mul (x i) (by rw [hcast]; exact hv) (by rw [hcast']; exact hv'),
      hcast, hcast']
    congr 2
    ring
  rw [Finset.prod_congr rfl fun i _ => hone i, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, heatKernelBM, sub_self, norm_zero,
    show (4 * Real.pi * (s + s') / (2 * (d : ℝ))) = 2 * Real.pi * ((s + s') / d) by
      field_simp; ring,
    inv_sqrt_pow_eq_rpow (by positivity) d]
  simp

end Sandpile.Support
