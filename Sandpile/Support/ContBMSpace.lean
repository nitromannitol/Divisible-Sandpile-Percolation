/-
The two estimates on the Brownian heat kernel of `eq:brownian-heat-green-kernels`
(`sandpile.tex:963-968`) that the Riemann-sum argument of
`prop:weighted-membrane-limit` (`sandpile.tex:4724-4729`) consumes.

The first is the space estimate.  The kernel is integrable in its second
variable with total mass one, so a double space integral against it is bounded
by the sup-norm times the `L¹` norm of the test function,

  `|∫∫ p^{BM}_t(u,v) φ(v) φ(u)| ≤ ‖φ‖_∞ ‖φ‖_1`,

UNIFORMLY in the time.  This is what removes the small times from the double
time integral: the strip of times removed has area `O(δ)` and the integrand is
bounded there by this estimate, with no Gaussian bound and no diagonal
singularity.

The second is the space regularity.  The kernel depends on its two space
arguments only through the squared distance, and the exponential is
one-Lipschitz, so on times bounded below by `t₀` it is Lipschitz in the squared
distance with a constant depending only on `t₀` and `d`.  This is what replaces
the mesh points by the points themselves in the integrand of the double time
sum: the limit theorems of `Sandpile.Support.ContMeshIntegral` take a FIXED
integrand, while the integrand the local central limit theorem produces depends
on `R` through the mesh.
-/
import Sandpile.Support.ContBMMass

open MeasureTheory Filter Topology
open scoped NNReal

namespace Sandpile.Support

open Sandpile.Continuum

/-! ### Integrability and the total mass -/

/-- A product of integrable one-dimensional factors is integrable on Euclidean
space. -/
theorem integrable_euclidean_prod (d : ℕ) (f : Fin d → ℝ → ℝ)
    (hf : ∀ i, Integrable (f i)) :
    Integrable (fun y : Space d => ∏ i, f i (y i)) := by
  have hpi : Integrable (fun w : Fin d → ℝ => ∏ i, f i (w i)) := by
    rw [MeasureTheory.volume_pi]
    exact MeasureTheory.Integrable.fintype_prod_dep (fun i => hf i)
  exact ((EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)).2 hpi

/-- The Brownian heat kernel is integrable in its second variable at every
positive time. -/
theorem integrable_heatKernelBM {d : ℕ} (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t) (x : Space d) :
    Integrable (fun y : Space d => heatKernelBM d t x y) := by
  have hbase := integrable_euclidean_prod d
    (fun i z => ProbabilityTheory.gaussianPDFReal (x i) (Real.toNNReal (t / d)) z)
    (fun i => ProbabilityTheory.integrable_gaussianPDFReal _ _)
  refine hbase.congr (Filter.Eventually.of_forall fun y => ?_)
  exact (heatKernelBM_eq_prod hd ht x y).symm

/-! ### The space estimate -/

/-- **The double space integral against the Brownian heat kernel is at most the
sup-norm times the `L¹` norm of the test function, uniformly in the time.**  The
kernel has total mass one, so the inner integral is bounded by the sup-norm at
every point and every time, with no dependence on the time and no Gaussian
estimate. -/
theorem abs_integral2_heatKernelBM_le {d : ℕ} (hd : 1 ≤ d) {t : ℝ} (ht : 0 < t)
    (φ : Space d → ℝ) (hφ : Integrable φ) (C : ℝ) (hC : ∀ z, |φ z| ≤ C) :
    |∫ u : Space d, (∫ v : Space d, heatKernelBM d t u v * φ v) * φ u|
      ≤ C * ∫ z, |φ z| := by
  have hker : ∀ u : Space d, Integrable (fun v : Space d => heatKernelBM d t u v) :=
    fun u => integrable_heatKernelBM hd ht u
  have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg (φ 0)) (hC 0)
  have hMbd : ∀ u : Space d, ∀ᵐ v : Space d,
      ‖heatKernelBM d t u v‖ ≤ (4 * Real.pi * t / (2 * d)) ^ (-(d : ℝ) / 2) := fun u =>
    Filter.Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (heatKernelBM_nonneg d ht.le u v)]
      exact heatKernelBM_le d ht u v
  have hint1 : ∀ u : Space d,
      Integrable (fun v : Space d => heatKernelBM d t u v * |φ v|) := fun u =>
    hφ.abs.bdd_mul (hker u).aestronglyMeasurable (hMbd u)
  have key : ∀ u : Space d, |∫ v : Space d, heatKernelBM d t u v * φ v| ≤ C := by
    intro u
    calc |∫ v : Space d, heatKernelBM d t u v * φ v|
        ≤ ∫ v : Space d, |heatKernelBM d t u v * φ v| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ = ∫ v : Space d, heatKernelBM d t u v * |φ v| := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
          show |heatKernelBM d t u v * φ v| = heatKernelBM d t u v * |φ v|
          rw [abs_mul, abs_of_nonneg (heatKernelBM_nonneg d ht.le u v)]
      _ ≤ ∫ v : Space d, heatKernelBM d t u v * C :=
          MeasureTheory.integral_mono (hint1 u) ((hker u).mul_const C)
            (fun v => mul_le_mul_of_nonneg_left (hC v) (heatKernelBM_nonneg d ht.le u v))
      _ = C := by
          rw [MeasureTheory.integral_mul_const, integral_heatKernelBM_eq_one hd ht u, one_mul]
  by_cases hI : Integrable (fun u : Space d =>
      (∫ v : Space d, heatKernelBM d t u v * φ v) * φ u)
  · calc |∫ u : Space d, (∫ v : Space d, heatKernelBM d t u v * φ v) * φ u|
        ≤ ∫ u : Space d, |(∫ v : Space d, heatKernelBM d t u v * φ v) * φ u| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ u : Space d, C * |φ u| := by
          refine MeasureTheory.integral_mono hI.abs (hφ.abs.const_mul C) (fun u => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (key u) (abs_nonneg (φ u))
      _ = C * ∫ z : Space d, |φ z| := MeasureTheory.integral_const_mul C _
  · rw [MeasureTheory.integral_undef hI]
    simpa using mul_nonneg hC0 (MeasureTheory.integral_nonneg fun z => abs_nonneg (φ z))

/-! ### The space regularity -/

theorem abs_exp_neg_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |Real.exp (-a) - Real.exp (-b)| ≤ |a - b| := by
  have key : ∀ c e : ℝ, 0 ≤ c → c ≤ e → Real.exp (-c) - Real.exp (-e) ≤ e - c := by
    intro c e hc hce
    have h1 : -(e - c) + 1 ≤ Real.exp (-(e - c)) := Real.add_one_le_exp _
    have h2 : Real.exp (-c) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h3 : Real.exp (-e) = Real.exp (-c) * Real.exp (-(e - c)) := by
      rw [← Real.exp_add]; ring_nf
    have h4 : (0 : ℝ) < Real.exp (-c) := Real.exp_pos _
    nlinarith
  rcases le_total a b with h | h
  · have h5 : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ Real.exp (-a) - Real.exp (-b)),
      abs_of_nonpos (by linarith : a - b ≤ 0)]
    linarith [key a b ha h]
  · have h5 : Real.exp (-a) ≤ Real.exp (-b) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonpos (by linarith : Real.exp (-a) - Real.exp (-b) ≤ 0),
      abs_of_nonneg (by linarith : (0:ℝ) ≤ a - b)]
    linarith [key b a hb h]

/-- **The Brownian heat kernel is Lipschitz in the squared distance, uniformly
over the times at least `t₀`.** -/
theorem abs_heatKernelBM_sub_le {d : ℕ} (hd : 1 ≤ d) {t₀ s : ℝ} (ht₀ : 0 < t₀) (hs : t₀ ≤ s)
    (x y x' y' : Space d) :
    |heatKernelBM d s x y - heatKernelBM d s x' y'|
      ≤ (4 * Real.pi * t₀ / (2 * d)) ^ (-(d : ℝ) / 2) *
        ((d : ℝ) * |‖x - y‖ ^ 2 - ‖x' - y'‖ ^ 2| / (2 * t₀)) := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le ht₀ hs
  have hpi := Real.pi_pos
  have hA0 : (0 : ℝ) < 4 * Real.pi * t₀ / (2 * d) := by positivity
  have hbase : 4 * Real.pi * t₀ / (2 * d) ≤ 4 * Real.pi * s / (2 * d) := by
    have h1 : 4 * Real.pi * t₀ ≤ 4 * Real.pi * s := by nlinarith
    gcongr
  have hAs := Real.rpow_le_rpow_of_nonpos hA0 hbase (by linarith : -(d : ℝ) / 2 ≤ 0)
  set a : ℝ := (d : ℝ) * ‖x - y‖ ^ 2 / (2 * s) with hadef
  set b : ℝ := (d : ℝ) * ‖x' - y'‖ ^ 2 / (2 * s) with hbdef
  have ha0 : 0 ≤ a := by rw [hadef]; positivity
  have hb0 : 0 ≤ b := by rw [hbdef]; positivity
  have hrw : heatKernelBM d s x y - heatKernelBM d s x' y'
      = (4 * Real.pi * s / (2 * d)) ^ (-(d : ℝ) / 2) * (Real.exp (-a) - Real.exp (-b)) := by
    rw [heatKernelBM, heatKernelBM, hadef, hbdef]
    ring_nf
  have hAsnn : 0 ≤ (4 * Real.pi * s / (2 * d)) ^ (-(d : ℝ) / 2) :=
    Real.rpow_nonneg (by positivity) _
  have hdiff : |a - b| = (d : ℝ) * |‖x - y‖ ^ 2 - ‖x' - y'‖ ^ 2| / (2 * s) := by
    rw [hadef, hbdef, ← sub_div, ← mul_sub, abs_div, abs_mul,
      abs_of_pos (by positivity : (0:ℝ) < 2 * s), abs_of_pos hd']
  rw [hrw, abs_mul, abs_of_nonneg hAsnn]
  have hstep : |Real.exp (-a) - Real.exp (-b)|
      ≤ (d : ℝ) * |‖x - y‖ ^ 2 - ‖x' - y'‖ ^ 2| / (2 * s) := by
    rw [← hdiff]; exact abs_exp_neg_sub_le ha0 hb0
  have hmono : (d : ℝ) * |‖x - y‖ ^ 2 - ‖x' - y'‖ ^ 2| / (2 * s)
      ≤ (d : ℝ) * |‖x - y‖ ^ 2 - ‖x' - y'‖ ^ 2| / (2 * t₀) := by
    have hnum : (0:ℝ) ≤ (d : ℝ) * |‖x - y‖ ^ 2 - ‖x' - y'‖ ^ 2| := by positivity
    gcongr
  exact mul_le_mul hAs (le_trans hstep hmono) (abs_nonneg _) (Real.rpow_nonneg hA0.le _)

/-! ### The kernel at a time bounded below

The double time sum of `prop:weighted-membrane-limit` is compared with a double
time integral whose integrand must be bounded and continuous on the WHOLE plane,
while the Brownian kernel is a junk value at time zero and unbounded near it.
Reading it at `max s t₀` repairs both, and agrees with the kernel itself
wherever the weight of the sum is supported. -/

/-- The Brownian heat kernel, read at a time bounded below, is continuous in the
time. -/
theorem continuous_heatKernelBM_max {d : ℕ} (hd : 1 ≤ d) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (u v : Space d) :
    Continuous fun s : ℝ => heatKernelBM d (max s t₀) u v := by
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpi := Real.pi_pos
  have hmax : Continuous fun s : ℝ => max s t₀ := continuous_id.max continuous_const
  have hposmax : ∀ s : ℝ, 0 < max s t₀ := fun s => lt_of_lt_of_le ht₀ (le_max_right s t₀)
  have hbase : Continuous fun s : ℝ => 4 * Real.pi * max s t₀ / (2 * (d : ℝ)) :=
    (continuous_const.mul hmax).div_const _
  have h1 : Continuous fun s : ℝ =>
      (4 * Real.pi * max s t₀ / (2 * (d : ℝ))) ^ (-(d : ℝ) / 2) := by
    refine hbase.rpow_const fun s => Or.inl ?_
    have hp : (0 : ℝ) < 4 * Real.pi * max s t₀ / (2 * (d : ℝ)) := by
      have := hposmax s
      positivity
    exact ne_of_gt hp
  have h2 : Continuous fun s : ℝ =>
      Real.exp (-(d : ℝ) * ‖u - v‖ ^ 2 / (2 * max s t₀)) := by
    refine Real.continuous_exp.comp (Continuous.div continuous_const (continuous_const.mul hmax) ?_)
    intro s
    have := hposmax s
    positivity
  exact h1.mul h2

/-- The kernel read at a time bounded below is bounded by its value on the diagonal at
that time. -/
theorem abs_heatKernelBM_max_le {d : ℕ} (hd : 1 ≤ d) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (u v : Space d) (s : ℝ) :
    |heatKernelBM d (max s t₀) u v| ≤ (4 * Real.pi * t₀ / (2 * d)) ^ (-(d : ℝ) / 2) := by
  have hposmax : (0 : ℝ) < max s t₀ := lt_of_lt_of_le ht₀ (le_max_right s t₀)
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpi := Real.pi_pos
  rw [abs_of_nonneg (heatKernelBM_nonneg d hposmax.le u v)]
  refine le_trans (heatKernelBM_le d hposmax u v) ?_
  refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
  have h1 : 4 * Real.pi * t₀ ≤ 4 * Real.pi * max s t₀ := by
    have := le_max_right s t₀
    nlinarith
  gcongr

end Sandpile.Support
