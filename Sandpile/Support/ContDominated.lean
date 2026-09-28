import Sandpile.Support.ContLcltPoint
import Sandpile.Support.ContRiemann
import Sandpile.External.HeatKernelBounds

/-!
# Dominated Convergence for the Scaled Double Time Sum

Dominated convergence in the two space variables of `prop:weighted-membrane-limit`
(`sandpile.tex:4692-4703`).

The sum of squares of the coefficients is a double space integral against the
scaled double time sum (`Sandpile.Support.sum_scaledCoeff_sq_eq_integral`), and
the local central limit theorem gives its limit at a FIXED pair of points
(`Sandpile.Support.tendsto_scaled_time_sum_meshSite`).  What is missing between
the two is a dominating function, and it is the crude one: on the times the
weight does not kill, the total time is at least `2δR²`, so the Gaussian upper
bound on the transition kernel makes the scaled double time sum bounded by a
constant depending on `δ`, `T` and the weight alone, uniformly in the scale and
in the two sites.  With that, the inner integral converges at every point of the
support of the test function and is bounded by `‖φ‖_1` times the same constant,
so the outer integral converges too.
-/

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-! ### The transition kernel bounded by its Gaussian upper bound -/

/-- The Gaussian upper bound with the off-diagonal factor dropped: the transition
probability at `n ≥ 1` steps is at most `C n^{-d/2}`. -/
theorem heatKernel_le_const (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ x y : Sandpile.Site d,
      Sandpile.heatKernel d n x y ≤ C * (n : ℝ) ^ (-(d : ℝ) / 2) := by
  obtain ⟨⟨C, c, hC, hc, hbd⟩, -, -⟩ := hHK d hd
  refine ⟨C, hC, fun n hn x y => ?_⟩
  have hdist : (0:ℝ) ≤ Sandpile.External.latticeDist x y ^ 2 := sq_nonneg _
  have hn0 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hexp : Real.exp (-c * Sandpile.External.latticeDist x y ^ 2 / (n : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ c * Sandpile.External.latticeDist x y ^ 2 := by positivity
    rw [div_nonpos_iff]
    right
    constructor <;> nlinarith
  have hpos : (0:ℝ) ≤ C * (n : ℝ) ^ (-(d : ℝ) / 2) := by positivity
  calc Sandpile.heatKernel d n x y
      ≤ C * (n : ℝ) ^ (-(d : ℝ) / 2) *
          Real.exp (-c * Sandpile.External.latticeDist x y ^ 2 / (n : ℝ)) := hbd n hn x y
    _ ≤ C * (n : ℝ) ^ (-(d : ℝ) / 2) * 1 := mul_le_mul_of_nonneg_left hexp hpos
    _ = C * (n : ℝ) ^ (-(d : ℝ) / 2) := mul_one _

/-! ### A limit reached through uniform approximations -/

/-- If a family is uniformly within `ε` of a convergent family whose limit is
within `ε` of `L`, for every `ε`, then it converges to `L`.  This is how the
cutoff `δ` is removed: the lattice quantity and its cut version differ by `O(δ)`
uniformly in the scale, and the two limits differ by `O(δ)`. -/
theorem tendsto_of_approx {f : ℝ → ℝ} {L : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ (g : ℝ → ℝ) (M R₁ : ℝ),
      (∀ R : ℝ, R₁ ≤ R → |f R - g R| ≤ ε) ∧ |M - L| ≤ ε ∧
        Tendsto g atTop (𝓝 M)) :
    Tendsto f atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, M, R₁, h1, h2, h3⟩ := h (ε / 4) (by linarith)
  rw [Metric.tendsto_atTop] at h3
  obtain ⟨R₂, h4⟩ := h3 (ε / 4) (by linarith)
  refine ⟨max R₁ R₂, fun R hR => ?_⟩
  have hR1 : R₁ ≤ R := le_trans (le_max_left R₁ R₂) hR
  have hR2 : R₂ ≤ R := le_trans (le_max_right R₁ R₂) hR
  have e1 := h1 R hR1
  have e2 := h4 R hR2
  rw [Real.dist_eq] at e2 ⊢
  have e3 : |g R - M| < ε / 4 := e2
  have e4 : |f R - L| ≤ |f R - g R| + |g R - M| + |M - L| := by
    have t1 : |f R - L| ≤ |f R - g R| + |g R - L| := abs_sub_le _ _ _
    have t2 : |g R - L| ≤ |g R - M| + |M - L| := abs_sub_le _ _ _
    linarith
  linarith

/-! ### The block estimate with a general time weight -/

/-- The crude block estimate of `Sandpile.Support.abs_scaled_time_block_le` with
the weight no longer a product: this is what bounds the difference between the
double time sum and its cut version, whose weight is a difference of products. -/
theorem abs_scaled_time_block_le' (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) (L : ℝ)
    (w : ℕ × ℕ → ℝ) (W : ℝ) (hW : ∀ p, |w p| ≤ W) (hW0 : 0 ≤ W)
    (φ : Space d → ℝ) (hφ : Integrable φ) (C : ℝ) (hC : ∀ z, |φ z| ≤ C)
    (A : Finset (ℕ × ℕ)) :
    |R ^ ((d : ℝ) - 4) * ∑ p ∈ A, w p *
        ∑ x ∈ supportBox d R L, ∑ y ∈ supportBox d R L,
          cellMass R φ x * cellMass R φ y * Sandpile.heatKernel d (p.1 + p.2) x y|
      ≤ (A.card : ℝ) * (W * (C * ∫ z, |φ z|)) * R ^ (-4 : ℝ) := by
  have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg (φ 0)) (hC 0)
  have hinv : (0 : ℝ) ≤ R⁻¹ ^ d := pow_nonneg (inv_pos.mpr hR).le d
  have hK0 : (0 : ℝ) ≤ C * R⁻¹ ^ d := mul_nonneg hC0 hinv
  have hpre : (0 : ℝ) < R ^ ((d : ℝ) - 4) := Real.rpow_pos_of_pos hR _
  have hmain := abs_time_double_le hd (supportBox d R L) (cellMass R φ)
    (C * R⁻¹ ^ d) (fun x => abs_cellMass_le hR φ C hC x) hK0
    (∫ z, |φ z|) (sum_abs_cellMass_le R φ hφ _)
    w W hW hW0 A
  have hexp : R ^ ((d : ℝ) - 4) * (R⁻¹ ^ d) = R ^ (-4 : ℝ) := by
    have h1 : (R⁻¹ : ℝ) ^ d = R ^ (-(d : ℝ)) := by
      rw [Real.rpow_neg hR.le, Real.rpow_natCast, inv_pow]
    rw [h1, ← Real.rpow_add hR]
    congr 1
    ring
  rw [abs_mul, abs_of_pos hpre]
  calc R ^ ((d : ℝ) - 4) * |∑ p ∈ A, w p *
        ∑ x ∈ supportBox d R L, ∑ y ∈ supportBox d R L,
          cellMass R φ x * cellMass R φ y * Sandpile.heatKernel d (p.1 + p.2) x y|
      ≤ R ^ ((d : ℝ) - 4) * ((A.card : ℝ) * (W * ((C * R⁻¹ ^ d) * ∫ z, |φ z|))) :=
        mul_le_mul_of_nonneg_left hmain hpre.le
    _ = (A.card : ℝ) * (W * (C * ∫ z, |φ z|)) * (R ^ ((d : ℝ) - 4) * R⁻¹ ^ d) := by
        ring
    _ = (A.card : ℝ) * (W * (C * ∫ z, |φ z|)) * R ^ (-4 : ℝ) := by rw [hexp]

/-! ### The scaled double time sum and its double space integral -/

/-- `Sandpile.Continuum.embed R f` multiplied by an integrable test function `φ`
supported (away from its vanishing set) in the box `s` is integrable, by
rewriting the product as the finite sum of indicator terms via
`embed_mul_eq_sum`. -/
theorem integrable_embed_mul (R : ℝ) (f : Sandpile.Site d → ℝ) (φ : Space d → ℝ)
    (hφ : Integrable φ) (s : Finset (Sandpile.Site d))
    (hs : ∀ z : Space d, φ z ≠ 0 → (fun i => ⌊R * z i⌋) ∈ s) :
    Integrable (fun z : Space d => Sandpile.Continuum.embed R f z * φ z) := by
  simp_rw [embed_mul_eq_sum R f φ s hs]
  refine MeasureTheory.integrable_finsetSum s (fun x _ => ?_)
  exact (hφ.const_mul (f x)).indicator (measurableSet_cell d R x)

/-- The scaled double time sum against the transition kernel. -/
noncomputable def timeKernel (d : ℕ) (T R : ℝ) (g : ℝ → ℝ) (x y : Sandpile.Site d) : ℝ :=
  R ^ ((d : ℝ) - 4) *
    ∑ a ∈ Finset.range ⌊R ^ 2 * T⌋₊, ∑ b ∈ Finset.range ⌊R ^ 2 * T⌋₊,
      g ((a : ℝ) * (R ^ 2)⁻¹) * g ((b : ℝ) * (R ^ 2)⁻¹) * Sandpile.heatKernel d (a + b) x y

/-- For `φ` supported in the ball of radius `L`, `v ↦ timeKernel d T R g x (⌊Rv⌋) * φ v`
is integrable, a special case of `integrable_embed_mul` with `f = timeKernel d T R g x`
and box `supportBox d R L`. -/
theorem integrable_timeKernel_mul {R : ℝ} (T : ℝ) (g : ℝ → ℝ) (x : Sandpile.Site d)
    (φ : Space d → ℝ) (hφ : Integrable φ) {L : ℝ}
    (hsupp : ∀ z : Space d, φ z ≠ 0 → ‖z‖ ≤ L) :
    Integrable (fun v : Space d => timeKernel d T R g x (fun i => ⌊R * v i⌋) * φ v) :=
  integrable_embed_mul R (fun y => timeKernel d T R g x y) φ hφ (supportBox d R L)
    (fun z hz => floor_mem_boxFinset R z (hsupp z hz))

/-- If `timeKernel d T R g x y` is bounded by `B` for every lattice point `y`,
then `∫ v, timeKernel d T R g x (⌊Rv⌋) * φ v` is bounded by `B` times the `L¹`
norm of `φ`. -/
theorem abs_integral_timeKernel_mul_le {R : ℝ} (T : ℝ) (g : ℝ → ℝ) (x : Sandpile.Site d)
    (φ : Space d → ℝ) (hφ : Integrable φ) (B : ℝ)
    (hB : ∀ y : Sandpile.Site d, |timeKernel d T R g x y| ≤ B) :
    |∫ v : Space d, timeKernel d T R g x (fun i => ⌊R * v i⌋) * φ v| ≤ B * ∫ z, |φ z| := by
  calc |∫ v : Space d, timeKernel d T R g x (fun i => ⌊R * v i⌋) * φ v|
      ≤ ∫ v : Space d, |timeKernel d T R g x (fun i => ⌊R * v i⌋) * φ v| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ v : Space d, B * |φ v| := by
        refine MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun v => abs_nonneg _)
          (hφ.abs.const_mul B) (Filter.Eventually.of_forall fun v => ?_)
        show |timeKernel d T R g x (fun i => ⌊R * v i⌋) * φ v| ≤ B * |φ v|
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hB _) (abs_nonneg _)
    _ = B * ∫ z, |φ z| := MeasureTheory.integral_const_mul _ _


/-- **The double space integral of the scaled double time sum converges.**  The
integrand converges at every pair of points of the support of the test function,
by the local central limit theorem, and it is bounded there uniformly in the
scale, by the Gaussian upper bound on the transition kernel at the times the
weight does not kill; dominated convergence does the rest, first in the inner
variable and then in the outer one. -/
theorem tendsto_integral2_timeKernel
    (hLCLT : Sandpile.External.LocalCLT) (hd : 1 ≤ d)
    {T δ L B : ℝ} (hT : 0 < T) (hδ : 0 < δ) (hδT : δ < T)
    (g : ℝ → ℝ) (hg : Continuous g) (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ : ∀ r, |g r| ≤ Q)
    (hg0 : ∀ r : ℝ, r < δ → g r = 0)
    (φ : Space d → ℝ) (hφ : Integrable φ)
    (hsupp : ∀ z : Space d, φ z ≠ 0 → ‖z‖ ≤ L)
    (hB : ∀ᶠ R : ℝ in atTop, ∀ x y : Sandpile.Site d, |timeKernel d T R g x y| ≤ B) :
    Tendsto (fun R : ℝ => ∫ u : Space d,
        (∫ v : Space d, timeKernel d T R g (fun i => ⌊R * u i⌋) (fun i => ⌊R * v i⌋) * φ v)
          * φ u) atTop
      (𝓝 (∫ u : Space d, (∫ v : Space d,
        (∫ r in Set.Ico (0:ℝ) T, ∫ r' in Set.Ico (0:ℝ) T,
          g r * g r' * heatKernelBM d (max (r + r') (2 * δ)) u v) * φ v) * φ u)) := by
  classical
  have hB0 : 0 ≤ B := by
    obtain ⟨R, hR⟩ := hB.exists
    exact le_trans (abs_nonneg _) (hR 0 0)
  have hL1 : (0:ℝ) ≤ ∫ z : Space d, |φ z| :=
    MeasureTheory.integral_nonneg fun z => abs_nonneg (φ z)
  -- the inner limit, at every point of space
  have hinner : ∀ u : Space d, ‖u‖ ≤ L →
      Tendsto (fun R : ℝ =>
        ∫ v : Space d, timeKernel d T R g (fun i => ⌊R * u i⌋) (fun i => ⌊R * v i⌋) * φ v)
        atTop (𝓝 (∫ v : Space d,
          (∫ r in Set.Ico (0:ℝ) T, ∫ r' in Set.Ico (0:ℝ) T,
            g r * g r' * heatKernelBM d (max (r + r') (2 * δ)) u v) * φ v)) := by
    intro u hu
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun v => B * |φ v|) ?_ ?_ (hφ.abs.const_mul B) ?_
    · filter_upwards with R
      exact (integrable_timeKernel_mul T g _ φ hφ hsupp).aestronglyMeasurable
    · filter_upwards [hB] with R hR
      refine Filter.Eventually.of_forall fun v => ?_
      show ‖timeKernel d T R g (fun i => ⌊R * u i⌋) (fun i => ⌊R * v i⌋) * φ v‖ ≤ B * |φ v|
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hR _ _) (abs_nonneg _)
    · refine Filter.Eventually.of_forall fun v => ?_
      by_cases hv : φ v = 0
      · simp [hv]
      · have hvL : ‖v‖ ≤ L := hsupp v hv
        exact (tendsto_scaled_time_sum_meshSite hLCLT hd hT hδ hδT g hg Q hQ0 hQ hg0
          hu hvL).mul_const (φ v)
  -- the outer limit
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun u => (B * ∫ z : Space d, |φ z|) * |φ u|) ?_ ?_
    (hφ.abs.const_mul (B * ∫ z : Space d, |φ z|)) ?_
  · filter_upwards with R
    exact (integrable_embed_mul R
      (fun x => ∫ v : Space d, timeKernel d T R g x (fun i => ⌊R * v i⌋) * φ v) φ hφ
      (supportBox d R L)
      (fun z hz => floor_mem_boxFinset R z (hsupp z hz))).aestronglyMeasurable
  · filter_upwards [hB] with R hR
    refine Filter.Eventually.of_forall fun u => ?_
    show ‖(∫ v : Space d,
      timeKernel d T R g (fun i => ⌊R * u i⌋) (fun i => ⌊R * v i⌋) * φ v) * φ u‖
        ≤ (B * ∫ z : Space d, |φ z|) * |φ u|
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    exact abs_integral_timeKernel_mul_le T g _ φ hφ B (fun y => hR _ y)
  · refine Filter.Eventually.of_forall fun u => ?_
    by_cases hu : φ u = 0
    · simp [hu]
    · exact (hinner u (hsupp u hu)).mul_const (φ u)

/-! ### The uniform bound on the scaled double time sum -/

/-- **The uniform bound on a single term of the scaled double time sum.** If the
transition kernel obeys the Gaussian upper bound `hker` and `g` vanishes below
`δ`, each term `g(a/R²) * g(b/R²) * heatKernel d (a+b) x y` is at most
`Q² * (Cbd * (2δR²)^{-d/2})`, since a nonvanishing term forces both `a` and `b`
to be at least `δR²`, hence `a + b ≥ 2δR²`. -/
theorem abs_time_term_le (hd : 1 ≤ d) {R δ Q Cbd : ℝ} (hR : 0 < R)
    (hδ : 0 < δ) (hRδ : (1:ℝ) ≤ 2 * δ * R ^ 2) (hCbd : 0 ≤ Cbd) (hQ0 : 0 ≤ Q)
    (hker : ∀ n : ℕ, 1 ≤ n → ∀ x y : Sandpile.Site d,
      Sandpile.heatKernel d n x y ≤ Cbd * (n : ℝ) ^ (-(d : ℝ) / 2))
    (g : ℝ → ℝ) (hQ : ∀ r, |g r| ≤ Q) (hg0 : ∀ r : ℝ, r < δ → g r = 0)
    (a b : ℕ) (x y : Sandpile.Site d) :
    |g ((a : ℝ) * (R ^ 2)⁻¹) * g ((b : ℝ) * (R ^ 2)⁻¹) * Sandpile.heatKernel d (a + b) x y|
      ≤ Q * Q * (Cbd * (2 * δ * R ^ 2) ^ (-(d : ℝ) / 2)) := by
  have hd' : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hR2 : (0:ℝ) < R ^ 2 := by positivity
  have hδR : (0:ℝ) < 2 * δ * R ^ 2 := by positivity
  have hexp : -(d : ℝ) / 2 ≤ 0 := by linarith
  have hRHS : (0:ℝ) ≤ Q * Q * (Cbd * (2 * δ * R ^ 2) ^ (-(d : ℝ) / 2)) := by positivity
  by_cases ha : (a : ℝ) * (R ^ 2)⁻¹ < δ
  · rw [hg0 _ ha, zero_mul, zero_mul, abs_zero]
    exact hRHS
  by_cases hb : (b : ℝ) * (R ^ 2)⁻¹ < δ
  · rw [hg0 _ hb, mul_zero, zero_mul, abs_zero]
    exact hRHS
  push Not at ha hb
  have ha' : δ * R ^ 2 ≤ (a : ℝ) := by
    have ha2 : δ ≤ (a : ℝ) / R ^ 2 := by rw [div_eq_mul_inv]; exact ha
    exact (le_div_iff₀ hR2).mp ha2
  have hb' : δ * R ^ 2 ≤ (b : ℝ) := by
    have hb2 : δ ≤ (b : ℝ) / R ^ 2 := by rw [div_eq_mul_inv]; exact hb
    exact (le_div_iff₀ hR2).mp hb2
  have hab : 2 * δ * R ^ 2 ≤ ((a + b : ℕ) : ℝ) := by
    push_cast
    linarith
  have hn1 : 1 ≤ a + b := by
    have hone : (1:ℝ) ≤ ((a + b : ℕ) : ℝ) := le_trans hRδ hab
    exact_mod_cast hone
  have hp : Sandpile.heatKernel d (a + b) x y
      ≤ Cbd * ((a + b : ℕ) : ℝ) ^ (-(d : ℝ) / 2) := hker (a + b) hn1 x y
  have hmono : ((a + b : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤ (2 * δ * R ^ 2) ^ (-(d : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos hδR hab hexp
  have hp2 : Sandpile.heatKernel d (a + b) x y
      ≤ Cbd * (2 * δ * R ^ 2) ^ (-(d : ℝ) / 2) :=
    le_trans hp (mul_le_mul_of_nonneg_left hmono hCbd)
  have hk0 : (0:ℝ) ≤ Sandpile.heatKernel d (a + b) x y := Sandpile.heatKernel_nonneg _ x y
  rw [abs_mul, abs_mul, abs_of_nonneg hk0]
  have h1 : |g ((a : ℝ) * (R ^ 2)⁻¹)| ≤ Q := hQ _
  have h2 : |g ((b : ℝ) * (R ^ 2)⁻¹)| ≤ Q := hQ _
  have hC2 : (0:ℝ) ≤ Cbd * (2 * δ * R ^ 2) ^ (-(d : ℝ) / 2) := by positivity
  calc |g ((a : ℝ) * (R ^ 2)⁻¹)| * |g ((b : ℝ) * (R ^ 2)⁻¹)| *
        Sandpile.heatKernel d (a + b) x y
      ≤ Q * Q * (Cbd * (2 * δ * R ^ 2) ^ (-(d : ℝ) / 2)) := by
        refine mul_le_mul ?_ hp2 hk0 (by positivity)
        exact mul_le_mul h1 h2 (abs_nonneg _) hQ0



/-- The algebraic identity that collapses the scale factor `R^(d-4)` against the
two occurrences of `R` produced by the number of terms `(R²T)²` and the kernel
bound `(2δR²)^{-d/2}`, leaving `T² * (Cbd * (2δ)^{-d/2})` with no dependence
on `R`. -/
theorem rpow_scale_identity (d : ℕ) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (T Cbd : ℝ) :
    R ^ ((d : ℝ) - 4) * ((R ^ 2 * T) ^ 2 * (Cbd * (2 * δ * R ^ 2) ^ (-(d : ℝ) / 2)))
      = T ^ 2 * (Cbd * (2 * δ) ^ (-(d : ℝ) / 2)) := by
  have h2δ : (0:ℝ) < 2 * δ := by linarith
  have hR2 : (0:ℝ) < R ^ 2 := by positivity
  -- split the rpow of the product
  have hsplit : (2 * δ * R ^ 2) ^ (-(d : ℝ) / 2)
      = (2 * δ) ^ (-(d : ℝ) / 2) * (R ^ 2) ^ (-(d : ℝ) / 2) :=
    Real.mul_rpow h2δ.le hR2.le
  -- the scale factor
  have hpow : (R ^ 2 : ℝ) ^ (-(d : ℝ) / 2) = R ^ (-(d : ℝ)) := by
    rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hR.le]
    congr 1
    ring
  have hfour : (R ^ 2 * T) ^ 2 = R ^ (4 : ℝ) * T ^ 2 := by
    have : (R : ℝ) ^ (4 : ℝ) = R ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast R 4]
      norm_num
    rw [this]
    ring
  have hcollapse : R ^ ((d : ℝ) - 4) * R ^ (4 : ℝ) * R ^ (-(d : ℝ)) = 1 := by
    rw [← Real.rpow_add hR, ← Real.rpow_add hR]
    norm_num
  rw [hsplit, hfour, hpow]
  calc R ^ ((d : ℝ) - 4) * (R ^ (4:ℝ) * T ^ 2 *
        (Cbd * ((2 * δ) ^ (-(d : ℝ) / 2) * R ^ (-(d : ℝ)))))
      = (R ^ ((d : ℝ) - 4) * R ^ (4:ℝ) * R ^ (-(d : ℝ))) *
          (T ^ 2 * (Cbd * (2 * δ) ^ (-(d : ℝ) / 2))) := by ring
    _ = T ^ 2 * (Cbd * (2 * δ) ^ (-(d : ℝ) / 2)) := by rw [hcollapse, one_mul]



/-- A double finite sum over `range N × range N` of terms bounded by `M` in
absolute value is at most `N * N * M`, by two applications of the triangle
inequality for finite sums. -/
theorem abs_double_sum_le (N : ℕ) (M : ℝ) (F : ℕ → ℕ → ℝ) (hF : ∀ a b, |F a b| ≤ M) :
    |∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, F a b| ≤ (N : ℝ) * (N : ℝ) * M := by
  calc |∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, F a b|
      ≤ ∑ a ∈ Finset.range N, |∑ b ∈ Finset.range N, F a b| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a ∈ Finset.range N, ((N : ℝ) * M) := by
        refine Finset.sum_le_sum fun a _ => ?_
        calc |∑ b ∈ Finset.range N, F a b|
            ≤ ∑ b ∈ Finset.range N, |F a b| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _b ∈ Finset.range N, M := Finset.sum_le_sum fun b _ => hF a b
          _ = (N : ℝ) * M := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (N : ℝ) * (N : ℝ) * M := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc]

/-- **The uniform bound on the scaled double time sum.** Combining the uniform
term bound `abs_time_term_le`, the double-sum bound `abs_double_sum_le`, and the
scale identity `rpow_scale_identity`, `timeKernel d T R g x y` is bounded by
`T² * (Q² * Cbd * (2δ)^{-d/2})`, uniformly in `R` (subject to `2δR² ≥ 1`) and in
the two lattice points `x, y`. -/
theorem abs_timeKernel_le (hd : 1 ≤ d) {T R δ Q Cbd : ℝ} (hR : 0 < R) (hT : 0 ≤ T)
    (hδ : 0 < δ) (hRδ : (1:ℝ) ≤ 2 * δ * R ^ 2) (hCbd : 0 ≤ Cbd) (hQ0 : 0 ≤ Q)
    (hker : ∀ n : ℕ, 1 ≤ n → ∀ x y : Sandpile.Site d,
      Sandpile.heatKernel d n x y ≤ Cbd * (n : ℝ) ^ (-(d : ℝ) / 2))
    (g : ℝ → ℝ) (hQ : ∀ r, |g r| ≤ Q) (hg0 : ∀ r : ℝ, r < δ → g r = 0)
    (x y : Sandpile.Site d) :
    |timeKernel d T R g x y| ≤ T ^ 2 * (Q * Q * Cbd * (2 * δ) ^ (-(d : ℝ) / 2)) := by
  classical
  have hδR : (0:ℝ) < 2 * δ * R ^ 2 := by positivity
  set M : ℝ := Q * Q * (Cbd * (2 * δ * R ^ 2) ^ (-(d : ℝ) / 2)) with hM
  have hM0 : (0:ℝ) ≤ M := by rw [hM]; positivity
  have hsum := abs_double_sum_le ⌊R ^ 2 * T⌋₊ M
    (fun a b => g ((a : ℝ) * (R ^ 2)⁻¹) * g ((b : ℝ) * (R ^ 2)⁻¹) *
      Sandpile.heatKernel d (a + b) x y)
    (fun a b => abs_time_term_le hd hR hδ hRδ hCbd hQ0 hker g hQ hg0 a b x y)
  have hN : ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) ≤ R ^ 2 * T := Nat.floor_le (by positivity)
  have hN0 : (0:ℝ) ≤ ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hpre : (0:ℝ) < R ^ ((d : ℝ) - 4) := Real.rpow_pos_of_pos hR _
  rw [timeKernel, abs_mul, abs_of_pos hpre]
  have hNN : ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) ≤ (R ^ 2 * T) ^ 2 := by
    have h := mul_le_mul hN hN hN0 (by positivity : (0:ℝ) ≤ R ^ 2 * T)
    calc ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ)
        ≤ (R ^ 2 * T) * (R ^ 2 * T) := h
      _ = (R ^ 2 * T) ^ 2 := by ring
  have hstep : ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * M
      ≤ (R ^ 2 * T) ^ 2 * M := mul_le_mul_of_nonneg_right hNN hM0
  have hid := rpow_scale_identity d hR hδ T (Q * Q * Cbd)
  calc R ^ ((d : ℝ) - 4) *
        |∑ a ∈ Finset.range ⌊R ^ 2 * T⌋₊, ∑ b ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          g ((a : ℝ) * (R ^ 2)⁻¹) * g ((b : ℝ) * (R ^ 2)⁻¹) *
            Sandpile.heatKernel d (a + b) x y|
      ≤ R ^ ((d : ℝ) - 4) * (((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) * M) :=
        mul_le_mul_of_nonneg_left hsum hpre.le
    _ ≤ R ^ ((d : ℝ) - 4) * ((R ^ 2 * T) ^ 2 * M) :=
        mul_le_mul_of_nonneg_left hstep hpre.le
    _ = R ^ ((d : ℝ) - 4) * ((R ^ 2 * T) ^ 2 *
          ((Q * Q * Cbd) * (2 * δ * R ^ 2) ^ (-(d : ℝ) / 2))) := by
        rw [hM]; ring
    _ = T ^ 2 * ((Q * Q * Cbd) * (2 * δ) ^ (-(d : ℝ) / 2)) := hid
    _ = T ^ 2 * (Q * Q * Cbd * (2 * δ) ^ (-(d : ℝ) / 2)) := by ring

end Sandpile.Support
