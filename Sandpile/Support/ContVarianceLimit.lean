import Sandpile.Support.ContDominated
import Sandpile.Support.ContCutLimit

/-!
# The limit of the variance of the rescaled pairing

`tendsto_sum_scaledCoeff_sq` proves that the sum of squares of the scaled coefficients
converges to the double space integral of the test function `φ` against the double time
integral of the Brownian heat kernel: the local central limit theorem and a Riemann-sum
argument give this limit for a time weight that vanishes near zero
(`tendsto_integral2_timeKernel`), cutting the weight there changes the lattice sum by `O(δ)`
uniformly in the scale (`abs_sum_scaledCoeff_sq_sub_cut_le`), and it changes the limit by `O(δ)`
as well, because moving the space integral through the two time integrals leaves the kernel
entering only through its pairing with `φ` (`abs_integral2_space_pairing_sub_le`). A quantity
uniformly within `ε` of a convergent one whose limit is within `ε` of `V` converges to `V`.
-/

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

/-! ### The sum of squares with the double time sum outside -/

/-- Interchanging the finite space sum over `s ×ˢ s` with the double time sum: the sum of the
mass-weighted kernel over pairs of sites, with the double time sum inside, equals the double
time sum with the space pairing inside. -/
theorem sum_space_time_comm' (s : Finset (Site d)) (m : Site d → ℝ) (w : ℕ → ℕ → ℝ) (N : ℕ)
    (K : ℕ → Site d → Site d → ℝ) :
    ∑ p ∈ s ×ˢ s, m p.1 * m p.2 *
        ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, w a b * K (a + b) p.1 p.2
      = ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
          w a b * ∑ x ∈ s, ∑ y ∈ s, m x * m y * K (a + b) x y := by
  have e1 : ∀ x y : Site d, m x * m y *
      (∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, w a b * K (a + b) x y)
      = ∑ r ∈ (Finset.range N) ×ˢ (Finset.range N),
          w r.1 r.2 * (m x * m y * K (r.1 + r.2) x y) := by
    intro x y
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  have e2 : ∀ a b : ℕ, w a b * (∑ x ∈ s, ∑ y ∈ s, m x * m y * K (a + b) x y)
      = ∑ p ∈ s ×ˢ s, w a b * (m p.1 * m p.2 * K (a + b) p.1 p.2) := by
    intro a b
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
  have hR : (∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
        w a b * ∑ x ∈ s, ∑ y ∈ s, m x * m y * K (a + b) x y)
      = ∑ r ∈ (Finset.range N) ×ˢ (Finset.range N), ∑ p ∈ s ×ˢ s,
          w r.1 r.2 * (m p.1 * m p.2 * K (r.1 + r.2) p.1 p.2) := by
    rw [Finset.sum_product]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => e2 a b
  rw [hR, Finset.sum_congr rfl fun p (_ : p ∈ s ×ˢ s) => e1 p.1 p.2]
  exact Finset.sum_comm

/-- The sum of squares of the coefficients, with the double time sum outside. -/
theorem sum_scaledCoeff_sq_eq_time {R : ℝ} (hR : 0 < R) (L T : ℝ) (q : ℝ → ℝ)
    (φ : Space d → ℝ) :
    ∑ z ∈ coeffBox d R L T, scaledCoeff d R L T q φ z ^ 2
      = R ^ ((d : ℝ) - 4) *
        ∑ p ∈ (Finset.range ⌊R ^ 2 * T⌋₊) ×ˢ (Finset.range ⌊R ^ 2 * T⌋₊),
          (q ((p.1 : ℝ) / R ^ 2) * q ((p.2 : ℝ) / R ^ 2)) *
            ∑ x ∈ supportBox d R L, ∑ y ∈ supportBox d R L,
              cellMass R φ x * cellMass R φ y * Sandpile.heatKernel d (p.1 + p.2) x y := by
  rw [sum_scaledCoeff_sq_eq hR L T q φ]
  congr 1
  rw [sum_space_time_comm' (supportBox d R L) (cellMass R φ)
    (fun a b => q ((a : ℝ) / R ^ 2) * q ((b : ℝ) / R ^ 2)) ⌊R ^ 2 * T⌋₊
    (fun n x y => Sandpile.heatKernel d n x y), Finset.sum_product]


/-- **The cut weight changes the sum of squares by `O(δ)`, uniformly in the
scale.**  The two weights agree unless one of the two times is below `2δR²`, and
the pairs of times with that property number at most `2(2δR²+1)(R²T)`, each
contributing at most `‖q‖_∞²‖φ‖_∞‖φ‖_1R^{-4}` by the crude block estimate. -/
theorem abs_sum_scaledCoeff_sq_sub_cut_le (hd : 1 ≤ d) {R T L δ Q C : ℝ} (hR : 0 < R)
    (hT : 0 ≤ T) (hδ : 0 < δ) (q' : ℝ → ℝ) (hQ0 : 0 ≤ Q) (hQ : ∀ r, |q' r| ≤ Q)
    (φ : Space d → ℝ) (hφ : Integrable φ) (hC : ∀ z, |φ z| ≤ C) :
    |(∑ z ∈ coeffBox d R L T, scaledCoeff d R L T q' φ z ^ 2)
        - (∑ z ∈ coeffBox d R L T,
            scaledCoeff d R L T (fun r => q' r * cutoffFn δ r) φ z ^ 2)|
      ≤ (4 * δ * T + 2 * T * (R ^ 2)⁻¹) * ((2 * (Q * Q)) * (C * ∫ z, |φ z|)) := by
  classical
  have hR2 : (0:ℝ) < R ^ 2 := by positivity
  have hR4 : (0:ℝ) < R ^ 4 := by positivity
  have hC0 : (0 : ℝ) ≤ C := le_trans (abs_nonneg (φ 0)) (hC 0)
  have hL1 : (0:ℝ) ≤ ∫ z : Space d, |φ z| :=
    MeasureTheory.integral_nonneg fun z => abs_nonneg (φ z)
  set N : ℕ := ⌊R ^ 2 * T⌋₊ with hN
  set M : ℕ := ⌈2 * δ * R ^ 2⌉₊ with hM
  set S : ℕ × ℕ → ℝ := fun p =>
    ∑ x ∈ supportBox d R L, ∑ y ∈ supportBox d R L,
      cellMass R φ x * cellMass R φ y * Sandpile.heatKernel d (p.1 + p.2) x y with hS
  set w : ℕ × ℕ → ℝ := fun p =>
    q' ((p.1 : ℝ) / R ^ 2) * q' ((p.2 : ℝ) / R ^ 2)
      - (q' ((p.1 : ℝ) / R ^ 2) * cutoffFn δ ((p.1 : ℝ) / R ^ 2)) *
        (q' ((p.2 : ℝ) / R ^ 2) * cutoffFn δ ((p.2 : ℝ) / R ^ 2)) with hw
  have hwbd : ∀ p : ℕ × ℕ, |w p| ≤ 2 * (Q * Q) := by
    intro p
    have h1 : |q' ((p.1 : ℝ) / R ^ 2) * q' ((p.2 : ℝ) / R ^ 2)| ≤ Q * Q := by
      rw [abs_mul]
      exact mul_le_mul (hQ _) (hQ _) (abs_nonneg _) hQ0
    have h2 : |(q' ((p.1 : ℝ) / R ^ 2) * cutoffFn δ ((p.1 : ℝ) / R ^ 2)) *
        (q' ((p.2 : ℝ) / R ^ 2) * cutoffFn δ ((p.2 : ℝ) / R ^ 2))| ≤ Q * Q := by
      rw [abs_mul]
      exact mul_le_mul (abs_mul_cutoffFn_le hQ0 hQ) (abs_mul_cutoffFn_le hQ0 hQ)
        (abs_nonneg _) hQ0
    calc |w p| ≤ |q' ((p.1 : ℝ) / R ^ 2) * q' ((p.2 : ℝ) / R ^ 2)|
          + |(q' ((p.1 : ℝ) / R ^ 2) * cutoffFn δ ((p.1 : ℝ) / R ^ 2)) *
            (q' ((p.2 : ℝ) / R ^ 2) * cutoffFn δ ((p.2 : ℝ) / R ^ 2))| := abs_sub _ _
      _ ≤ 2 * (Q * Q) := by linarith
  have hdiff : (∑ z ∈ coeffBox d R L T, scaledCoeff d R L T q' φ z ^ 2)
      - (∑ z ∈ coeffBox d R L T,
          scaledCoeff d R L T (fun r => q' r * cutoffFn δ r) φ z ^ 2)
      = R ^ ((d : ℝ) - 4) * ∑ p ∈ (Finset.range N) ×ˢ (Finset.range N), w p * S p := by
    rw [sum_scaledCoeff_sq_eq_time hR L T q' φ,
      sum_scaledCoeff_sq_eq_time hR L T (fun r => q' r * cutoffFn δ r) φ, ← mul_sub,
      ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hw, hS]
    ring
  have hzero : ∀ p ∈ (Finset.range N) ×ˢ (Finset.range N), w p * S p ≠ 0 →
      (p.1 < M ∨ p.2 < M) := by
    intro p _ hne
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have e1 : 2 * δ ≤ (p.1 : ℝ) / R ^ 2 := by
      have : 2 * δ * R ^ 2 ≤ (p.1 : ℝ) := by
        have := Nat.ceil_le.mp h1
        exact_mod_cast this
      rw [le_div_iff₀ hR2]
      linarith
    have e2 : 2 * δ ≤ (p.2 : ℝ) / R ^ 2 := by
      have : 2 * δ * R ^ 2 ≤ (p.2 : ℝ) := by
        have := Nat.ceil_le.mp h2
        exact_mod_cast this
      rw [le_div_iff₀ hR2]
      linarith
    apply hne
    have : w p = 0 := by
      rw [hw]
      simp only
      rw [cutoffFn_eq_one hδ e1, cutoffFn_eq_one hδ e2]
      ring
    rw [this, zero_mul]
  have hfilter : ∑ p ∈ (Finset.range N) ×ˢ (Finset.range N), w p * S p
      = ∑ p ∈ ((Finset.range N) ×ˢ (Finset.range N)).filter
          (fun p : ℕ × ℕ => p.1 < M ∨ p.2 < M), w p * S p :=
    (Finset.sum_filter_of_ne hzero).symm
  rw [hdiff, hfilter]
  have hmain := abs_scaled_time_block_le' hd hR L w (2 * (Q * Q)) hwbd
    (by positivity) φ hφ C hC
    (((Finset.range N) ×ˢ (Finset.range N)).filter (fun p : ℕ × ℕ => p.1 < M ∨ p.2 < M))
  refine le_trans hmain ?_
  have hcard : ((((Finset.range N) ×ˢ (Finset.range N)).filter
      (fun p : ℕ × ℕ => p.1 < M ∨ p.2 < M)).card : ℝ) ≤ 2 * ((M : ℝ) * (N : ℝ)) := by
    have h := card_edge_block_le N M
    have : ((((Finset.range N) ×ˢ (Finset.range N)).filter
        (fun p : ℕ × ℕ => p.1 < M ∨ p.2 < M)).card : ℝ) ≤ ((2 * (M * N) : ℕ) : ℝ) := by
      exact_mod_cast h
    calc ((((Finset.range N) ×ˢ (Finset.range N)).filter
        (fun p : ℕ × ℕ => p.1 < M ∨ p.2 < M)).card : ℝ)
        ≤ ((2 * (M * N) : ℕ) : ℝ) := this
      _ = 2 * ((M : ℝ) * (N : ℝ)) := by push_cast; ring
  have hMle : (M : ℝ) ≤ 2 * δ * R ^ 2 + 1 := by
    have := Nat.ceil_lt_add_one (by positivity : (0:ℝ) ≤ 2 * δ * R ^ 2)
    linarith
  have hNle : (N : ℝ) ≤ R ^ 2 * T := Nat.floor_le (by positivity)
  have hK0 : (0:ℝ) ≤ (2 * (Q * Q)) * (C * ∫ z : Space d, |φ z|) := by positivity
  have hpow : R ^ (-4 : ℝ) = (R ^ 4)⁻¹ := by
    rw [Real.rpow_neg hR.le]
    norm_num
  have hcard2 : ((((Finset.range N) ×ˢ (Finset.range N)).filter
      (fun p : ℕ × ℕ => p.1 < M ∨ p.2 < M)).card : ℝ) * (R ^ 4)⁻¹
      ≤ 4 * δ * T + 2 * T * (R ^ 2)⁻¹ := by
    have hMN : (M : ℝ) * (N : ℝ) ≤ (2 * δ * R ^ 2 + 1) * (R ^ 2 * T) := by
      have hM0 : (0:ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
      have hN0 : (0:ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
      exact mul_le_mul hMle hNle hN0 (by positivity)
    have hstep : ((((Finset.range N) ×ˢ (Finset.range N)).filter
        (fun p : ℕ × ℕ => p.1 < M ∨ p.2 < M)).card : ℝ)
        ≤ 2 * ((2 * δ * R ^ 2 + 1) * (R ^ 2 * T)) := by
      refine le_trans hcard ?_
      linarith
    have hfin : 2 * ((2 * δ * R ^ 2 + 1) * (R ^ 2 * T)) * (R ^ 4)⁻¹
        = 4 * δ * T + 2 * T * (R ^ 2)⁻¹ := by
      field_simp
      ring
    calc ((((Finset.range N) ×ˢ (Finset.range N)).filter
        (fun p : ℕ × ℕ => p.1 < M ∨ p.2 < M)).card : ℝ) * (R ^ 4)⁻¹
        ≤ 2 * ((2 * δ * R ^ 2 + 1) * (R ^ 2 * T)) * (R ^ 4)⁻¹ :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = 4 * δ * T + 2 * T * (R ^ 2)⁻¹ := hfin
  rw [hpow, mul_assoc, mul_comm ((2 * (Q * Q)) * (C * ∫ z : Space d, |φ z|)) ((R ^ 4)⁻¹),
    ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hcard2 hK0

/-! ### Bridges to the continuum form -/

/-- The interval integral `∫ r in 0..T, f r` (an integral over `Set.Ioc 0 T`) equals the
integral of `f` over the open interval `Set.Ioo 0 T`, since a single point does not affect a
Lebesgue integral. -/
theorem intervalIntegral_eq_Ioo {T : ℝ} (hT : 0 ≤ T) (f : ℝ → ℝ) :
    ∫ r in (0:ℝ)..T, f r = ∫ r in Set.Ioo (0:ℝ) T, f r := by
  rw [intervalIntegral.integral_of_le hT, MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- On the support of the cut weight the total time is at least `2δ`, so the
kernel read at the larger of the total time and `2δ` is the kernel at the total
time, and the two time integrals may be taken over the open interval. -/
theorem cut_time_integral_eq {T δ : ℝ} (hδ : 0 < δ) (q' : ℝ → ℝ) (u v : Space d) :
    (∫ r in Set.Ico (0:ℝ) T, ∫ r' in Set.Ico (0:ℝ) T,
        (q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') *
          heatKernelBM d (max (r + r') (2 * δ)) u v)
      = ∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
          (q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') * heatKernelBM d (r + r') u v := by
  have hpt : ∀ r r' : ℝ,
      (q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') *
          heatKernelBM d (max (r + r') (2 * δ)) u v
        = (q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') * heatKernelBM d (r + r') u v := by
    intro r r'
    by_cases hc : cutoffFn δ r = 0
    · rw [hc]; ring
    by_cases hc' : cutoffFn δ r' = 0
    · rw [hc']; ring
    have hr : δ < r := by
      by_contra hcon
      exact hc (cutoffFn_eq_zero hδ (not_lt.mp hcon))
    have hr' : δ < r' := by
      by_contra hcon
      exact hc' (cutoffFn_eq_zero hδ (not_lt.mp hcon))
    rw [max_eq_left (by linarith)]
  calc (∫ r in Set.Ico (0:ℝ) T, ∫ r' in Set.Ico (0:ℝ) T,
        (q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') *
          heatKernelBM d (max (r + r') (2 * δ)) u v)
      = ∫ r in Set.Ico (0:ℝ) T, ∫ r' in Set.Ico (0:ℝ) T,
          (q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') * heatKernelBM d (r + r') u v := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
        exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun r' => hpt r r')
    _ = ∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ico (0:ℝ) T,
          (q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') * heatKernelBM d (r + r') u v :=
        MeasureTheory.integral_Ico_eq_integral_Ioo
    _ = ∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
          (q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') * heatKernelBM d (r + r') u v := by
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
        exact MeasureTheory.integral_Ico_eq_integral_Ioo

/-- The sum of squares of the coefficients as the double space integral of the
scaled double time sum read at the mesh sites. -/
theorem sum_scaledCoeff_sq_eq_timeKernel {R : ℝ} (hR : 0 < R) (L T : ℝ) (g : ℝ → ℝ)
    (φ : Space d → ℝ) (hint : Integrable φ)
    (hsupp : ∀ z : Space d, φ z ≠ 0 → ‖z‖ ≤ L) :
    ∑ z ∈ coeffBox d R L T, scaledCoeff d R L T g φ z ^ 2
      = ∫ u : Space d, (∫ v : Space d,
          timeKernel d T R g (fun i => ⌊R * u i⌋) (fun i => ⌊R * v i⌋) * φ v) * φ u := by
  rw [sum_scaledCoeff_sq_eq_integral hR L T g φ hint hsupp, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  show R ^ ((d : ℝ) - 4) * ((∫ v : Space d,
      (∑ a ∈ Finset.range ⌊R ^ 2 * T⌋₊, ∑ b ∈ Finset.range ⌊R ^ 2 * T⌋₊,
        g ((a : ℝ) / R ^ 2) * g ((b : ℝ) / R ^ 2) *
          Sandpile.heatKernel d (a + b) (fun i => ⌊R * u i⌋) (fun i => ⌊R * v i⌋)) * φ v) * φ u)
    = (∫ v : Space d,
        timeKernel d T R g (fun i => ⌊R * u i⌋) (fun i => ⌊R * v i⌋) * φ v) * φ u
  rw [← mul_assoc, ← MeasureTheory.integral_const_mul]
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  show R ^ ((d : ℝ) - 4) *
      ((∑ a ∈ Finset.range ⌊R ^ 2 * T⌋₊, ∑ b ∈ Finset.range ⌊R ^ 2 * T⌋₊,
        g ((a : ℝ) / R ^ 2) * g ((b : ℝ) / R ^ 2) *
          Sandpile.heatKernel d (a + b) (fun i => ⌊R * u i⌋) (fun i => ⌊R * v i⌋)) * φ v)
    = timeKernel d T R g (fun i => ⌊R * u i⌋) (fun i => ⌊R * v i⌋) * φ v
  rw [timeKernel]
  simp only [div_eq_mul_inv]
  ring


/-- The double interval integral of `q` against the Brownian heat kernel equals the double
integral over the open square of any `q'` agreeing with `q` on `[0, T]`, by applying
`intervalIntegral_eq_Ioo` in each time variable. -/
theorem time2_integral_eq {T : ℝ} (hT : 0 ≤ T) (q q' : ℝ → ℝ)
    (hqq : ∀ r ∈ Set.Icc (0:ℝ) T, q' r = q r) (x y : Space d) :
    (∫ r in (0:ℝ)..T, ∫ r' in (0:ℝ)..T, q r * q r' * heatKernelBM d (r + r') x y)
      = ∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
          q' r * q' r' * heatKernelBM d (r + r') x y := by
  have hsub : Set.Ioo (0:ℝ) T ⊆ Set.Icc (0:ℝ) T := Set.Ioo_subset_Icc_self
  rw [intervalIntegral_eq_Ioo hT]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun r hr => ?_
  rw [intervalIntegral_eq_Ioo hT]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun r' hr' => ?_
  rw [hqq r (hsub hr), hqq r' (hsub hr')]

/-- The paper's covariance, read as a double space integral of the exchanged
form: the weight may be replaced by any function agreeing with it on `[0,T]`,
and the two time integrals may be taken over the open interval. -/
theorem cov_eq_space_pairing {T : ℝ} (hT : 0 ≤ T) (q q' : ℝ → ℝ)
    (hqq : ∀ r ∈ Set.Icc (0:ℝ) T, q' r = q r) (φ : Space d → ℝ) :
    (∫ x : Space d, ∫ y : Space d, φ x * φ y *
        (∫ r in (0:ℝ)..T, ∫ r' in (0:ℝ)..T, q r * q r' * heatKernelBM d (r + r') x y))
      = ∫ u : Space d, (∫ v : Space d, (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
          q' r * q' r' * heatKernelBM d (r + r') u v) * φ v) * φ u := by
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (∫ y : Space d, φ x * φ y *
      (∫ r in (0:ℝ)..T, ∫ r' in (0:ℝ)..T, q r * q r' * heatKernelBM d (r + r') x y))
    = (∫ v : Space d, (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
        q' r * q' r' * heatKernelBM d (r + r') x v) * φ v) * φ x
  rw [mul_comm _ (φ x), ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show φ x * φ y *
      (∫ r in (0:ℝ)..T, ∫ r' in (0:ℝ)..T, q r * q r' * heatKernelBM d (r + r') x y)
    = φ x * ((∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
        q' r * q' r' * heatKernelBM d (r + r') x y) * φ y)
  rw [time2_integral_eq hT q q' hqq x y]
  ring

/-! ### The limit -/

/-- A function continuous on `Set.Icc 0 T` extends, via `Set.IccExtend`, to a bounded
continuous function `q'` on all of `ℝ` that agrees with `q` on `Set.Icc 0 T`. -/
theorem exists_continuous_extension_bdd {T : ℝ} (hT : (0:ℝ) ≤ T) (q : ℝ → ℝ)
    (hq : ContinuousOn q (Set.Icc 0 T)) :
    ∃ (q' : ℝ → ℝ) (Q : ℝ), Continuous q' ∧ 0 ≤ Q ∧ (∀ r, |q' r| ≤ Q) ∧
      (∀ r ∈ Set.Icc (0:ℝ) T, q' r = q r) := by
  obtain ⟨Q, hQ0, hQ⟩ := exists_bound_of_continuousOn_Icc hT q hq
  refine ⟨Set.IccExtend hT ((Set.Icc (0:ℝ) T).restrict q), Q, hq.restrict.Icc_extend', hQ0,
    ?_, ?_⟩
  · intro r
    show |q ((Set.projIcc (0:ℝ) T hT r : Set.Icc (0:ℝ) T) : ℝ)| ≤ Q
    exact hQ _ (Set.projIcc (0:ℝ) T hT r).2
  · intro r hr
    rw [Set.IccExtend_of_mem hT _ hr]
    rfl

/-- The sum of squares of the scaled coefficients depends on the time weight only through its
values on `[0, T]`: replacing `q` by any `q'` agreeing with it there leaves the sum unchanged,
since only the arguments `a / R ^ 2` for `a < ⌊R ^ 2 T⌋` are ever read. -/
theorem sum_scaledCoeff_sq_congr {R : ℝ} (hR : 0 < R) (L : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (q q' : ℝ → ℝ) (hqq : ∀ r ∈ Set.Icc (0:ℝ) T, q' r = q r) (φ : Space d → ℝ) :
    ∑ z ∈ coeffBox d R L T, scaledCoeff d R L T q' φ z ^ 2
      = ∑ z ∈ coeffBox d R L T, scaledCoeff d R L T q φ z ^ 2 := by
  have hR2 : (0:ℝ) < R ^ 2 := by positivity
  have hmem : ∀ a : ℕ, a < ⌊R ^ 2 * T⌋₊ → ((a : ℝ) / R ^ 2) ∈ Set.Icc (0:ℝ) T := by
    intro a ha
    have h1 : ((a : ℕ) : ℝ) < ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) := by exact_mod_cast ha
    have h2 : ((⌊R ^ 2 * T⌋₊ : ℕ) : ℝ) ≤ R ^ 2 * T := Nat.floor_le (by positivity)
    constructor
    · positivity
    · rw [div_le_iff₀ hR2]
      nlinarith
  rw [sum_scaledCoeff_sq_eq_time hR L T q' φ, sum_scaledCoeff_sq_eq_time hR L T q φ]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
  rw [hqq _ (hmem p.1 hp.1), hqq _ (hmem p.2 hp.2)]

/-- **The limit of the variance of the rescaled pairing**, which is the sentence
of `sandpile.tex:4719-4724`: `Var(𝓕_R(φ)) → Var(𝓖(φ))`, divided by the scenery
variance. -/
theorem tendsto_sum_scaledCoeff_sq
    (hLCLT : Sandpile.External.LocalCLT) (hHK : Sandpile.External.HeatKernelBounds)
    (hd : 1 ≤ d) {T L C : ℝ} (hT : 0 < T) (q : ℝ → ℝ) (hq : ContinuousOn q (Set.Icc 0 T))
    (φ : Space d → ℝ) (hφ : Integrable φ) (hC : ∀ z, |φ z| ≤ C)
    (hsupp : ∀ z : Space d, φ z ≠ 0 → ‖z‖ ≤ L) :
    Tendsto (fun R : ℝ => ∑ z ∈ coeffBox d R L T, scaledCoeff d R L T q φ z ^ 2) atTop
      (𝓝 (∫ x : Space d, ∫ y : Space d, φ x * φ y *
        (∫ r in (0:ℝ)..T, ∫ r' in (0:ℝ)..T,
          q r * q r' * heatKernelBM d (r + r') x y))) := by
  classical
  obtain ⟨q', Q, hq'c, hQ0, hQ, hqq⟩ := exists_continuous_extension_bdd hT.le q hq
  obtain ⟨Cbd, hCbd0, hker⟩ := heatKernel_le_const hHK hd
  have hC0 : (0:ℝ) ≤ C := le_trans (abs_nonneg (φ 0)) (hC 0)
  have hL1 : (0:ℝ) ≤ ∫ z : Space d, |φ z| :=
    MeasureTheory.integral_nonneg fun z => abs_nonneg _
  rw [cov_eq_space_pairing hT.le q q' hqq φ]
  have key : Tendsto (fun R : ℝ => ∑ z ∈ coeffBox d R L T, scaledCoeff d R L T q' φ z ^ 2)
      atTop (𝓝 (∫ u : Space d, (∫ v : Space d,
        (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
          q' r * q' r' * heatKernelBM d (r + r') u v) * φ v) * φ u)) := by
   refine tendsto_of_approx ?_
   intro ε hε
   set K1 : ℝ := (2 * (Q * Q)) * (C * ∫ z : Space d, |φ z|) with hK1def
   set K2 : ℝ := 4 * T * (Q * Q * C) * ∫ z : Space d, |φ z| with hK2def
   have hK10 : (0:ℝ) ≤ K1 := by rw [hK1def]; positivity
   have hK20 : (0:ℝ) ≤ K2 := by
     rw [hK2def]
     exact mul_nonneg (mul_nonneg (by linarith) (by positivity)) hL1
   have h8 : (0:ℝ) ≤ 8 * T * K1 :=
     mul_nonneg (mul_nonneg (by norm_num) hT.le) hK10
   have hden : (0:ℝ) < 8 * T * K1 + K2 + 1 := by linarith
   set δ : ℝ := min (T / 2) (ε / (8 * T * K1 + K2 + 1)) with hδdef
   have hδ0 : 0 < δ := lt_min (by linarith) (by positivity)
   have hδT : δ < T := lt_of_le_of_lt (min_le_left _ _) (by linarith)
   have hδε : δ ≤ ε / (8 * T * K1 + K2 + 1) := min_le_right _ _
   have hthr : ∀ R : ℝ, max (1:ℝ) (1 / δ) ≤ R → (1:ℝ) ≤ R ∧ 1 / δ ≤ R ^ 2 := by
     intro R hR
     have hR1 : (1:ℝ) ≤ R := le_trans (le_max_left _ _) hR
     have hRδ : 1 / δ ≤ R := le_trans (le_max_right _ _) hR
     exact ⟨hR1, le_trans hRδ (by nlinarith)⟩
   refine ⟨fun R => ∑ z ∈ coeffBox d R L T,
       scaledCoeff d R L T (fun r => q' r * cutoffFn δ r) φ z ^ 2,
     ∫ u : Space d, (∫ v : Space d, (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
       (q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') * heatKernelBM d (r + r') u v) * φ v)
         * φ u,
     max (1:ℝ) (1 / δ), ?_, ?_, ?_⟩
   · -- the lattice side
     intro R hR
     obtain ⟨hR1, hRsq⟩ := hthr R hR
     have hR0 : (0:ℝ) < R := lt_of_lt_of_le one_pos hR1
     have hR2 : (0:ℝ) < R ^ 2 := by positivity
     have hinv : (R ^ 2)⁻¹ ≤ δ := by
       rw [inv_le_comm₀ hR2 hδ0]
       rw [one_div] at hRsq
       exact hRsq
     refine le_trans (abs_sum_scaledCoeff_sq_sub_cut_le hd hR0 hT.le hδ0 q' hQ0 hQ φ hφ hC) ?_
     have hcoef : 4 * δ * T + 2 * T * (R ^ 2)⁻¹ ≤ 8 * T * δ := by nlinarith [hT.le]
     have hstep : (4 * δ * T + 2 * T * (R ^ 2)⁻¹) * K1 ≤ (8 * T * δ) * K1 :=
       mul_le_mul_of_nonneg_right hcoef hK10
     refine le_trans hstep ?_
     have h1 : (8 * T * δ) * K1 ≤ (ε / (8 * T * K1 + K2 + 1)) * (8 * T * K1) := by
       have := mul_le_mul_of_nonneg_right hδε h8
       nlinarith
     refine le_trans h1 ?_
     rw [div_mul_eq_mul_div, div_le_iff₀ hden]
     nlinarith
   · -- the continuum side
     obtain ⟨hDint, hD⟩ := integral2_cut_diff_le hT.le hδ0 hQ0 hC0 q' hq'c hQ
     have hmeas1 : Measurable (Function.uncurry fun r r' : ℝ =>
         (q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r')) := by
       have : Continuous (fun p : ℝ × ℝ =>
           (q' p.1 * cutoffFn δ p.1) * (q' p.2 * cutoffFn δ p.2)) :=
         ((hq'c.comp continuous_fst).mul ((continuous_cutoffFn δ).comp continuous_fst)).mul
           ((hq'c.comp continuous_snd).mul ((continuous_cutoffFn δ).comp continuous_snd))
       exact this.measurable
     have hmeas2 : Measurable (Function.uncurry fun r r' : ℝ => q' r * q' r') := by
       have : Continuous (fun p : ℝ × ℝ => q' p.1 * q' p.2) :=
         (hq'c.comp continuous_fst).mul (hq'c.comp continuous_snd)
       exact this.measurable
     have hbd1 : ∀ s s' : ℝ, |(q' s * cutoffFn δ s) * (q' s' * cutoffFn δ s')| ≤ Q * Q := by
       intro s s'
       rw [abs_mul]
       exact mul_le_mul (abs_mul_cutoffFn_le hQ0 hQ) (abs_mul_cutoffFn_le hQ0 hQ)
         (abs_nonneg _) hQ0
     have hbd2 : ∀ s s' : ℝ, |q' s * q' s'| ≤ Q * Q := by
       intro s s'
       rw [abs_mul]
       exact mul_le_mul (hQ s) (hQ s') (abs_nonneg _) hQ0
     have hmain := abs_integral2_space_pairing_sub_le hd hT.le
       (fun r r' => (q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r'))
       (fun r r' => q' r * q' r') hmeas1 hmeas2 (Q * Q) hbd1 hbd2 φ hφ C hC
       (4 * δ * T * (Q * Q * C)) hDint hD
     refine le_trans hmain ?_
     have he : 4 * δ * T * (Q * Q * C) * (∫ z : Space d, |φ z|) = δ * K2 := by
       rw [hK2def]; ring
     rw [he]
     have h1 : δ * K2 ≤ (ε / (8 * T * K1 + K2 + 1)) * K2 :=
       mul_le_mul_of_nonneg_right hδε hK20
     refine le_trans h1 ?_
     rw [div_mul_eq_mul_div, div_le_iff₀ hden]
     nlinarith
   · -- the limit of the cut quantity
     have hB : ∀ᶠ R : ℝ in atTop, ∀ x y : Sandpile.Site d,
         |timeKernel d T R (fun r => q' r * cutoffFn δ r) x y|
           ≤ T ^ 2 * (Q * Q * Cbd * (2 * δ) ^ (-(d : ℝ) / 2)) := by
       filter_upwards [eventually_ge_atTop (max (1:ℝ) (1 / δ))] with R hR
       obtain ⟨hR1, hRsq⟩ := hthr R hR
       have hR0 : (0:ℝ) < R := lt_of_lt_of_le one_pos hR1
       have hRδ : (1:ℝ) ≤ 2 * δ * R ^ 2 := by
         have hd1 : δ * (1 / δ) = 1 := by field_simp
         nlinarith
       intro x y
       exact abs_timeKernel_le hd hR0 hT.le hδ0 hRδ hCbd0.le hQ0 hker
         (fun r => q' r * cutoffFn δ r) (fun r => abs_mul_cutoffFn_le hQ0 hQ)
         (fun r hr => mul_cutoffFn_eq_zero hδ0 hr.le q') x y
     have hbase := tendsto_integral2_timeKernel hLCLT hd hT hδ0 hδT
       (fun r => q' r * cutoffFn δ r) (hq'c.mul (continuous_cutoffFn δ)) Q hQ0
       (fun r => abs_mul_cutoffFn_le hQ0 hQ)
       (fun r hr => mul_cutoffFn_eq_zero hδ0 hr.le q') φ hφ hsupp hB
     have hlim : (∫ u : Space d, (∫ v : Space d,
         (∫ r in Set.Ico (0:ℝ) T, ∫ r' in Set.Ico (0:ℝ) T,
           (q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') *
             heatKernelBM d (max (r + r') (2 * δ)) u v) * φ v) * φ u)
         = ∫ u : Space d, (∫ v : Space d,
           (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
             (q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') *
               heatKernelBM d (r + r') u v) * φ v) * φ u := by
       refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
       have hinner : (∫ v : Space d,
           (∫ r in Set.Ico (0:ℝ) T, ∫ r' in Set.Ico (0:ℝ) T,
             (q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') *
               heatKernelBM d (max (r + r') (2 * δ)) u v) * φ v)
           = ∫ v : Space d,
             (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
               (q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') *
                 heatKernelBM d (r + r') u v) * φ v := by
         refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
         show (∫ r in Set.Ico (0:ℝ) T, ∫ r' in Set.Ico (0:ℝ) T,
             (q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') *
               heatKernelBM d (max (r + r') (2 * δ)) u v) * φ v
           = (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
               (q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') *
                 heatKernelBM d (r + r') u v) * φ v
         rw [cut_time_integral_eq hδ0 q' u v]
       show (∫ v : Space d,
           (∫ r in Set.Ico (0:ℝ) T, ∫ r' in Set.Ico (0:ℝ) T,
             (q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') *
               heatKernelBM d (max (r + r') (2 * δ)) u v) * φ v) * φ u
         = (∫ v : Space d,
             (∫ r in Set.Ioo (0:ℝ) T, ∫ r' in Set.Ioo (0:ℝ) T,
               (q' r * cutoffFn δ r) * (q' r' * cutoffFn δ r') *
                 heatKernelBM d (r + r') u v) * φ v) * φ u
       rw [hinner]
     rw [hlim] at hbase
     refine hbase.congr' ?_
     filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
     exact (sum_scaledCoeff_sq_eq_timeKernel hR L T (fun r => q' r * cutoffFn δ r) φ hφ
       hsupp).symm

  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
  exact sum_scaledCoeff_sq_congr hR L hT.le q q' hqq φ

end Sandpile.Support
