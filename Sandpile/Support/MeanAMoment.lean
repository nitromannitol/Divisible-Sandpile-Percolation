import Sandpile.Support.MeanATrunc

/-!
# Convergence of moments and variance under a uniform exponential moment

Convergence in distribution together with a uniform exponential moment gives
convergence of the first two moments, and hence of the variance.

This is the whole of the word "immediately" in `sandpile.tex:2029-2031`: "The
uniform exponential moment in Proposition~\ref{prop:continuum-value-selfsimilar}
immediately implies the following corollary."  Weak convergence sees only
bounded continuous functions; the exponential moment supplies a modulus, uniform
over the family, for the error made by truncating the identity and the square at
a level, and the two are combined by the usual three-term estimate.
-/

open MeasureTheory Filter Topology ProbabilityTheory

namespace Sandpile.Support

variable {ι : Type*} {l : Filter ι} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {X : (i : ι) → Ω i → ℝ} {Z : Ω' → ℝ}

/-- Convergence in distribution, read at a bounded continuous test function in the
vocabulary of the random variables rather than of their laws. -/
theorem tendsto_integral_bdd_of_tendstoInDistribution
    (h : TendstoInDistribution X l Z μ μ') (f : BoundedContinuousFunction ℝ ℝ) :
    Tendsto (fun i => ∫ ω, f (X i ω) ∂(μ i)) l (𝓝 (∫ ω, f (Z ω) ∂μ')) := by
  have key := MeasureTheory.ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h.tendsto f
  have hX : ∀ i, ∫ y, f y ∂((μ i).map (X i)) = ∫ ω, f (X i ω) ∂(μ i) := fun i =>
    integral_map (h.forall_aemeasurable i) f.continuous.aestronglyMeasurable
  have hZ : ∫ y, f y ∂(μ'.map Z) = ∫ ω, f (Z ω) ∂μ' :=
    integral_map h.aemeasurable_limit f.continuous.aestronglyMeasurable
  rw [← hZ]
  exact key.congr fun i => hX i

/-- The three-term estimate: a family approximated uniformly by convergent families,
with a modulus tending to zero, converges. -/
theorem tendsto_of_uniform_approx (G : ι → ℝ) (G' : ℝ) (A : ℕ → ι → ℝ) (A' : ℕ → ℝ) (e : ℕ → ℝ)
    (hA : ∀ n, Tendsto (A n) l (𝓝 (A' n)))
    (he : Tendsto e atTop (𝓝 0))
    (hap : ∀ᶠ n in atTop, (∀ i, |G i - A n i| ≤ e n) ∧ |G' - A' n| ≤ e n) :
    Tendsto G l (𝓝 G') := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h3 : (0:ℝ) < ε / 3 := by linarith
  have hsmall : ∀ᶠ n in atTop, e n < ε / 3 := he.eventually (gt_mem_nhds h3)
  obtain ⟨n, hn⟩ := (hsmall.and hap).exists
  have hen : e n < ε / 3 := hn.1
  have hG : ∀ i, |G i - A n i| ≤ e n := hn.2.1
  have hG' : |G' - A' n| ≤ e n := hn.2.2
  have hmid := (hA n).eventually (Metric.ball_mem_nhds (A' n) h3)
  filter_upwards [hmid] with i hi
  have hmid' : |A n i - A' n| < ε / 3 := by
    rw [Real.dist_eq] at hi; exact hi
  rw [Real.dist_eq]
  have h1 : |G i - A n i| < ε / 3 := lt_of_le_of_lt (hG i) hen
  have h2 : |A' n - G'| < ε / 3 := by
    rw [abs_sub_comm]; exact lt_of_le_of_lt hG' hen
  calc |G i - G'| ≤ |G i - A n i| + |A n i - G'| := abs_sub_le _ _ _
    _ ≤ |G i - A n i| + (|A n i - A' n| + |A' n - G'|) := by
        gcongr; exact abs_sub_le _ _ _
    _ < ε / 3 + (ε / 3 + ε / 3) := by gcongr
    _ = ε := by ring

/-- The truncation of a nonnegative random variable is integrable. -/
theorem integrable_trunc {Ω₀ : Type*} [MeasurableSpace Ω₀] (P : Measure Ω₀)
    [IsFiniteMeasure P] (Y : Ω₀ → ℝ) (hY : AEStronglyMeasurable Y P) (M : ℝ) :
    Integrable (fun ω => truncBdd M (Y ω)) P := by
  refine Integrable.mono' (integrable_const |M|)
    ((truncBdd M).continuous.comp_aestronglyMeasurable hY) ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  have h0 : (0:ℝ) ≤ max 0 (min (Y ω) M) := le_max_left _ _
  have hMa : M ≤ |M| := le_abs_self M
  have hle : max 0 (min (Y ω) M) ≤ |M| :=
    max_le (abs_nonneg M) ((min_le_right _ _).trans hMa)
  rw [truncBdd_apply, Real.norm_eq_abs, abs_of_nonneg h0]
  exact hle

/-- The squared truncation of a random variable is integrable. -/
theorem integrable_truncSq {Ω₀ : Type*} [MeasurableSpace Ω₀] (P : Measure Ω₀)
    [IsFiniteMeasure P] (Y : Ω₀ → ℝ) (hY : AEStronglyMeasurable Y P) (M : ℝ) :
    Integrable (fun ω => truncSqBdd M (Y ω)) P := by
  refine Integrable.mono' (integrable_const (M ^ 2))
    ((truncSqBdd M).continuous.comp_aestronglyMeasurable hY) ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  have h0 : (0:ℝ) ≤ max 0 (min (Y ω) M) := le_max_left _ _
  have hMa : M ≤ |M| := le_abs_self M
  have hle : max 0 (min (Y ω) M) ≤ |M| :=
    max_le (abs_nonneg M) ((min_le_right _ _).trans hMa)
  have hsq : |M| ^ 2 = M ^ 2 := sq_abs M
  rw [truncSqBdd_apply, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith

/-- **The first-moment truncation error, bounded by the exponential moment.** -/
theorem abs_integral_sub_trunc_le {Ω₀ : Type*} [MeasurableSpace Ω₀] (P : Measure Ω₀)
    [IsProbabilityMeasure P] (Y : Ω₀ → ℝ) (hYnn : ∀ᵐ ω ∂P, 0 ≤ Y ω) (hYint : Integrable Y P)
    (θ M C : ℝ) (hθ : 0 < θ) (hM : 1 ≤ θ * M)
    (hexp : Integrable (fun ω => Real.exp (θ * Y ω)) P)
    (hexpC : ∫ ω, Real.exp (θ * Y ω) ∂P ≤ C) :
    |(∫ ω, Y ω ∂P) - ∫ ω, truncBdd M (Y ω) ∂P| ≤ M * Real.exp (-(θ * M)) * C := by
  have hM0 : 0 < M := by nlinarith
  have hti := integrable_trunc P Y hYint.aestronglyMeasurable M
  have hsub : (∫ ω, Y ω ∂P) - ∫ ω, truncBdd M (Y ω) ∂P
      = ∫ ω, (Y ω - truncBdd M (Y ω)) ∂P := (integral_sub hYint hti).symm
  have hnn : 0 ≤ ∫ ω, (Y ω - truncBdd M (Y ω)) ∂P := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hYnn] with ω hω
    have h := trunc_le_self M (Y ω) hω
    have hrfl : (truncBdd M) (Y ω) = max 0 (min (Y ω) M) := rfl
    show (0:ℝ) ≤ Y ω - (truncBdd M) (Y ω)
    rw [hrfl]
    linarith
  have hle : ∫ ω, (Y ω - truncBdd M (Y ω)) ∂P
      ≤ ∫ ω, M * Real.exp (-(θ * M)) * Real.exp (θ * Y ω) ∂P := by
    refine integral_mono_ae (hYint.sub hti) (hexp.const_mul _) ?_
    filter_upwards [hYnn] with ω hω
    have hrfl : (truncBdd M) (Y ω) = max 0 (min (Y ω) M) := rfl
    rw [hrfl]
    exact sub_trunc_le θ M (Y ω) hθ hM hω
  have hconst : ∫ ω, M * Real.exp (-(θ * M)) * Real.exp (θ * Y ω) ∂P
      = M * Real.exp (-(θ * M)) * ∫ ω, Real.exp (θ * Y ω) ∂P := integral_const_mul _ _
  have hfin : ∫ ω, (Y ω - truncBdd M (Y ω)) ∂P ≤ M * Real.exp (-(θ * M)) * C := by
    refine hle.trans ?_
    rw [hconst]
    exact mul_le_mul_of_nonneg_left hexpC (by positivity)
  rw [hsub, abs_of_nonneg hnn]
  exact hfin

/-- **The second-moment truncation error, bounded by the exponential moment.** -/
theorem abs_integral_sq_sub_truncSq_le {Ω₀ : Type*} [MeasurableSpace Ω₀] (P : Measure Ω₀)
    [IsProbabilityMeasure P] (Y : Ω₀ → ℝ) (hYnn : ∀ᵐ ω ∂P, 0 ≤ Y ω)
    (hYint : Integrable (fun ω => Y ω ^ 2) P) (hYm : AEStronglyMeasurable Y P)
    (θ M C : ℝ) (hθ : 0 < θ) (hM : 2 ≤ θ * M)
    (hexp : Integrable (fun ω => Real.exp (θ * Y ω)) P)
    (hexpC : ∫ ω, Real.exp (θ * Y ω) ∂P ≤ C) :
    |(∫ ω, Y ω ^ 2 ∂P) - ∫ ω, truncSqBdd M (Y ω) ∂P| ≤ M ^ 2 * Real.exp (-(θ * M)) * C := by
  have hM0 : 0 < M := by nlinarith
  have hti := integrable_truncSq P Y hYm M
  have hsub : (∫ ω, Y ω ^ 2 ∂P) - ∫ ω, truncSqBdd M (Y ω) ∂P
      = ∫ ω, (Y ω ^ 2 - truncSqBdd M (Y ω)) ∂P := (integral_sub hYint hti).symm
  have hnn : 0 ≤ ∫ ω, (Y ω ^ 2 - truncSqBdd M (Y ω)) ∂P := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hYnn] with ω hω
    have h := trunc_sq_le_sq M (Y ω) hω
    have hrfl : (truncSqBdd M) (Y ω) = (max 0 (min (Y ω) M)) ^ 2 := rfl
    show (0:ℝ) ≤ Y ω ^ 2 - (truncSqBdd M) (Y ω)
    rw [hrfl]
    linarith
  have hle : ∫ ω, (Y ω ^ 2 - truncSqBdd M (Y ω)) ∂P
      ≤ ∫ ω, M ^ 2 * Real.exp (-(θ * M)) * Real.exp (θ * Y ω) ∂P := by
    refine integral_mono_ae (hYint.sub hti) (hexp.const_mul _) ?_
    filter_upwards [hYnn] with ω hω
    have hrfl : (truncSqBdd M) (Y ω) = (max 0 (min (Y ω) M)) ^ 2 := rfl
    rw [hrfl]
    exact sq_sub_trunc_sq_le θ M (Y ω) hθ hM hω
  have hconst : ∫ ω, M ^ 2 * Real.exp (-(θ * M)) * Real.exp (θ * Y ω) ∂P
      = M ^ 2 * Real.exp (-(θ * M)) * ∫ ω, Real.exp (θ * Y ω) ∂P := integral_const_mul _ _
  have hfin : ∫ ω, (Y ω ^ 2 - truncSqBdd M (Y ω)) ∂P ≤ M ^ 2 * Real.exp (-(θ * M)) * C := by
    refine hle.trans ?_
    rw [hconst]
    exact mul_le_mul_of_nonneg_left hexpC (by positivity)
  rw [hsub, abs_of_nonneg hnn]
  exact hfin


/-- `a ≤ θ n` eventually, for every real `a` and every `θ > 0`. -/
theorem eventually_le_mul_nat (θ a : ℝ) (hθ : 0 < θ) : ∀ᶠ n : ℕ in atTop, a ≤ θ * n := by
  have h : Tendsto (fun n : ℕ => θ * (n : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hθ tendsto_natCast_atTop_atTop
  exact h.eventually_ge_atTop a

/-- The truncation modulus `n e^{-θn} C` tends to zero. -/
theorem tendsto_nat_mul_exp_neg (θ C : ℝ) (hθ : 0 < θ) :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-(θ * n)) * C) atTop (𝓝 0) := by
  have hbase : Tendsto (fun x : ℝ => x ^ 1 * Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hθn : Tendsto (fun n : ℕ => θ * (n : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hθ tendsto_natCast_atTop_atTop
  have hcomp := hbase.comp hθn
  have hmul : Tendsto
      (fun n : ℕ => (θ * (n : ℝ)) ^ 1 * Real.exp (-(θ * n)) * (θ⁻¹ * C)) atTop
      (𝓝 (0 * (θ⁻¹ * C))) := hcomp.mul_const (θ⁻¹ * C)
  rw [zero_mul] at hmul
  refine hmul.congr fun n => ?_
  have hne : θ ≠ 0 := ne_of_gt hθ
  field_simp

/-- The squared truncation modulus `n² e^{-θn} C` tends to zero. -/
theorem tendsto_nat_sq_mul_exp_neg (θ C : ℝ) (hθ : 0 < θ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * Real.exp (-(θ * n)) * C) atTop (𝓝 0) := by
  have hbase : Tendsto (fun x : ℝ => x ^ 2 * Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  have hθn : Tendsto (fun n : ℕ => θ * (n : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hθ tendsto_natCast_atTop_atTop
  have hcomp := hbase.comp hθn
  have hmul : Tendsto
      (fun n : ℕ => (θ * (n : ℝ)) ^ 2 * Real.exp (-(θ * n)) * (θ⁻¹ ^ 2 * C)) atTop
      (𝓝 (0 * (θ⁻¹ ^ 2 * C))) := hcomp.mul_const (θ⁻¹ ^ 2 * C)
  rw [zero_mul] at hmul
  refine hmul.congr fun n => ?_
  have hne : θ ≠ 0 := ne_of_gt hθ
  field_simp

/-- **The first moment passes to the limit** under convergence in distribution and a
uniform exponential moment on the nonnegative half-line. -/
theorem tendsto_integral_of_uniform_exp
    (h : TendstoInDistribution X l Z μ μ')
    (hXnn : ∀ i, ∀ᵐ ω ∂(μ i), 0 ≤ X i ω) (hZnn : ∀ᵐ ω ∂μ', 0 ≤ Z ω)
    (hXint : ∀ i, Integrable (X i) (μ i)) (hZint : Integrable Z μ')
    (θ C : ℝ) (hθ : 0 < θ)
    (hXexp : ∀ i, Integrable (fun ω => Real.exp (θ * X i ω)) (μ i))
    (hXexpC : ∀ i, ∫ ω, Real.exp (θ * X i ω) ∂(μ i) ≤ C)
    (hZexp : Integrable (fun ω => Real.exp (θ * Z ω)) μ')
    (hZexpC : ∫ ω, Real.exp (θ * Z ω) ∂μ' ≤ C) :
    Tendsto (fun i => ∫ ω, X i ω ∂(μ i)) l (𝓝 (∫ ω, Z ω ∂μ')) := by
  refine tendsto_of_uniform_approx _ _
    (fun n i => ∫ ω, truncBdd (n : ℝ) (X i ω) ∂(μ i))
    (fun n => ∫ ω, truncBdd (n : ℝ) (Z ω) ∂μ')
    (fun n => (n : ℝ) * Real.exp (-(θ * n)) * C)
    (fun n => tendsto_integral_bdd_of_tendstoInDistribution h (truncBdd (n : ℝ)))
    (tendsto_nat_mul_exp_neg θ C hθ) ?_
  filter_upwards [eventually_le_mul_nat θ 1 hθ] with n hn
  exact ⟨fun i => abs_integral_sub_trunc_le (μ i) (X i) (hXnn i) (hXint i) θ (n : ℝ) C hθ hn
      (hXexp i) (hXexpC i),
    abs_integral_sub_trunc_le μ' Z hZnn hZint θ (n : ℝ) C hθ hn hZexp hZexpC⟩

/-- **The second moment passes to the limit** under the same hypotheses. -/
theorem tendsto_integral_sq_of_uniform_exp
    (h : TendstoInDistribution X l Z μ μ')
    (hXnn : ∀ i, ∀ᵐ ω ∂(μ i), 0 ≤ X i ω) (hZnn : ∀ᵐ ω ∂μ', 0 ≤ Z ω)
    (hXint : ∀ i, Integrable (fun ω => X i ω ^ 2) (μ i))
    (hXm : ∀ i, AEStronglyMeasurable (X i) (μ i))
    (hZint : Integrable (fun ω => Z ω ^ 2) μ') (hZm : AEStronglyMeasurable Z μ')
    (θ C : ℝ) (hθ : 0 < θ)
    (hXexp : ∀ i, Integrable (fun ω => Real.exp (θ * X i ω)) (μ i))
    (hXexpC : ∀ i, ∫ ω, Real.exp (θ * X i ω) ∂(μ i) ≤ C)
    (hZexp : Integrable (fun ω => Real.exp (θ * Z ω)) μ')
    (hZexpC : ∫ ω, Real.exp (θ * Z ω) ∂μ' ≤ C) :
    Tendsto (fun i => ∫ ω, X i ω ^ 2 ∂(μ i)) l (𝓝 (∫ ω, Z ω ^ 2 ∂μ')) := by
  refine tendsto_of_uniform_approx _ _
    (fun n i => ∫ ω, truncSqBdd (n : ℝ) (X i ω) ∂(μ i))
    (fun n => ∫ ω, truncSqBdd (n : ℝ) (Z ω) ∂μ')
    (fun n => (n : ℝ) ^ 2 * Real.exp (-(θ * n)) * C)
    (fun n => tendsto_integral_bdd_of_tendstoInDistribution h (truncSqBdd (n : ℝ)))
    (tendsto_nat_sq_mul_exp_neg θ C hθ) ?_
  filter_upwards [eventually_le_mul_nat θ 2 hθ] with n hn
  exact ⟨fun i => abs_integral_sq_sub_truncSq_le (μ i) (X i) (hXnn i) (hXint i) (hXm i)
      θ (n : ℝ) C hθ hn (hXexp i) (hXexpC i),
    abs_integral_sq_sub_truncSq_le μ' Z hZnn hZint hZm θ (n : ℝ) C hθ hn hZexp hZexpC⟩

/-- **The variance passes to the limit** under convergence in distribution and a uniform
exponential moment on the nonnegative half-line. -/
theorem tendsto_variance_of_uniform_exp
    (h : TendstoInDistribution X l Z μ μ')
    (hXnn : ∀ i, ∀ᵐ ω ∂(μ i), 0 ≤ X i ω) (hZnn : ∀ᵐ ω ∂μ', 0 ≤ Z ω)
    (hXL2 : ∀ i, MemLp (X i) 2 (μ i)) (hZL2 : MemLp Z 2 μ')
    (θ C : ℝ) (hθ : 0 < θ)
    (hXexp : ∀ i, Integrable (fun ω => Real.exp (θ * X i ω)) (μ i))
    (hXexpC : ∀ i, ∫ ω, Real.exp (θ * X i ω) ∂(μ i) ≤ C)
    (hZexp : Integrable (fun ω => Real.exp (θ * Z ω)) μ')
    (hZexpC : ∫ ω, Real.exp (θ * Z ω) ∂μ' ≤ C) :
    Tendsto (fun i => variance (X i) (μ i)) l (𝓝 (variance Z μ')) := by
  have hXsq : ∀ i, Integrable (fun ω => X i ω ^ 2) (μ i) := fun i => by
    simpa [pow_two] using (hXL2 i).integrable_sq
  have hZsq : Integrable (fun ω => Z ω ^ 2) μ' := by
    simpa [pow_two] using hZL2.integrable_sq
  have hfirst := tendsto_integral_of_uniform_exp h hXnn hZnn
    (fun i => (hXL2 i).integrable one_le_two) (hZL2.integrable one_le_two)
    θ C hθ hXexp hXexpC hZexp hZexpC
  have hsecond := tendsto_integral_sq_of_uniform_exp h hXnn hZnn hXsq
    (fun i => (hXL2 i).aestronglyMeasurable) hZsq hZL2.aestronglyMeasurable
    θ C hθ hXexp hXexpC hZexp hZexpC
  have hlim := hsecond.sub (hfirst.mul hfirst)
  have hZv : variance Z μ' = (∫ ω, Z ω ^ 2 ∂μ') - (∫ ω, Z ω ∂μ') * (∫ ω, Z ω ∂μ') := by
    rw [variance_eq_sub hZL2]
    simp [pow_two]
  rw [hZv]
  refine hlim.congr fun i => ?_
  rw [variance_eq_sub (hXL2 i)]
  simp [pow_two]

end Sandpile.Support
