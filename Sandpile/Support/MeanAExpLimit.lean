import Sandpile.Support.MeanAMoment

/-!
# The limit of a uniform exponential moment has the same moment

The limit of a family with a uniform exponential moment has the same exponential moment.
This is the paper's own sentence at `sandpile.tex:2005-2007`, "Passing to the limit along
bounded truncations of `e^{θx}` gives `E e^{θ𝒰(1,0)} < ∞`": each truncation
`y ↦ e^{θ(0∨(y∧M))}` (`expTruncBdd`) is bounded and continuous, so weak convergence sees it
(`integral_expTruncBdd_le`), and each is below `e^{θy}` on the nonnegative half-line
(`expTruncBdd_le`); monotone convergence in the truncation level `M` then transfers the bound
to the limit (`integrable_exp_of_uniform_exp`). Together with `Sandpile.Support.MeanAMoment`
this makes the continuum exponential moment a consequence of the discrete one, so that no
property of the limiting field beyond its being the limit is used.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped NNReal ENNReal

namespace Sandpile.Support

variable {ι : Type*} {l : Filter ι} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {Ω' : Type*} [MeasurableSpace Ω'] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {X : (i : ι) → Ω i → ℝ} {Z : Ω' → ℝ}

/-- `y ↦ exp(θ·(0∨(y∧M)))`, as a bounded continuous function. -/
noncomputable def expTruncBdd (θ M : ℝ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun y => Real.exp (θ * max 0 (min y M)), by fun_prop⟩ (Real.exp (|θ| * |M|)) (by
      intro x y
      have key : ∀ z : ℝ, 0 < Real.exp (θ * max 0 (min z M)) ∧
          Real.exp (θ * max 0 (min z M)) ≤ Real.exp (|θ| * |M|) := by
        intro z
        refine ⟨Real.exp_pos _, Real.exp_le_exp.mpr ?_⟩
        have h0 : (0:ℝ) ≤ max 0 (min z M) := le_max_left _ _
        have hM : max 0 (min z M) ≤ |M| :=
          max_le (abs_nonneg M) ((min_le_right _ _).trans (le_abs_self M))
        calc θ * max 0 (min z M) ≤ |θ * max 0 (min z M)| := le_abs_self _
          _ = |θ| * |max 0 (min z M)| := abs_mul _ _
          _ = |θ| * max 0 (min z M) := by rw [abs_of_nonneg h0]
          _ ≤ |θ| * |M| := mul_le_mul_of_nonneg_left hM (abs_nonneg θ)
      obtain ⟨hx0, hx1⟩ := key x
      obtain ⟨hy0, hy1⟩ := key y
      simp only [ContinuousMap.coe_mk]
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith)

/-- The bounded continuous function `expTruncBdd` unfolds to its defining formula. -/
@[simp] theorem expTruncBdd_apply (θ M y : ℝ) :
    expTruncBdd θ M y = Real.exp (θ * max 0 (min y M)) := rfl

/-- The truncated exponential is below the exponential on the nonnegative half-line. -/
theorem expTruncBdd_le (θ M y : ℝ) (hθ : 0 ≤ θ) (hy : 0 ≤ y) :
    expTruncBdd θ M y ≤ Real.exp (θ * y) := by
  have h : max 0 (min y M) ≤ y := max_le hy (min_le_left _ _)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h hθ)

/-- The truncated exponential is positive. -/
theorem expTruncBdd_pos (θ M y : ℝ) : 0 < expTruncBdd θ M y := Real.exp_pos _

/-- **The limit inherits the uniform bound at each truncation level.** -/
theorem integral_expTruncBdd_le
    (h : TendstoInDistribution X l Z μ μ') [l.NeBot]
    (θ C : ℝ) (hθ : 0 ≤ θ) (M : ℝ)
    (hX : ∀ᶠ i in l, (∀ᵐ ω ∂(μ i), 0 ≤ X i ω) ∧
      Integrable (fun ω => Real.exp (θ * X i ω)) (μ i) ∧
      ∫ ω, Real.exp (θ * X i ω) ∂(μ i) ≤ C) :
    ∫ ω, expTruncBdd θ M (Z ω) ∂μ' ≤ C := by
  have hlim := tendsto_integral_bdd_of_tendstoInDistribution h (expTruncBdd θ M)
  refine le_of_tendsto hlim ?_
  filter_upwards [hX] with i hi
  obtain ⟨hnn, hint, hle⟩ := hi
  have hbdd : Integrable (fun ω => expTruncBdd θ M (X i ω)) (μ i) := by
    refine Integrable.mono' (integrable_const (Real.exp (|θ| * |M|)))
      ((expTruncBdd θ M).continuous.comp_aestronglyMeasurable
        ((h.forall_aemeasurable i).aestronglyMeasurable)) ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    have h0 : (0:ℝ) < expTruncBdd θ M (X i ω) := expTruncBdd_pos _ _ _
    have h1 : expTruncBdd θ M (X i ω) ≤ Real.exp (|θ| * |M|) := by
      have hb := (expTruncBdd θ M).norm_coe_le_norm
      have : max 0 (min (X i ω) M) ≤ |M| :=
        max_le (abs_nonneg M) ((min_le_right _ _).trans (le_abs_self M))
      refine Real.exp_le_exp.mpr ?_
      calc θ * max 0 (min (X i ω) M) ≤ |θ * max 0 (min (X i ω) M)| := le_abs_self _
        _ = |θ| * |max 0 (min (X i ω) M)| := abs_mul _ _
        _ = |θ| * max 0 (min (X i ω) M) := by
            rw [abs_of_nonneg (le_max_left (0:ℝ) (min (X i ω) M))]
        _ ≤ |θ| * |M| := mul_le_mul_of_nonneg_left this (abs_nonneg θ)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt h0)]
    exact h1
  calc ∫ ω, expTruncBdd θ M (X i ω) ∂(μ i)
      ≤ ∫ ω, Real.exp (θ * X i ω) ∂(μ i) := by
        refine integral_mono_ae hbdd hint ?_
        filter_upwards [hnn] with ω hω
        exact expTruncBdd_le θ M (X i ω) hθ hω
    _ ≤ C := hle

/-- **The limit has the same exponential moment.**  Monotone convergence along the
truncation levels. -/
theorem integrable_exp_of_uniform_exp
    (h : TendstoInDistribution X l Z μ μ') [l.NeBot]
    (hZnn : ∀ᵐ ω ∂μ', 0 ≤ Z ω)
    (θ C : ℝ) (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (hX : ∀ᶠ i in l, (∀ᵐ ω ∂(μ i), 0 ≤ X i ω) ∧
      Integrable (fun ω => Real.exp (θ * X i ω)) (μ i) ∧
      ∫ ω, Real.exp (θ * X i ω) ∂(μ i) ≤ C) :
    Integrable (fun ω => Real.exp (θ * Z ω)) μ' ∧
      ∫ ω, Real.exp (θ * Z ω) ∂μ' ≤ C := by
  set g : ℕ → Ω' → ℝ≥0∞ := fun n ω => ENNReal.ofReal (expTruncBdd θ (n : ℝ) (Z ω)) with hg
  have hZm : AEStronglyMeasurable Z μ' := h.aemeasurable_limit.aestronglyMeasurable
  have hgm : ∀ n, AEMeasurable (g n) μ' := by
    intro n
    exact (ENNReal.measurable_ofReal.comp
      ((expTruncBdd θ (n : ℝ)).continuous.measurable)).comp_aemeasurable h.aemeasurable_limit
  have hmono : ∀ᵐ ω ∂μ', Monotone fun n => g n ω := by
    filter_upwards [hZnn] with ω hω
    intro m n hmn
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    refine mul_le_mul_of_nonneg_left ?_ hθ
    exact max_le_max (le_refl 0) (min_le_min (le_refl (Z ω)) (by exact_mod_cast hmn))
  have hsup : ∀ᵐ ω ∂μ', (⨆ n, g n ω) = ENNReal.ofReal (Real.exp (θ * Z ω)) := by
    filter_upwards [hZnn] with ω hω
    refine le_antisymm (iSup_le fun n => ?_) ?_
    · exact ENNReal.ofReal_le_ofReal (expTruncBdd_le θ (n : ℝ) (Z ω) hθ hω)
    · obtain ⟨n, hn⟩ := exists_nat_ge (Z ω)
      refine le_iSup_of_le n ?_
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      refine mul_le_mul_of_nonneg_left ?_ hθ
      rw [min_eq_left hn, max_eq_right hω]
  have hkey : ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * Z ω)) ∂μ' ≤ ENNReal.ofReal C := by
    have h1 : ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * Z ω)) ∂μ' = ∫⁻ ω, (⨆ n, g n ω) ∂μ' :=
      lintegral_congr_ae (hsup.mono fun ω hω => hω.symm)
    have h2 : ∫⁻ ω, (⨆ n, g n ω) ∂μ' = ⨆ n, ∫⁻ ω, g n ω ∂μ' := lintegral_iSup' hgm hmono
    have h3 : ∀ n, ∫⁻ ω, g n ω ∂μ' ≤ ENNReal.ofReal C := by
      intro n
      have hbdd : Integrable (fun ω => expTruncBdd θ (n : ℝ) (Z ω)) μ' := by
        refine Integrable.mono' (integrable_const (Real.exp (|θ| * |(n : ℝ)|)))
          ((expTruncBdd θ (n : ℝ)).continuous.comp_aestronglyMeasurable hZm) ?_
        refine Filter.Eventually.of_forall fun ω => ?_
        have h0 : (0:ℝ) < expTruncBdd θ (n : ℝ) (Z ω) := expTruncBdd_pos _ _ _
        have hle : max 0 (min (Z ω) (n : ℝ)) ≤ |(n : ℝ)| :=
          max_le (abs_nonneg _) ((min_le_right _ _).trans (le_abs_self _))
        rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt h0)]
        refine Real.exp_le_exp.mpr ?_
        calc θ * max 0 (min (Z ω) (n : ℝ)) ≤ |θ * max 0 (min (Z ω) (n : ℝ))| := le_abs_self _
          _ = |θ| * |max 0 (min (Z ω) (n : ℝ))| := abs_mul _ _
          _ = |θ| * max 0 (min (Z ω) (n : ℝ)) := by
            rw [abs_of_nonneg (le_max_left (0:ℝ) (min (Z ω) (n:ℝ)))]
          _ ≤ |θ| * |(n : ℝ)| := mul_le_mul_of_nonneg_left hle (abs_nonneg θ)
      have heq : ∫⁻ ω, g n ω ∂μ'
          = ENNReal.ofReal (∫ ω, expTruncBdd θ (n : ℝ) (Z ω) ∂μ') :=
        (ofReal_integral_eq_lintegral_ofReal hbdd
          (Filter.Eventually.of_forall fun ω => le_of_lt (expTruncBdd_pos _ _ _))).symm
      rw [heq]
      exact ENNReal.ofReal_le_ofReal (integral_expTruncBdd_le h θ C hθ (n : ℝ) hX)
    rw [h1, h2]
    exact iSup_le h3
  have hexpm : AEStronglyMeasurable (fun ω => Real.exp (θ * Z ω)) μ' :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).comp_aestronglyMeasurable hZm
  have hfin : HasFiniteIntegral (fun ω => Real.exp (θ * Z ω)) μ' := by
    have henorm : ∀ ω, ‖Real.exp (θ * Z ω)‖ₑ = ENNReal.ofReal (Real.exp (θ * Z ω)) := by
      intro ω
      rw [Real.enorm_eq_ofReal (le_of_lt (Real.exp_pos _))]
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ ω, ‖Real.exp (θ * Z ω)‖ₑ ∂μ'
        = ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * Z ω)) ∂μ' := by
          exact lintegral_congr fun ω => henorm ω
      _ ≤ ENNReal.ofReal C := hkey
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hint : Integrable (fun ω => Real.exp (θ * Z ω)) μ' := ⟨hexpm, hfin⟩
  refine ⟨hint, ?_⟩
  have hofr : ENNReal.ofReal (∫ ω, Real.exp (θ * Z ω) ∂μ')
      = ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * Z ω)) ∂μ' :=
    ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ω => le_of_lt (Real.exp_pos _))
  have hle : ENNReal.ofReal (∫ ω, Real.exp (θ * Z ω) ∂μ') ≤ ENNReal.ofReal C := by
    rw [hofr]; exact hkey
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hle

end Sandpile.Support
