import Sandpile.Support.TightNegSobolev

/-!
# Markov's inequality for a norm dominated by a square root

This file proves Markov's inequality in the form Steps 2 and 3 of `prop:d4-superdiffusive-limit`
consume it (`sandpile.tex:3368-3404`). Both steps bound the `H^{-s}(D)` norm of a rescaled
field by a constant times the square root of a nonnegative random variable whose expectation
vanishes: Step 2 by the mesh sum of the squares of the smoothed error, Step 3 by the square of
the centred window. The paper states the conclusion as convergence of the expected squared
norm, but what the limit theorem needs is convergence to zero in probability, and Markov's
inequality gives it directly from the expectation of the dominating variable, with no second
moment of the norm itself required.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Sandpile.Support

/-- **Markov for a norm dominated by a square root.**  If `N_R ≤ K_R√(Y_R)`
pointwise with `Y_R ≥ 0` integrable, and `K_R²E Y_R ≤ B_R → 0`, then `N_R → 0`
in probability. -/
theorem tendsto_measure_gt_of_tendsto_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (N : ℝ → Ω → ℝ≥0∞) (Y : ℝ → Ω → ℝ) (B K : ℝ → ℝ)
    (hK : ∀ᶠ R : ℝ in atTop, 0 ≤ K R)
    (hnn : ∀ (R : ℝ) (ω : Ω), 0 ≤ Y R ω)
    (hint : ∀ᶠ R : ℝ in atTop, Integrable (Y R) P)
    (hdom : ∀ᶠ R : ℝ in atTop, ∀ ω : Ω, N R ω ≤ ENNReal.ofReal (K R * Real.sqrt (Y R ω)))
    (hB : ∀ᶠ R : ℝ in atTop, K R ^ 2 * ∫ ω, Y R ω ∂P ≤ B R)
    (hB0 : Tendsto B atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun R : ℝ => P {ω | ENNReal.ofReal ε < N R ω}) atTop (𝓝 0) := by
  have hε2 : (0:ℝ) < ε ^ 2 := by positivity
  have hmaj : Tendsto (fun R : ℝ => ENNReal.ofReal (B R / ε ^ 2)) atTop (𝓝 0) := by
    have h : Tendsto (fun R : ℝ => B R / ε ^ 2) atTop (𝓝 0) := by
      simpa using hB0.div_const (ε ^ 2)
    have h2 := (ENNReal.continuous_ofReal.tendsto (0:ℝ)).comp h
    simpa [Function.comp_def] using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmaj
    (Filter.Eventually.of_forall fun R => by simp) ?_
  filter_upwards [hK, hint, hdom, hB] with R hKR hintR hdomR hBR
  -- the event is inside a level set of `K_R²Y_R`
  have hsub : {ω : Ω | ENNReal.ofReal ε < N R ω} ⊆
      {ω : Ω | ε ^ 2 ≤ K R ^ 2 * Y R ω} := by
    intro ω hω
    have h1 : ENNReal.ofReal ε < ENNReal.ofReal (K R * Real.sqrt (Y R ω)) :=
      lt_of_lt_of_le hω (hdomR ω)
    have h2 : ε < K R * Real.sqrt (Y R ω) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hε.le).mp h1
    have h3 : Real.sqrt (Y R ω) ^ 2 = Y R ω := Real.sq_sqrt (hnn R ω)
    have h4 : 0 ≤ K R * Real.sqrt (Y R ω) := mul_nonneg hKR (Real.sqrt_nonneg _)
    have h5 : ε ^ 2 < (K R * Real.sqrt (Y R ω)) ^ 2 := by nlinarith
    have h6 : (K R * Real.sqrt (Y R ω)) ^ 2 = K R ^ 2 * Y R ω := by rw [mul_pow, h3]
    have h7 : ε ^ 2 < K R ^ 2 * Y R ω := by rw [← h6]; exact h5
    exact h7.le
  -- Markov for `K_R²Y_R`
  have hTnn : 0 ≤ᵐ[P] fun ω => K R ^ 2 * Y R ω :=
    Filter.Eventually.of_forall fun ω => by
      show (0:ℝ) ≤ K R ^ 2 * Y R ω
      exact mul_nonneg (sq_nonneg _) (hnn R ω)
  have hTint : Integrable (fun ω => K R ^ 2 * Y R ω) P := hintR.const_mul _
  have hmk := mul_meas_ge_le_integral_of_nonneg hTnn hTint (ε ^ 2)
  rw [measureReal_def, integral_const_mul] at hmk
  have hreal : (P {ω : Ω | ε ^ 2 ≤ K R ^ 2 * Y R ω}).toReal ≤ B R / ε ^ 2 := by
    rw [le_div_iff₀ hε2]
    have hb := hBR
    nlinarith [hmk]
  have hfin : P {ω : Ω | ε ^ 2 ≤ K R ^ 2 * Y R ω} ≠ ⊤ := measure_ne_top P _
  calc P {ω : Ω | ENNReal.ofReal ε < N R ω}
      ≤ P {ω : Ω | ε ^ 2 ≤ K R ^ 2 * Y R ω} := measure_mono hsub
    _ = ENNReal.ofReal ((P {ω : Ω | ε ^ 2 ≤ K R ^ 2 * Y R ω}).toReal) :=
        (ENNReal.ofReal_toReal hfin).symm
    _ ≤ ENNReal.ofReal (B R / ε ^ 2) := ENNReal.ofReal_le_ofReal hreal

/-- **The `H^{-s}(D)` norm is subadditive along any pointwise splitting** of the
functional, not only a literal difference. -/
theorem negSobolevNorm_le_add {d : ℕ} (s : ℝ) (D : Set (Sandpile.Continuum.Space d))
    (F G H : (Sandpile.Continuum.Space d → ℝ) → ℝ)
    (h : ∀ φ : Sandpile.Continuum.Space d → ℝ, Sandpile.Continuum.IsTestFn D φ →
      |F φ| ≤ |G φ| + |H φ|) :
    Sandpile.Continuum.negSobolevNorm d s D F
      ≤ Sandpile.Continuum.negSobolevNorm d s D G
        + Sandpile.Continuum.negSobolevNorm d s D H := by
  unfold Sandpile.Continuum.negSobolevNorm
  apply sSup_le
  rintro v ⟨φ, hφ, hn, rfl⟩
  have hG : ENNReal.ofReal |G φ| ≤
      sSup {v : ℝ≥0∞ | ∃ ψ : Sandpile.Continuum.Space d → ℝ,
        Sandpile.Continuum.IsTestFn D ψ ∧ Sandpile.Continuum.sobolevNormSq d s ψ ≤ 1 ∧
          v = ENNReal.ofReal |G ψ|} :=
    le_sSup ⟨φ, hφ, hn, rfl⟩
  have hH : ENNReal.ofReal |H φ| ≤
      sSup {v : ℝ≥0∞ | ∃ ψ : Sandpile.Continuum.Space d → ℝ,
        Sandpile.Continuum.IsTestFn D ψ ∧ Sandpile.Continuum.sobolevNormSq d s ψ ≤ 1 ∧
          v = ENNReal.ofReal |H ψ|} :=
    le_sSup ⟨φ, hφ, hn, rfl⟩
  calc ENNReal.ofReal |F φ|
      ≤ ENNReal.ofReal (|G φ| + |H φ|) := ENNReal.ofReal_le_ofReal (h φ hφ)
    _ = ENNReal.ofReal |G φ| + ENNReal.ofReal |H φ| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ _ := add_le_add hG hH

/-- **A norm split into two pieces is small when each piece is small.** -/
theorem measure_gt_le_add {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (N N₁ N₂ : Ω → ℝ≥0∞) (h : ∀ ω, N ω ≤ N₁ ω + N₂ ω) {ε : ℝ} (hε : 0 < ε) :
    P {ω | ENNReal.ofReal ε < N ω} ≤
      P {ω | ENNReal.ofReal (ε / 2) < N₁ ω} + P {ω | ENNReal.ofReal (ε / 2) < N₂ ω} := by
  have hsub : {ω | ENNReal.ofReal ε < N ω} ⊆
      {ω | ENNReal.ofReal (ε / 2) < N₁ ω} ∪ {ω | ENNReal.ofReal (ε / 2) < N₂ ω} := by
    intro ω hω
    by_contra hc
    rw [Set.mem_union, not_or] at hc
    have h1 : N₁ ω ≤ ENNReal.ofReal (ε / 2) := not_lt.mp hc.1
    have h2 : N₂ ω ≤ ENNReal.ofReal (ε / 2) := not_lt.mp hc.2
    have hsum : N ω ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      le_trans (h ω) (add_le_add h1 h2)
    have heq : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      norm_num
    rw [heq] at hsum
    exact absurd hω (not_lt.mpr hsum)
  exact le_trans (measure_mono hsub) (measure_union_le _ _)

end Sandpile.Support
