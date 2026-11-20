import Sandpile.Support.BrownianPolynomialReward

/-!
# Uniform bounds for translated Brownian rewards

Polynomial-growth rewards along Brownian paths have an integrable bound
uniformly over bounded shifts and a finite time strip.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped NNReal ENNReal

/-- Polynomial rewards along Brownian paths are dominated uniformly over a
bounded set of spatial shifts and a finite time strip. -/
theorem Sandpile.Support.exists_integrable_shifted_brownian_reward_bound
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (x : Sandpile.Continuum.Space d)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → Sandpile.Continuum.Space d)
    (hB : Sandpile.Continuum.IsBrownian d x B P)
    (hBm : ∀ t, StronglyMeasurable (B t))
    (hBc : ∀ ω, Continuous fun t => B t ω) (T : ℝ≥0)
    (G : ℝ → Sandpile.Continuum.Space d → ℝ)
    (hgrow : ∃ C k : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) (T : ℝ),
      ∀ y, |G t y| ≤ C * (1 + ‖y‖) ^ k)
    (K : Set (Sandpile.Continuum.Space d)) (R : ℝ) (hR : 0 ≤ R)
    (hK : ∀ y ∈ K, ‖y‖ ≤ R) :
    ∃ bound : Ω → ℝ, Integrable bound P ∧
      ∀ᵐ ω ∂P, ∀ u ∈ Set.Icc (0 : ℝ) (T : ℝ), ∀ y ∈ K, ∀ t ≤ T,
        ‖G u (y + B t ω)‖ ≤ bound ω := by
  obtain ⟨C, k, hCk⟩ := hgrow
  have hC : 0 ≤ C := by
    have h := hCk 0 ⟨le_rfl, T.coe_nonneg⟩ 0
    simp only [norm_zero, add_zero, Real.one_rpow, mul_one] at h
    exact (abs_nonneg _).trans h
  obtain ⟨n, hn⟩ := exists_nat_ge k
  obtain ⟨M, hMm, hM0, hMbound, hMint⟩ :=
    Sandpile.Support.exists_brownian_path_bound x P B hB hBm hBc T
  let bound : Ω → ℝ := fun ω => C * (1 + R + M ω) ^ n
  have hint : Integrable bound P := by
    have hmom : Integrable (fun ω => (1 + R + M ω) ^ n) P := by
      by_cases hn0 : n = 0
      · subst n
        simpa only [pow_zero] using (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) P)
      · have hLp : MemLp M n P := by
          apply (integrable_norm_rpow_iff hMm.aestronglyMeasurable
            (by exact_mod_cast hn0) (ENNReal.natCast_ne_top n)).mp
          simpa only [ENNReal.toReal_natCast, Real.rpow_natCast, Real.norm_eq_abs,
            abs_of_nonneg (hM0 _)] using hMint n
        have hLp' : MemLp (fun ω => (1 + R) + M ω) n P := (memLp_const (1 + R)).add hLp
        have hi := hLp'.integrable_norm_pow hn0
        have hnonneg : ∀ ω, 0 ≤ 1 + R + M ω := fun ω => by linarith [hM0 ω]
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg _)] using hi
    exact hmom.const_mul C
  refine ⟨bound, hint, ?_⟩
  filter_upwards [hMbound] with ω hω u hu y hy t ht
  calc
    ‖G u (y + B t ω)‖ = |G u (y + B t ω)| := Real.norm_eq_abs _
    _ ≤ C * (1 + ‖y + B t ω‖) ^ k := hCk u hu _
    _ ≤ C * (1 + ‖y + B t ω‖) ^ n := by
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [Real.rpow_natCast] using
        (Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 1 + ‖y + B t ω‖ by linarith [norm_nonneg (y + B t ω)]) hn)
    _ ≤ bound ω := by
      dsimp [bound]
      have hm : 1 + ‖y + B t ω‖ ≤ 1 + R + M ω := by
        linarith [norm_add_le y (B t ω), hK y hy, hω t ht]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hm n) hC
