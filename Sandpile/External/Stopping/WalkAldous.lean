import Sandpile.External.Stopping.WalkIncrement

/-!
# Rescaled walk increments at stopping times

The Gaussian maximal-displacement estimate yields a uniform small-increment
bound after diffusive rescaling. This is the walk estimate for the Aldous
condition in Coquet and Toldo, *Convergence of values in optimal stopping and
convergence of optimal stopping times*, Section 2.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Sandpile.External.Stopping

/-- Diffusively rescaled walk increments over a short interval are uniformly
small in probability, including at bounded stopping times. The terminal index
may depend arbitrarily on the path. -/
theorem rescaled_increment_small (d : ℕ) (hd : 1 ≤ d) (ε η : ℝ)
    (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ R₀ : ℝ, 0 < δ ∧ 0 < R₀ ∧
      ∀ (R : ℝ), R₀ ≤ R → ∀ (N n : ℕ), 1 ≤ n → (n : ℝ) ≤ δ * R ^ 2 + 1 →
        ∀ (x : Site d) (τ σ : (ℕ → Site d) → ℕ), IsWalkStopping τ →
          (∀ X, τ X ≤ N) → (∀ X, τ X ≤ σ X ∧ σ X ≤ τ X + n) →
          walkLaw d x {X | ε * R ≤
            ((LatticeProb.graphNorm (X (σ X) - X (τ X)) : ℕ) : ℝ)} ≤ ENNReal.ofReal η := by
  obtain ⟨C, c, hC, hc, hmax⟩ := exists_stopped_maxDisplacement_bound d hd
  have hevent : ∀ᶠ t : ℝ in atTop, C * Real.exp (-t) < η := by
    have hlim : Tendsto (fun t : ℝ => C * Real.exp (-t)) atTop (𝓝 0) := by
      simpa only [mul_zero] using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C
    exact hlim.eventually (Iio_mem_nhds hη)
  obtain ⟨H, hH⟩ := eventually_atTop.1 hevent
  let K : ℝ := max H 1
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_right H 1)
  have hsmall : C * Real.exp (-K) < η := hH K (le_max_left H 1)
  let δ : ℝ := c * ε ^ 2 / (2 * K)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let R₀ : ℝ := max 1 (max ε⁻¹ δ⁻¹)
  have hR₀ : 0 < R₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨δ, R₀, hδ, hR₀, ?_⟩
  intro R hR N n hn hnR x τ σ hτ hτN hτσ
  have hR1 : 1 ≤ R := (le_max_left _ _).trans hR
  have hRε : ε⁻¹ ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hRδ : δ⁻¹ ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hR)
  have ha : 1 ≤ ε * R := by
    calc 1 = ε * ε⁻¹ := (mul_inv_cancel₀ hε.ne').symm
      _ ≤ ε * R := mul_le_mul_of_nonneg_left hRε hε.le
  have hRδsq : 1 ≤ δ * R ^ 2 := by
    have hmul : 1 ≤ δ * R := by
      calc 1 = δ * δ⁻¹ := (mul_inv_cancel₀ hδ.ne').symm
        _ ≤ δ * R := mul_le_mul_of_nonneg_left hRδ hδ.le
    have hsq : R ≤ R ^ 2 := by nlinarith
    exact hmul.trans (mul_le_mul_of_nonneg_left hsq hδ.le)
  have hn' : (0 : ℝ) < n := by exact_mod_cast (zero_lt_one.trans_le hn)
  have hn2 : (n : ℝ) ≤ 2 * δ * R ^ 2 := by nlinarith
  have hδeq : K * (2 * δ * R ^ 2) = c * (ε * R) ^ 2 := by
    dsimp [δ]
    field_simp
  have hlarge : K ≤ c * (ε * R) ^ 2 / n := by
    apply (le_div_iff₀ hn').2
    calc K * (n : ℝ) ≤ K * (2 * δ * R ^ 2) :=
          mul_le_mul_of_nonneg_left hn2 hK.le
      _ = c * (ε * R) ^ 2 := hδeq
  have hsub : {X : ℕ → Site d | ε * R ≤
        ((LatticeProb.graphNorm (X (σ X) - X (τ X)) : ℕ) : ℝ)} ⊆
      {X : ℕ → Site d | ∃ k ≤ n, ε * R ≤
        ((LatticeProb.graphNorm (X (τ X + k) - X (τ X)) : ℕ) : ℝ)} := by
    intro X hX
    have hk : σ X - τ X ≤ n := by
      have hs := hτσ X
      omega
    refine ⟨σ X - τ X, hk, ?_⟩
    change ε * R ≤ ((LatticeProb.graphNorm (X (σ X) - X (τ X)) : ℕ) : ℝ) at hX
    simpa only [Nat.add_sub_of_le (hτσ X).1] using hX
  calc walkLaw d x {X | ε * R ≤
        ((LatticeProb.graphNorm (X (σ X) - X (τ X)) : ℕ) : ℝ)}
      ≤ walkLaw d x {X | ∃ k ≤ n, ε * R ≤
        ((LatticeProb.graphNorm (X (τ X + k) - X (τ X)) : ℕ) : ℝ)} := measure_mono hsub
    _ ≤ ENNReal.ofReal (C * Real.exp (-c * (ε * R) ^ 2 / n)) :=
      hmax N n (ε * R) hn ha x τ hτ hτN
    _ ≤ ENNReal.ofReal (C * Real.exp (-K)) := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.exp_le_exp.mpr
      rw [neg_mul, neg_div]
      exact neg_le_neg hlarge
    _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal hsmall.le

end Sandpile.External.Stopping
