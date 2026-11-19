import Sandpile.External.Stopping.GaussianTail

/-!
# Uniform moduli for rescaled walks

The Gaussian modulus bound and exponential decay yield uniform control of
short-lag oscillations on a bounded time interval, as the scale grows.
-/

open Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace Sandpile.External.Stopping

/-- At sufficiently large scales, short-lag oscillations on a bounded time
interval are uniformly small in probability over all starting sites. -/
theorem diffusiveWalk_modulus_small (d : ℕ) (hd : 1 ≤ d) (L ε η : ℝ)
    (hL : 0 < L) (hε : 0 < ε) (hη : 0 < η) :
    ∃ (δ : ℝ≥0) (R₀ : ℝ), 0 < δ ∧ 0 < R₀ ∧
      ∀ (R : ℝ), R₀ ≤ R → ∀ x : Site d,
        walkLaw d x {X | ∃ s t : ℝ≥0, (s : ℝ) ≤ L ∧ (t : ℝ) ≤ L ∧
          |(s : ℝ) - t| ≤ δ ∧ ε < dist (diffusiveWalk R s X) (diffusiveWalk R t X)} ≤
            ENNReal.ofReal η := by
  obtain ⟨C, c, hC, hc, hmod⟩ := exists_diffusiveWalk_modulus_gaussian d hd
  let a := c * (ε / 4) ^ 2 / 3
  have ha : 0 < a := by dsimp [a]; positivity
  have hlim := tendsto_linear_mul_exp_neg_mul L C a ha
  have hevent : ∀ᶠ u : ℝ in atTop, (L * u + 1) * C * Real.exp (-a * u) < η :=
    hlim.eventually (Iio_mem_nhds hη)
  obtain ⟨U, hU⟩ := eventually_atTop.1 hevent
  let u := max U 1
  have hu : 1 ≤ u := le_max_right U 1
  have hupos : 0 < u := zero_lt_one.trans_le hu
  have hsmall := hU u (le_max_left U 1)
  let δ : ℝ≥0 := ⟨u⁻¹, inv_nonneg.mpr hupos.le⟩
  have hδ : 0 < δ := by change 0 < u⁻¹; positivity
  let R₀ := max u (8 / ε)
  have hR₀ : 0 < R₀ := hupos.trans_le (le_max_left _ _)
  refine ⟨δ, R₀, hδ, hR₀, ?_⟩
  intro R hR x
  have hRu : u ≤ R := (le_max_left _ _).trans hR
  have hRpos : 0 < R := hupos.trans_le hRu
  have hRε : 8 ≤ R * ε := (div_le_iff₀ hε).mp ((le_max_right _ _).trans hR)
  have hRsq : u ≤ R ^ 2 := by nlinarith
  have hRdiv : 1 ≤ R ^ 2 / u := (le_div_iff₀ hupos).2 (by nlinarith)
  let n : ℕ := ⌊(2 * (δ : ℝ)) * R ^ 2⌋₊ + 1
  have hnpos : 0 < (n : ℝ) := by dsimp [n]; positivity
  have hden : (n : ℝ) ≤ 3 * R ^ 2 / u := by
    have hf := Nat.floor_le (show 0 ≤ (2 * (δ : ℝ)) * R ^ 2 by positivity)
    change ((⌊(2 * (δ : ℝ)) * R ^ 2⌋₊ : ℕ) : ℝ) ≤ _ at hf
    have hco : (δ : ℝ) = u⁻¹ := rfl
    rw [hco] at hf
    dsimp [n]
    rw [hco]
    push_cast
    rw [div_eq_mul_inv] at hRdiv ⊢
    nlinarith
  have hrate : a * u ≤ c * ((ε / 4) * R) ^ 2 / n := by
    apply (le_div_iff₀ hnpos).2
    have hh := mul_le_mul_of_nonneg_left hden (show 0 ≤ a * u by positivity)
    calc
      a * u * n ≤ a * u * (3 * R ^ 2 / u) := hh
      _ = c * ((ε / 4) * R) ^ 2 := by dsimp [a]; field_simp
  have hcount : (((⌊L / (δ : ℝ)⌋₊ + 1 : ℕ) : ℝ)) ≤ L * u + 1 := by
    have hf := Nat.floor_le (show 0 ≤ L / (δ : ℝ) by positivity)
    have hco : (δ : ℝ) = u⁻¹ := rfl
    rw [hco, div_inv_eq_mul] at hf
    rw [hco, div_inv_eq_mul]
    push_cast
    linarith
  have hcountE : ((⌊L / (δ : ℝ)⌋₊ + 1 : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal (L * u + 1) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal hcount
  have hexp : C * Real.exp (-c * ((ε / 4) * R) ^ 2 / (n : ℝ)) ≤
      C * Real.exp (-a * u) := by
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.exp_le_exp.mpr
    rw [neg_mul, neg_div]
    simpa only [neg_mul] using neg_le_neg hrate
  calc
    _ ≤ ((⌊L / (δ : ℝ)⌋₊ + 1 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (C * Real.exp (-c * ((ε / 4) * R) ^ 2 / n)) :=
      hmod R ε L δ hRpos hδ hRε x
    _ ≤ ENNReal.ofReal (L * u + 1) * ENNReal.ofReal (C * Real.exp (-a * u)) :=
      mul_le_mul' hcountE (ENNReal.ofReal_le_ofReal hexp)
    _ = ENNReal.ofReal ((L * u + 1) * C * Real.exp (-a * u)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal hsmall.le

end Sandpile.External.Stopping
