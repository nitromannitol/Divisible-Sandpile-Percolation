import Mathlib

/-!
# The floor-to-continuum passage

The floor-to-continuum passage of Step 2 of `thm:dgt4-many-limits` (`sandpile.tex:6245-6250`):
`⌊t R²⌋/R² → t` as `R → ∞`, uniformly for `t` in a compact interval `[δ,T]`
(`tendsto_floor_mul_div`), obtained by squeezing the pointwise error `|⌊tR²⌋/R² - t|` between
`0` and `1/R²` using `Nat.floor_le` and `Nat.lt_floor_add_one`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile.Support

/-- `⌊t R²⌋/R² → t` as `R → ∞`, uniformly for `t ∈ [δ,T]`. -/
theorem tendsto_floor_mul_div (δ T : ℝ) (hδ : 0 < δ) (_hδT : δ < T) :
    Tendsto (fun R : ℝ => ⨆ t ∈ Set.Icc δ T,
        |(⌊t * R ^ 2⌋₊ : ℝ) / R ^ 2 - t|) atTop (𝓝 0) := by
  have hbound : ∀ᶠ R : ℝ in atTop, ∀ t ∈ Set.Icc δ T,
      |(⌊t * R ^ 2⌋₊ : ℝ) / R ^ 2 - t| ≤ 1 / R ^ 2 := by
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with R hR
    intro t ht
    have ht0 : 0 ≤ t := le_trans hδ.le ht.1
    have hR2 : 0 < R ^ 2 := by positivity
    have h1 : (⌊t * R ^ 2⌋₊ : ℝ) ≤ t * R ^ 2 := Nat.floor_le (mul_nonneg ht0 (sq_nonneg R))
    have h2 : t * R ^ 2 < (⌊t * R ^ 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : |(⌊t * R ^ 2⌋₊ : ℝ) - t * R ^ 2| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith [h1, h2]
    have h4 : (⌊t * R ^ 2⌋₊ : ℝ) / R ^ 2 - t = ((⌊t * R ^ 2⌋₊ : ℝ) - t * R ^ 2) / R ^ 2 := by
      field_simp
    rw [h4, abs_div, abs_of_pos hR2, div_le_iff₀ hR2, one_div, inv_mul_cancel₀ (ne_of_gt hR2)]
    exact h3
  have hsup : ∀ᶠ R : ℝ in atTop, (⨆ t ∈ Set.Icc δ T,
      |(⌊t * R ^ 2⌋₊ : ℝ) / R ^ 2 - t|) ≤ 1 / R ^ 2 := by
    filter_upwards [hbound, Filter.eventually_gt_atTop (1 : ℝ)] with R hR hR1
    refine ciSup_le fun t => ?_
    by_cases ht : t ∈ Set.Icc δ T
    · rw [ciSup_pos ht]
      exact hR t ht
    · rw [ciSup_neg ht, Real.sSup_empty]
      positivity
  have hlim : Tendsto (fun R : ℝ => 1 / R ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun R : ℝ => R ^ 2) atTop atTop := by
      have := tendsto_pow_atTop_atTop_of_one_lt (α := ℝ) (r := 2) (by norm_num)
      simp
    exact tendsto_const_nhds.div_atTop h1
  have hnonneg : ∀ R : ℝ, 0 ≤ ⨆ t ∈ Set.Icc δ T,
      |(⌊t * R ^ 2⌋₊ : ℝ) / R ^ 2 - t| := fun R =>
    Real.iSup_nonneg fun t => Real.iSup_nonneg fun _ => abs_nonneg _
  exact squeeze_zero' (Filter.Eventually.of_forall hnonneg) hsup hlim

end Sandpile.Support
