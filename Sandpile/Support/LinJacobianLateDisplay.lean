/-
The late display of Step 1 of `lem:dgt4-linearization-from-survival`
(`eq:dgt4-late-derivative-variance`, `sandpile.tex:5755-5767`) in the form the
assembly of `Support/LinJacobianStep1Limit.lean` asks for.

The paper writes the late bound as `(δR²+2)² ∑_z a_R(z)²` and then reads it as
`C(φ)δ²+o(1)` through `eq:dgt4-tested-cell-l2`, `∑_z a_R(z)² ≤ C(φ)R^{-4}`.  The
expansion `(δR²+1)²C(φ)R^{-4} = C(φ)δ² + 2C(φ)δR^{-2} + C(φ)R^{-4}` makes the
`o(1)` explicit.
-/
import Sandpile.Support.LinJacobianStep1Limit

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

theorem tendsto_late_error (b c : ℝ) :
    Tendsto (fun R : ℝ => b * (R ^ 2)⁻¹ + c * (R ^ 4)⁻¹) atTop (𝓝 0) := by
  have h2 : Tendsto (fun R : ℝ => (R ^ 2)⁻¹) atTop (𝓝 0) :=
    (tendsto_pow_atTop (two_ne_zero)).inv_tendsto_atTop
  have h4 : Tendsto (fun R : ℝ => (R ^ 4)⁻¹) atTop (𝓝 0) :=
    (tendsto_pow_atTop (by norm_num : (4 : ℕ) ≠ 0)).inv_tendsto_atTop
  simpa using (h2.const_mul b).add (h4.const_mul c)

/-- **`eq:dgt4-late-derivative-variance` as the hypothesis `hlate`**: from
`eq:dgt4-tested-cell-l2` the late display holds with `C = C(φ)` and the explicit
error `2C(φ)δR^{-2} + C(φ)R^{-4}`. -/
theorem late_display_of_cell_l2 {l : Filter ℝ} (Cphi : ℝ) (hCphi : 0 ≤ Cphi) (n : ℝ → ℕ)
    (S : ℝ → ℝ)
    (hcell : ∀ᶠ R : ℝ in l, S R ≤ Cphi * (R ^ 4)⁻¹) (δ : ℝ) (hδ : 0 < δ)
    (hl : l ≤ atTop := by exact le_rfl) :
    ∃ o : ℝ → ℝ, Tendsto o l (𝓝 0) ∧
      ∀ᶠ R : ℝ in l, ((lateTimes (n R) δ R).card : ℝ) ^ 2 * S R ≤ Cphi * δ ^ 2 + o R := by
  refine ⟨fun R => (2 * Cphi * δ) * (R ^ 2)⁻¹ + Cphi * (R ^ 4)⁻¹,
    (tendsto_late_error _ _).mono_left hl, ?_⟩
  filter_upwards [hcell, (eventually_ge_atTop (1 : ℝ)).filter_mono hl] with R hR hR1
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR1
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have hR4 : (0 : ℝ) < R ^ 4 := by positivity
  have hδR : 0 ≤ δ * R ^ 2 := by positivity
  have hcard := card_lateTimes_le (n R) δ R hδR
  have hcard0 : (0 : ℝ) ≤ ((lateTimes (n R) δ R).card : ℝ) := Nat.cast_nonneg _
  have hsq : ((lateTimes (n R) δ R).card : ℝ) ^ 2 ≤ (δ * R ^ 2 + 1) ^ 2 :=
    pow_le_pow_left₀ hcard0 hcard 2
  have hbound : ((lateTimes (n R) δ R).card : ℝ) ^ 2 * S R
      ≤ (δ * R ^ 2 + 1) ^ 2 * (Cphi * (R ^ 4)⁻¹) := by
    refine le_trans (mul_le_mul_of_nonneg_left hR (by positivity)) ?_
    exact mul_le_mul_of_nonneg_right hsq (by positivity)
  refine hbound.trans (le_of_eq ?_)
  field_simp
  ring
end Sandpile
