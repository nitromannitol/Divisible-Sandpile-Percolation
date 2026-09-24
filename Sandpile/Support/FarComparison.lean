/-
Logarithmic-scale Gaussian comparison for cut-off ball Green fields on
rectangles with polynomially bounded cardinality.
-/
import Sandpile.Support.RectangleComparison

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal

namespace Sandpile

lemma inv_floor_sq_le {x : ℝ} (hx : 2 ≤ x) :
    1 / (⌊x⌋₊ : ℝ) ^ 2 ≤ 4 / x ^ 2 := by
  have hxpos : 0 < x := by linarith
  have hfloor : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one x
    linarith
  have hfloorpos : 0 < (⌊x⌋₊ : ℝ) := lt_of_lt_of_le (by positivity) hfloor
  apply (div_le_div_iff₀ (pow_pos hfloorpos 2) (pow_pos hxpos 2)).mpr
  have hs := (sq_le_sq₀ (by positivity : 0 ≤ x / 2) hfloorpos.le).mpr hfloor
  nlinarith

lemma log_card_bounds {r N m : ℕ} (hr : 2 ≤ r) (hlo : r ≤ N) (hhi : N ≤ r ^ m) :
    Real.log r ≤ Real.log N ∧ Real.log N ≤ (m : ℝ) * Real.log r := by
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  refine ⟨Real.log_le_log hrpos (by exact_mod_cast hlo), ?_⟩
  have h := Real.log_le_log hNpos (by exact_mod_cast hhi : (N : ℝ) ≤ (r : ℝ) ^ m)
  simpa only [Real.log_pow] using h

lemma far_comparison_exponent_le {D η x l m α : ℝ}
    (hD : 0 ≤ D) (hη : 0 < η) (hx : 1 < x) (hl : 0 ≤ l)
    (hm : 0 ≤ m) (hbound : l ≤ m * Real.log x) (hpow : 2 ≤ x ^ α) :
    D * l ^ 3 / ((η * Real.log x) * (⌊x ^ α⌋₊ : ℝ) ^ 2) ≤
      (4 * D * m ^ 3 / η) * ((Real.log x) ^ 2 / x ^ (2 * α)) := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hxpos : 0 < x := by linarith
  have hfloor := inv_floor_sq_le hpow
  have hl3 := pow_le_pow_left₀ hl hbound 3
  have hid : (x ^ α) ^ (2 : ℕ) = x ^ (2 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    congr 1
    norm_num
    ring
  calc
    _ = (D * l ^ 3 / (η * Real.log x)) * (1 / (⌊x ^ α⌋₊ : ℝ) ^ 2) := by ring
    _ ≤ (D * (m * Real.log x) ^ 3 / (η * Real.log x)) * (4 / (x ^ α) ^ 2) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl3 hD) (by positivity)
      · exact hfloor
      · positivity
      · positivity
    _ = _ := by rw [hid]; field_simp

lemma far_comparison_error_le {C η x l m α : ℝ}
    (hC : 0 ≤ C) (hη : 0 < η) (hx : 1 < x) (hl : 0 ≤ l)
    (_hm : 0 ≤ m) (hbound : l ≤ m * Real.log x) (hpow : 2 ≤ x ^ α) :
    C * l ^ 6 / ((η * Real.log x) ^ 3 * (⌊x ^ α⌋₊ : ℝ) ^ 2) ≤
      (4 * C * m ^ 6 / η ^ 3) * (Real.log x) ^ 3 * x ^ (-2 * α) := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hxpos : 0 < x := by linarith
  have hfloor := inv_floor_sq_le hpow
  have hl6 := pow_le_pow_left₀ hl hbound 6
  have hid : (x ^ α) ^ (2 : ℕ) = x ^ (2 * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hxpos.le]
    congr 1
    norm_num
    ring
  have hneg : x ^ (-2 * α) = (x ^ (2 * α))⁻¹ := by
    rw [show -2 * α = -(2 * α) by ring, Real.rpow_neg hxpos.le]
  calc
    _ = (C * l ^ 6 / (η * Real.log x) ^ 3) * (1 / (⌊x ^ α⌋₊ : ℝ) ^ 2) := by ring
    _ ≤ (C * (m * Real.log x) ^ 6 / (η * Real.log x) ^ 3) * (4 / (x ^ α) ^ 2) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl6 hC) (by positivity)
      · exact hfloor
      · positivity
      · positivity
    _ = _ := by rw [hid, hneg]; field_simp

lemma eventually_far_comparison_conditions {B D θ η α : ℝ} (hB : 1 ≤ B)
    (hD : 0 ≤ D) (hθ : 0 < θ) (hη : 0 < η) (hα : 0 < α) (m : ℕ) :
    ∃ r₀ : ℕ, ∀ r : ℕ, r₀ ≤ r →
      2 ≤ r ∧ 2 ≤ ⌊(r : ℝ) ^ α⌋₊ ∧
      ∀ N : ℕ, r ≤ N → N ≤ r ^ m →
        0 < η * Real.log r ∧ 1 ≤ B * (Real.log N) ^ 2 / (η * Real.log r) ∧
        D * (Real.log N) ^ 3 / ((η * Real.log r) * (⌊(r : ℝ) ^ α⌋₊ : ℝ) ^ 2) ≤ θ / 2 := by
  have hloglim : Tendsto (fun r : ℕ => Real.log (r : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpowlim : Tendsto (fun r : ℕ => (r : ℝ) ^ α) atTop atTop :=
    (tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun r : ℕ => (4 * D * (m : ℝ) ^ 3 / η) *
      ((Real.log (r : ℝ)) ^ 2 / (r : ℝ) ^ (2 * α))) atTop (𝓝 0) := by
    have hh := ((isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by positivity : 0 < 2 * α)).tendsto_div_nhds_zero).comp
      tendsto_natCast_atTop_atTop
    simpa only [Real.rpow_two, mul_zero, Function.comp_apply] using hh.const_mul (4 * D * (m : ℝ) ^ 3 / η)
  have hev : ∀ᶠ r : ℕ in atTop, 2 ≤ r ∧ η ≤ Real.log (r : ℝ) ∧
      2 ≤ (r : ℝ) ^ α ∧
      (4 * D * (m : ℝ) ^ 3 / η) * ((Real.log (r : ℝ)) ^ 2 / (r : ℝ) ^ (2 * α)) < θ / 2 := by
    filter_upwards [eventually_ge_atTop 2, hloglim.eventually (eventually_ge_atTop η),
      hpowlim.eventually (eventually_ge_atTop 2), (tendsto_order.mp hsmall).2 (θ / 2) (by positivity)]
      with r hr hl hp hs
    exact ⟨hr, hl, hp, hs⟩
  obtain ⟨r₀, hr₀⟩ := hev.exists_forall_of_atTop
  refine ⟨r₀, ?_⟩
  intro r hr
  obtain ⟨hr2, hlog, hpow, hsmallr⟩ := hr₀ r hr
  have hrR : (1 : ℝ) < r := by exact_mod_cast (by omega : 1 < r)
  have hlogpos : 0 < Real.log (r : ℝ) := Real.log_pos hrR
  refine ⟨hr2, (Nat.le_floor_iff (by positivity)).mpr (by simpa only [Nat.cast_ofNat] using hpow), ?_⟩
  intro N hlo hhi
  obtain ⟨hlo', hhi'⟩ := log_card_bounds hr2 hlo hhi
  have hlN : 0 ≤ Real.log (N : ℝ) := hlogpos.le.trans hlo'
  refine ⟨by positivity, ?_, ?_⟩
  · apply (le_div_iff₀ (by positivity : 0 < η * Real.log (r : ℝ))).mpr
    have hs := (sq_le_sq₀ hlogpos.le hlN).mpr hlo'
    have hb := mul_le_mul_of_nonneg_right hB (sq_nonneg (Real.log (N : ℝ)))
    nlinarith [mul_nonneg (sub_nonneg.mpr hlog) hlogpos.le]
  · exact (far_comparison_exponent_le hD hη hrR hlN (Nat.cast_nonneg m) hhi' hpow).trans hsmallr.le

lemma exists_gaussian_far_comparison (hBall : External.BallGreenBounds)
    (θ K α η : ℝ) (hθ : 0 < θ) (hα : 0 < α) (hη : 0 < η) (m : ℕ) (hm : 1 ≤ m) :
    ∃ C > 0, ∃ r₀ : ℕ, ∀ (μ : Measure ℝ), IsProbabilityMeasure μ →
      Integrable (fun x : ℝ => Real.exp (θ * |x|)) μ →
      (∫ x : ℝ, Real.exp (θ * |x|) ∂μ) ≤ K → (∫ x : ℝ, x ∂μ) = 0 →
      ∀ v : ℝ≥0, (∫ x : ℝ, x ^ 2 ∂μ) = v →
      ∀ r : ℕ, r₀ ≤ r → ∀ Q : Finset (Site 2), IsLatticeRectangle Q → r ≤ Q.card → Q.card ≤ r ^ m →
      ∀ φ : ℝ → ℝ, External.BallGreen.IsCutoff φ → ∀ z : Q → Site 4, ∀ level : ℝ,
        (LatticeProb.iidLaw 4 μ).real
          {ζ | crossingValue Q (fun w => finiteKernelField
            (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ φ) ζ (z w)) ≤ level} ≤
        (LatticeProb.iidLaw 4 (gaussianReal 0 v)).real
          {ζ | crossingValue Q (fun w => finiteKernelField
            (External.BallGreen.cutField r ⌊(r : ℝ) ^ α⌋₊ φ) ζ (z w)) ≤ level + 3 * η * Real.log r} +
          C * (Real.log r) ^ 3 * (r : ℝ) ^ (-2 * α) := by
  obtain ⟨B, hB, C, hC, D, hD, hcompare⟩ := exists_gaussian_far_rectangle_comparison_constants hBall θ K hθ
  obtain ⟨r₀, hr₀⟩ := eventually_far_comparison_conditions hB hD.le hθ hη hα m
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  refine ⟨4 * C * (m : ℝ) ^ 6 / η ^ 3, by positivity, r₀, ?_⟩
  intro μ hμ hexp hK hmean v hsecond r hr Q hQ hlo hhi φ hφ z level
  letI : IsProbabilityMeasure μ := hμ
  obtain ⟨hr2, hL, hcond⟩ := hr₀ r hr
  obtain ⟨herr, hβ, hκ⟩ := hcond Q.card hlo hhi
  have hcard : 2 ≤ Q.card := hr2.trans hlo
  have hh := hcompare Q hQ hcard r ⌊(r : ℝ) ^ α⌋₊ hr2 hL φ hφ z
    μ hμ hexp hK hmean v hsecond level (η * Real.log r) herr hβ hκ
  have hlevel : level + 3 * (η * Real.log r) = level + 3 * η * Real.log r := by ring
  rw [hlevel] at hh
  apply hh.trans (add_le_add le_rfl ?_)
  have hrR : (1 : ℝ) < r := by exact_mod_cast (by omega : 1 < r)
  have hpow : 2 ≤ (r : ℝ) ^ α := by
    have hh := (Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg r) α)).mp hL
    simpa only [Nat.cast_ofNat] using hh
  exact far_comparison_error_le hC.le hη hrR (Real.log_natCast_nonneg _)
    (Nat.cast_nonneg m) (log_card_bounds hr2 hlo hhi).2 hpow

end Sandpile
