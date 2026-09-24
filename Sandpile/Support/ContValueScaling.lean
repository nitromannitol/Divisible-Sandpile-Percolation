/-
The parabolic scaling of the Brownian optimal-stopping value, and the field
congruence behind it.

`sandpile.tex:1991-1993` reads "Rescaling time by $T$ identifies Brownian stopping
times bounded by $T$ with Brownian stopping times bounded by $1$, and the stopping
value scales by the same factor."  That sentence is an exact algebraic identity, and
it needs nothing of the field: for every field `h`, every `β`, every `T > 0` and
every `x`,

  `𝒰_h(T,x) = T^β 𝒰_{h'}(1,0)` for the rescaled motion,

where `h'(s,z) = T^{-β} h(Ts, x + √T z)`.  The two sets of attainable values are
carried onto one another by multiplication by `T^β`, because `τ ↦ τ/T` is a bijection
between the two families of stopping times and the integrands correspond exactly.

Two fields that agree on the range of arguments a stopping problem can reach have the
same optimal-stopping value.

The stopping value `𝒟_h(t,x)` of `ssec:brownian-stopping` reads `h` only at times
`t - τ` with `0 ≤ τ ≤ t`, so it depends on `h` only through its restriction to
`[0,t] × ℝ^d`.  This is the elementary step that lets the scaling of
`prop:continuum-value-selfsimilar` replace one field by another.
-/
import Sandpile.Support.ContBrownianScale
import Sandpile.Support.ContNoiseScaling

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Pointwise

namespace Sandpile.Support

open Sandpile.Continuum

/-- The motion rescaled about `x` at the parabolic scale `T`. -/
noncomputable def scaledMotion {ΩB : Type*} (d : ℕ) (T : ℝ≥0) (x : Space d)
    (B : ℝ≥0 → ΩB → Space d) : ℝ≥0 → ΩB → Space d :=
  fun s ω => (Real.sqrt (T : ℝ))⁻¹ • (B (T * s) ω - x)

/-- The field rescaled about `(T,x)` with exponent `β`. -/
noncomputable def scaledField (d : ℕ) (T : ℝ≥0) (β : ℝ) (x : Space d)
    (h : ℝ → Space d → ℝ) : ℝ → Space d → ℝ :=
  fun s z => (T : ℝ) ^ (-β) * h ((T : ℝ) * s) (x + Real.sqrt (T : ℝ) • z)

/-- The optimal-stopping value depends on the field only through its restriction to
`[0,t] × ℝ^d`. -/
theorem brownianDiscount_congr {ΩB : Type*} [MeasurableSpace ΩB] (d : ℕ)
    (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB) (h h' : ℝ → Space d → ℝ) (t : ℝ)
    (hEq : ∀ r : ℝ, 0 ≤ r → r ≤ t → ∀ z : Space d, h r z = h' r z) :
    brownianDiscount B P h t = brownianDiscount B P h' t := by
  have hint : ∀ τ : ΩB → ℝ≥0, (∀ ω, (τ ω : ℝ) ≤ t) →
      (∫ ω, -h (t - τ ω) (B (τ ω) ω) ∂P) = ∫ ω, -h' (t - τ ω) (B (τ ω) ω) ∂P := by
    intro τ hle
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only
    have h0 : (0:ℝ) ≤ t - (τ ω : ℝ) := by
      have := hle ω
      linarith
    have h1 : t - (τ ω : ℝ) ≤ t := by
      have hn : (0:ℝ) ≤ (τ ω : ℝ) := (τ ω).coe_nonneg
      linarith
    rw [hEq _ h0 h1]
  unfold brownianDiscount
  congr 1
  ext a
  constructor
  · rintro ⟨τ, hstop, hle, rfl⟩
    exact ⟨τ, hstop, hle, hint τ hle⟩
  · rintro ⟨τ, hstop, hle, rfl⟩
    exact ⟨τ, hstop, hle, (hint τ hle).symm⟩

/-- **The two sets of attainable values correspond under multiplication by `T^β`.**
This is the whole content of "rescaling time by `T` identifies Brownian stopping
times bounded by `T` with Brownian stopping times bounded by `1`, and the stopping
value scales by the same factor". -/
theorem attainable_scaled {ΩB : Type*} [MeasurableSpace ΩB] (d : ℕ) {T : ℝ≥0}
    (hT : T ≠ 0) (x : Space d) (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (β : ℝ) (h : ℝ → Space d → ℝ) :
    {a : ℝ | ∃ τ : ΩB → ℝ≥0, IsBrownianStopping B τ ∧ (∀ ω, (τ ω : ℝ) ≤ (T : ℝ)) ∧
        a = ∫ ω, -h ((T : ℝ) - τ ω) (B (τ ω) ω) ∂P}
      = ((T : ℝ) ^ β) • {a : ℝ | ∃ σ : ΩB → ℝ≥0,
          IsBrownianStopping (scaledMotion d T x B) σ ∧ (∀ ω, (σ ω : ℝ) ≤ 1) ∧
          a = ∫ ω, -(scaledField d T β x h) (1 - σ ω)
                (scaledMotion d T x B (σ ω) ω) ∂P} := by
  have hTpos : (0:ℝ) < (T : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hT)
  have hsq : Real.sqrt (T : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hTpos)
  have hinv : (Real.sqrt (T : ℝ))⁻¹ ≠ 0 := inv_ne_zero hsq
  have hpow : (T : ℝ) ^ β * (T : ℝ) ^ (-β) = 1 := by
    rw [← Real.rpow_add hTpos]
    simp
  have key : ∀ σ : ΩB → ℝ≥0,
      (∫ ω, -(scaledField d T β x h) (1 - σ ω) (scaledMotion d T x B (σ ω) ω) ∂P)
        = (T : ℝ) ^ (-β) * ∫ ω, -h ((T : ℝ) - ((T * σ ω : ℝ≥0) : ℝ)) (B (T * σ ω) ω) ∂P := by
    intro σ
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have harg : (T : ℝ) * (1 - (σ ω : ℝ)) = (T : ℝ) - ((T * σ ω : ℝ≥0) : ℝ) := by
      push_cast
      ring
    show -((T : ℝ) ^ (-β) * h ((T : ℝ) * (1 - (σ ω : ℝ)))
        (x + Real.sqrt (T : ℝ) • ((Real.sqrt (T : ℝ))⁻¹ • (B (T * σ ω) ω - x))))
      = (T : ℝ) ^ (-β) * -h ((T : ℝ) - ((T * σ ω : ℝ≥0) : ℝ)) (B (T * σ ω) ω)
    rw [scaled_point_eq d hT x B (σ ω) ω, harg]
    ring
  ext a
  constructor
  · rintro ⟨τ, hstop, hle, rfl⟩
    refine Set.mem_smul_set.2 ⟨(T : ℝ) ^ (-β) *
      ∫ ω, -h ((T : ℝ) - τ ω) (B (τ ω) ω) ∂P, ⟨fun ω => τ ω / T, ?_, ?_, ?_⟩, ?_⟩
    · exact isBrownianStopping_scaled d hT hinv x B τ hstop
    · intro ω
      have h1 : τ ω / T ≤ 1 := by
        rw [div_le_one (pos_iff_ne_zero.mpr hT)]
        exact_mod_cast hle ω
      exact_mod_cast h1
    · rw [key (fun ω => τ ω / T)]
      congr 2
      funext ω
      rw [mul_div_cancel₀ _ hT]
    · rw [smul_eq_mul, ← mul_assoc, hpow, one_mul]
  · rintro hmem
    obtain ⟨b, ⟨σ, hstop, hle, rfl⟩, rfl⟩ := Set.mem_smul_set.1 hmem
    refine ⟨fun ω => T * σ ω, isBrownianStopping_unscaled d x B σ hstop, ?_, ?_⟩
    · intro ω
      have hb : (T : ℝ) * (σ ω : ℝ) ≤ (T : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (hle ω) hTpos.le
      push_cast
      linarith
    · rw [key σ, smul_eq_mul, ← mul_assoc, hpow, one_mul]

/-- **The Brownian optimal-stopping discount scales by `T^β`.**  No regularity of the
field and no measurability is used: the two sets of attainable values correspond under
multiplication by `T^β`, and on `ℝ` the supremum of a nonnegative dilate of a set is that
dilate of its supremum, junk values included. -/
theorem brownianDiscount_scaled {ΩB : Type*} [MeasurableSpace ΩB] (d : ℕ) {T : ℝ≥0}
    (hT : T ≠ 0) (x : Space d) (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (β : ℝ) (h : ℝ → Space d → ℝ) :
    brownianDiscount B P h (T : ℝ)
      = (T : ℝ) ^ β *
        brownianDiscount (scaledMotion d T x B) P (scaledField d T β x h) 1 := by
  have hTpos : (0:ℝ) < (T : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hT)
  show sSup _ = _
  rw [attainable_scaled d hT x B P β h,
    Real.sSup_smul_of_nonneg (Real.rpow_nonneg hTpos.le β), smul_eq_mul]
  rfl

/-- **The Brownian optimal-stopping value scales by `T^β`**, which is the identity
`sandpile.tex:1991-1993` asserts.  At `β = (4-d)/4` and `h = Z` this is the scaling of
`𝒰` of `prop:continuum-value-selfsimilar`, for the rescaled field and the rescaled
motion. -/
theorem brownianValue_scaled {ΩB : Type*} [MeasurableSpace ΩB] (d : ℕ) {T : ℝ≥0}
    (hT : T ≠ 0) (x : Space d) (B : ℝ≥0 → ΩB → Space d) (P : Measure ΩB)
    (β : ℝ) (h : ℝ → Space d → ℝ) :
    brownianValue B P h (T : ℝ) x
      = (T : ℝ) ^ β *
        brownianValue (scaledMotion d T x B) P (scaledField d T β x h) 1 0 := by
  have hTpos : (0:ℝ) < (T : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hT)
  have hpow : (T : ℝ) ^ β * (T : ℝ) ^ (-β) = 1 := by
    rw [← Real.rpow_add hTpos]
    simp
  have hfield : scaledField d T β x h 1 0 = (T : ℝ) ^ (-β) * h (T : ℝ) x := by
    show (T : ℝ) ^ (-β) * h ((T : ℝ) * 1) (x + Real.sqrt (T : ℝ) • (0 : Space d))
      = (T : ℝ) ^ (-β) * h (T : ℝ) x
    rw [mul_one, smul_zero, add_zero]
  show h (T : ℝ) x + brownianDiscount B P h (T : ℝ) = _
  rw [brownianDiscount_scaled d hT x B P β h]
  show _ = (T : ℝ) ^ β * (scaledField d T β x h 1 0 + _)
  rw [hfield, mul_add, ← mul_assoc, hpow, one_mul]

/-- The continuum value of `eq:continuum-membrane-stopping-value` at `(T,x)`, written
through the rescaled motion and the rescaled field.  The left-hand side is, by
definition, `Sandpile.Continuum.continuumValue d ν2 W B PB T x ω`
for the member `B` of the Brownian family started at `x`. -/
theorem gaussianValue_scaled {ΩW ΩB : Type*} [MeasurableSpace ΩB] (d : ℕ) (ν2 : ℝ)
    (W : (Space d → ℝ) → ΩW → ℝ) (ω : ΩW)
    {T : ℝ≥0} (hT : T ≠ 0) (x : Space d) (B : ℝ≥0 → ΩB → Space d) (PB : Measure ΩB)
    (β : ℝ) :
    brownianValue B PB (fun t z => gaussianPotential d ν2 W t z ω) (T : ℝ) x
      = (T : ℝ) ^ β * brownianValue (scaledMotion d T x B) PB
          (scaledField d T β x (fun t z => gaussianPotential d ν2 W t z ω)) 1 0 :=
  brownianValue_scaled d hT x B PB β _

/-- At the exponent `β = 1 - d/4` the rescaled field is, at each point and almost
surely, the Gaussian heat potential of the rescaled white noise.  This is the point at
which the algebraic scaling above meets the probabilistic scaling of
`Sandpile.Support.gaussianPotential_scaled`. -/
theorem scaledField_gaussianPotential_ae {ΩW : Type*} [MeasurableSpace ΩW] (d : ℕ)
    (hd : 1 ≤ d) (hd3 : d ≤ 3) (ν2 : ℝ)
    (W : (Space d → ℝ) → ΩW → ℝ) (PW : Measure ΩW) [IsProbabilityMeasure PW]
    (hW : IsWhiteNoise d W PW) {T : ℝ≥0} (hT : T ≠ 0) (x : Space d)
    {s : ℝ} (hs : 0 ≤ s) (z : Space d) :
    (fun ω => scaledField d T (1 - (d : ℝ) / 4) x
        (fun t y => gaussianPotential d ν2 W t y ω) s z)
      =ᵐ[PW] fun ω =>
        gaussianPotential d ν2 (scaledNoise d (T : ℝ) x W) s z ω := by
  have hTpos : (0:ℝ) < (T : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hT)
  have hsqrt : Real.sqrt (T : ℝ) = (T : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
  have hpow : (T : ℝ) ^ (-(1 - (d : ℝ) / 4)) * (T : ℝ) ^ (1 - (d : ℝ) / 4) = 1 := by
    rw [← Real.rpow_add hTpos]
    simp
  have hae := gaussianPotential_scaled d hd hd3 ν2 W PW hW hTpos x hs z
  filter_upwards [hae] with ω hω
  show (T : ℝ) ^ (-(1 - (d : ℝ) / 4)) *
      gaussianPotential d ν2 W ((T : ℝ) * s) (x + Real.sqrt (T : ℝ) • z) ω
    = gaussianPotential d ν2 (scaledNoise d (T : ℝ) x W) s z ω
  rw [hsqrt, hω, ← mul_assoc, hpow, one_mul]

end Sandpile.Support
