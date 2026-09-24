/-
The smooth band profile of Step 1 of `thm:dgt4-many-limits`
(`sandpile.tex:5930-6055`).

The paper's `k`th band variable has the tail `((1-y)/(1-ℓ₁))^{ϑ_k}` on
`[ℓ₁,1]` (`eq:dgt4-band-tail`), whose density is not smooth at the endpoints,
while the one-site law of the theorem must have a `C^∞` density.  The profile
built here is a smooth nondecreasing function that vanishes below `0`, equals
one above `1`, approximates `r ↦ r^ϑ` uniformly on `[0,1]` to within `2/m`, and
whose density is bounded by a constant that does not depend on `m` or on `ϑ`.
That accuracy is all Step 1 uses: `eq:dgt4-band-profile` only asks for the
profile up to a vanishing error, and `eq:dgt4-band-density` only asks for a
density bound.
-/
import Sandpile.Support.Dgt4ABandBump

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace Sandpile.Support

/-- The mass the profile puts on the `i`th of `m` equal subintervals of `[0,1]`. -/
def bandCoeff (θ : ℝ) (m i : ℕ) : ℝ :=
  (((i : ℝ) + 1) / (m : ℝ)) ^ θ - ((i : ℝ) / (m : ℝ)) ^ θ

lemma bandCoeff_nonneg {θ : ℝ} (hθ : 0 ≤ θ) (m i : ℕ) : 0 ≤ bandCoeff θ m i := by
  have h : ((i : ℝ) / (m : ℝ)) ≤ (((i : ℝ) + 1) / (m : ℝ)) := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · simp [hm]
    · have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      gcongr
      linarith
  exact sub_nonneg.mpr (Real.rpow_le_rpow (by positivity) h hθ)

/-- The profile's value at the left endpoint of the `j`th subinterval. -/
lemma sum_bandCoeff_range {θ : ℝ} (hθ : 0 < θ) (m j : ℕ) :
    ∑ i ∈ Finset.range j, bandCoeff θ m i = ((j : ℝ) / (m : ℝ)) ^ θ := by
  have h := Finset.sum_range_sub (f := fun i : ℕ => ((i : ℝ) / (m : ℝ)) ^ θ) j
  simp only [bandCoeff]
  rw [show (∑ i ∈ Finset.range j, ((((i : ℝ) + 1) / (m : ℝ)) ^ θ - ((i : ℝ) / (m : ℝ)) ^ θ))
      = ∑ i ∈ Finset.range j,
        (((((i + 1 : ℕ) : ℝ)) / (m : ℝ)) ^ θ - (((i : ℕ) : ℝ) / (m : ℝ)) ^ θ) from by
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring_nf]
  rw [h]
  simp [Real.zero_rpow hθ.ne']

lemma sum_bandCoeff {θ : ℝ} (hθ : 0 < θ) {m : ℕ} (hm : 0 < m) :
    ∑ i ∈ Finset.range m, bandCoeff θ m i = 1 := by
  rw [sum_bandCoeff_range hθ m m]
  have : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  rw [div_self this, Real.one_rpow]

/-- The elementary step behind the profile bound: `(u-1)^2 ≥ 0`. -/
lemma one_sub_le_two_mul_of_mul_self_le {u X : ℝ} (h : u * u ≤ X) :
    1 - X ≤ 2 * (1 - u) := by
  nlinarith [h, sq_nonneg (u - 1)]

/-- `1 - u ^ ϑ ≤ 2 (1 - u)` on `(0,1]` for `ϑ ≤ 2`. -/
lemma one_sub_rpow_le_two_mul {u θ : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) (hθ2 : θ ≤ 2) :
    1 - u ^ θ ≤ 2 * (1 - u) := by
  have husq : u ^ (2 : ℝ) ≤ u ^ θ := Real.rpow_le_rpow_of_exponent_ge hu0 hu1 hθ2
  have hu2 : u ^ (2 : ℝ) = u * u := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  exact one_sub_le_two_mul_of_mul_self_le (by rw [← hu2]; exact husq)

/-- On `[0,1]` the power `r ↦ r^ϑ` is Lipschitz with constant `2` whenever
`1 ≤ ϑ ≤ 2`.  This is the only place the restriction on `ϑ` is used. -/
lemma rpow_sub_rpow_le_two_mul {a b θ : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1)
    (hθ1 : 1 ≤ θ) (hθ2 : θ ≤ 2) : b ^ θ - a ^ θ ≤ 2 * (b - a) := by
  have hθ0 : θ ≠ 0 := by linarith
  rcases eq_or_lt_of_le (ha.trans hab) with hb0 | hb0
  · have hae : a = 0 := le_antisymm (hab.trans hb0.symm.le) ha
    have hbe : b = 0 := hb0.symm
    rw [hae, hbe, Real.zero_rpow hθ0]
    norm_num
  · have hbθ : b ^ θ ≤ b := by
      simpa using Real.rpow_le_rpow_of_exponent_ge hb0 hb hθ1
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · rw [← ha0, Real.zero_rpow hθ0, sub_zero]
      have : b - a = b := by rw [← ha0]; ring
      linarith [this ▸ hbθ]
    · have hu0 : 0 < a / b := div_pos ha0 hb0
      have hu1 : a / b ≤ 1 := (div_le_one hb0).mpr hab
      have hkey : 1 - (a / b) ^ θ ≤ 2 * (1 - a / b) := one_sub_rpow_le_two_mul hu0 hu1 hθ2
      have hbu : a = (a / b) * b := by field_simp
      have hexp : a ^ θ = (a / b) ^ θ * b ^ θ := by
        rw [hbu, Real.mul_rpow hu0.le hb0.le]
        congr 1
        rw [← hbu]
      have hsplit : b ^ θ - a ^ θ = b ^ θ * (1 - (a / b) ^ θ) := by rw [hexp]; ring
      have hbn : (0 : ℝ) < b ^ θ := Real.rpow_pos_of_pos hb0 θ
      rw [hsplit]
      calc b ^ θ * (1 - (a / b) ^ θ) ≤ b ^ θ * (2 * (1 - a / b)) :=
            mul_le_mul_of_nonneg_left hkey hbn.le
        _ ≤ b * (2 * (1 - a / b)) := by
            refine mul_le_mul_of_nonneg_right hbθ ?_
            linarith
        _ = 2 * (b - a) := by field_simp

/-- Each of the `m` subintervals carries mass at most `2/m`. -/
lemma bandCoeff_le {θ : ℝ} (hθ1 : 1 ≤ θ) (hθ2 : θ ≤ 2) {m i : ℕ} (hm : 0 < m)
    (hi : i + 1 ≤ m) : bandCoeff θ m i ≤ 2 / (m : ℝ) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have ha0 : (0 : ℝ) ≤ (i : ℝ) / (m : ℝ) := by positivity
  have hab : (i : ℝ) / (m : ℝ) ≤ ((i : ℝ) + 1) / (m : ℝ) := by gcongr; linarith
  have hb1 : ((i : ℝ) + 1) / (m : ℝ) ≤ 1 := by
    rw [div_le_one hmR]
    exact_mod_cast hi
  have hdiff : ((i : ℝ) + 1) / (m : ℝ) - (i : ℝ) / (m : ℝ) = 1 / (m : ℝ) := by
    rw [div_sub_div_same]
    norm_num
  have := rpow_sub_rpow_le_two_mul ha0 hab hb1 hθ1 hθ2
  rw [hdiff] at this
  calc bandCoeff θ m i ≤ 2 * (1 / (m : ℝ)) := this
    _ = 2 / (m : ℝ) := by ring

/-- The smoothed profile with `m` steps. -/
def bandShape (θ : ℝ) (m : ℕ) (r : ℝ) : ℝ :=
  ∑ i ∈ Finset.range m, bandCoeff θ m i * bandStep (r * (m : ℝ) - (i : ℝ))

/-- Its density. -/
def bandShapeDensity (θ : ℝ) (m : ℕ) (r : ℝ) : ℝ :=
  ∑ i ∈ Finset.range m, bandCoeff θ m i * (m : ℝ) * bandBump (r * (m : ℝ) - (i : ℝ))

lemma contDiff_bandShape (θ : ℝ) (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (bandShape θ m) := by
  refine ContDiff.sum (fun i _ => ?_)
  exact contDiff_const.mul
    (contDiff_bandStep.comp ((contDiff_id.mul contDiff_const).sub contDiff_const))

lemma contDiff_bandShapeDensity (θ : ℝ) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (bandShapeDensity θ m) := by
  refine ContDiff.sum (fun i _ => ?_)
  exact contDiff_const.mul
    (contDiff_bandBump.comp ((contDiff_id.mul contDiff_const).sub contDiff_const))

lemma hasDerivAt_bandShape (θ : ℝ) (m : ℕ) (r : ℝ) :
    HasDerivAt (bandShape θ m) (bandShapeDensity θ m r) r := by
  have h : ∀ i ∈ Finset.range m,
      HasDerivAt (fun x : ℝ => bandCoeff θ m i * bandStep (x * (m : ℝ) - (i : ℝ)))
        (bandCoeff θ m i * (m : ℝ) * bandBump (r * (m : ℝ) - (i : ℝ))) r := by
    intro i _
    have hin : HasDerivAt (fun x : ℝ => x * (m : ℝ) - (i : ℝ)) ((m : ℝ)) r := by
      simpa using ((hasDerivAt_id r).mul_const (m : ℝ)).sub_const ((i : ℝ))
    have h0 := (hasDerivAt_bandStep (r * (m : ℝ) - (i : ℝ))).comp r hin
    rw [Function.comp_def] at h0
    have h2 : HasDerivAt (fun x : ℝ => bandCoeff θ m i * bandStep (x * (m : ℝ) - (i : ℝ)))
        (bandCoeff θ m i * (bandBump (r * (m : ℝ) - (i : ℝ)) * (m : ℝ))) r := h0.const_mul _
    have heq : bandCoeff θ m i * (bandBump (r * (m : ℝ) - (i : ℝ)) * (m : ℝ))
        = bandCoeff θ m i * (m : ℝ) * bandBump (r * (m : ℝ) - (i : ℝ)) := by ring
    rw [heq] at h2
    exact h2
  have heq : bandShape θ m
      = ∑ i ∈ Finset.range m, fun x : ℝ => bandCoeff θ m i * bandStep (x * (m : ℝ) - (i : ℝ)) := by
    funext x
    simp only [bandShape, Finset.sum_apply]
  rw [heq, bandShapeDensity]
  exact HasDerivAt.sum h

lemma bandShape_eq_zero_of_nonpos {θ : ℝ} {m : ℕ} {r : ℝ} (hr : r ≤ 0) :
    bandShape θ m r = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have : r * (m : ℝ) - (i : ℝ) ≤ 0 := by
    have : r * (m : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hr hm
    have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  rw [bandStep_eq_zero_of_nonpos this, mul_zero]

lemma bandShapeDensity_eq_zero_of_nonpos {θ : ℝ} {m : ℕ} {r : ℝ} (hr : r ≤ 0) :
    bandShapeDensity θ m r = 0 := by
  refine Finset.sum_eq_zero fun i _ => ?_
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have : r * (m : ℝ) - (i : ℝ) ≤ 0 := by
    have : r * (m : ℝ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hr hm
    have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
    linarith
  rw [bandBump_eq_zero_of_nonpos this, mul_zero]

lemma bandShape_eq_one_of_one_le {θ : ℝ} (hθ : 0 < θ) {m : ℕ} (hm : 0 < m) {r : ℝ}
    (hr : 1 ≤ r) : bandShape θ m r = 1 := by
  have : ∀ i ∈ Finset.range m,
      bandCoeff θ m i * bandStep (r * (m : ℝ) - (i : ℝ)) = bandCoeff θ m i := by
    intro i hi
    have him : i + 1 ≤ m := Finset.mem_range.mp hi
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h1 : ((i : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast him
    have : (1 : ℝ) ≤ r * (m : ℝ) - (i : ℝ) := by
      have : (m : ℝ) ≤ r * (m : ℝ) := le_mul_of_one_le_left (by linarith) hr
      linarith
    rw [bandStep_eq_one_of_one_le this, mul_one]
  simp only [bandShape]
  rw [Finset.sum_congr rfl this, sum_bandCoeff hθ hm]

lemma bandShapeDensity_eq_zero_of_one_le {θ : ℝ} {m : ℕ} {r : ℝ} (hm : 0 < m) (hr : 1 ≤ r) :
    bandShapeDensity θ m r = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  have him : i + 1 ≤ m := Finset.mem_range.mp hi
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h1 : ((i : ℝ) + 1) ≤ (m : ℝ) := by exact_mod_cast him
  have : (1 : ℝ) ≤ r * (m : ℝ) - (i : ℝ) := by
    have : (m : ℝ) ≤ r * (m : ℝ) := le_mul_of_one_le_left (by linarith) hr
    linarith
  rw [bandBump_eq_zero_of_one_le this, mul_zero]

lemma bandShapeDensity_nonneg {θ : ℝ} (hθ : 0 ≤ θ) (m : ℕ) (r : ℝ) :
    0 ≤ bandShapeDensity θ m r :=
  Finset.sum_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (bandCoeff_nonneg hθ m i) (Nat.cast_nonneg m)) (bandBump_nonneg _)

lemma bandShape_monotone {θ : ℝ} (hθ : 0 ≤ θ) (m : ℕ) : Monotone (bandShape θ m) := by
  intro a b hab
  refine Finset.sum_le_sum fun i _ => ?_
  refine mul_le_mul_of_nonneg_left (bandStep_monotone ?_) (bandCoeff_nonneg hθ m i)
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have := mul_le_mul_of_nonneg_right hab hm
  linarith



lemma bandShape_nonneg {θ : ℝ} (hθ : 0 ≤ θ) (m : ℕ) (r : ℝ) : 0 ≤ bandShape θ m r :=
  Finset.sum_nonneg fun i _ => mul_nonneg (bandCoeff_nonneg hθ m i) (bandStep_nonneg _)

lemma bandShape_le_one {θ : ℝ} (hθ : 0 < θ) {m : ℕ} (hm : 0 < m) (r : ℝ) :
    bandShape θ m r ≤ 1 := by
  rw [← sum_bandCoeff hθ hm]
  refine Finset.sum_le_sum fun i _ => ?_
  calc bandCoeff θ m i * bandStep (r * (m : ℝ) - (i : ℝ))
      ≤ bandCoeff θ m i * 1 :=
        mul_le_mul_of_nonneg_left (bandStep_le_one _) (bandCoeff_nonneg hθ.le m i)
    _ = bandCoeff θ m i := mul_one _

section Localization

variable {θ : ℝ} {m : ℕ} {r : ℝ}

/-- Only the subinterval containing `r` contributes to the density. -/
lemma bandShapeDensity_eq_single (hm : 0 < m) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    bandShapeDensity θ m r
      = bandCoeff θ m ⌊r * (m : ℝ)⌋₊ * (m : ℝ) *
          bandBump (r * (m : ℝ) - (⌊r * (m : ℝ)⌋₊ : ℝ)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hrm0 : (0 : ℝ) ≤ r * (m : ℝ) := by positivity
  have hfl : (⌊r * (m : ℝ)⌋₊ : ℝ) ≤ r * (m : ℝ) := Nat.floor_le hrm0
  have hfl' : r * (m : ℝ) < (⌊r * (m : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlt : ⌊r * (m : ℝ)⌋₊ < m := by
    rw [Nat.floor_lt hrm0]
    calc r * (m : ℝ) < 1 * (m : ℝ) := by
          exact mul_lt_mul_of_pos_right hr1 hmR
      _ = (m : ℝ) := one_mul _
  refine Finset.sum_eq_single_of_mem _ (Finset.mem_range.mpr hlt) fun i hi hne => ?_
  rcases lt_or_gt_of_ne hne with h | h
  · have hle : (i : ℝ) + 1 ≤ (⌊r * (m : ℝ)⌋₊ : ℝ) := by exact_mod_cast h
    have : (1 : ℝ) ≤ r * (m : ℝ) - (i : ℝ) := by linarith
    rw [bandBump_eq_zero_of_one_le this, mul_zero]
  · have hge : (⌊r * (m : ℝ)⌋₊ : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast h
    have : r * (m : ℝ) - (i : ℝ) ≤ 0 := by linarith
    rw [bandBump_eq_zero_of_nonpos this, mul_zero]

/-- The profile is the total mass to the left of the subinterval containing `r`
plus a fraction of that subinterval's own mass. -/
lemma bandShape_eq_partial (hθ : 0 < θ) (hm : 0 < m) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    bandShape θ m r
      = ((⌊r * (m : ℝ)⌋₊ : ℝ) / (m : ℝ)) ^ θ
        + bandCoeff θ m ⌊r * (m : ℝ)⌋₊ *
            bandStep (r * (m : ℝ) - (⌊r * (m : ℝ)⌋₊ : ℝ)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hrm0 : (0 : ℝ) ≤ r * (m : ℝ) := by positivity
  have hfl : (⌊r * (m : ℝ)⌋₊ : ℝ) ≤ r * (m : ℝ) := Nat.floor_le hrm0
  have hfl' : r * (m : ℝ) < (⌊r * (m : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlt : ⌊r * (m : ℝ)⌋₊ < m := by
    rw [Nat.floor_lt hrm0]
    calc r * (m : ℝ) < 1 * (m : ℝ) := mul_lt_mul_of_pos_right hr1 hmR
      _ = (m : ℝ) := one_mul _
  set j : ℕ := ⌊r * (m : ℝ)⌋₊ with hj
  set F : ℕ → ℝ := fun i => bandCoeff θ m i * bandStep (r * (m : ℝ) - (i : ℝ)) with hF
  have hsplit : ∑ i ∈ Finset.range m, F i
      = (∑ i ∈ Finset.range (j + 1), F i) + ∑ i ∈ Finset.Ico (j + 1) m, F i := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive F (Nat.zero_le (j + 1)) hlt]
  have htail : ∑ i ∈ Finset.Ico (j + 1) m, F i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hge : (j : ℝ) + 1 ≤ (i : ℝ) := by
      exact_mod_cast (Finset.mem_Ico.mp hi).1
    have : r * (m : ℝ) - (i : ℝ) ≤ 0 := by linarith
    show bandCoeff θ m i * bandStep (r * (m : ℝ) - (i : ℝ)) = 0
    rw [bandStep_eq_zero_of_nonpos this, mul_zero]
  have hhead : ∑ i ∈ Finset.range j, F i = ((j : ℝ) / (m : ℝ)) ^ θ := by
    rw [← sum_bandCoeff_range hθ m j]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hle : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Finset.mem_range.mp hi
    have : (1 : ℝ) ≤ r * (m : ℝ) - (i : ℝ) := by linarith
    show bandCoeff θ m i * bandStep (r * (m : ℝ) - (i : ℝ)) = bandCoeff θ m i
    rw [bandStep_eq_one_of_one_le this, mul_one]
  calc bandShape θ m r = ∑ i ∈ Finset.range m, F i := rfl
    _ = (∑ i ∈ Finset.range (j + 1), F i) + ∑ i ∈ Finset.Ico (j + 1) m, F i := hsplit
    _ = ∑ i ∈ Finset.range (j + 1), F i := by rw [htail, add_zero]
    _ = (∑ i ∈ Finset.range j, F i) + F j := Finset.sum_range_succ F j
    _ = ((j : ℝ) / (m : ℝ)) ^ θ + F j := by rw [hhead]

end Localization

/-- **The profile approximates `r ↦ r^ϑ` to within `2/m`.**  This is the smooth
replacement for the exact band tail `eq:dgt4-band-tail` of the paper. -/
theorem abs_bandShape_sub_rpow_le {θ : ℝ} (hθ1 : 1 ≤ θ) (hθ2 : θ ≤ 2) {m : ℕ} (hm : 0 < m)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |bandShape θ m r - r ^ θ| ≤ 2 / (m : ℝ) := by
  have hθ : 0 < θ := lt_of_lt_of_le one_pos hθ1
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rcases eq_or_lt_of_le hr1 with hone | hlt
  · subst hone
    rw [bandShape_eq_one_of_one_le hθ hm le_rfl, Real.one_rpow, sub_self, abs_zero]
    positivity
  · have hrm0 : (0 : ℝ) ≤ r * (m : ℝ) := by positivity
    have hfl : (⌊r * (m : ℝ)⌋₊ : ℝ) ≤ r * (m : ℝ) := Nat.floor_le hrm0
    have hfl' : r * (m : ℝ) < (⌊r * (m : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have hlt' : ⌊r * (m : ℝ)⌋₊ < m := by
      rw [Nat.floor_lt hrm0]
      calc r * (m : ℝ) < 1 * (m : ℝ) := mul_lt_mul_of_pos_right hlt hmR
        _ = (m : ℝ) := one_mul _
    set j : ℕ := ⌊r * (m : ℝ)⌋₊ with hj
    have hlow : (j : ℝ) / (m : ℝ) ≤ r := by
      rw [div_le_iff₀ hmR]; exact hfl
    have hhigh : r ≤ ((j : ℝ) + 1) / (m : ℝ) := by
      rw [le_div_iff₀ hmR]; linarith
    have hj0 : (0 : ℝ) ≤ (j : ℝ) / (m : ℝ) := by positivity
    have hpow_low : ((j : ℝ) / (m : ℝ)) ^ θ ≤ r ^ θ := Real.rpow_le_rpow hj0 hlow hθ.le
    have hpow_high : r ^ θ ≤ (((j : ℝ) + 1) / (m : ℝ)) ^ θ := Real.rpow_le_rpow hr0 hhigh hθ.le
    have hshape := bandShape_eq_partial hθ hm hr0 hlt
    have hstep0 : 0 ≤ bandStep (r * (m : ℝ) - (j : ℝ)) := bandStep_nonneg _
    have hstep1 : bandStep (r * (m : ℝ) - (j : ℝ)) ≤ 1 := bandStep_le_one _
    have hc0 : 0 ≤ bandCoeff θ m j := bandCoeff_nonneg hθ.le m j
    have hcle : bandCoeff θ m j ≤ 2 / (m : ℝ) := bandCoeff_le hθ1 hθ2 hm hlt'
    have hlow' : ((j : ℝ) / (m : ℝ)) ^ θ ≤ bandShape θ m r := by
      rw [hshape]
      nlinarith [hc0, hstep0]
    have hhigh' : bandShape θ m r ≤ (((j : ℝ) + 1) / (m : ℝ)) ^ θ := by
      rw [hshape]
      have : bandCoeff θ m j * bandStep (r * (m : ℝ) - (j : ℝ)) ≤ bandCoeff θ m j := by
        nlinarith [hc0, hstep1]
      have hsum : ((j : ℝ) / (m : ℝ)) ^ θ + bandCoeff θ m j = (((j : ℝ) + 1) / (m : ℝ)) ^ θ := by
        rw [bandCoeff]; ring
      linarith
    have hcoeff : (((j : ℝ) + 1) / (m : ℝ)) ^ θ - ((j : ℝ) / (m : ℝ)) ^ θ = bandCoeff θ m j := rfl
    rw [abs_le]
    constructor <;> linarith

/-- The density is bounded by a constant that depends neither on `m` nor on `ϑ`. -/
theorem bandShapeDensity_le {θ : ℝ} (hθ1 : 1 ≤ θ) (hθ2 : θ ≤ 2) {m : ℕ} (hm : 0 < m)
    {M : ℝ} (hM : ∀ x : ℝ, |bandBump x| ≤ M) (r : ℝ) :
    bandShapeDensity θ m r ≤ 2 * M := by
  have hθ : 0 < θ := lt_of_lt_of_le one_pos hθ1
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  rcases le_or_gt r 0 with hr | hr
  · rw [bandShapeDensity_eq_zero_of_nonpos hr]; positivity
  rcases le_or_gt 1 r with hr1 | hr1
  · rw [bandShapeDensity_eq_zero_of_one_le hm hr1]; positivity
  · rw [bandShapeDensity_eq_single hm hr.le hr1]
    have hrm0 : (0 : ℝ) ≤ r * (m : ℝ) := by positivity
    have hlt' : ⌊r * (m : ℝ)⌋₊ < m := by
      rw [Nat.floor_lt hrm0]
      calc r * (m : ℝ) < 1 * (m : ℝ) := mul_lt_mul_of_pos_right hr1 hmR
        _ = (m : ℝ) := one_mul _
    have hc0 : 0 ≤ bandCoeff θ m ⌊r * (m : ℝ)⌋₊ := bandCoeff_nonneg hθ.le m _
    have hcle : bandCoeff θ m ⌊r * (m : ℝ)⌋₊ ≤ 2 / (m : ℝ) := bandCoeff_le hθ1 hθ2 hm hlt'
    have hb : bandBump (r * (m : ℝ) - (⌊r * (m : ℝ)⌋₊ : ℝ)) ≤ M :=
      le_trans (le_abs_self _) (hM _)
    have hb0 : 0 ≤ bandBump (r * (m : ℝ) - (⌊r * (m : ℝ)⌋₊ : ℝ)) := bandBump_nonneg _
    calc bandCoeff θ m ⌊r * (m : ℝ)⌋₊ * (m : ℝ) *
            bandBump (r * (m : ℝ) - (⌊r * (m : ℝ)⌋₊ : ℝ))
        ≤ (2 / (m : ℝ)) * (m : ℝ) * M := by
          apply mul_le_mul _ hb hb0 (by positivity)
          exact mul_le_mul_of_nonneg_right hcle hmR.le
      _ = 2 * M := by field_simp

/-- The density integrates to one. -/
theorem integral_bandShapeDensity {θ : ℝ} (hθ : 0 < θ) {m : ℕ} (hm : 0 < m) :
    ∫ r in (0 : ℝ)..1, bandShapeDensity θ m r = 1 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := bandShape θ m) (f' := bandShapeDensity θ m) (a := 0) (b := 1)
    (fun x _ => hasDerivAt_bandShape θ m x)
    ((contDiff_bandShapeDensity θ m).continuous.intervalIntegrable 0 1)
  rw [h, bandShape_eq_one_of_one_le hθ hm le_rfl, bandShape_eq_zero_of_nonpos le_rfl, sub_zero]

end Sandpile.Support
