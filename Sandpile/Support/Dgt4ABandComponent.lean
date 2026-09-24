/-
The `k`th band component of the one-site law of Step 1 of `thm:dgt4-many-limits`
(`sandpile.tex:5930-6055`).

The paper's `k`th component is the law of `-a_k B_k` with
`P(B_k > y) = ((1-y)/(1-ℓ₁))^{ϑ_k}` on `[ℓ₁,1]` (`eq:dgt4-band-tail`), so that
it is carried by `[-a_k, -ℓ₁ a_k]` and its distribution function, read in the
variable `r = (a_k + x)/((1-ℓ₁)a_k)`, is `r^{ϑ_k}`.  Here the exact power is
replaced by the smooth profile of `Dgt4ABandShape`, which changes the
distribution function by at most `2/m` and leaves the carrier unchanged.  The
density bound `eq:dgt4-band-density` is `C/((1-ℓ₁)a_k)` with `C` independent of
`k`.
-/
import Sandpile.Support.Dgt4ABandShape

open Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace Sandpile.Support

/-- The width of the `k`th band. -/
def bandWidth (l1 a : ℝ) : ℝ := (1 - l1) * a

lemma bandWidth_pos {l1 a : ℝ} (hl1 : l1 < 1) (ha : 0 < a) : 0 < bandWidth l1 a :=
  mul_pos (by linarith) ha

/-- The density of the `k`th band component, carried by `[-a, -ℓ₁ a]`. -/
def bandComponent (l1 a θ : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  bandShapeDensity θ m ((a + x) / bandWidth l1 a) / bandWidth l1 a

/-- Its distribution function. -/
def bandComponentCDF (l1 a θ : ℝ) (m : ℕ) (s : ℝ) : ℝ :=
  bandShape θ m ((a + s) / bandWidth l1 a)

variable {l1 a θ : ℝ} {m : ℕ}

lemma contDiff_bandComponent (l1 a θ : ℝ) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (bandComponent l1 a θ m) :=
  ((contDiff_bandShapeDensity θ m).comp
    ((contDiff_const.add contDiff_id).div_const _)).div_const _

lemma contDiff_bandComponentCDF (l1 a θ : ℝ) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (bandComponentCDF l1 a θ m) :=
  (contDiff_bandShape θ m).comp ((contDiff_const.add contDiff_id).div_const _)

lemma bandComponent_nonneg (hθ : 0 ≤ θ) (hl1 : l1 < 1) (ha : 0 < a) (x : ℝ) :
    0 ≤ bandComponent l1 a θ m x :=
  div_nonneg (bandShapeDensity_nonneg hθ m _) (bandWidth_pos hl1 ha).le

lemma bandComponent_eq_zero_of_le (hl1 : l1 < 1) (ha : 0 < a) {x : ℝ} (hx : x ≤ -a) :
    bandComponent l1 a θ m x = 0 := by
  have hw : 0 < bandWidth l1 a := bandWidth_pos hl1 ha
  have : (a + x) / bandWidth l1 a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le
  rw [bandComponent, bandShapeDensity_eq_zero_of_nonpos this, zero_div]

lemma bandComponent_eq_zero_of_ge (hm : 0 < m) (hl1 : l1 < 1) (ha : 0 < a) {x : ℝ}
    (hx : -(l1 * a) ≤ x) : bandComponent l1 a θ m x = 0 := by
  have hw : 0 < bandWidth l1 a := bandWidth_pos hl1 ha
  have : (1 : ℝ) ≤ (a + x) / bandWidth l1 a := by
    rw [le_div_iff₀ hw, bandWidth]
    nlinarith
  rw [bandComponent, bandShapeDensity_eq_zero_of_one_le hm this, zero_div]

lemma bandComponentCDF_eq_zero_of_le (hl1 : l1 < 1) (ha : 0 < a) {s : ℝ} (hs : s ≤ -a) :
    bandComponentCDF l1 a θ m s = 0 := by
  have hw : 0 < bandWidth l1 a := bandWidth_pos hl1 ha
  have : (a + s) / bandWidth l1 a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hw.le
  rw [bandComponentCDF, bandShape_eq_zero_of_nonpos this]

lemma bandComponentCDF_eq_one_of_ge (hθ : 0 < θ) (hm : 0 < m) (hl1 : l1 < 1) (ha : 0 < a)
    {s : ℝ} (hs : -(l1 * a) ≤ s) : bandComponentCDF l1 a θ m s = 1 := by
  have hw : 0 < bandWidth l1 a := bandWidth_pos hl1 ha
  have : (1 : ℝ) ≤ (a + s) / bandWidth l1 a := by
    rw [le_div_iff₀ hw, bandWidth]
    nlinarith
  rw [bandComponentCDF, bandShape_eq_one_of_one_le hθ hm this]


lemma bandComponentCDF_nonneg (hθ : 0 ≤ θ) (s : ℝ) : 0 ≤ bandComponentCDF l1 a θ m s :=
  bandShape_nonneg hθ m _

lemma bandComponentCDF_le_one (hθ : 0 < θ) (hm : 0 < m) (s : ℝ) :
    bandComponentCDF l1 a θ m s ≤ 1 :=
  bandShape_le_one hθ hm _

lemma hasDerivAt_bandComponentCDF (hl1 : l1 < 1) (ha : 0 < a) (s : ℝ) :
    HasDerivAt (bandComponentCDF l1 a θ m) (bandComponent l1 a θ m s) s := by
  have hw : 0 < bandWidth l1 a := bandWidth_pos hl1 ha
  have hin : HasDerivAt (fun x : ℝ => (a + x) / bandWidth l1 a) (1 / bandWidth l1 a) s := by
    simpa using ((hasDerivAt_id s).const_add a).div_const (bandWidth l1 a)
  have h0 := (hasDerivAt_bandShape θ m ((a + s) / bandWidth l1 a)).comp s hin
  rw [Function.comp_def] at h0
  have heq : bandShapeDensity θ m ((a + s) / bandWidth l1 a) * (1 / bandWidth l1 a)
      = bandComponent l1 a θ m s := by
    rw [bandComponent]
    field_simp
  rw [heq] at h0
  exact h0

lemma bandComponentCDF_monotone (hθ : 0 ≤ θ) (hl1 : l1 < 1) (ha : 0 < a) :
    Monotone (bandComponentCDF l1 a θ m) := by
  intro x y hxy
  have hw : 0 < bandWidth l1 a := bandWidth_pos hl1 ha
  refine bandShape_monotone hθ m ?_
  gcongr

/-- The band component integrates to one over any interval carrying it. -/
theorem integral_bandComponent (hθ : 0 < θ) (hm : 0 < m) (hl1 : l1 < 1) (ha : 0 < a)
    {u v : ℝ} (hu : u ≤ -a) (hv : -(l1 * a) ≤ v) :
    ∫ x in u..v, bandComponent l1 a θ m x = 1 := by
  have hle : u ≤ v := by nlinarith
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := bandComponentCDF l1 a θ m) (f' := bandComponent l1 a θ m) (a := u) (b := v)
    (fun x _ => hasDerivAt_bandComponentCDF hl1 ha x)
    ((contDiff_bandComponent l1 a θ m).continuous.intervalIntegrable u v)
  rw [h, bandComponentCDF_eq_one_of_ge hθ hm hl1 ha hv,
    bandComponentCDF_eq_zero_of_le hl1 ha hu, sub_zero]

/-- **The tail profile of the band component** (`eq:dgt4-band-profile` for a
single component).  At the level `a - (1-ℓ₁) a r` the mass the component puts
below that level differs from `r^ϑ` by at most `2/m`. -/
theorem abs_bandComponentCDF_sub_rpow_le (hθ1 : 1 ≤ θ) (hθ2 : θ ≤ 2) (hm : 0 < m)
    (hl1 : l1 < 1) (ha : 0 < a) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |bandComponentCDF l1 a θ m (-(a - bandWidth l1 a * r)) - r ^ θ| ≤ 2 / (m : ℝ) := by
  have hw : 0 < bandWidth l1 a := bandWidth_pos hl1 ha
  have harg : (a + -(a - bandWidth l1 a * r)) / bandWidth l1 a = r := by
    field_simp
    ring
  rw [bandComponentCDF, harg]
  exact abs_bandShape_sub_rpow_le hθ1 hθ2 hm hr0 hr1

/-- **The density bound** (`eq:dgt4-band-density` for a single component). -/
theorem bandComponent_le (hθ1 : 1 ≤ θ) (hθ2 : θ ≤ 2) (hm : 0 < m) (hl1 : l1 < 1) (ha : 0 < a)
    {M : ℝ} (hM : ∀ x : ℝ, |bandBump x| ≤ M) (x : ℝ) :
    bandComponent l1 a θ m x ≤ 2 * M / bandWidth l1 a := by
  have hw : 0 < bandWidth l1 a := bandWidth_pos hl1 ha
  rw [bandComponent, div_le_div_iff_of_pos_right hw]
  exact bandShapeDensity_le hθ1 hθ2 hm hM _

end Sandpile.Support
