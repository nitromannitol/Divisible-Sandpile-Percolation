/-
The Step-1 tail profile of `thm:dgt4-many-limits` (`sandpile.tex:5930-6055`,
`eq:dgt4-band-profile`) for the constructed one-site law.

Read on the `k`th band, the law's lower tail is the `k`th component's own
distribution function, plus the total mass of the components below it, plus the
mass the positive summand puts that far out.  The first is the profile `r^{ϑ_k}`
up to `2/m_k`; the second is `o(ω_k)` by the weight estimates; the third is
`o(ω_k)` because the positive summand has exponential moments and the band
levels grow.
-/
import Sandpile.Support.Dgt4ABandMeasure

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

namespace Sandpile.Support

variable {w0 mu : ℝ} {v : ℝ≥0} {l1 : ℝ} {a w θ : ℕ → ℝ} {m : ℕ → ℕ}

/-- **The positive summand's lower tail decays at every exponential rate.**
A Chernoff bound on the Gaussian. -/
theorem gaussian_Iic_le (hv : v ≠ 0) {lam : ℝ} (hlam : 0 < lam) (s : ℝ) :
    ∫ x in Iic (-s), gaussianPDFReal mu v x
      ≤ Real.exp (-(mu * lam) + (v : ℝ) * lam ^ 2 / 2) * Real.exp (-(lam * s)) := by
  have hmgf := mgf_gaussianReal (X := id) (μ := mu) (v := v) (p := gaussianReal mu v)
    (by simp) (-lam)
  have hint : Integrable (fun x : ℝ => Real.exp (-lam * x)) (gaussianReal mu v) :=
    integrable_exp_mul_gaussianReal (-lam)
  have hcher := measure_le_le_exp_mul_mgf (X := id) (μ := gaussianReal mu v) (-s)
    (by linarith : (-lam : ℝ) ≤ 0) hint
  rw [hmgf] at hcher
  have hset : {ω : ℝ | id ω ≤ -s} = Iic (-s) := rfl
  rw [hset] at hcher
  have happly : gaussianReal mu v (Iic (-s))
      = ENNReal.ofReal (∫ x in Iic (-s), gaussianPDFReal mu v x) :=
    gaussianReal_apply_eq_integral mu hv _
  have hnn : 0 ≤ ∫ x in Iic (-s), gaussianPDFReal mu v x :=
    setIntegral_nonneg measurableSet_Iic fun x _ => gaussianPDFReal_nonneg mu v x
  rw [measureReal_def, happly, ENNReal.toReal_ofReal hnn] at hcher
  have e1 : (- -lam) * (-s) = -(lam * s) := by ring
  have e2 : mu * (-lam) + (v : ℝ) * (-lam) ^ 2 / 2 = -(mu * lam) + (v : ℝ) * lam ^ 2 / 2 := by
    ring
  rw [e1, e2, mul_comm] at hcher
  exact hcher

/-- The lower tail of the law, as a real number. -/
theorem bandLaw_toReal_Iic (hw0 : 0 ≤ w0) (hw : ∀ k, 0 ≤ w k) (hθ : ∀ k, 0 < θ k)
    (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k) (hm : ∀ k, 0 < m k)
    (hatop : Tendsto a atTop atTop) (hsum : Summable w) (s : ℝ) :
    (bandLaw w0 mu v l1 a w θ m (Iic s)).toReal
      = w0 * (∫ x in Iic s, gaussianPDFReal mu v x)
        + ∑' k, w k * bandComponentCDF l1 (a k) (θ k) (m k) s := by
  have hcdf0 : ∀ k, 0 ≤ w k * bandComponentCDF l1 (a k) (θ k) (m k) s := fun k =>
    mul_nonneg (hw k) (bandComponentCDF_nonneg (hθ k).le s)
  have hcdfle : ∀ k, w k * bandComponentCDF l1 (a k) (θ k) (m k) s ≤ w k := fun k => by
    calc w k * bandComponentCDF l1 (a k) (θ k) (m k) s
        ≤ w k * 1 := mul_le_mul_of_nonneg_left
          (bandComponentCDF_le_one (hθ k) (hm k) s) (hw k)
      _ = w k := mul_one _
  have hcdfsum : Summable fun k => w k * bandComponentCDF l1 (a k) (θ k) (m k) s :=
    hsum.of_nonneg_of_le hcdf0 hcdfle
  have hgnn : 0 ≤ ∫ x in Iic s, gaussianPDFReal mu v x :=
    setIntegral_nonneg measurableSet_Iic fun x _ => gaussianPDFReal_nonneg mu v x
  rw [bandLaw_Iic hw0 hw (fun k => (hθ k).le) hl0 hl1 ha hm hatop s,
    ← ENNReal.ofReal_tsum_of_nonneg hcdf0 hcdfsum,
    ← ENNReal.ofReal_add (mul_nonneg hw0 hgnn) (tsum_nonneg hcdf0),
    ENNReal.toReal_ofReal (add_nonneg (mul_nonneg hw0 hgnn) (tsum_nonneg hcdf0))]


lemma summable_weight_mul_bandComponentCDF (hw : ∀ k, 0 ≤ w k) (hθ : ∀ k, 0 < θ k)
    (hm : ∀ k, 0 < m k) (hsum : Summable w) (s : ℝ) :
    Summable fun k => w k * bandComponentCDF l1 (a k) (θ k) (m k) s := by
  refine hsum.of_nonneg_of_le
    (fun k => mul_nonneg (hw k) (bandComponentCDF_nonneg (hθ k).le s)) fun k => ?_
  calc w k * bandComponentCDF l1 (a k) (θ k) (m k) s
      ≤ w k * 1 := mul_le_mul_of_nonneg_left
        (bandComponentCDF_le_one (hθ k) (hm k) s) (hw k)
    _ = w k := mul_one _

/-- **The lower tail of the law on the `k`th band.**  The components below the
band contribute nothing, the `k`th contributes its own distribution function,
and those above contribute their whole mass. -/
theorem bandLaw_toReal_Iic_band (hw0 : 0 ≤ w0) (hw : ∀ k, 0 ≤ w k) (hθ : ∀ k, 0 < θ k)
    (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k) (hm : ∀ k, 0 < m k)
    (hatop : Tendsto a atTop atTop) (hsum : Summable w)
    (hsep : ∀ i j : ℕ, i < j → a i ≤ l1 * a j)
    (k : ℕ) {t : ℝ} (htlow : l1 * a k ≤ t) (hthigh : t ≤ a k) :
    (bandLaw w0 mu v l1 a w θ m (Iic (-t))).toReal
      = w0 * (∫ x in Iic (-t), gaussianPDFReal mu v x)
        + w k * bandComponentCDF l1 (a k) (θ k) (m k) (-t)
        + ∑' j, w (k + 1 + j) := by
  have hfsum := summable_weight_mul_bandComponentCDF (l1 := l1) (a := a) (θ := θ) (m := m)
    hw hθ hm hsum (-t)
  rw [bandLaw_toReal_Iic hw0 hw hθ hl0 hl1 ha hm hatop hsum (-t)]
  have hsplit := hfsum.sum_add_tsum_nat_add k
  have hlow : ∑ i ∈ Finset.range k,
      w i * bandComponentCDF l1 (a i) (θ i) (m i) (-t) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hik : i < k := Finset.mem_range.mp hi
    have : a i ≤ t := le_trans (hsep i k hik) htlow
    rw [bandComponentCDF_eq_zero_of_le hl1 (ha i) (by linarith), mul_zero]
  have hshift := (hfsum.comp_injective (add_left_injective k)).tsum_eq_zero_add
  have hhigh : ∀ i : ℕ,
      w (i + 1 + k) * bandComponentCDF l1 (a (i + 1 + k)) (θ (i + 1 + k)) (m (i + 1 + k)) (-t)
        = w (i + 1 + k) := by
    intro i
    have hki : k < i + 1 + k := by omega
    have : t ≤ l1 * a (i + 1 + k) := le_trans hthigh (hsep k (i + 1 + k) hki)
    rw [bandComponentCDF_eq_one_of_ge (hθ _) (hm _) hl1 (ha _) (by linarith), mul_one]
  have hreindex : ∑' i : ℕ, w (i + 1 + k) = ∑' j : ℕ, w (k + 1 + j) := by
    refine tsum_congr fun i => ?_
    congr 1
    omega
  simp only [Function.comp_def] at hshift
  rw [← hsplit, hlow, zero_add, hshift, zero_add,
    show (∑' b : ℕ, w (b + 1 + k) *
        bandComponentCDF l1 (a (b + 1 + k)) (θ (b + 1 + k)) (m (b + 1 + k)) (-t))
        = ∑' i : ℕ, w (i + 1 + k) from tsum_congr hhigh, hreindex, add_assoc]


/-- **The Step-1 tail profile estimate** (`eq:dgt4-band-profile`).  On the `k`th
band the law's lower tail, divided by the band's weight, is `r^{ϑ_k}` up to the
sum of three errors: the positive summand's exponentially small tail, the
accuracy `2/m_k` of the smooth profile, and the relative mass of the bands
above. -/
theorem abs_bandLaw_profile_le (hw0 : 0 ≤ w0) (hw : ∀ k, 0 < w k)
    (hθ1 : ∀ k, 1 ≤ θ k) (hθ2 : ∀ k, θ k ≤ 2)
    (hl0 : 0 < l1) (hl1 : l1 < 1) (ha : ∀ k, 0 < a k) (hm : ∀ k, 0 < m k)
    (hatop : Tendsto a atTop atTop) (hsum : Summable w)
    (hsep : ∀ i j : ℕ, i < j → a i ≤ l1 * a j)
    (hv : v ≠ 0) {lam : ℝ} (hlam : 0 < lam)
    (k : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |(bandLaw w0 mu v l1 a w θ m (Iio (-(a k - bandWidth l1 (a k) * r)))).toReal / w k
        - r ^ θ k|
      ≤ w0 * (Real.exp (-(mu * lam) + (v : ℝ) * lam ^ 2 / 2) *
            Real.exp (-(lam * (l1 * a k)))) / w k
        + 2 / (m k : ℝ) + (∑' j, w (k + 1 + j)) / w k := by
  have hθpos : ∀ k, 0 < θ k := fun k => lt_of_lt_of_le one_pos (hθ1 k)
  have hwk : 0 < w k := hw k
  have hak : 0 < a k := ha k
  set t : ℝ := a k - bandWidth l1 (a k) * r with ht
  have hwid : bandWidth l1 (a k) = (1 - l1) * a k := rfl
  have htlow : l1 * a k ≤ t := by
    rw [ht, hwid]
    have key : a k - (1 - l1) * a k * r - l1 * a k = a k * ((1 - l1) * (1 - r)) := by ring
    have hnn : 0 ≤ a k * ((1 - l1) * (1 - r)) :=
      mul_nonneg hak.le (mul_nonneg (by linarith) (by linarith))
    linarith
  have hthigh : t ≤ a k := by
    rw [ht, hwid]
    have hnn : 0 ≤ (1 - l1) * a k * r :=
      mul_nonneg (mul_nonneg (by linarith) hak.le) hr0
    linarith
  have hsplit := bandLaw_toReal_Iic_band (w0 := w0) (mu := mu) (v := v)
    hw0 (fun k => (hw k).le) hθpos
    hl0 hl1 ha hm hatop hsum hsep k htlow hthigh
  rw [bandLaw_Iio, hsplit]
  set G : ℝ := ∫ x in Iic (-t), gaussianPDFReal mu v x with hG
  set C : ℝ := bandComponentCDF l1 (a k) (θ k) (m k) (-t) with hC
  set S : ℝ := ∑' j, w (k + 1 + j) with hS
  have hGnn : 0 ≤ G := setIntegral_nonneg measurableSet_Iic fun x _ => gaussianPDFReal_nonneg mu v x
  have hSnn : 0 ≤ S := tsum_nonneg fun j => (hw _).le
  have hform : (w0 * G + w k * C + S) / w k - r ^ θ k
      = w0 * G / w k + (C - r ^ θ k) + S / w k := by
    field_simp
    ring
  rw [hform]
  have hGbound : G ≤ Real.exp (-(mu * lam) + (v : ℝ) * lam ^ 2 / 2) *
      Real.exp (-(lam * (l1 * a k))) := by
    refine (gaussian_Iic_le hv hlam t).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
    refine Real.exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_left htlow hlam.le
    linarith
  have hCbound : |C - r ^ θ k| ≤ 2 / (m k : ℝ) :=
    abs_bandComponentCDF_sub_rpow_le (hθ1 k) (hθ2 k) (hm k) hl1 hak hr0 hr1
  have h1 : |w0 * G / w k| = w0 * G / w k := abs_of_nonneg (by positivity)
  have h2 : |S / w k| = S / w k := abs_of_nonneg (by positivity)
  have hGdiv : w0 * G / w k
      ≤ w0 * (Real.exp (-(mu * lam) + (v : ℝ) * lam ^ 2 / 2) *
        Real.exp (-(lam * (l1 * a k)))) / w k := by
    gcongr
  calc |w0 * G / w k + (C - r ^ θ k) + S / w k|
      ≤ |w0 * G / w k + (C - r ^ θ k)| + |S / w k| := abs_add_le _ _
    _ ≤ |w0 * G / w k| + |C - r ^ θ k| + |S / w k| := by
        have := abs_add_le (w0 * G / w k) (C - r ^ θ k)
        linarith
    _ ≤ w0 * (Real.exp (-(mu * lam) + (v : ℝ) * lam ^ 2 / 2) *
            Real.exp (-(lam * (l1 * a k)))) / w k
          + 2 / (m k : ℝ) + S / w k := by
        rw [h1, h2]
        linarith

end Sandpile.Support
