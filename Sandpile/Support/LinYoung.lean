import Sandpile.Support.LinTestedGreen

/-! # A discrete Young's inequality for the coefficient replacement

`eq:dgt4-linear-coefficient-replacement` (`sandpile.tex:5831-5841`) as an
inequality about coefficient arrays.

The paper replaces the mean-gradient coefficients by the profile coefficients at
the cost of the second moment of the linear functional whose coefficient at `z`
is `∑_x a_R(x)(c_R(z-x)-b_R(z-x))`.  The bound it uses is Young's inequality: the
`ℓ²` mass of a convolution is at most the `ℓ²` mass of the weights times the
square of the `ℓ¹` mass of the difference.  This is where the paper's factor
`R^{-4}` comes from, through `eq:dgt4-tested-cell-l2`; the `ℓ¹` norm of the
weights would be too weak.
-/

open Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- Reindexing a sum of `|e|` along an injection and dropping the sites where `e`
vanishes. -/
theorem sum_abs_comp_le {ι : Type*} [DecidableEq ι] (t : Finset (Site d)) (I : Finset ι)
    (e : Site d → ℝ) (hesupp : ∀ w, w ∉ t → e w = 0)
    (g : ι → Site d) (hg : ∀ i ∈ I, ∀ j ∈ I, g i = g j → i = j) :
    ∑ i ∈ I, |e (g i)| ≤ ∑ w ∈ t, |e w| := by
  classical
  have himg : ∑ w ∈ I.image g, |e w| = ∑ i ∈ I, |e (g i)| := Finset.sum_image hg
  rw [← himg]
  have hinter : ∑ w ∈ (I.image g) ∩ t, |e w| = ∑ w ∈ I.image g, |e w| := by
    refine Finset.sum_subset Finset.inter_subset_left ?_
    intro w hw hwn
    have : w ∉ t := fun hs => hwn (Finset.mem_inter.2 ⟨hw, hs⟩)
    rw [hesupp w this, abs_zero]
  rw [← hinter]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    fun w _ _ => abs_nonneg _

/-- **Young's inequality `‖a ∗ e‖₂ ≤ ‖a‖₂‖e‖₁` for finite sums**, the estimate
behind `eq:dgt4-linear-coefficient-replacement` (`sandpile.tex:5826-5836`): the
`ℓ²` mass of the coefficient array `∑_x a_R(x)(c_R-b_R)(z-x)` is at most
`∑_x a_R(x)²` times the square of `∑_w |c_R(w)-b_R(w)|`. -/
theorem sum_sq_weighted_conv_le (s u t : Finset (Site d)) (a e : Site d → ℝ)
    (hesupp : ∀ w, w ∉ t → e w = 0) :
    ∑ v ∈ u, (∑ x ∈ s, a x * e (v - x)) ^ 2
      ≤ (∑ x ∈ s, a x ^ 2) * (∑ w ∈ t, |e w|) ^ 2 := by
  classical
  have hE0 : 0 ≤ ∑ w ∈ t, |e w| := Finset.sum_nonneg fun w _ => abs_nonneg _
  have hE1 : ∀ v : Site d, ∑ x ∈ s, |e (v - x)| ≤ ∑ w ∈ t, |e w| := fun v =>
    sum_abs_comp_le t s e hesupp (fun x => v - x)
      (fun x _ y _ h => by simpa using sub_right_injective h)
  have hE2 : ∀ x : Site d, ∑ v ∈ u, |e (v - x)| ≤ ∑ w ∈ t, |e w| := fun x =>
    sum_abs_comp_le t u e hesupp (fun v => v - x)
      (fun v _ y _ h => by simpa using sub_left_inj.mp h)
  have hcs : ∀ v : Site d, (∑ x ∈ s, a x * e (v - x)) ^ 2
      ≤ (∑ w ∈ t, |e w|) * ∑ x ∈ s, |e (v - x)| * a x ^ 2 := by
    intro v
    have h1 : |∑ x ∈ s, a x * e (v - x)| ≤ ∑ x ∈ s, |e (v - x)| * |a x| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
      exact Finset.sum_congr rfl fun x _ => by rw [abs_mul, mul_comm]
    have h2 : (∑ x ∈ s, |e (v - x)| * |a x|) ^ 2
        ≤ (∑ x ∈ s, |e (v - x)|) * ∑ x ∈ s, |e (v - x)| * a x ^ 2 :=
      Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
        (fun x _ => abs_nonneg _)
        (fun x _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
        (fun x _ => by rw [mul_pow, sq_abs, sq_abs, ← mul_assoc, abs_mul_abs_self, ← sq])
    have h3 : (∑ x ∈ s, |e (v - x)|) * ∑ x ∈ s, |e (v - x)| * a x ^ 2
        ≤ (∑ w ∈ t, |e w|) * ∑ x ∈ s, |e (v - x)| * a x ^ 2 :=
      mul_le_mul_of_nonneg_right (hE1 v)
        (Finset.sum_nonneg fun x _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    calc (∑ x ∈ s, a x * e (v - x)) ^ 2
        = |∑ x ∈ s, a x * e (v - x)| ^ 2 := (sq_abs _).symm
      _ ≤ (∑ x ∈ s, |e (v - x)| * |a x|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ ≤ _ := h2.trans h3
  calc ∑ v ∈ u, (∑ x ∈ s, a x * e (v - x)) ^ 2
      ≤ ∑ v ∈ u, (∑ w ∈ t, |e w|) * ∑ x ∈ s, |e (v - x)| * a x ^ 2 :=
        Finset.sum_le_sum fun v _ => hcs v
    _ = (∑ w ∈ t, |e w|) * ∑ x ∈ s, a x ^ 2 * ∑ v ∈ u, |e (v - x)| := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun x _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => by ring
    _ ≤ (∑ w ∈ t, |e w|) * ∑ x ∈ s, a x ^ 2 * ∑ w ∈ t, |e w| := by
        refine mul_le_mul_of_nonneg_left ?_ hE0
        exact Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (hE2 x) (sq_nonneg _)
    _ = (∑ x ∈ s, a x ^ 2) * (∑ w ∈ t, |e w|) ^ 2 := by
        rw [← Finset.sum_mul]
        ring

end Sandpile
