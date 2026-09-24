/-
The total-variation gradient bound in the `R²/n` form Step 2 of
`prop:d4-superdiffusive-limit` uses (`sandpile.tex:3374-3380`).

Step 2 smooths the linearization error flat: `F_R = P^{n_R}E_{t_R-n_R}` is
compared with the constant `C_R` of its own parity class, and the comparison
costs the `ℓ¹` gradient of the smoothing kernel.  Squared, the gradient bound
`eq:rw-tv-gradient` reads `(∑_y|p_n(x,y)-p_n(b,y)|)² ≤ C|x-b|²/n`, and on the
box of radius `CR` that the rescaled domain meets this is the paper's `R²/n_R`.
-/
import Sandpile.Support.ContPairedGradient

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- **The gradient bound, squared.**  `(∑_y|p_n(x,y)-p_n(b,y)|)² ≤ C|x-b|²/n`
for sites of equal parity. -/
theorem exists_heatKernel_gradient_sq_four (hHK : Sandpile.External.HeatKernelBounds) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ x b : Site 4, Sandpile.External.SameParity x b →
      (∑' y : Site 4, |heatKernel 4 n x y - heatKernel 4 n b y|) ^ 2 ≤
        C * Sandpile.External.latticeDist x b ^ 2 / (n : ℝ) := by
  obtain ⟨-, ⟨C2, hC2, hgrad⟩, -⟩ := hHK 4 (by norm_num)
  refine ⟨C2 ^ 2, by positivity, fun n hn x b hpar => ?_⟩
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hdist : (0 : ℝ) ≤ Sandpile.External.latticeDist x b := Real.sqrt_nonneg _
  have hnn : (0 : ℝ) ≤ ∑' y : Site 4, |heatKernel 4 n x y - heatKernel 4 n b y| :=
    tsum_nonneg fun y => abs_nonneg _
  have hg := hgrad n hn x b hpar
  have hrpow : ((n : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 = ((n : ℝ))⁻¹ := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ (-(1 : ℝ) / 2)) 2, ← Real.rpow_mul hn0.le]
    norm_num
    rw [Real.rpow_neg_one]
  have hpow : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hn0.le _
  calc (∑' y : Site 4, |heatKernel 4 n x y - heatKernel 4 n b y|) ^ 2
      ≤ (C2 * Sandpile.External.latticeDist x b * (n : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 :=
        pow_le_pow_left₀ hnn hg 2
    _ = C2 ^ 2 * Sandpile.External.latticeDist x b ^ 2 * ((n : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 := by
        ring
    _ = C2 ^ 2 * Sandpile.External.latticeDist x b ^ 2 / (n : ℝ) := by
        rw [hrpow, div_eq_mul_inv]

/-- **Weighted Cauchy-Schwarz over a finset**, in the form Step 2 needs: for a
finite linear combination `∑_z c_z u_z`, `(∑_z c_z u_z)² ≤ (∑_z|c_z|)(∑_z|c_z|u_z²)`.
Against a family of random variables `u_z` with `E u_z² ≤ V` this is Minkowski
in `L²`: `E(∑_z c_z u_z)² ≤ (∑_z|c_z|)²V`, which is how the smoothing gradient
enters the first display of Step 2. -/
theorem sq_finset_sum_mul_le {ι : Type*} (s : Finset ι) (c u : ι → ℝ) :
    (∑ z ∈ s, c z * u z) ^ 2 ≤ (∑ z ∈ s, |c z|) * ∑ z ∈ s, |c z| * u z ^ 2 := by
  have habs : |∑ z ∈ s, c z * u z| ≤
      ∑ z ∈ s, Real.sqrt |c z| * (|u z| * Real.sqrt |c z|) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [abs_mul]
    have hsq : Real.sqrt |c z| * Real.sqrt |c z| = |c z| := Real.mul_self_sqrt (abs_nonneg _)
    calc |c z| * |u z| = (Real.sqrt |c z| * Real.sqrt |c z|) * |u z| := by rw [hsq]
      _ = Real.sqrt |c z| * (|u z| * Real.sqrt |c z|) := by ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun z => Real.sqrt |c z|)
    (fun z => |u z| * Real.sqrt |c z|)
  have h1 : ∑ z ∈ s, Real.sqrt |c z| ^ 2 = ∑ z ∈ s, |c z| :=
    Finset.sum_congr rfl fun z _ => Real.sq_sqrt (abs_nonneg _)
  have h2 : ∑ z ∈ s, (|u z| * Real.sqrt |c z|) ^ 2 = ∑ z ∈ s, |c z| * u z ^ 2 := by
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _), sq_abs]
    ring
  rw [h1, h2] at hcs
  calc (∑ z ∈ s, c z * u z) ^ 2
      = |∑ z ∈ s, c z * u z| ^ 2 := (sq_abs _).symm
    _ ≤ (∑ z ∈ s, Real.sqrt |c z| * (|u z| * Real.sqrt |c z|)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ ≤ (∑ z ∈ s, |c z|) * ∑ z ∈ s, |c z| * u z ^ 2 := hcs

end Sandpile
