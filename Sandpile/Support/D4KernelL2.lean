import Sandpile.Support.D4PotentialKernel
import Sandpile.Support.Iterate

/-!
# The ℓ² size of a heat-kernel increment

Step 1 of `prop:d4-superdiffusive-limit` needs the time truncation in `V_{t_R}` to wash out, and
the quantity that measures it is the `ℓ²` norm in the second variable of
`∑_{j≥t}(p_j(x,y) - p_j(0,y))`. At a single time the two registered heat-kernel inputs
interpolate: the Gaussian upper bound `eq:rw-gaussian-upper` gives `|p_j(x,·) - p_j(w,·)| ≤
Cj^{-2}` in `ℓ^∞`, the total-variation gradient bound `eq:rw-tv-gradient` gives
`C|x-w|j^{-1/2}` in `ℓ¹`, and `‖f‖₂² ≤ ‖f‖_∞‖f‖₁` turns the pair into `C|x-w|j^{-5/2}` in `ℓ²`.
-/

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- `‖f‖₂² ≤ ‖f‖_∞ ‖f‖₁`. -/
theorem tsum_sq_le_sup_mul_tsum_abs {ι : Type*} {f : ι → ℝ} {M : ℝ}
    (hM : ∀ y, |f y| ≤ M) (hs : Summable fun y => |f y|) :
    ∑' y, f y ^ 2 ≤ M * ∑' y, |f y| := by
  have hkey : ∀ y, f y ^ 2 ≤ M * |f y| := by
    intro y
    have h1 : f y ^ 2 = |f y| * |f y| := by rw [← sq_abs, sq]
    rw [h1]
    exact mul_le_mul_of_nonneg_right (hM y) (abs_nonneg _)
  have hsq : Summable (fun y => f y ^ 2) :=
    Summable.of_nonneg_of_le (fun y => sq_nonneg _) hkey (hs.mul_left M)
  calc ∑' y, f y ^ 2 ≤ ∑' y, M * |f y| := hsq.tsum_le_tsum hkey (hs.mul_left M)
    _ = M * ∑' y, |f y| := hs.tsum_mul_left M

/-- Weighted Cauchy-Schwarz for a series over `ℕ`: `(∑ g)² ≤ (∑ a)(∑ g²/a)` for
positive weights `a`.  This is what turns a bound on each time slice of a tail
sum into a bound on the `ℓ²` norm of the tail. -/
theorem sq_tsum_le_tsum_mul_tsum_div {g a : ℕ → ℝ} (ha : ∀ j, 0 < a j)
    (hsa : Summable a) (hsd : Summable fun j => g j ^ 2 / a j)
    (hsg : Summable g) :
    (∑' j, g j) ^ 2 ≤ (∑' j, a j) * ∑' j, g j ^ 2 / a j := by
  have hlim : Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, g j) ^ 2) atTop
      (nhds ((∑' j, g j) ^ 2)) := (hsg.tendsto_sum_tsum_nat).pow 2
  refine le_of_tendsto hlim (Filter.Eventually.of_forall fun n => ?_)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n)
    (fun j => Real.sqrt (a j)) (fun j => g j / Real.sqrt (a j))
  have he : ∀ j ∈ Finset.range n, Real.sqrt (a j) * (g j / Real.sqrt (a j)) = g j := by
    intro j _
    have hne : Real.sqrt (a j) ≠ 0 := Real.sqrt_ne_zero'.mpr (ha j)
    field_simp
  rw [Finset.sum_congr rfl he] at hcs
  have h1 : ∑ j ∈ Finset.range n, Real.sqrt (a j) ^ 2 = ∑ j ∈ Finset.range n, a j :=
    Finset.sum_congr rfl fun j _ => Real.sq_sqrt (ha j).le
  have h2 : ∑ j ∈ Finset.range n, (g j / Real.sqrt (a j)) ^ 2 =
      ∑ j ∈ Finset.range n, g j ^ 2 / a j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_pow, Real.sq_sqrt (ha j).le]
  rw [h1, h2] at hcs
  refine hcs.trans (mul_le_mul (hsa.sum_le_tsum _ fun j _ => (ha j).le)
    (hsd.sum_le_tsum _ fun j _ => div_nonneg (sq_nonneg _) (ha j).le)
    (Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (ha j).le)
    (tsum_nonneg fun j => (ha j).le))

/-- The heat kernel is summable in its second variable. -/
theorem summable_heatKernel_site (n : ℕ) (x : Site d) :
    Summable fun y : Site d => heatKernel d n x y := by
  simpa using summable_heatKernel_mul n x (fun _ => (1 : ℝ))

/-- **The `ℓ²` increment bound in dimension four.**  For sites of equal parity,
`∑_y (p_n(x,y) - p_n(w,y))² ≤ C|x-w|n^{-5/2}`. -/
theorem exists_heatKernel_increment_l2_four (hHK : Sandpile.External.HeatKernelBounds) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ x w : Site 4, Sandpile.External.SameParity x w →
      ∑' y : Site 4, (heatKernel 4 n x y - heatKernel 4 n w y) ^ 2 ≤
        C * Sandpile.External.latticeDist x w * (n : ℝ) ^ (-(5 : ℝ) / 2) := by
  obtain ⟨C1, hC1, hgauss⟩ := exists_heatKernel_sq_bound_four hHK
  obtain ⟨-, ⟨C2, hC2, hgrad⟩, -⟩ := hHK 4 (by norm_num)
  refine ⟨C1 * C2, by positivity, fun n hn x w hpar => ?_⟩
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hsum : Summable fun y : Site 4 => |heatKernel 4 n x y - heatKernel 4 n w y| :=
    ((summable_heatKernel_site n x).sub (summable_heatKernel_site n w)).abs
  have hM : ∀ y : Site 4, |heatKernel 4 n x y - heatKernel 4 n w y| ≤ C1 * ((n : ℝ) ^ 2)⁻¹ := by
    intro y
    rw [abs_le]
    have h1 := hgauss n hn x y
    have h2 := hgauss n hn w y
    have h3 := heatKernel_nonneg (d := 4) n x y
    have h4 := heatKernel_nonneg (d := 4) n w y
    constructor <;> linarith
  have hbase := tsum_sq_le_sup_mul_tsum_abs hM hsum
  have hgr := hgrad n hn x w hpar
  have hdist : 0 ≤ Sandpile.External.latticeDist x w := Real.sqrt_nonneg _
  have hMnn : (0 : ℝ) ≤ C1 * ((n : ℝ) ^ 2)⁻¹ := by positivity
  have hstep : C1 * ((n : ℝ) ^ 2)⁻¹ * (∑' y : Site 4, |heatKernel 4 n x y - heatKernel 4 n w y|) ≤
      C1 * ((n : ℝ) ^ 2)⁻¹ * (C2 * Sandpile.External.latticeDist x w * (n : ℝ) ^ (-(1 : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left hgr hMnn
  have hrpow : ((n : ℝ) ^ 2)⁻¹ * (n : ℝ) ^ (-(1 : ℝ) / 2) = (n : ℝ) ^ (-(5 : ℝ) / 2) := by
    rw [show ((n : ℝ) ^ 2)⁻¹ = (n : ℝ) ^ (-(2 : ℝ)) by
      rw [Real.rpow_neg hn0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    , ← Real.rpow_add hn0]
    norm_num
  calc ∑' y : Site 4, (heatKernel 4 n x y - heatKernel 4 n w y) ^ 2
      ≤ C1 * ((n : ℝ) ^ 2)⁻¹ * ∑' y : Site 4, |heatKernel 4 n x y - heatKernel 4 n w y| := hbase
    _ ≤ C1 * ((n : ℝ) ^ 2)⁻¹ *
        (C2 * Sandpile.External.latticeDist x w * (n : ℝ) ^ (-(1 : ℝ) / 2)) := hstep
    _ = C1 * C2 * Sandpile.External.latticeDist x w *
        (((n : ℝ) ^ 2)⁻¹ * (n : ℝ) ^ (-(1 : ℝ) / 2)) := by ring
    _ = C1 * C2 * Sandpile.External.latticeDist x w * (n : ℝ) ^ (-(5 : ℝ) / 2) := by rw [hrpow]

end Sandpile
