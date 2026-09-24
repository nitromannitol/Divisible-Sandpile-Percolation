/-
The four-dimensional potential kernel `a(x,y) = ∑_{j≥0}(p_j(x,y) - p_j(0,y))`,
the kernel of the untruncated centred membrane field of Step 1 of
`prop:d4-superdiffusive-limit` (`sandpile.tex:3341-3366`).

In dimension four the walk is transient, so each of the two series converges on
its own and `a(x,y) = G(x,y) - G(0,y)` is a difference of Green functions.  The
subtraction at the base point is what the field needs: the centred field is
defined modulo additive constants, and `a(0,y) = 0`.

The Gaussian upper bound `eq:rw-gaussian-upper` gives `p_n(x,y) ≤ Cn^{-2}` in
dimension four, hence a bound on `G` and on `a` that is uniform in both sites.
-/
import Sandpile.Support.ExitGreen
import Sandpile.External.HeatKernelBounds

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- The potential kernel `a(x,y) = ∑_{j≥0}(p_j(x,y) - p_j(0,y))` of
`sandpile.tex:3341-3366`, the kernel of the untruncated centred membrane
field. -/
noncomputable def potentialKernel (d : ℕ) (x y : Site d) : ℝ :=
  ∑' j : ℕ, (heatKernel d j x y - heatKernel d j 0 y)

/-- The defining series of the potential kernel is summable in a transient
dimension. -/
theorem summable_potentialKernel (hd : 3 ≤ d) (x y : Site d) :
    Summable fun j : ℕ => heatKernel d j x y - heatKernel d j 0 y :=
  (summable_heatKernel_transient hd x y).sub (summable_heatKernel_transient hd 0 y)

/-- The potential kernel is the difference of the two Green functions. -/
theorem potentialKernel_eq_green_sub (hd : 3 ≤ d) (x y : Site d) :
    potentialKernel d x y = green d x y - green d 0 y := by
  rw [potentialKernel, green, green]
  exact (summable_heatKernel_transient hd x y).tsum_sub (summable_heatKernel_transient hd 0 y)

/-- The potential kernel vanishes at the base point. -/
theorem potentialKernel_base (hd : 3 ≤ d) (y : Site d) : potentialKernel d 0 y = 0 := by
  rw [potentialKernel_eq_green_sub hd, sub_self]

/-- In dimension four the Gaussian upper bound gives `p_n(x,y) ≤ Cn^{-2}` for
`n ≥ 1`, uniformly in the two sites. -/
theorem exists_heatKernel_sq_bound_four (hHK : Sandpile.External.HeatKernelBounds) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ x y : Site 4,
      heatKernel 4 n x y ≤ C * ((n : ℝ) ^ 2)⁻¹ := by
  obtain ⟨⟨C, c, hC, hc, hb⟩, -, -⟩ := hHK 4 (by norm_num)
  refine ⟨C, hC, fun n hn x y => ?_⟩
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hrpow : ((n : ℝ)) ^ (-((4 : ℕ) : ℝ) / 2) = ((n : ℝ) ^ 2)⁻¹ := by
    rw [show (-((4 : ℕ) : ℝ) / 2) = -((2 : ℕ) : ℝ) by norm_num,
      Real.rpow_neg hn0.le, Real.rpow_natCast]
  have hexp : Real.exp (-c * Sandpile.External.latticeDist x y ^ 2 / (n : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    apply div_nonpos_of_nonpos_of_nonneg _ hn0.le
    nlinarith [sq_nonneg (Sandpile.External.latticeDist x y)]
  have hnn : (0 : ℝ) ≤ C * ((n : ℝ)) ^ (-((4 : ℕ) : ℝ) / 2) :=
    mul_nonneg hC.le (Real.rpow_nonneg hn0.le _)
  calc Sandpile.heatKernel 4 n x y ≤ C * ((n : ℝ)) ^ (-((4 : ℕ) : ℝ) / 2) *
        Real.exp (-c * Sandpile.External.latticeDist x y ^ 2 / (n : ℝ)) := hb n hn x y
    _ ≤ C * ((n : ℝ)) ^ (-((4 : ℕ) : ℝ) / 2) * 1 := mul_le_mul_of_nonneg_left hexp hnn
    _ = C * ((n : ℝ) ^ 2)⁻¹ := by rw [mul_one, hrpow]

/-- The four-dimensional Green function is bounded, uniformly in both sites. -/
theorem exists_green_bound_four (hHK : Sandpile.External.HeatKernelBounds) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : Site 4, green 4 x y ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_heatKernel_sq_bound_four hHK
  have hsum2 : Summable (fun k : ℕ => (((k : ℝ) + 1) ^ 2)⁻¹) := by
    have h1 : Summable (fun k : ℕ => (((k : ℕ) : ℝ) ^ 2)⁻¹) := by
      simp
    have h2 := (summable_nat_add_iff 1).mpr h1
    simpa using h2
  set B : ℝ := ∑' k : ℕ, (((k : ℝ) + 1) ^ 2)⁻¹ with hB
  have hBnn : 0 ≤ B := tsum_nonneg fun k => by positivity
  refine ⟨1 + C * B, by positivity, fun x y => ?_⟩
  have hsum : Summable (fun k : ℕ => heatKernel 4 k x y) :=
    summable_heatKernel_transient (by norm_num) x y
  rw [green, hsum.tsum_eq_zero_add]
  have h0 : heatKernel 4 0 x y ≤ 1 := by
    simp only [heatKernel, LatticeProb.LocalCLT.heatKernel]
    split <;> norm_num
  have htail : (∑' k : ℕ, heatKernel 4 (k + 1) x y) ≤ C * B := by
    have hle : ∀ k : ℕ, heatKernel 4 (k + 1) x y ≤ C * ((((k : ℝ) + 1)) ^ 2)⁻¹ := by
      intro k
      have := hb (k + 1) (by omega) x y
      simpa using this
    have hs1 : Summable (fun k : ℕ => heatKernel 4 (k + 1) x y) :=
      (summable_nat_add_iff 1).mpr hsum
    have hs2 : Summable (fun k : ℕ => C * ((((k : ℝ) + 1)) ^ 2)⁻¹) := hsum2.mul_left C
    calc (∑' k : ℕ, heatKernel 4 (k + 1) x y)
        ≤ ∑' k : ℕ, C * ((((k : ℝ) + 1)) ^ 2)⁻¹ := hs1.tsum_le_tsum hle hs2
      _ = C * B := by rw [hB, ← hsum2.tsum_mul_left]
  linarith

/-- The four-dimensional potential kernel is bounded, uniformly in both sites:
the bound Step 1 needs for the untruncated field. -/
theorem exists_potentialKernel_bound_four (hHK : Sandpile.External.HeatKernelBounds) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : Site 4, |potentialKernel 4 x y| ≤ C := by
  obtain ⟨C, hC, hb⟩ := exists_green_bound_four hHK
  refine ⟨2 * C, by linarith, fun x y => ?_⟩
  rw [potentialKernel_eq_green_sub (by norm_num), abs_le]
  have h1 := hb x y
  have h2 := hb 0 y
  have h3 := green_nonneg (d := 4) x y
  have h4 := green_nonneg (d := 4) 0 y
  constructor <;> linarith

end Sandpile
