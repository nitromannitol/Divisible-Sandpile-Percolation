/-
Consequences of the `d ≥ 5` Green estimates that the tail arguments of
`ssec:d5-height-upper` use in a pointwise form.  The assumed estimate
`eq:dgt4-green-tail` bounds `G(0,z)` on a half-space `|z| ≥ r` with `r` an
integer; the arguments split space at a real radius, so the bound is turned into
the pointwise form `G(0,y) ≤ C(1+|y|)^{2-d}` valid at every site, the origin
included, where the value is read off the square summability instead.
-/
import Sandpile.External.GreenBoundsHigh
import Sandpile.Support.Kernel
import Sandpile.Support.Radial

open MeasureTheory

namespace Sandpile

variable {d : ℕ}

/-- A family on `ℕ` summable from the first index on is summable. -/
theorem summable_of_summable_ge_one {f : ℕ → ℝ}
    (h : Summable fun j : {j : ℕ // 1 ≤ j} => f j) : Summable f := by
  have hinj : Function.Injective
      (fun n : ℕ => (⟨n + 1, Nat.le_add_left 1 n⟩ : {j : ℕ // 1 ≤ j})) := by
    intro a b hab
    simpa using hab
  have h2 : Summable fun n : ℕ => f (n + 1) := (h.comp_injective hinj).congr fun n => rfl
  exact (summable_nat_add_iff 1).mp h2

/-- The heat kernel at a site is summable in time in dimension five and above. -/
theorem summable_heatKernel_high (hGH : Sandpile.External.GreenBoundsHigh)
    (hd : 5 ≤ d) (y : Site d) : Summable fun k : ℕ => heatKernel d k 0 y := by
  obtain ⟨-, -, hc3, -, -⟩ := hGH d hd
  obtain ⟨C3, -, htail⟩ := hc3
  exact summable_of_summable_ge_one ((htail 1 le_rfl).1 y).1

/-- The finite-time Green function is below the Green function. -/
theorem greenTime_le_green (hGH : Sandpile.External.GreenBoundsHigh)
    (hd : 5 ≤ d) (m : ℕ) (y : Site d) : greenTime d m 0 y ≤ green d 0 y := by
  rw [greenTime, green]
  exact (summable_heatKernel_high hGH hd y).sum_le_tsum _
    (fun k _ => heatKernel_nonneg _ _ _)

/-- The Euclidean norm of a nonzero site is at least one. -/
theorem one_le_latticeNorm {y : Site d} (hy : y ≠ 0) :
    1 ≤ Sandpile.External.latticeNorm y := by
  obtain ⟨i, hi⟩ : ∃ i : Fin d, y i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hy (funext h)
  have h1 : (1 : ℝ) ≤ ((y i : ℤ) : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ (y i) ^ 2 := by
      rcases lt_trichotomy (y i) 0 with h | h | h
      · nlinarith
      · exact absurd h hi
      · nlinarith
    exact_mod_cast this
  have h2 : (1 : ℝ) ≤ ∑ j : Fin d, ((y j : ℤ) : ℝ) ^ 2 := by
    refine le_trans h1 (Finset.single_le_sum (f := fun j : Fin d => ((y j : ℤ) : ℝ) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  have := Real.one_le_sqrt.mpr h2
  simpa [Sandpile.External.latticeNorm] using this

/-- **The pointwise Green bound.**  `G(0,y) ≤ C_G (1+|y|)^{2-d}` at every site
in dimension five and above.  Away from the origin this is
`eq:dgt4-green-tail` at the integer radius `⌊|y|⌋`, which is at least a quarter
of `1+|y|`; at the origin it is the square summability `eq:dgt4-green-l2`, whose
single term at the origin bounds `G(0,0)`. -/
theorem exists_green_pointwise (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) :
    ∃ CG : ℝ, 0 < CG ∧ ∀ y : Site d,
      green d 0 y ≤ CG * (1 + Sandpile.External.latticeNorm y) ^ (2 - (d : ℝ)) := by
  obtain ⟨⟨C, hC, htail⟩, hl2, -, -, -⟩ := hGH d hd
  have hd2 : (2 : ℝ) - (d : ℝ) < 0 := by
    have : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  have hnonneg : ∀ z : Site d, 0 ≤ green d 0 z := fun z =>
    tsum_nonneg fun k => heatKernel_nonneg _ _ _
  set A : ℝ := ∑' z : Site d, green d 0 z ^ 2 with hA
  have hA0 : green d 0 0 ^ 2 ≤ A := by
    rw [hA]
    exact hl2.le_tsum 0 (fun b _ => sq_nonneg _)
  have hG00 : green d 0 0 ≤ Real.sqrt A := by
    have := Real.sqrt_le_sqrt hA0
    rwa [Real.sqrt_sq (hnonneg 0)] at this
  refine ⟨max (Real.sqrt A + 1) (C * 4 ^ ((d : ℝ) - 2)), ?_, fun y => ?_⟩
  · refine lt_of_lt_of_le (by positivity) (le_max_left _ _)
  by_cases hy : y = 0
  · subst hy
    have hnorm : Sandpile.External.latticeNorm (0 : Site d) = 0 := by
      simp [Sandpile.External.latticeNorm]
    rw [hnorm, add_zero, Real.one_rpow, mul_one]
    calc green d 0 0 ≤ Real.sqrt A := hG00
      _ ≤ Real.sqrt A + 1 := by linarith
      _ ≤ max (Real.sqrt A + 1) (C * 4 ^ ((d : ℝ) - 2)) := le_max_left _ _
  · have hn1 : 1 ≤ Sandpile.External.latticeNorm y := one_le_latticeNorm hy
    set N : ℝ := Sandpile.External.latticeNorm y with hN
    set r : ℕ := ⌊N⌋₊ with hr
    have hr1 : 1 ≤ r := Nat.le_floor (by exact_mod_cast hn1)
    have hrN : (r : ℝ) ≤ N := Nat.floor_le (by linarith)
    have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
    have hquarter : (1 + N) / 4 ≤ (r : ℝ) := by
      have hfl : N - 1 < (r : ℝ) := by
        have := Nat.lt_floor_add_one N
        linarith
      have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
      rcases le_or_gt N 3 with hcase | hcase
      · linarith
      · linarith
    have hgb : green d 0 y ≤ C * (r : ℝ) ^ (2 - (d : ℝ)) :=
      (htail r hr1).2.2 y (by rw [← hN]; exact hrN)
    have hmono : (r : ℝ) ^ (2 - (d : ℝ)) ≤ ((1 + N) / 4) ^ (2 - (d : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hquarter hd2.le
    have hsplit : ((1 + N) / 4) ^ (2 - (d : ℝ))
        = 4 ^ ((d : ℝ) - 2) * (1 + N) ^ (2 - (d : ℝ)) := by
      rw [Real.div_rpow (by linarith) (by norm_num)]
      rw [show (4 : ℝ) ^ ((d : ℝ) - 2) = ((4 : ℝ) ^ (2 - (d : ℝ)))⁻¹ by
        rw [← Real.rpow_neg (by norm_num)]
        congr 1
        ring]
      field_simp
    have hfin : green d 0 y ≤ C * 4 ^ ((d : ℝ) - 2) * (1 + N) ^ (2 - (d : ℝ)) := by
      calc green d 0 y ≤ C * (r : ℝ) ^ (2 - (d : ℝ)) := hgb
        _ ≤ C * (((1 + N) / 4) ^ (2 - (d : ℝ))) := mul_le_mul_of_nonneg_left hmono hC.le
        _ = C * 4 ^ ((d : ℝ) - 2) * (1 + N) ^ (2 - (d : ℝ)) := by rw [hsplit]; ring
    refine le_trans hfin (mul_le_mul_of_nonneg_right (le_max_right _ _) ?_)
    positivity

/-- **Summability of a power of the Green function above the critical exponent.**
For `p > d/(d-2)` the family `G(0,y)^p` is summable over the lattice, which is
what the case `γ < d/2` of `lem:dgt4-stretched-green-scenery-tail` uses when it
writes `∑_y G(0,y)^{γ/(γ-1)} < ∞`. -/
theorem summable_green_rpow (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (p : ℝ) (hp : (d : ℝ) / ((d : ℝ) - 2) < p) :
    Summable fun y : Site d => green d 0 y ^ p := by
  have hdR : (5 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd2 : (0 : ℝ) < (d : ℝ) - 2 := by linarith
  have hp0 : (0 : ℝ) < p := lt_of_le_of_lt (by positivity) hp
  have hexp : (d : ℝ) < ((d : ℝ) - 2) * p := by
    rw [div_lt_iff₀ hd2] at hp
    linarith
  obtain ⟨CG, hCG, hbound⟩ := exists_green_pointwise hGH hd
  have hnonneg : ∀ y : Site d, 0 ≤ green d 0 y := fun y =>
    tsum_nonneg fun k => heatKernel_nonneg _ _ _
  have hmaj : Summable fun y : Site d =>
      CG ^ p * (1 + LatticeProb.euclidNorm y) ^ (-(((d : ℝ) - 2) * p)) :=
    (LatticeProb.summable_one_add_euclidNorm_rpow d hexp).mul_left _
  refine Summable.of_nonneg_of_le (fun y => Real.rpow_nonneg (hnonneg y) _) (fun y => ?_) hmaj
  have hnorm : Sandpile.External.latticeNorm y = LatticeProb.euclidNorm y := rfl
  have h1 : green d 0 y ^ p ≤
      (CG * (1 + LatticeProb.euclidNorm y) ^ (2 - (d : ℝ))) ^ p := by
    refine Real.rpow_le_rpow (hnonneg y) ?_ hp0.le
    have := hbound y
    rwa [hnorm] at this
  refine le_trans h1 (le_of_eq ?_)
  have hbase : (0 : ℝ) < 1 + LatticeProb.euclidNorm y := by
    have := LatticeProb.euclidNorm_nonneg y
    linarith
  rw [Real.mul_rpow hCG.le (Real.rpow_nonneg hbase.le _), ← Real.rpow_mul hbase.le]
  congr 2
  ring

end Sandpile
