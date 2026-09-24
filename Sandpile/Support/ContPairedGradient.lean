/-
The kernel of two consecutive times, and the gradient bound it carries with no
parity hypothesis.

The total variation gradient bound of `ssec:green-estimates`,
`∑_y|p_n(x,y)-p_n(w,y)| ≤ C|x-w|n^{-1/2}`, holds only when `x` and `w` have the
same parity, and it must: at a single time the walk from `x` and the walk from a
site of the opposite parity are supported on disjoint sets, so the difference is
as large as the two kernels themselves.  The `L²` increment of the Green
coefficients at two mesh sites `⌊Rw⌋` and `⌊Rw'⌋` cannot avoid that case, since
two nearby points of `ℝ^d` have mesh sites of either parity.

Summing the kernel over two consecutive times removes the obstruction.  Write
`P_n(x,y) = p_n(x,y)+p_{n+1}(x,y)`.  If `x` and `x'` have the same parity the
bound applies to both summands.  If they do not, the one-step recursion in the
base point,
`p_{n+1}(x',y) = (2d)^{-1}∑_i (p_n(x'+e_i,y)+p_n(x'-e_i,y))`, pairs `p_n(x,·)`
with `p_{n+1}(x',·)` and `p_{n+1}(x,·)` with `p_n(x',·)`: every site `x'±e_i` has
the parity of `x`, and its distance to `x` exceeds `|x-x'|` by at most one.  Both
cases give
`∑_y|P_n(x,y)-P_n(x',y)| ≤ C(|x-x'|+1)n^{-1/2}` with no hypothesis on the parity.

Chapman-Kolmogorov then upgrades that to the pointwise bound
`|P_n(x,y)-P_n(x',y)| ≤ C(|x-x'|+1)n^{-(d+1)/2}` exactly as in
`ContHeatGradient`: the pairing sits on the first half of the time, which is what
`tsum_pairedKernel_mul` records, and the second half contributes its uniform
Gaussian bound.
-/
import Sandpile.Support.ContHeatGradient
import Sandpile.Support.ContLcltPoint

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile

variable {d : ℕ}

/-- The lattice Euclidean distance obeys the triangle inequality. -/
theorem latticeDist_triangle (x y z : Site d) :
    Sandpile.External.latticeDist x z ≤
      Sandpile.External.latticeDist x y + Sandpile.External.latticeDist y z := by
  have key : ∀ a b : Site d, Sandpile.External.latticeDist a b
      = ‖Sandpile.External.Lclt.scaledSite 1 a - Sandpile.External.Lclt.scaledSite 1 b‖ := by
    intro a b
    have h := Sandpile.Support.latticeDist_eq_mul_norm (d := d) (R := 1) one_pos a b
    rw [one_mul] at h
    exact h
  rw [key x z, key x y, key y z]
  exact norm_sub_le_norm_sub_add_norm_sub _ _ _

/-- A unit step changes the lattice Euclidean distance from the base point by one. -/
theorem latticeDist_add_unit (x : Site d) (i : Fin d) :
    Sandpile.External.latticeDist x (x + unit i) = 1 := by
  have h : ∀ j : Fin d, ((x j - (x + unit i) j : ℤ) : ℝ) ^ 2 = if j = i then (1:ℝ) else 0 := by
    intro j
    have hu : (x + unit i) j = x j + (if j = i then (1:ℤ) else 0) := by
      simp [unit, Pi.add_apply, Pi.single_apply]
    rw [hu]
    split_ifs with hj
    · push_cast; ring
    · push_cast; ring
  show Real.sqrt (∑ j : Fin d, ((x j - (x + unit i) j : ℤ) : ℝ) ^ 2) = 1
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_ite_eq' Finset.univ i (fun _ => (1:ℝ))]
  simp

/-- If two sites have opposite parity then a unit shift of the second has the
parity of the first. -/
theorem sameParity_add_unit_of_not {x x' : Site d}
    (h : ¬ Sandpile.External.SameParity x x') (i : Fin d) :
    Sandpile.External.SameParity x (x' + unit i) := by
  have hsum : ∑ j : Fin d, (x j - (x' + unit i) j)
      = (∑ j : Fin d, (x j - x' j)) - 1 := by
    have hu : ∀ j : Fin d, x j - (x' + unit i) j
        = (x j - x' j) - (if j = i then (1:ℤ) else 0) := by
      intro j
      simp [unit, Pi.add_apply, Pi.single_apply]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hu j), Finset.sum_sub_distrib,
      Finset.sum_ite_eq' Finset.univ i (fun _ => (1:ℤ))]
    simp
  show Even (∑ j : Fin d, (x j - (x' + unit i) j))
  rw [hsum]
  rcases Int.even_or_odd (∑ j : Fin d, (x j - x' j)) with he | ho
  · exact absurd he h
  · obtain ⟨k, hk⟩ := ho
    exact ⟨k, by omega⟩

/-- The total variation of a finite sum is at most the sum of the total variations. -/
theorem tsum_abs_finsum_le {ι : Type*} [Fintype ι] (F : ι → Site d → ℝ)
    (hsum : ∀ i, Summable fun y : Site d => |F i y|) :
    ∑' y : Site d, |∑ i, F i y| ≤ ∑ i, ∑' y : Site d, |F i y| := by
  have habs : Summable fun y : Site d => ∑ i, |F i y| := summable_sum (fun i _ => hsum i)
  have hS : Summable fun y : Site d => |∑ i, F i y| :=
    Summable.of_nonneg_of_le (fun y => abs_nonneg _)
      (fun y => Finset.abs_sum_le_sum_abs _ _) habs
  calc ∑' y : Site d, |∑ i, F i y|
      ≤ ∑' y : Site d, ∑ i, |F i y| :=
        Summable.tsum_le_tsum (fun y => Finset.abs_sum_le_sum_abs _ _) hS habs
    _ = ∑ i, ∑' y : Site d, |F i y| := Summable.tsum_finsetSum (fun i _ => hsum i)

/-- The kernel of two consecutive times, which is supported on both parity
classes. -/
noncomputable def pairedKernel (d : ℕ) (n : ℕ) (x y : Site d) : ℝ :=
  Sandpile.heatKernel d n x y + Sandpile.heatKernel d (n + 1) x y

/-- Chapman-Kolmogorov for the paired kernel: the pairing sits on the first
factor. -/
theorem tsum_pairedKernel_mul (m m' : ℕ) (x y : Site d) :
    pairedKernel d (m + m') x y
      = ∑' z : Site d, pairedKernel d m x z * Sandpile.heatKernel d m' z y := by
  have hsum : m + m' + 1 = m + 1 + m' := by omega
  have h1 := Sandpile.tsum_heatKernel_mul_heatKernel m m' x y
  have h2 := Sandpile.tsum_heatKernel_mul_heatKernel (m + 1) m' x y
  show Sandpile.heatKernel d (m + m') x y + Sandpile.heatKernel d (m + m' + 1) x y
      = ∑' z : Site d, pairedKernel d m x z * Sandpile.heatKernel d m' z y
  rw [hsum, ← h1, ← h2, ← Summable.tsum_add
    (summable_heatKernel_mul m x (fun z => Sandpile.heatKernel d m' z y))
    (summable_heatKernel_mul (m + 1) x (fun z => Sandpile.heatKernel d m' z y))]
  refine tsum_congr fun z => ?_
  rw [pairedKernel]
  ring

/-- A backward unit step changes the lattice Euclidean distance from the base
point by one. -/
theorem latticeDist_sub_unit (x : Site d) (i : Fin d) :
    Sandpile.External.latticeDist x (x - unit i) = 1 := by
  have h : ∀ j : Fin d, ((x j - (x - unit i) j : ℤ) : ℝ) ^ 2 = if j = i then (1:ℝ) else 0 := by
    intro j
    have hu : (x - unit i) j = x j - (if j = i then (1:ℤ) else 0) := by
      simp [unit, Pi.sub_apply, Pi.single_apply]
    rw [hu]
    split_ifs with hj
    · push_cast; ring
    · push_cast; ring
  show Real.sqrt (∑ j : Fin d, ((x j - (x - unit i) j : ℤ) : ℝ) ^ 2) = 1
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_ite_eq' Finset.univ i (fun _ => (1:ℝ))]
  simp

/-- If two sites have opposite parity then a backward unit shift of the second has
the parity of the first. -/
theorem sameParity_sub_unit_of_not {x x' : Site d}
    (h : ¬ Sandpile.External.SameParity x x') (i : Fin d) :
    Sandpile.External.SameParity x (x' - unit i) := by
  have hsum : ∑ j : Fin d, (x j - (x' - unit i) j)
      = (∑ j : Fin d, (x j - x' j)) + 1 := by
    have hu : ∀ j : Fin d, x j - (x' - unit i) j
        = (x j - x' j) + (if j = i then (1:ℤ) else 0) := by
      intro j
      simp [unit, Pi.sub_apply, Pi.single_apply]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hu j), Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ i (fun _ => (1:ℤ))]
    simp
  show Even (∑ j : Fin d, (x j - (x' - unit i) j))
  rw [hsum]
  rcases Int.even_or_odd (∑ j : Fin d, (x j - x' j)) with he | ho
  · exact absurd he h
  · obtain ⟨k, hk⟩ := ho
    exact ⟨k + 1, by omega⟩

/-- The total variation of a sum is at most the sum of the total variations. -/
theorem tsum_abs_add_le (f g : Site d → ℝ) (hf : Summable fun y : Site d => |f y|)
    (hg : Summable fun y : Site d => |g y|) :
    ∑' y : Site d, |f y + g y| ≤ (∑' y : Site d, |f y|) + ∑' y : Site d, |g y| := by
  have hsum : Summable fun y : Site d => |f y| + |g y| := hf.add hg
  have hS : Summable fun y : Site d => |f y + g y| :=
    Summable.of_nonneg_of_le (fun y => abs_nonneg _) (fun y => abs_add_le _ _) hsum
  calc ∑' y : Site d, |f y + g y|
      ≤ ∑' y : Site d, (|f y| + |g y|) :=
        Summable.tsum_le_tsum (fun y => abs_add_le _ _) hS hsum
    _ = (∑' y : Site d, |f y|) + ∑' y : Site d, |g y| := Summable.tsum_add hf hg

/-- The difference of two heat kernels at a common time is absolutely summable. -/
theorem summable_abs_heatKernel_sub (n : ℕ) (x w : Site d) :
    Summable fun y : Site d =>
      |Sandpile.heatKernel d n x y - Sandpile.heatKernel d n w y| := by
  have h1 : Summable fun y : Site d => Sandpile.heatKernel d n x y := by
    simpa using summable_heatKernel_mul n x (fun _ => (1:ℝ))
  have h2 : Summable fun y : Site d => Sandpile.heatKernel d n w y := by
    simpa using summable_heatKernel_mul n w (fun _ => (1:ℝ))
  exact (h1.sub h2).abs

/-- The one-step recursion in the base point, written as the average over the
`2d` neighbours of the differences from a fixed site. -/
theorem heatKernel_sub_succ_eq (hd : 1 ≤ d) (n : ℕ) (x x' y : Site d) :
    Sandpile.heatKernel d n x y - Sandpile.heatKernel d (n + 1) x' y
      = (∑ i : Fin d,
          ((Sandpile.heatKernel d n x y - Sandpile.heatKernel d n (x' + unit i) y)
            + (Sandpile.heatKernel d n x y - Sandpile.heatKernel d n (x' - unit i) y)))
          / (2 * (d : ℝ)) := by
  have hdR : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hne : (2 * (d : ℝ)) ≠ 0 := by positivity
  have hsucc : Sandpile.heatKernel d (n + 1) x' y
      = (∑ i : Fin d, (Sandpile.heatKernel d n (x' + unit i) y
          + Sandpile.heatKernel d n (x' - unit i) y)) / (2 * (d : ℝ)) := rfl
  have hterm : ∀ i : Fin d,
      ((Sandpile.heatKernel d n x y - Sandpile.heatKernel d n (x' + unit i) y)
        + (Sandpile.heatKernel d n x y - Sandpile.heatKernel d n (x' - unit i) y))
      = 2 * Sandpile.heatKernel d n x y
        - (Sandpile.heatKernel d n (x' + unit i) y
            + Sandpile.heatKernel d n (x' - unit i) y) := by
    intro i; ring
  rw [hsucc, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- The lattice Euclidean distance is symmetric. -/
theorem latticeDist_comm (x y : Site d) :
    Sandpile.External.latticeDist x y = Sandpile.External.latticeDist y x := by
  show Real.sqrt (∑ i : Fin d, ((x i - y i : ℤ) : ℝ) ^ 2)
      = Real.sqrt (∑ i : Fin d, ((y i - x i : ℤ) : ℝ) ^ 2)
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-- Equality of parity is symmetric. -/
theorem sameParity_comm {x y : Site d} (h : Sandpile.External.SameParity x y) :
    Sandpile.External.SameParity y x := by
  have hsum : ∑ i : Fin d, (y i - x i) = -∑ i : Fin d, (x i - y i) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  show Even (∑ i : Fin d, (y i - x i))
  rw [hsum]
  exact Even.neg h

/-- The difference of two heat kernels at two times is absolutely summable. -/
theorem summable_abs_heatKernel_sub' (n m : ℕ) (x w : Site d) :
    Summable fun y : Site d =>
      |Sandpile.heatKernel d n x y - Sandpile.heatKernel d m w y| := by
  have h1 : Summable fun y : Site d => Sandpile.heatKernel d n x y := by
    simpa using summable_heatKernel_mul n x (fun _ => (1:ℝ))
  have h2 : Summable fun y : Site d => Sandpile.heatKernel d m w y := by
    simpa using summable_heatKernel_mul m w (fun _ => (1:ℝ))
  exact (h1.sub h2).abs

/-- A sum of two absolutely summable families is absolutely summable. -/
theorem summable_abs_add (f g : Site d → ℝ) (hf : Summable fun y : Site d => |f y|)
    (hg : Summable fun y : Site d => |g y|) :
    Summable fun y : Site d => |f y + g y| := by
  exact Summable.of_nonneg_of_le (fun y => abs_nonneg _) (fun y => abs_add_le _ _) (hf.add hg)

/-- **The gradient bound across a parity change, one time against the next.**  The
one-step recursion in the base point replaces `p_{n+1}(x',·)` by the average of
`p_n` over the `2d` neighbours of `x'`, every one of which has the parity of `x`
and lies within `|x-x'|+1` of it. -/
theorem tsum_abs_heatKernel_sub_succ_le {C₂ : ℝ} (hC₂ : 0 < C₂) (hd : 1 ≤ d)
    (hgrad : ∀ n : ℕ, 1 ≤ n → ∀ x w : Site d, Sandpile.External.SameParity x w →
      ∑' y : Site d, |Sandpile.heatKernel d n x y - Sandpile.heatKernel d n w y| ≤
        C₂ * Sandpile.External.latticeDist x w * (n : ℝ) ^ (-(1 : ℝ) / 2))
    (n : ℕ) (hn : 1 ≤ n) (x x' : Site d)
    (hpar : ¬ Sandpile.External.SameParity x x') :
    ∑' y : Site d, |Sandpile.heatKernel d n x y - Sandpile.heatKernel d (n + 1) x' y|
      ≤ C₂ * (Sandpile.External.latticeDist x x' + 1) * (n : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hdR : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h2d : (0:ℝ) < 2 * (d : ℝ) := by positivity
  have hnpow : (0:ℝ) ≤ (n : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hnbr : ∀ i : Fin d,
      ∑' y : Site d,
          |(Sandpile.heatKernel d n x y - Sandpile.heatKernel d n (x' + unit i) y)
            + (Sandpile.heatKernel d n x y - Sandpile.heatKernel d n (x' - unit i) y)|
        ≤ 2 * (C₂ * (Sandpile.External.latticeDist x x' + 1) * (n : ℝ) ^ (-(1 : ℝ) / 2)) := by
    intro i
    have hs1 := summable_abs_heatKernel_sub' (d := d) n n x (x' + unit i)
    have hs2 := summable_abs_heatKernel_sub' (d := d) n n x (x' - unit i)
    have hsplit := tsum_abs_add_le
      (fun y : Site d => Sandpile.heatKernel d n x y - Sandpile.heatKernel d n (x' + unit i) y)
      (fun y : Site d => Sandpile.heatKernel d n x y - Sandpile.heatKernel d n (x' - unit i) y)
      hs1 hs2
    have hb1 : ∑' y : Site d,
        |Sandpile.heatKernel d n x y - Sandpile.heatKernel d n (x' + unit i) y|
          ≤ C₂ * (Sandpile.External.latticeDist x x' + 1) * (n : ℝ) ^ (-(1 : ℝ) / 2) := by
      have ht := latticeDist_triangle x x' (x' + unit i)
      rw [latticeDist_add_unit] at ht
      have hmul : C₂ * Sandpile.External.latticeDist x (x' + unit i)
          ≤ C₂ * (Sandpile.External.latticeDist x x' + 1) :=
        mul_le_mul_of_nonneg_left ht hC₂.le
      exact le_trans (hgrad n hn x (x' + unit i) (sameParity_add_unit_of_not hpar i))
        (mul_le_mul_of_nonneg_right hmul hnpow)
    have hb2 : ∑' y : Site d,
        |Sandpile.heatKernel d n x y - Sandpile.heatKernel d n (x' - unit i) y|
          ≤ C₂ * (Sandpile.External.latticeDist x x' + 1) * (n : ℝ) ^ (-(1 : ℝ) / 2) := by
      have ht := latticeDist_triangle x x' (x' - unit i)
      rw [latticeDist_sub_unit] at ht
      have hmul : C₂ * Sandpile.External.latticeDist x (x' - unit i)
          ≤ C₂ * (Sandpile.External.latticeDist x x' + 1) :=
        mul_le_mul_of_nonneg_left ht hC₂.le
      exact le_trans (hgrad n hn x (x' - unit i) (sameParity_sub_unit_of_not hpar i))
        (mul_le_mul_of_nonneg_right hmul hnpow)
    linarith
  have hrw : ∀ y : Site d,
      |Sandpile.heatKernel d n x y - Sandpile.heatKernel d (n + 1) x' y|
        = |∑ i : Fin d,
            ((Sandpile.heatKernel d n x y - Sandpile.heatKernel d n (x' + unit i) y)
              + (Sandpile.heatKernel d n x y - Sandpile.heatKernel d n (x' - unit i) y))|
            / (2 * (d : ℝ)) := by
    intro y
    rw [heatKernel_sub_succ_eq hd n x x' y, abs_div, abs_of_pos h2d]
  have hsummA : ∀ i : Fin d, Summable fun y : Site d =>
      |(Sandpile.heatKernel d n x y - Sandpile.heatKernel d n (x' + unit i) y)
        + (Sandpile.heatKernel d n x y - Sandpile.heatKernel d n (x' - unit i) y)| :=
    fun i => summable_abs_add _ _ (summable_abs_heatKernel_sub' n n x (x' + unit i))
      (summable_abs_heatKernel_sub' n n x (x' - unit i))
  have hfin := tsum_abs_finsum_le
    (fun (i : Fin d) (y : Site d) =>
      (Sandpile.heatKernel d n x y - Sandpile.heatKernel d n (x' + unit i) y)
        + (Sandpile.heatKernel d n x y - Sandpile.heatKernel d n (x' - unit i) y)) hsummA
  have hcard : (∑ i : Fin d, ∑' y : Site d,
      |(Sandpile.heatKernel d n x y - Sandpile.heatKernel d n (x' + unit i) y)
        + (Sandpile.heatKernel d n x y - Sandpile.heatKernel d n (x' - unit i) y)|)
      ≤ (d : ℝ) * (2 * (C₂ * (Sandpile.External.latticeDist x x' + 1)
          * (n : ℝ) ^ (-(1 : ℝ) / 2))) := by
    have hstep := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hnbr i)
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hstep
  rw [tsum_congr hrw, tsum_div_const, div_le_iff₀ h2d]
  exact le_trans (le_trans hfin hcard) (le_of_eq (by ring))

/-- The paired gradient bound when the two sites have the same parity. -/
theorem tsum_abs_pairedKernel_sub_le_of_sameParity {C₂ : ℝ} (hC₂ : 0 < C₂)
    (hgrad : ∀ n : ℕ, 1 ≤ n → ∀ x w : Site d, Sandpile.External.SameParity x w →
      ∑' y : Site d, |Sandpile.heatKernel d n x y - Sandpile.heatKernel d n w y| ≤
        C₂ * Sandpile.External.latticeDist x w * (n : ℝ) ^ (-(1 : ℝ) / 2))
    (n : ℕ) (hn : 1 ≤ n) (x x' : Site d)
    (hpar : Sandpile.External.SameParity x x') :
    ∑' y : Site d, |pairedKernel d n x y - pairedKernel d n x' y|
      ≤ 2 * (C₂ * (Sandpile.External.latticeDist x x' + 1)
          * (n : ℝ) ^ (-(1 : ℝ) / 2)) := by
  have hnpow : (0:ℝ) ≤ (n : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hD0 : (0:ℝ) ≤ Sandpile.External.latticeDist x x' := Real.sqrt_nonneg _
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hrw : ∀ y : Site d, |pairedKernel d n x y - pairedKernel d n x' y|
      = |(Sandpile.heatKernel d n x y - Sandpile.heatKernel d n x' y)
        + (Sandpile.heatKernel d (n + 1) x y - Sandpile.heatKernel d (n + 1) x' y)| := by
    intro y
    congr 1
    rw [pairedKernel, pairedKernel]
    ring
  have hs1 := summable_abs_heatKernel_sub' (d := d) n n x x'
  have hs2 := summable_abs_heatKernel_sub' (d := d) (n + 1) (n + 1) x x'
  have hsplit := tsum_abs_add_le
    (fun y : Site d => Sandpile.heatKernel d n x y - Sandpile.heatKernel d n x' y)
    (fun y : Site d => Sandpile.heatKernel d (n + 1) x y - Sandpile.heatKernel d (n + 1) x' y)
    hs1 hs2
  have hb1 := hgrad n hn x x' hpar
  have hb2 := hgrad (n + 1) (by omega) x x' hpar
  have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast] at hb2
  have hmono : ((n : ℝ) + 1) ^ (-(1 : ℝ) / 2) ≤ (n : ℝ) ^ (-(1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_nonpos hn0 (by linarith) (by norm_num)
  have hb2' : ∑' y : Site d,
      |Sandpile.heatKernel d (n + 1) x y - Sandpile.heatKernel d (n + 1) x' y|
        ≤ C₂ * Sandpile.External.latticeDist x x' * (n : ℝ) ^ (-(1 : ℝ) / 2) :=
    le_trans hb2 (mul_le_mul_of_nonneg_left hmono (mul_nonneg hC₂.le hD0))
  have hfinal : C₂ * Sandpile.External.latticeDist x x' * (n : ℝ) ^ (-(1 : ℝ) / 2)
      ≤ C₂ * (Sandpile.External.latticeDist x x' + 1) * (n : ℝ) ^ (-(1 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by linarith) hC₂.le) hnpow
  rw [tsum_congr hrw]
  linarith

/-- The paired gradient bound when the two sites have opposite parity. -/
theorem tsum_abs_pairedKernel_sub_le_of_not_sameParity {C₂ : ℝ} (hC₂ : 0 < C₂) (hd : 1 ≤ d)
    (hgrad : ∀ n : ℕ, 1 ≤ n → ∀ x w : Site d, Sandpile.External.SameParity x w →
      ∑' y : Site d, |Sandpile.heatKernel d n x y - Sandpile.heatKernel d n w y| ≤
        C₂ * Sandpile.External.latticeDist x w * (n : ℝ) ^ (-(1 : ℝ) / 2))
    (n : ℕ) (hn : 1 ≤ n) (x x' : Site d)
    (hpar : ¬ Sandpile.External.SameParity x x') :
    ∑' y : Site d, |pairedKernel d n x y - pairedKernel d n x' y|
      ≤ 2 * (C₂ * (Sandpile.External.latticeDist x x' + 1)
          * (n : ℝ) ^ (-(1 : ℝ) / 2)) := by
  have hrw : ∀ y : Site d, |pairedKernel d n x y - pairedKernel d n x' y|
      = |(Sandpile.heatKernel d n x y - Sandpile.heatKernel d (n + 1) x' y)
        + (Sandpile.heatKernel d (n + 1) x y - Sandpile.heatKernel d n x' y)| := by
    intro y
    congr 1
    rw [pairedKernel, pairedKernel]
    ring
  have hs1 := summable_abs_heatKernel_sub' (d := d) n (n + 1) x x'
  have hs2 := summable_abs_heatKernel_sub' (d := d) (n + 1) n x x'
  have hsplit := tsum_abs_add_le
    (fun y : Site d => Sandpile.heatKernel d n x y - Sandpile.heatKernel d (n + 1) x' y)
    (fun y : Site d => Sandpile.heatKernel d (n + 1) x y - Sandpile.heatKernel d n x' y)
    hs1 hs2
  have hb1 := tsum_abs_heatKernel_sub_succ_le hC₂ hd hgrad n hn x x' hpar
  have hpar' : ¬ Sandpile.External.SameParity x' x := fun h => hpar (sameParity_comm h)
  have hb2 := tsum_abs_heatKernel_sub_succ_le hC₂ hd hgrad n hn x' x hpar'
  rw [latticeDist_comm x' x] at hb2
  have heq : ∑' y : Site d,
      |Sandpile.heatKernel d (n + 1) x y - Sandpile.heatKernel d n x' y|
      = ∑' y : Site d,
      |Sandpile.heatKernel d n x' y - Sandpile.heatKernel d (n + 1) x y| :=
    tsum_congr fun y => abs_sub_comm _ _
  have hb2' : ∑' y : Site d,
      |Sandpile.heatKernel d (n + 1) x y - Sandpile.heatKernel d n x' y|
        ≤ C₂ * (Sandpile.External.latticeDist x x' + 1) * (n : ℝ) ^ (-(1 : ℝ) / 2) := by
    rw [heq]
    exact hb2
  rw [tsum_congr hrw]
  linarith

/-- **The total variation gradient bound for the paired kernel, with no parity
hypothesis.** -/
theorem exists_paired_tv_gradient (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ x x' : Site d,
      ∑' y : Site d, |pairedKernel d n x y - pairedKernel d n x' y|
        ≤ C * (Sandpile.External.latticeDist x x' + 1) * (n : ℝ) ^ (-(1 : ℝ) / 2) := by
  obtain ⟨-, ⟨C₂, hC₂, hgrad⟩, -⟩ := hHK d hd
  refine ⟨2 * C₂, by positivity, ?_⟩
  intro n hn x x'
  by_cases hpar : Sandpile.External.SameParity x x'
  · exact le_trans (tsum_abs_pairedKernel_sub_le_of_sameParity hC₂ hgrad n hn x x' hpar)
      (le_of_eq (by ring))
  · exact le_trans (tsum_abs_pairedKernel_sub_le_of_not_sameParity hC₂ hd hgrad n hn x x' hpar)
      (le_of_eq (by ring))

/-- **The pointwise gradient bound for the paired kernel, with no parity
hypothesis.** -/
theorem exists_paired_pointwise_gradient
    (hHK : Sandpile.External.HeatKernelBounds) (hd : 1 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ x x' y : Site d,
      |pairedKernel d n x y - pairedKernel d n x' y| ≤
        C * (Sandpile.External.latticeDist x x' + 1)
          * (n : ℝ) ^ (-((d : ℝ) + 1) / 2) := by
  obtain ⟨⟨C₁, c₁, hC₁, hc₁, hgauss⟩, -, -⟩ := hHK d hd
  obtain ⟨C₀, hC₀, htv⟩ := exists_paired_tv_gradient hHK hd
  refine ⟨C₁ * C₀ * 3 ^ (((d : ℝ) + 1) / 2), by positivity, ?_⟩
  intro n hn x x' y
  have hn0 : 1 ≤ n := by omega
  have hn0' : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hm1 : 1 ≤ n / 2 := by omega
  have hm'1 : 1 ≤ n - n / 2 := by omega
  have hsum : n / 2 + (n - n / 2) = n := by omega
  have h3m : n ≤ 3 * (n / 2) := by omega
  have h3m' : n ≤ 3 * (n - n / 2) := by omega
  set m : ℕ := n / 2 with hmdef
  set m' : ℕ := n - n / 2 with hm'def
  have hld : (0:ℝ) ≤ Sandpile.External.latticeDist x x' := Real.sqrt_nonneg _
  set D : ℝ := Sandpile.External.latticeDist x x' + 1 with hD
  have hD0 : (0:ℝ) ≤ D := by rw [hD]; linarith
  have hb : ∀ z : Site d,
      |Sandpile.heatKernel d m' z y| ≤ C₁ * (m' : ℝ) ^ (-((d : ℝ) / 2)) := by
    intro z
    rw [abs_of_nonneg (heatKernel_nonneg m' z y)]
    have hg := hgauss m' hm'1 z y
    have hexp : Real.exp (-c₁ * Sandpile.External.latticeDist z y ^ 2 / (m' : ℝ)) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      have hm'0 : (0:ℝ) < (m' : ℝ) := by exact_mod_cast hm'1
      have : 0 ≤ c₁ * Sandpile.External.latticeDist z y ^ 2 := by positivity
      rw [div_nonpos_iff]
      exact Or.inr ⟨by linarith, hm'0.le⟩
    have hfac : 0 ≤ C₁ * (m' : ℝ) ^ (-(d : ℝ) / 2) := by positivity
    calc Sandpile.heatKernel d m' z y
        ≤ C₁ * (m' : ℝ) ^ (-(d : ℝ) / 2) *
            Real.exp (-c₁ * Sandpile.External.latticeDist z y ^ 2 / (m' : ℝ)) := hg
      _ ≤ C₁ * (m' : ℝ) ^ (-(d : ℝ) / 2) * 1 := mul_le_mul_of_nonneg_left hexp hfac
      _ = C₁ * (m' : ℝ) ^ (-((d : ℝ) / 2)) := by rw [mul_one, neg_div]
  have hs1 : Summable fun z : Site d =>
      pairedKernel d m x z * Sandpile.heatKernel d m' z y := by
    have ha := summable_heatKernel_mul m x (fun z => Sandpile.heatKernel d m' z y)
    have hbb := summable_heatKernel_mul (m + 1) x (fun z => Sandpile.heatKernel d m' z y)
    exact (ha.add hbb).congr fun z => by rw [pairedKernel]; ring
  have hs2 : Summable fun z : Site d =>
      pairedKernel d m x' z * Sandpile.heatKernel d m' z y := by
    have ha := summable_heatKernel_mul m x' (fun z => Sandpile.heatKernel d m' z y)
    have hbb := summable_heatKernel_mul (m + 1) x' (fun z => Sandpile.heatKernel d m' z y)
    exact (ha.add hbb).congr fun z => by rw [pairedKernel]; ring
  have hsx : Summable fun z : Site d => pairedKernel d m x z := by
    have h1 : Summable fun z : Site d => Sandpile.heatKernel d m x z := by
      simpa using summable_heatKernel_mul m x (fun _ => (1:ℝ))
    have h2 : Summable fun z : Site d => Sandpile.heatKernel d (m + 1) x z := by
      simpa using summable_heatKernel_mul (m + 1) x (fun _ => (1:ℝ))
    exact (h1.add h2).congr fun z => by rw [pairedKernel]
  have hsx' : Summable fun z : Site d => pairedKernel d m x' z := by
    have h1 : Summable fun z : Site d => Sandpile.heatKernel d m x' z := by
      simpa using summable_heatKernel_mul m x' (fun _ => (1:ℝ))
    have h2 : Summable fun z : Site d => Sandpile.heatKernel d (m + 1) x' z := by
      simpa using summable_heatKernel_mul (m + 1) x' (fun _ => (1:ℝ))
    exact (h1.add h2).congr fun z => by rw [pairedKernel]
  have hkey : pairedKernel d n x y - pairedKernel d n x' y
      = ∑' z : Site d, (pairedKernel d m x z - pairedKernel d m x' z)
          * Sandpile.heatKernel d m' z y := by
    rw [← hsum, tsum_pairedKernel_mul m m' x y, tsum_pairedKernel_mul m m' x' y,
      ← Summable.tsum_sub hs1 hs2]
    exact tsum_congr fun z => (sub_mul _ _ _).symm
  have hA : (m' : ℝ) ^ (-((d : ℝ) / 2)) ≤ 3 ^ ((d : ℝ) / 2) * (n : ℝ) ^ (-((d : ℝ) / 2)) :=
    rpow_neg_third_le hn0 hm'1 h3m' (by positivity)
  have hB : (m : ℝ) ^ (-((1 : ℝ) / 2)) ≤ 3 ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (-((1 : ℝ) / 2)) :=
    rpow_neg_third_le hn0 hm1 h3m (by norm_num)
  have hgradm : ∑' z : Site d, |pairedKernel d m x z - pairedKernel d m x' z|
      ≤ C₀ * D * (m : ℝ) ^ (-((1 : ℝ) / 2)) := by
    have h := htv m hm1 x x'
    rwa [neg_div, ← hD] at h
  have e3 : (3:ℝ) ^ ((d : ℝ) / 2) * (3:ℝ) ^ ((1 : ℝ) / 2) = (3:ℝ) ^ (((d : ℝ) + 1) / 2) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 3)]
    congr 1
    ring
  have e4 : (n:ℝ) ^ (-((d : ℝ) / 2)) * (n:ℝ) ^ (-((1 : ℝ) / 2))
      = (n:ℝ) ^ (-((d : ℝ) + 1) / 2) := by
    rw [← Real.rpow_add hn0']
    congr 1
    ring
  have heq : C₁ * (3 ^ ((d : ℝ) / 2) * (n : ℝ) ^ (-((d : ℝ) / 2))) *
      (C₀ * D * (3 ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (-((1 : ℝ) / 2))))
      = C₁ * C₀ * 3 ^ (((d : ℝ) + 1) / 2) * D * (n : ℝ) ^ (-((d : ℝ) + 1) / 2) := by
    calc C₁ * (3 ^ ((d : ℝ) / 2) * (n : ℝ) ^ (-((d : ℝ) / 2))) *
        (C₀ * D * (3 ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (-((1 : ℝ) / 2))))
        = C₁ * C₀ * (3 ^ ((d : ℝ) / 2) * 3 ^ ((1 : ℝ) / 2)) * D *
            ((n : ℝ) ^ (-((d : ℝ) / 2)) * (n : ℝ) ^ (-((1 : ℝ) / 2))) := by ring
      _ = C₁ * C₀ * 3 ^ (((d : ℝ) + 1) / 2) * D * (n : ℝ) ^ (-((d : ℝ) + 1) / 2) := by
          rw [e3, e4]
  rw [hkey]
  calc |∑' z : Site d,
        (pairedKernel d m x z - pairedKernel d m x' z) * Sandpile.heatKernel d m' z y|
      ≤ C₁ * (m' : ℝ) ^ (-((d : ℝ) / 2)) *
          ∑' z : Site d, |pairedKernel d m x z - pairedKernel d m x' z| :=
        abs_tsum_mul_le _ _ _ hb (hsx.sub hsx')
    _ ≤ C₁ * (3 ^ ((d : ℝ) / 2) * (n : ℝ) ^ (-((d : ℝ) / 2))) *
          (C₀ * D * (3 ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (-((1 : ℝ) / 2)))) := by
        have hS0 : (0:ℝ) ≤ ∑' z : Site d, |pairedKernel d m x z - pairedKernel d m x' z| :=
          tsum_nonneg fun z => abs_nonneg _
        have hS : (∑' z : Site d, |pairedKernel d m x z - pairedKernel d m x' z|)
            ≤ C₀ * D * (3 ^ ((1 : ℝ) / 2) * (n : ℝ) ^ (-((1 : ℝ) / 2))) :=
          le_trans hgradm (mul_le_mul_of_nonneg_left hB (mul_nonneg hC₀.le hD0))
        have hAA : C₁ * (m' : ℝ) ^ (-((d : ℝ) / 2))
            ≤ C₁ * (3 ^ ((d : ℝ) / 2) * (n : ℝ) ^ (-((d : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left hA hC₁.le
        exact mul_le_mul hAA hS hS0 (mul_nonneg hC₁.le (by positivity))
    _ = C₁ * C₀ * 3 ^ (((d : ℝ) + 1) / 2) * D * (n : ℝ) ^ (-((d : ℝ) + 1) / 2) := heq

end Sandpile.Support
