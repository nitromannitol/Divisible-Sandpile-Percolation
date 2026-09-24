/-
The tested intersection kernel, `eq:dgt4-tested-intersection-moments`
(`sandpile.tex:5703-5709`):

  "Compact support, annular summation, and
   \eqref{eq:dgt4-intersection-first-moment}--\eqref{eq:dgt4-intersection-second-moment}
   give that for $k=1,2$,
   $\sum_{x,y\in\Z^d}a_R(x)a_R(y)\mathbf E_x\mathbf E_y[\mathcal I(X,Y)^k]\leq C(\varphi)$."

Both moments are bounded by `C(1+|x-y|)^{4-d}`, the first by
`Sandpile.lintegral_interCount_le` and the second by the cited input
`Sandpile.External.IntersectionSecondMoment`, so the display reduces to the
weighted kernel sum proved here:

  `∑_{x,y} |a_R(x)| |a_R(y)| (1+|x-y|)^{4-d} ≤ C(φ)`,

uniformly in `R ≥ 1`.  The three inputs are the `ℓ¹` bound on the cell masses
(their sum is at most the integral of the absolute value of the test function),
the sup bound on one cell mass (at most the sup of the test function times the
cell volume `R^{-d}`), and the annular summation over the box of the support.
-/
import Sandpile.Support.LinAnnular
import Sandpile.Support.LinIntersect
import Sandpile.Support.ContRiemann
import Sandpile.Support.ContWeightedLimit

open Finset MeasureTheory
open scoped ENNReal
open Sandpile.Continuum

namespace Sandpile

variable {d : ℕ}

/-- The annular sum seen from a site of the box: reindexing by `y ↦ x - y` sends
the box of radius `K` into the box of radius `2K`. -/
theorem sum_boxFinset_shift_interKernel_le (hd : 5 ≤ d) (K : ℕ) (x : Site d)
    (hx : boxDist (0 : Site d) x ≤ K) :
    ∑ y ∈ boxFinset (0 : Site d) K, (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))
      ≤ ((d : ℝ) * 2 ^ d) * ((2 * K : ℕ) + 1 : ℝ) ^ 4 := by
  classical
  have hinj : ∀ y ∈ boxFinset (0 : Site d) K, ∀ y' ∈ boxFinset (0 : Site d) K,
      x - y = x - y' → y = y' := by
    intro y _ y' _ h
    have := congrArg (fun z : Site d => x - z) h
    simpa using sub_right_injective h
  have himg : ((boxFinset (0 : Site d) K).image fun y : Site d => x - y)
      ⊆ boxFinset (0 : Site d) (2 * K) := by
    intro u hu
    rw [Finset.mem_image] at hu
    obtain ⟨y, hy, rfl⟩ := hu
    refine mem_boxFinset ?_
    have hy' : boxDist (0 : Site d) y ≤ K := mem_boxFinset_iff.mp hy
    have htri : boxDist (0 : Site d) (x - y) ≤ boxDist (0 : Site d) x + boxDist (0 : Site d) y := by
      refine Finset.sup_le fun i _ => ?_
      have h1 : ((0 : Site d) i - x i).natAbs ≤ boxDist (0 : Site d) x :=
        Finset.le_sup (f := fun i => ((0 : Site d) i - x i).natAbs) (Finset.mem_univ i)
      have h2 : ((0 : Site d) i - y i).natAbs ≤ boxDist (0 : Site d) y :=
        Finset.le_sup (f := fun i => ((0 : Site d) i - y i).natAbs) (Finset.mem_univ i)
      have hcoord : ((0 : Site d) i - (x - y) i) = ((0 : Site d) i - x i) + ((0 : Site d) i - y i) *
          (-1) + 0 := by
        simp [sub_eq_add_neg]
        ring
      have : ((0 : Site d) i - (x - y) i).natAbs ≤ ((0 : Site d) i - x i).natAbs +
          ((0 : Site d) i - y i).natAbs := by
        have hv : ((0 : Site d) i - (x - y) i) = ((0 : Site d) i - x i) - ((0 : Site d) i - y i) := by
          simp [sub_eq_add_neg]
          ring
        rw [hv]
        exact Int.natAbs_sub_le _ _
      omega
    omega
  have hnn : ∀ u : Site d, (0 : ℝ) ≤ (1 + Sandpile.External.latticeNorm u) ^ (4 - (d : ℝ)) := by
    intro u
    refine Real.rpow_nonneg ?_ _
    have : 0 ≤ Sandpile.External.latticeNorm u := Real.sqrt_nonneg _
    linarith
  have himage : ∑ u ∈ (boxFinset (0 : Site d) K).image (fun y : Site d => x - y),
      (1 + Sandpile.External.latticeNorm u) ^ (4 - (d : ℝ))
      = ∑ y ∈ boxFinset (0 : Site d) K,
          (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)) :=
    Finset.sum_image hinj
  calc ∑ y ∈ boxFinset (0 : Site d) K,
        (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))
      = ∑ u ∈ (boxFinset (0 : Site d) K).image (fun y : Site d => x - y),
          (1 + Sandpile.External.latticeNorm u) ^ (4 - (d : ℝ)) := himage.symm
    _ ≤ ∑ u ∈ boxFinset (0 : Site d) (2 * K),
          (1 + Sandpile.External.latticeNorm u) ^ (4 - (d : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg himg fun u _ _ => hnn u
    _ ≤ ((d : ℝ) * 2 ^ d) * (((2 * K : ℕ) : ℝ) + 1) ^ 4 :=
        sum_boxFinset_interKernel_le hd (2 * K)

/-- **The tested intersection kernel is bounded uniformly in the scale**, the
content of `eq:dgt4-tested-intersection-moments` once both intersection moments
are bounded by `C(1+|x-y|)^{4-d}`:

  `∑_{x,y} |a_R(x)| |a_R(y)| (1+|x-y|)^{4-d} ≤ C(φ)`,

with `a_R(x) = R^{(d-4)/2} φ_R(x)` and the sums over the sites whose cells meet
the support of the test function. -/
theorem sum_tested_kernel_le (hd : 5 ≤ d) (φ : Space d → ℝ) (Cφ L : ℝ)
    (hCφ : 0 ≤ Cφ) (hL : 0 ≤ L) (hb : ∀ z, |φ z| ≤ Cφ) (hint : Integrable φ)
    (R : ℝ) (hR : 1 ≤ R) :
    ∑ x ∈ Sandpile.Support.supportBox d R L, ∑ y ∈ Sandpile.Support.supportBox d R L,
        (R ^ (((d : ℝ) - 4) / 2) * |Sandpile.Support.cellMass R φ x|) *
          (R ^ (((d : ℝ) - 4) / 2) * |Sandpile.Support.cellMass R φ y|) *
          (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))
      ≤ (∫ z, |φ z|) * Cφ * ((d : ℝ) * 2 ^ d) * (2 * L + 5) ^ 4 := by
  classical
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  set K : ℕ := ⌈|R| * L⌉₊ + 1 with hK
  have hbox : Sandpile.Support.supportBox d R L = boxFinset (0 : Site d) K := rfl
  set A : ℝ := R ^ (((d : ℝ) - 4) / 2) with hA
  have hA0 : 0 < A := Real.rpow_pos_of_pos hR0 _
  have hcellsup : ∀ x : Site d, |Sandpile.Support.cellMass R φ x| ≤ Cφ * R⁻¹ ^ d :=
    fun x => Sandpile.Support.abs_cellMass_le hR0 φ Cφ hb x
  have hkernel : ∀ x ∈ boxFinset (0 : Site d) K,
      ∑ y ∈ boxFinset (0 : Site d) K,
          (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))
        ≤ ((d : ℝ) * 2 ^ d) * (((2 * K : ℕ) : ℝ) + 1) ^ 4 := by
    intro x hx
    exact sum_boxFinset_shift_interKernel_le hd K x (mem_boxFinset_iff.mp hx)
  have hknn : ∀ u : Site d, (0 : ℝ) ≤ (1 + Sandpile.External.latticeNorm u) ^ (4 - (d : ℝ)) := by
    intro u
    refine Real.rpow_nonneg ?_ _
    have : 0 ≤ Sandpile.External.latticeNorm u := Real.sqrt_nonneg _
    linarith
  -- the inner sum, for one site of the box
  have hinner : ∀ x ∈ boxFinset (0 : Site d) K,
      ∑ y ∈ boxFinset (0 : Site d) K,
          (A * |Sandpile.Support.cellMass R φ x|) * (A * |Sandpile.Support.cellMass R φ y|) *
            (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))
        ≤ (A * |Sandpile.Support.cellMass R φ x|) *
            ((A * (Cφ * R⁻¹ ^ d)) * (((d : ℝ) * 2 ^ d) * (((2 * K : ℕ) : ℝ) + 1) ^ 4)) := by
    intro x hx
    have hstep : ∀ y ∈ boxFinset (0 : Site d) K,
        (A * |Sandpile.Support.cellMass R φ x|) * (A * |Sandpile.Support.cellMass R φ y|) *
            (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))
          ≤ (A * |Sandpile.Support.cellMass R φ x|) * (A * (Cφ * R⁻¹ ^ d)) *
            (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)) := by
      intro y _
      refine mul_le_mul_of_nonneg_right ?_ (hknn _)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left (hcellsup y) hA0.le
    calc ∑ y ∈ boxFinset (0 : Site d) K,
          (A * |Sandpile.Support.cellMass R φ x|) * (A * |Sandpile.Support.cellMass R φ y|) *
            (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))
        ≤ ∑ y ∈ boxFinset (0 : Site d) K,
            (A * |Sandpile.Support.cellMass R φ x|) * (A * (Cφ * R⁻¹ ^ d)) *
              (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)) :=
          Finset.sum_le_sum hstep
      _ = (A * |Sandpile.Support.cellMass R φ x|) * (A * (Cφ * R⁻¹ ^ d)) *
            ∑ y ∈ boxFinset (0 : Site d) K,
              (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ (A * |Sandpile.Support.cellMass R φ x|) * (A * (Cφ * R⁻¹ ^ d)) *
            (((d : ℝ) * 2 ^ d) * (((2 * K : ℕ) : ℝ) + 1) ^ 4) :=
          mul_le_mul_of_nonneg_left (hkernel x hx) (by positivity)
      _ = (A * |Sandpile.Support.cellMass R φ x|) *
            ((A * (Cφ * R⁻¹ ^ d)) * (((d : ℝ) * 2 ^ d) * (((2 * K : ℕ) : ℝ) + 1) ^ 4)) := by
          ring
  -- the outer sum
  have houter : ∑ x ∈ boxFinset (0 : Site d) K, (A * |Sandpile.Support.cellMass R φ x|)
      ≤ A * ∫ z, |φ z| := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hA0.le
    exact Sandpile.Support.sum_abs_cellMass_le R φ hint _
  -- the scale arithmetic
  have hKle : ((2 * K : ℕ) : ℝ) + 1 ≤ R * (2 * L + 5) := by
    have habs : |R| = R := abs_of_pos hR0
    have hceil : (⌈|R| * L⌉₊ : ℝ) ≤ |R| * L + 1 := by
      have hnn : (0 : ℝ) ≤ |R| * L := by positivity
      exact le_of_lt (Nat.ceil_lt_add_one hnn)
    have : ((2 * K : ℕ) : ℝ) + 1 = 2 * (⌈|R| * L⌉₊ : ℝ) + 3 := by
      rw [hK]
      push_cast
      ring
    rw [this, habs] at *
    nlinarith [hceil, hR, hL, hR0]
  have hApow : A * A = R ^ ((d : ℝ) - 4) := by
    rw [hA, ← Real.rpow_add hR0]
    ring_nf
  have hinvpow : (R⁻¹ : ℝ) ^ d = R ^ (-(d : ℝ)) := by
    rw [Real.rpow_neg hR0.le, Real.rpow_natCast R d, inv_pow]
  have hscale : (A * A) * (R⁻¹ ^ d) * (R * (2 * L + 5)) ^ 4 = (2 * L + 5) ^ 4 := by
    rw [hApow, hinvpow, mul_pow, ← Real.rpow_natCast R 4]
    rw [show R ^ ((d : ℝ) - 4) * R ^ (-(d : ℝ)) * (R ^ (((4 : ℕ) : ℝ)) * (2 * L + 5) ^ 4)
        = (R ^ ((d : ℝ) - 4) * R ^ (-(d : ℝ)) * R ^ (((4 : ℕ) : ℝ))) * (2 * L + 5) ^ 4 from by
      ring]
    rw [← Real.rpow_add hR0, ← Real.rpow_add hR0]
    have hexp : ((d : ℝ) - 4 + -(d : ℝ) + ((4 : ℕ) : ℝ)) = 0 := by push_cast; ring
    rw [hexp, Real.rpow_zero, one_mul]
  calc ∑ x ∈ Sandpile.Support.supportBox d R L, ∑ y ∈ Sandpile.Support.supportBox d R L,
        (A * |Sandpile.Support.cellMass R φ x|) * (A * |Sandpile.Support.cellMass R φ y|) *
          (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))
      ≤ ∑ x ∈ boxFinset (0 : Site d) K, (A * |Sandpile.Support.cellMass R φ x|) *
          ((A * (Cφ * R⁻¹ ^ d)) * (((d : ℝ) * 2 ^ d) * (((2 * K : ℕ) : ℝ) + 1) ^ 4)) := by
        rw [hbox]
        exact Finset.sum_le_sum hinner
    _ = (∑ x ∈ boxFinset (0 : Site d) K, (A * |Sandpile.Support.cellMass R φ x|)) *
          ((A * (Cφ * R⁻¹ ^ d)) * (((d : ℝ) * 2 ^ d) * (((2 * K : ℕ) : ℝ) + 1) ^ 4)) := by
        rw [Finset.sum_mul]
    _ ≤ (A * ∫ z, |φ z|) *
          ((A * (Cφ * R⁻¹ ^ d)) * (((d : ℝ) * 2 ^ d) * (R * (2 * L + 5)) ^ 4)) := by
        refine mul_le_mul houter ?_ (by positivity) (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine pow_le_pow_left₀ (by positivity) hKle 4
    _ = (∫ z, |φ z|) * Cφ * ((d : ℝ) * 2 ^ d) * (2 * L + 5) ^ 4 := by
        rw [← hscale]
        ring

/-- **`eq:dgt4-tested-intersection-moments`** (`sandpile.tex:5698-5704`): any
quantity dominated by `C₀(1+|x-y|)^{4-d}`, in particular either of the two
intersection moments, has tested double sum bounded uniformly in the scale. -/
theorem sum_tested_moment_le (hd : 5 ≤ d) (φ : Space d → ℝ) (Cφ L : ℝ)
    (hCφ : 0 ≤ Cφ) (hL : 0 ≤ L) (hb : ∀ z, |φ z| ≤ Cφ) (hint : Integrable φ)
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (M : Site d → Site d → ℝ≥0∞)
    (hM : ∀ x y : Site d, M x y ≤
        ENNReal.ofReal (C₀ * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))))
    (R : ℝ) (hR : 1 ≤ R) :
    ∑ x ∈ Sandpile.Support.supportBox d R L, ∑ y ∈ Sandpile.Support.supportBox d R L,
        ENNReal.ofReal ((R ^ (((d : ℝ) - 4) / 2) * |Sandpile.Support.cellMass R φ x|) *
            (R ^ (((d : ℝ) - 4) / 2) * |Sandpile.Support.cellMass R φ y|)) * M x y
      ≤ ENNReal.ofReal (C₀ * ((∫ z, |φ z|) * Cφ * ((d : ℝ) * 2 ^ d) * (2 * L + 5) ^ 4)) := by
  classical
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  set A : ℝ := R ^ (((d : ℝ) - 4) / 2) with hA
  have hA0 : 0 < A := Real.rpow_pos_of_pos hR0 _
  have hknn : ∀ u : Site d, (0 : ℝ) ≤ (1 + Sandpile.External.latticeNorm u) ^ (4 - (d : ℝ)) := by
    intro u
    refine Real.rpow_nonneg ?_ _
    have : 0 ≤ Sandpile.External.latticeNorm u := Real.sqrt_nonneg _
    linarith
  have hterm : ∀ x y : Site d,
      ENNReal.ofReal ((A * |Sandpile.Support.cellMass R φ x|) *
          (A * |Sandpile.Support.cellMass R φ y|)) * M x y
        ≤ ENNReal.ofReal ((A * |Sandpile.Support.cellMass R φ x|) *
            (A * |Sandpile.Support.cellMass R φ y|) *
            (C₀ * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)))) := by
    intro x y
    have hsplit : ENNReal.ofReal ((A * |Sandpile.Support.cellMass R φ x|) *
          (A * |Sandpile.Support.cellMass R φ y|) *
          (C₀ * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))))
        = ENNReal.ofReal ((A * |Sandpile.Support.cellMass R φ x|) *
            (A * |Sandpile.Support.cellMass R φ y|)) *
          ENNReal.ofReal (C₀ * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))) :=
      ENNReal.ofReal_mul (by positivity)
    rw [hsplit]
    exact mul_le_mul' le_rfl (hM x y)
  have hnnterm : ∀ x y : Site d, (0 : ℝ) ≤
      (A * |Sandpile.Support.cellMass R φ x|) * (A * |Sandpile.Support.cellMass R φ y|) *
        (C₀ * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))) := by
    intro x y
    have h1 : (0 : ℝ) ≤ A * |Sandpile.Support.cellMass R φ x| :=
      mul_nonneg hA0.le (abs_nonneg _)
    have h2 : (0 : ℝ) ≤ A * |Sandpile.Support.cellMass R φ y| :=
      mul_nonneg hA0.le (abs_nonneg _)
    have h3 : (0 : ℝ) ≤ C₀ * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)) :=
      mul_nonneg hC₀ (hknn _)
    exact mul_nonneg (mul_nonneg h1 h2) h3
  have hsum : ∑ x ∈ Sandpile.Support.supportBox d R L, ∑ y ∈ Sandpile.Support.supportBox d R L,
      ENNReal.ofReal ((A * |Sandpile.Support.cellMass R φ x|) *
          (A * |Sandpile.Support.cellMass R φ y|) *
          (C₀ * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))))
      = ENNReal.ofReal (∑ x ∈ Sandpile.Support.supportBox d R L,
          ∑ y ∈ Sandpile.Support.supportBox d R L,
            (A * |Sandpile.Support.cellMass R φ x|) * (A * |Sandpile.Support.cellMass R φ y|) *
              (C₀ * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)))) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => Finset.sum_nonneg fun y _ => hnnterm x y)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun y _ => hnnterm x y)]
  have hkernel := sum_tested_kernel_le hd φ Cφ L hCφ hL hb hint R hR
  have hfinal : ∑ x ∈ Sandpile.Support.supportBox d R L,
      ∑ y ∈ Sandpile.Support.supportBox d R L,
        (A * |Sandpile.Support.cellMass R φ x|) * (A * |Sandpile.Support.cellMass R φ y|) *
          (C₀ * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)))
      ≤ C₀ * ((∫ z, |φ z|) * Cφ * ((d : ℝ) * 2 ^ d) * (2 * L + 5) ^ 4) := by
    have hrew : ∀ x ∈ Sandpile.Support.supportBox d R L,
        ∑ y ∈ Sandpile.Support.supportBox d R L,
          (A * |Sandpile.Support.cellMass R φ x|) * (A * |Sandpile.Support.cellMass R φ y|) *
            (C₀ * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)))
          = C₀ * ∑ y ∈ Sandpile.Support.supportBox d R L,
              (A * |Sandpile.Support.cellMass R φ x|) *
                (A * |Sandpile.Support.cellMass R φ y|) *
                (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)) := by
      intro x _
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [Finset.sum_congr rfl hrew, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hkernel hC₀
  calc ∑ x ∈ Sandpile.Support.supportBox d R L, ∑ y ∈ Sandpile.Support.supportBox d R L,
        ENNReal.ofReal ((A * |Sandpile.Support.cellMass R φ x|) *
            (A * |Sandpile.Support.cellMass R φ y|)) * M x y
      ≤ ∑ x ∈ Sandpile.Support.supportBox d R L, ∑ y ∈ Sandpile.Support.supportBox d R L,
          ENNReal.ofReal ((A * |Sandpile.Support.cellMass R φ x|) *
              (A * |Sandpile.Support.cellMass R φ y|) *
              (C₀ * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)))) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
    _ = ENNReal.ofReal (∑ x ∈ Sandpile.Support.supportBox d R L,
          ∑ y ∈ Sandpile.Support.supportBox d R L,
            (A * |Sandpile.Support.cellMass R φ x|) * (A * |Sandpile.Support.cellMass R φ y|) *
              (C₀ * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)))) := hsum
    _ ≤ ENNReal.ofReal (C₀ * ((∫ z, |φ z|) * Cφ * ((d : ℝ) * 2 ^ d) * (2 * L + 5) ^ 4)) :=
        ENNReal.ofReal_le_ofReal hfinal

/-- The tested FIRST intersection moment, `eq:dgt4-tested-intersection-moments`
at `k = 1`: it is bounded uniformly in the scale.  The moment itself is the
proved `Sandpile.lintegral_interCount_le`, so no cited input enters here beyond
the Green-function estimates. -/
theorem exists_sum_tested_first_moment_le (hd : 5 ≤ d)
    (hGreen : Sandpile.External.GreenBoundsHigh)
    (φ : Space d → ℝ) (Cφ L : ℝ) (hCφ : 0 ≤ Cφ) (hL : 0 ≤ L) (hb : ∀ z, |φ z| ≤ Cφ)
    (hint : Integrable φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      ∑ x ∈ Sandpile.Support.supportBox d R L, ∑ y ∈ Sandpile.Support.supportBox d R L,
          ENNReal.ofReal ((R ^ (((d : ℝ) - 4) / 2) * |Sandpile.Support.cellMass R φ x|) *
              (R ^ (((d : ℝ) - 4) / 2) * |Sandpile.Support.cellMass R φ y|)) *
            (∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y
              ∂(walkLaw d y) ∂(walkLaw d x))
        ≤ ENNReal.ofReal C := by
  haveI : NeZero d := ⟨by omega⟩
  obtain ⟨C₁, hC₁, hbound⟩ := lintegral_interCount_le (d := d) hd hGreen
  refine ⟨C₁ * ((∫ z, |φ z|) * Cφ * ((d : ℝ) * 2 ^ d) * (2 * L + 5) ^ 4), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ ∫ z, |φ z| := integral_nonneg fun z => abs_nonneg _
    have h2 : (0 : ℝ) ≤ (2 * L + 5) ^ 4 := by positivity
    have h3 : (0 : ℝ) ≤ (d : ℝ) * 2 ^ d := by positivity
    have := mul_nonneg (mul_nonneg (mul_nonneg h1 hCφ) h3) h2
    exact mul_nonneg hC₁.le this
  · intro R hR
    exact sum_tested_moment_le hd φ Cφ L hCφ hL hb hint C₁ hC₁.le _
      (fun x y => hbound x y) R hR

/-- The tested SECOND intersection moment, `eq:dgt4-tested-intersection-moments`
at `k = 2`, from the cited input `Sandpile.External.IntersectionSecondMoment`. -/
theorem exists_sum_tested_second_moment_le (hd : 5 ≤ d)
    (hInter : Sandpile.External.IntersectionSecondMoment)
    (φ : Space d → ℝ) (Cφ L : ℝ) (hCφ : 0 ≤ Cφ) (hL : 0 ≤ L) (hb : ∀ z, |φ z| ≤ Cφ)
    (hint : Integrable φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      ∑ x ∈ Sandpile.Support.supportBox d R L, ∑ y ∈ Sandpile.Support.supportBox d R L,
          ENNReal.ofReal ((R ^ (((d : ℝ) - 4) / 2) * |Sandpile.Support.cellMass R φ x|) *
              (R ^ (((d : ℝ) - 4) / 2) * |Sandpile.Support.cellMass R φ y|)) *
            (∫⁻ X, ∫⁻ Y, Sandpile.External.interCount X Y ^ 2
              ∂(walkLaw d y) ∂(walkLaw d x))
        ≤ ENNReal.ofReal C := by
  obtain ⟨C₂, hC₂, hbound⟩ := hInter d hd
  refine ⟨C₂ * ((∫ z, |φ z|) * Cφ * ((d : ℝ) * 2 ^ d) * (2 * L + 5) ^ 4), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ ∫ z, |φ z| := integral_nonneg fun z => abs_nonneg _
    have h2 : (0 : ℝ) ≤ (2 * L + 5) ^ 4 := by positivity
    have h3 : (0 : ℝ) ≤ (d : ℝ) * 2 ^ d := by positivity
    have := mul_nonneg (mul_nonneg (mul_nonneg h1 hCφ) h3) h2
    exact mul_nonneg hC₂.le this
  · intro R hR
    exact sum_tested_moment_le hd φ Cφ L hCφ hL hb hint C₂ hC₂.le _
      (fun x y => hbound x y) R hR

/-- **`eq:dgt4-tested-green-bound`** (`sandpile.tex:5793-5798`): the tested Green
field is bounded in `ℓ²`, uniformly in the scale.  The paper deduces it from the
identity `∑_z G(x,z)G(y,z) = E_x E_y I(X,Y)` and the tested intersection
moments; here the Green form is used directly, so only the Green-function
estimates enter. -/
theorem exists_sum_tested_green_le (hd : 5 ≤ d)
    (hGreen : Sandpile.External.GreenBoundsHigh)
    (φ : Space d → ℝ) (Cφ L : ℝ) (hCφ : 0 ≤ Cφ) (hL : 0 ≤ L) (hb : ∀ z, |φ z| ≤ Cφ)
    (hint : Integrable φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
      ∑' z : Site d, (∑ x ∈ Sandpile.Support.supportBox d R L,
          (R ^ (((d : ℝ) - 4) / 2) * Sandpile.Support.cellMass R φ x) * green d x z) ^ 2
        ≤ C := by
  classical
  obtain ⟨-, -, -, ⟨C₁, hC₁, hgreen⟩, -⟩ := hGreen d hd
  refine ⟨C₁ * ((∫ z, |φ z|) * Cφ * ((d : ℝ) * 2 ^ d) * (2 * L + 5) ^ 4), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ ∫ z, |φ z| := integral_nonneg fun z => abs_nonneg _
    have h2 : (0 : ℝ) ≤ (2 * L + 5) ^ 4 := by positivity
    have h3 : (0 : ℝ) ≤ (d : ℝ) * 2 ^ d := by positivity
    exact mul_nonneg hC₁.le (mul_nonneg (mul_nonneg (mul_nonneg h1 hCφ) h3) h2)
  · intro R hR
    set A : ℝ := R ^ (((d : ℝ) - 4) / 2) with hA
    set s : Finset (Site d) := Sandpile.Support.supportBox d R L with hs
    set a : Site d → ℝ := fun x => A * Sandpile.Support.cellMass R φ x with ha
    have hsq : ∀ z : Site d, (∑ x ∈ s, a x * green d x z) ^ 2
        = ∑ x ∈ s, ∑ y ∈ s, (a x * green d x z) * (a y * green d y z) := by
      intro z
      rw [sq, Finset.sum_mul_sum]
    have hsummable : ∀ x y : Site d,
        Summable fun z : Site d => (a x * green d x z) * (a y * green d y z) := by
      intro x y
      have hxy := (hgreen x y).1
      have : (fun z : Site d => (a x * green d x z) * (a y * green d y z))
          = fun z : Site d => (a x * a y) * (green d x z * green d y z) := by
        funext z; ring
      rw [this]
      exact hxy.mul_left _
    have hswap : ∑' z : Site d, (∑ x ∈ s, a x * green d x z) ^ 2
        = ∑ x ∈ s, ∑ y ∈ s, ∑' z : Site d, (a x * green d x z) * (a y * green d y z) := by
      rw [tsum_congr hsq]
      rw [Summable.tsum_finsetSum fun x _ =>
        (summable_sum fun y _ => hsummable x y)]
      exact Finset.sum_congr rfl fun x _ =>
        Summable.tsum_finsetSum fun y _ => hsummable x y
    have hterm : ∀ x ∈ s, ∀ y ∈ s,
        (∑' z : Site d, (a x * green d x z) * (a y * green d y z))
          ≤ |a x| * |a y| *
            (C₁ * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))) := by
      intro x _ y _
      have hfac : (fun z : Site d => (a x * green d x z) * (a y * green d y z))
          = fun z : Site d => (a x * a y) * (green d x z * green d y z) := by
        funext z; ring
      rw [hfac, (hgreen x y).1.tsum_mul_left]
      have hnn : (0 : ℝ) ≤ ∑' z : Site d, green d x z * green d y z :=
        tsum_nonneg fun z => mul_nonneg (green_nonneg x z) (green_nonneg y z)
      have hle : (∑' z : Site d, green d x z * green d y z)
          ≤ C₁ * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)) := (hgreen x y).2
      calc a x * a y * ∑' z : Site d, green d x z * green d y z
          ≤ |a x * a y| * ∑' z : Site d, green d x z * green d y z :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hnn
        _ = |a x| * |a y| * ∑' z : Site d, green d x z * green d y z := by rw [abs_mul]
        _ ≤ |a x| * |a y| *
              (C₁ * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))) :=
            mul_le_mul_of_nonneg_left hle (by positivity)
    have hkernel := sum_tested_kernel_le hd φ Cφ L hCφ hL hb hint R hR
    have habs : ∀ x : Site d, |a x| = A * |Sandpile.Support.cellMass R φ x| := by
      intro x
      rw [ha, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hR) _)]
    calc ∑' z : Site d, (∑ x ∈ s, a x * green d x z) ^ 2
        = ∑ x ∈ s, ∑ y ∈ s, ∑' z : Site d, (a x * green d x z) * (a y * green d y z) := hswap
      _ ≤ ∑ x ∈ s, ∑ y ∈ s, |a x| * |a y| *
            (C₁ * (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ))) :=
          Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hterm x hx y hy
      _ = C₁ * ∑ x ∈ s, ∑ y ∈ s, (A * |Sandpile.Support.cellMass R φ x|) *
            (A * |Sandpile.Support.cellMass R φ y|) *
            (1 + Sandpile.External.latticeNorm (x - y)) ^ (4 - (d : ℝ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [habs x, habs y]
          ring
      _ ≤ C₁ * ((∫ z, |φ z|) * Cφ * ((d : ℝ) * 2 ^ d) * (2 * L + 5) ^ 4) :=
          mul_le_mul_of_nonneg_left hkernel hC₁.le

end Sandpile
