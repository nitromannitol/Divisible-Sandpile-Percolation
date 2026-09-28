import Sandpile.Continuum.Membrane

/-!
# Scaled Distance Comparison

The comparison between the Euclidean distance of two points of `ℝ^d` at scale
`R` and the lattice distance of the two sites they are embedded into by
`f^{(R)}(z) = f(⌊Rz⌋)`.  The embedding moves each coordinate by less than one,
so the two distances differ by at most `√d`, and the decaying powers
`(1 + ·)^{-β}` of the two are comparable with the constant `(1 + √d)^β`.  This
is the passage from the lattice hypothesis of `lem:sobolev-tightness` to the
continuum hypothesis of the tightness criterion it invokes.
-/

open MeasureTheory Filter Topology

namespace Sandpile.Support

/-- The Euclidean distance between two lattice sites, the notation `|x - y|` of
`sandpile.tex:678`. -/
noncomputable def siteDist {d : ℕ} (x y : Sandpile.Site d) : ℝ :=
  Real.sqrt (∑ i : Fin d, ((x i - y i : ℤ) : ℝ) ^ 2)

/-- The Euclidean distance at scale `R` exceeds the lattice distance of the
embedded sites by at most `√d`. -/
theorem scaled_dist_le_latticeDist_floor {d : ℕ} (R : ℝ) (hR : 0 ≤ R)
    (y y' : Sandpile.Continuum.Space d) :
    R * ‖y - y'‖ ≤
      Sandpile.Support.siteDist
        (fun i => ⌊R * y i⌋) (fun i => ⌊R * y' i⌋) + Real.sqrt d := by
  set w : Sandpile.Continuum.Space d :=
    (WithLp.toLp 2 (fun i => ((⌊R * y i⌋ - ⌊R * y' i⌋ : ℤ) : ℝ))) with hwdef
  have hw : Sandpile.Support.siteDist
      (fun i => ⌊R * y i⌋) (fun i => ⌊R * y' i⌋) = ‖w‖ := by
    rw [EuclideanSpace.norm_eq]
    simp [Sandpile.Support.siteDist, hwdef, sq_abs]
  have hcoord : ∀ i : Fin d, (R • (y - y') - w) i
      = Int.fract (R * y i) - Int.fract (R * y' i) := by
    intro i
    have h1 : (R • (y - y') - w) i
        = R * (y i - y' i) - ((⌊R * y i⌋ : ℝ) - (⌊R * y' i⌋ : ℝ)) := by
      simp [hwdef]
    rw [h1, Int.fract, Int.fract]
    ring
  have h2 : ‖R • (y - y') - w‖ ≤ Real.sqrt d := by
    rw [EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    calc ∑ i : Fin d, ‖(R • (y - y') - w) i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro i _
          rw [hcoord i, Real.norm_eq_abs, sq_abs]
          have ha := Int.fract_nonneg (R * y i)
          have hb := Int.fract_lt_one (R * y i)
          have hc := Int.fract_nonneg (R * y' i)
          have hd := Int.fract_lt_one (R * y' i)
          nlinarith
      _ = (d : ℝ) := by simp
  calc R * ‖y - y'‖ = ‖R • (y - y')‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hR]
    _ = ‖w + (R • (y - y') - w)‖ := by congr 1; abel
    _ ≤ ‖w‖ + ‖R • (y - y') - w‖ := norm_add_le _ _
    _ ≤ Sandpile.Support.siteDist
          (fun i => ⌊R * y i⌋) (fun i => ⌊R * y' i⌋) + Real.sqrt d := by
        rw [hw]; linarith

/-- The decaying power of one plus the lattice distance of the embedded sites
is dominated by `(1 + √d)^β` times the decaying power of one plus the Euclidean
distance at scale `R`. -/
theorem rpow_neg_latticeDist_le {d : ℕ} (β : ℝ) (hβ : 0 < β) (R : ℝ) (hR : 0 ≤ R)
    (y y' : Sandpile.Continuum.Space d) :
    (1 + Sandpile.Support.siteDist
        (fun i => ⌊R * y i⌋) (fun i => ⌊R * y' i⌋)) ^ (-β)
      ≤ (1 + Real.sqrt d) ^ β * (1 + R * ‖y - y'‖) ^ (-β) := by
  have hL : 0 ≤ Sandpile.Support.siteDist
      (fun i => ⌊R * y i⌋) (fun i => ⌊R * y' i⌋) := Real.sqrt_nonneg _
  have ht : 0 ≤ R * ‖y - y'‖ := mul_nonneg hR (norm_nonneg _)
  have hsd : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hstep := scaled_dist_le_latticeDist_floor R hR y y'
  have hx : (0 : ℝ) < (1 + R * ‖y - y'‖) / (1 + Real.sqrt (d : ℝ)) := by positivity
  have hxy : (1 + R * ‖y - y'‖) / (1 + Real.sqrt (d : ℝ))
      ≤ 1 + Sandpile.Support.siteDist
        (fun i => ⌊R * y i⌋) (fun i => ⌊R * y' i⌋) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hmain := Real.rpow_le_rpow_of_nonpos hx hxy (by linarith : -β ≤ 0)
  refine hmain.trans ?_
  rw [Real.div_rpow (by positivity) (by positivity),
    Real.rpow_neg (by positivity : (0:ℝ) ≤ 1 + Real.sqrt (d : ℝ)), div_inv_eq_mul, mul_comm]

end Sandpile.Support
