/-
The two points of `ℝ^d` at which the local central limit theorem is applied.

The double space sum of `prop:weighted-membrane-limit` is an integral over pairs
`(u,v)` of points of space, and the sites the transition kernel is read at are
the mesh sites `⌊Ru⌋` and `⌊Rv⌋`.  This file records what
`Sandpile.Support.tendsto_scaled_time_sum_of_localCLT` asks of them: that the
Euclidean distance between the two sites is `O(R)`, which it is because a test
function is supported in a ball, and that the squared distance between their
rescalings converges to the squared distance between `u` and `v`, which it does
because the mesh point converges to the point.
-/
import Sandpile.Support.ContLcltStep
import Sandpile.Support.ContMeshPoint

open MeasureTheory Filter Topology

namespace Sandpile.Support

open Sandpile Sandpile.Continuum

variable {d : ℕ}

theorem latticeDist_eq_mul_norm {R : ℝ} (hR : 0 < R) (x y : Site d) :
    Sandpile.External.Lclt.latticeDist x y
      = R * ‖Sandpile.External.Lclt.scaledSite R x
          - Sandpile.External.Lclt.scaledSite R y‖ := by
  have hc : ∀ i : Fin d, (Sandpile.External.Lclt.scaledSite R x
      - Sandpile.External.Lclt.scaledSite R y) i = ((x i - y i : ℤ) : ℝ) / R := by
    intro i
    show ((x i : ℤ) : ℝ) / R - ((y i : ℤ) : ℝ) / R = ((x i - y i : ℤ) : ℝ) / R
    push_cast
    ring
  have hA : (0:ℝ) ≤ ∑ i : Fin d, ((x i - y i : ℤ) : ℝ) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsum : ∑ i : Fin d, ‖(Sandpile.External.Lclt.scaledSite R x
      - Sandpile.External.Lclt.scaledSite R y) i‖ ^ 2
      = (∑ i : Fin d, ((x i - y i : ℤ) : ℝ) ^ 2) / R ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc i, Real.norm_eq_abs, sq_abs]
    field_simp
  rw [EuclideanSpace.norm_eq, hsum, Real.sqrt_div hA, Real.sqrt_sq hR.le]
  show Real.sqrt (∑ i : Fin d, ((x i - y i : ℤ) : ℝ) ^ 2)
    = R * (Real.sqrt (∑ i : Fin d, ((x i - y i : ℤ) : ℝ) ^ 2) / R)
  field_simp

/-- The rescaling of the mesh site of a point is the mesh point. -/
theorem scaledSite_floor_eq_meshPoint (R : ℝ) (u : Space d) :
    Sandpile.External.Lclt.scaledSite R (fun i => ⌊R * u i⌋) = meshPoint R u := rfl

theorem tendsto_norm_sq_meshPoint (u v : Space d) :
    Tendsto (fun R : ℝ => ‖meshPoint R u - meshPoint R v‖ ^ 2) atTop (𝓝 (‖u - v‖ ^ 2)) := by
  have hsub : Tendsto (fun R : ℝ => meshPoint R u - meshPoint R v) atTop (𝓝 (u - v)) :=
    (tendsto_meshPoint u).sub (tendsto_meshPoint v)
  exact (hsub.norm).pow 2

theorem latticeDist_floor_le {R : ℝ} (hR : 1 ≤ R) {L : ℝ} {u v : Space d}
    (hu : ‖u‖ ≤ L) (hv : ‖v‖ ≤ L) :
    Sandpile.External.Lclt.latticeDist (fun i => ⌊R * u i⌋) (fun i => ⌊R * v i⌋)
      ≤ (2 * L + 2 * Real.sqrt d) * R := by
  have hR0 : (0:ℝ) < R := lt_of_lt_of_le one_pos hR
  have hmu : ‖meshPoint R u - u‖ ≤ Real.sqrt d / R := norm_meshPoint_sub_le hR0 u
  have hmv : ‖meshPoint R v - v‖ ≤ Real.sqrt d / R := norm_meshPoint_sub_le hR0 v
  have hsplit : ‖meshPoint R u - meshPoint R v‖
      ≤ ‖meshPoint R u - u‖ + ‖u - v‖ + ‖v - meshPoint R v‖ := by
    calc ‖meshPoint R u - meshPoint R v‖
        = ‖(meshPoint R u - u) + (u - v) + (v - meshPoint R v)‖ := by congr 1; abel
      _ ≤ ‖(meshPoint R u - u) + (u - v)‖ + ‖v - meshPoint R v‖ := norm_add_le _ _
      _ ≤ ‖meshPoint R u - u‖ + ‖u - v‖ + ‖v - meshPoint R v‖ := by
          have := norm_add_le (meshPoint R u - u) (u - v)
          linarith
  have hvm : ‖v - meshPoint R v‖ = ‖meshPoint R v - v‖ := norm_sub_rev _ _
  have huv : ‖u - v‖ ≤ 2 * L := le_trans (norm_sub_le u v) (by linarith)
  have hsq : (0:ℝ) ≤ Real.sqrt d := Real.sqrt_nonneg _
  have hkey : ‖meshPoint R u - meshPoint R v‖ ≤ 2 * L + 2 * (Real.sqrt d / R) := by
    rw [hvm] at hsplit
    linarith
  rw [latticeDist_eq_mul_norm hR0]
  rw [scaledSite_floor_eq_meshPoint, scaledSite_floor_eq_meshPoint]
  have hfin : R * (2 * L + 2 * (Real.sqrt d / R)) = 2 * L * R + 2 * Real.sqrt d := by
    field_simp
  calc R * ‖meshPoint R u - meshPoint R v‖ ≤ R * (2 * L + 2 * (Real.sqrt d / R)) :=
        mul_le_mul_of_nonneg_left hkey hR0.le
    _ = 2 * L * R + 2 * Real.sqrt d := hfin
    _ ≤ (2 * L + 2 * Real.sqrt d) * R := by nlinarith

/-- **The scaled double time sum read at the mesh sites of two points of a ball
converges to the double time integral against the Brownian kernel at those two
points.**  This is the local central limit theorem and the Riemann-sum argument
of `sandpile.tex:4719-4724` at a fixed pair of points of space; what remains of
that sentence is the passage from the fixed pair to the double space integral,
which is dominated convergence, and the removal of the cutoff `δ`. -/
theorem tendsto_scaled_time_sum_meshSite
    (hLCLT : Sandpile.External.LocalCLT)
    (hd : 1 ≤ d) {T δ L : ℝ} (hT : 0 < T) (hδ : 0 < δ) (hδT : δ < T)
    (g : ℝ → ℝ) (hg : Continuous g) (Q : ℝ) (hQ0 : 0 ≤ Q) (hQ : ∀ r, |g r| ≤ Q)
    (hg0 : ∀ r : ℝ, r < δ → g r = 0)
    {u v : Space d} (hu : ‖u‖ ≤ L) (hv : ‖v‖ ≤ L) :
    Tendsto (fun R : ℝ => R ^ ((d : ℝ) - 4) *
        ∑ a ∈ Finset.range ⌊R ^ 2 * T⌋₊, ∑ b ∈ Finset.range ⌊R ^ 2 * T⌋₊,
          g ((a : ℝ) * (R ^ 2)⁻¹) * g ((b : ℝ) * (R ^ 2)⁻¹) *
            Sandpile.heatKernel d (a + b) (fun i => ⌊R * u i⌋) (fun i => ⌊R * v i⌋))
      atTop (𝓝 (∫ r in Set.Ico (0 : ℝ) T, ∫ r' in Set.Ico (0 : ℝ) T,
        g r * g r' * heatKernelBM d (max (r + r') (2 * δ)) u v)) := by
  refine tendsto_scaled_time_sum_of_localCLT (C₀ := 2 * L + 2 * Real.sqrt d)
    hLCLT hd hT hδ hδT g hg Q hQ0 hQ hg0 u v
    (fun R => fun i => ⌊R * u i⌋) (fun R => fun i => ⌊R * v i⌋) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
    exact latticeDist_floor_le hR hu hv
  · simp only [scaledSite_floor_eq_meshPoint]
    exact tendsto_norm_sq_meshPoint u v

end Sandpile.Support
