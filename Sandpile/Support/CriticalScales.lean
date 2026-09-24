/-
The scales, the standardized coefficients, and the correlation matrix.

`thm:critical-toppling` tests the odometer against the membrane field at the
geometric times `n_j = N q^j`, standardized by their own standard deviations.
This file builds those coefficients, computes the covariance matrix of the
standardized fields, and shows that it is the correlation matrix of the Green
kernels: the variance of the one-site law cancels.
-/
import Sandpile.Support.FiniteCoord
import Sandpile.Support.GreenSup
import Sandpile.Support.Gram
import Sandpile.Support.Schur

open MeasureTheory ProbabilityTheory

namespace Sandpile

variable {d : ℕ}

noncomputable def greenSq (d n : ℕ) : ℝ := ∑' y : Site d, greenTime d n 0 y ^ 2

theorem greenSq_nonneg (d n : ℕ) : 0 ≤ greenSq d n := by
  rw [greenSq, tsum_greenTime_sq_eq_sum]
  exact Finset.sum_nonneg fun z _ => sq_nonneg _

theorem one_le_greenTime_diag {n : ℕ} (hn : 1 ≤ n) : (1 : ℝ) ≤ greenTime d n 0 0 := by
  show (1 : ℝ) ≤ ∑ k ∈ Finset.range n, heatKernel d k (0 : Site d) 0
  have h0 : heatKernel d 0 (0 : Site d) 0 = 1 := by
    simp [heatKernel, LatticeProb.LocalCLT.heatKernel]
  have := Finset.single_le_sum (f := fun k => heatKernel d k (0 : Site d) 0)
    (fun k _ => heatKernel_nonneg k 0 0) (Finset.mem_range.mpr (by omega : 0 < n))
  rw [h0] at this
  exact this

theorem one_le_greenSq {n : ℕ} (hn : 1 ≤ n) : (1 : ℝ) ≤ greenSq d n := by
  rw [greenSq, tsum_greenTime_sq_eq_sum]
  have hmem : (0 : Site d) ∈ boxFinset (0 : Site d) n := mem_boxFinset (by simp [boxDist_self])
  have := Finset.single_le_sum (f := fun z : Site d => greenTime d n 0 z ^ 2)
    (fun z _ => sq_nonneg _) hmem
  have h1 := one_le_greenTime_diag (d := d) hn
  nlinarith

theorem greenSq_pos {n : ℕ} (hn : 1 ≤ n) : 0 < greenSq d n :=
  lt_of_lt_of_le zero_lt_one (one_le_greenSq hn)

/-- `√Var(V_n(0))`, the standard deviation of the membrane field at the origin. -/
noncomputable def membraneSd (d : ℕ) (ν : Measure ℝ) (n : ℕ) : ℝ :=
  Real.sqrt (variance id ν * greenSq d n)

theorem membraneSd_pos (ν : Measure ℝ) (hvar : 0 < variance (id : ℝ → ℝ) ν)
    {n : ℕ} (hn : 1 ≤ n) : 0 < membraneSd d ν n :=
  Real.sqrt_pos.mpr (mul_pos hvar (greenSq_pos hn))

theorem membraneSd_eq (ν : Measure ℝ) (hvar : 0 ≤ variance (id : ℝ → ℝ) ν) (n : ℕ) :
    membraneSd d ν n = Real.sqrt (variance id ν) * Real.sqrt (greenSq d n) := by
  rw [membraneSd, Real.sqrt_mul hvar]

/-- The standardized coefficients `a_j(x) = g_{n_j}(0,x)/√Var(V_{n_j}(0))` of
`sandpile.tex:1762-1769`, read through an enumeration of a finite set of sites. -/
noncomputable def stdCoeff (d : ℕ) (ν : Measure ℝ) (s : Finset (Site d)) {m : ℕ}
    (ns : Fin m → ℕ) (i : Fin s.card) (j : Fin m) : ℝ :=
  greenTime d (ns j) 0 (siteEnum s i) / membraneSd d ν (ns j)

/-- **The covariance matrix of the standardized membrane fields is the
correlation matrix of the Green kernels**: the variance of the one-site law
cancels. -/
theorem gram_stdCoeff (ν : Measure ℝ) (hvar : 0 < variance (id : ℝ → ℝ) ν)
    {s : Finset (Site d)} {m : ℕ} {ns : Fin m → ℕ} (hns : ∀ j, 1 ≤ ns j)
    (hsub : ∀ j, boxFinset (0 : Site d) (ns j) ⊆ s) (j k : Fin m) :
    Sandpile.External.BerryEsseen.gram ν (stdCoeff d ν s ns) j k
      = (∑' z : Site d, greenTime d (ns j) 0 z * greenTime d (ns k) 0 z) /
        (Real.sqrt (greenSq d (ns j)) * Real.sqrt (greenSq d (ns k))) := by
  have hQj : 0 < greenSq d (ns j) := greenSq_pos (hns j)
  have hQk : 0 < greenSq d (ns k) := greenSq_pos (hns k)
  have hsj : 0 < Real.sqrt (greenSq d (ns j)) := Real.sqrt_pos.mpr hQj
  have hsk : 0 < Real.sqrt (greenSq d (ns k)) := Real.sqrt_pos.mpr hQk
  have hmj : 0 < membraneSd d ν (ns j) := membraneSd_pos ν hvar (hns j)
  have hmk : 0 < membraneSd d ν (ns k) := membraneSd_pos ν hvar (hns k)
  have hsum : ∑ i : Fin s.card, stdCoeff d ν s ns i j * stdCoeff d ν s ns i k
      = (∑' z : Site d, greenTime d (ns j) 0 z * greenTime d (ns k) 0 z) /
          (membraneSd d ν (ns j) * membraneSd d ν (ns k)) := by
    rw [eq_div_iff (by positivity), Finset.sum_mul,
      ← sum_siteEnum_greenTime_mul (hsub j) (m := ns k) (y := (0 : Site d))]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold stdCoeff
    field_simp
  have hprod : membraneSd d ν (ns j) * membraneSd d ν (ns k)
      = variance (id : ℝ → ℝ) ν *
        (Real.sqrt (greenSq d (ns j)) * Real.sqrt (greenSq d (ns k))) := by
    rw [membraneSd_eq ν hvar.le, membraneSd_eq ν hvar.le]
    calc Real.sqrt (variance (id : ℝ → ℝ) ν) * Real.sqrt (greenSq d (ns j)) *
          (Real.sqrt (variance (id : ℝ → ℝ) ν) * Real.sqrt (greenSq d (ns k)))
        = (Real.sqrt (variance (id : ℝ → ℝ) ν) * Real.sqrt (variance (id : ℝ → ℝ) ν)) *
            (Real.sqrt (greenSq d (ns j)) * Real.sqrt (greenSq d (ns k))) := by ring
      _ = variance (id : ℝ → ℝ) ν *
            (Real.sqrt (greenSq d (ns j)) * Real.sqrt (greenSq d (ns k))) := by
          rw [Real.mul_self_sqrt hvar.le]
  rw [Sandpile.External.BerryEsseen.gram]
  show variance (id : ℝ → ℝ) ν * ∑ i, stdCoeff d ν s ns i j * stdCoeff d ν s ns i k = _
  rw [hsum, hprod]
  field_simp

end Sandpile
