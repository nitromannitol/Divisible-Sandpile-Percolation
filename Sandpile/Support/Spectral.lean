/-
The covariance matrix at the geometric scales is nearly isotropic.

The diagonal of the correlation matrix is one, its rows carry off-diagonal mass
at most `12 C q^{-1/4}`, and the Schur test turns that into the two-sided bound
on the quadratic form that the Gaussian persistence estimate of
`sandpile.tex:1745-1758` needs.  The ratio `q^{-1/4}` can be made as small as
one likes, so the tolerance is whatever the persistence estimate asks for.
-/
import Sandpile.Support.CorrelationRow
import Sandpile.Support.GaussPersist

open MeasureTheory ProbabilityTheory
open Sandpile.External.BerryEsseen

namespace Sandpile

variable {d : ℕ}

theorem gram_stdCoeff_diag (ν : Measure ℝ) (hvar : 0 < variance (id : ℝ → ℝ) ν)
    {s : Finset (Site d)} {m : ℕ} {ns : Fin m → ℕ} (hns : ∀ j, 1 ≤ ns j)
    (hsub : ∀ j, boxFinset (0 : Site d) (ns j) ⊆ s) (j : Fin m) :
    Sandpile.External.BerryEsseen.gram ν (stdCoeff d ν s ns) j j = 1 := by
  have hQ : 0 < greenSq d (ns j) := greenSq_pos (hns j)
  rw [gram_stdCoeff ν hvar hns hsub j j]
  have hnum : (∑' z : Site d, greenTime d (ns j) 0 z * greenTime d (ns j) 0 z)
      = greenSq d (ns j) := by
    rw [greenSq]
    exact tsum_congr fun z => by ring
  rw [hnum, Real.mul_self_sqrt hQ.le, div_self (ne_of_gt hQ)]

/-- **The covariance matrix of the standardized membrane fields at the scales
`N q^j` is nearly isotropic** once `q` is large. -/
theorem gram_quadForm_bounds (ν : Measure ℝ) (hvar : 0 < variance (id : ℝ → ℝ) ν)
    {C : ℝ} (hC : 0 ≤ C)
    (hcorr : ∀ m n : ℕ, 1 ≤ m → m ≤ n →
      (∑' x : Site d, greenTime d m 0 x * greenTime d n 0 x) ≤
        C * Sandpile.External.Variance.corrRate d m n *
          Real.sqrt (∑' x : Site d, greenTime d m 0 x ^ 2) *
          Real.sqrt (∑' x : Site d, greenTime d n 0 x ^ 2))
    (hd : 1 ≤ d) (hd3 : d ≤ 3) {q N : ℕ} (hq : 1 ≤ q) (hN : 1 ≤ N)
    (hr : geomRatio q ≤ 1 / 2) {ρ : ℝ} (hρ : 12 * C * geomRatio q ≤ ρ)
    {m : ℕ} {s : Finset (Site d)}
    (hsub : ∀ j : Fin m, boxFinset (0 : Site d) (N * q ^ (j : ℕ)) ⊆ s)
    (v : Fin m → ℝ) :
    (1 - ρ) * ∑ j, v j ^ 2 ≤
        quadForm (Sandpile.External.BerryEsseen.gram ν
          (stdCoeff d ν s (fun j : Fin m => N * q ^ (j : ℕ)))) v ∧
      quadForm (Sandpile.External.BerryEsseen.gram ν
          (stdCoeff d ν s (fun j : Fin m => N * q ^ (j : ℕ)))) v
        ≤ (1 + ρ) * ∑ j, v j ^ 2 := by
  set ns : Fin m → ℕ := fun j => N * q ^ (j : ℕ) with hnsdef
  have hns : ∀ j : Fin m, 1 ≤ ns j := by
    intro j
    have h1 : 1 ≤ q ^ (j : ℕ) := Nat.one_le_pow _ _ (by omega)
    calc 1 = 1 * 1 := by ring
      _ ≤ N * q ^ (j : ℕ) := Nat.mul_le_mul hN h1
  set S := Sandpile.External.BerryEsseen.gram ν (stdCoeff d ν s ns) with hSdef
  have hsymm : ∀ a b : Fin m, S a b = S b a := by
    intro a b
    rw [hSdef]
    exact gram_symm ν _ a b
  have hdiag : ∀ j : Fin m, S j j = 1 := by
    intro j
    rw [hSdef]
    exact gram_stdCoeff_diag ν hvar hns hsub j
  have hrow : ∀ j : Fin m, offRow S j ≤ ρ := by
    intro j
    exact le_trans (gram_offRow_geom_le ν hvar hC hcorr hd hd3 hq hN hr hsub j) hρ
  have habs := abs_quadForm_sub_le S hsymm hdiag ρ hrow v
  rw [abs_le] at habs
  constructor
  · nlinarith [habs.1]
  · nlinarith [habs.2]

end Sandpile

namespace Sandpile

/-- The geometric ratio can be made as small as one likes by taking `q` large. -/
theorem exists_geomRatio_le {ε : ℝ} (hε : 0 < ε) :
    ∃ q : ℕ, 1 ≤ q ∧ geomRatio q ≤ ε := by
  set K : ℕ := max 1 ⌈ε⁻¹ ^ 4⌉₊ with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKge : ε⁻¹ ^ 4 ≤ (K : ℝ) := by
    have h1 : ε⁻¹ ^ 4 ≤ (⌈ε⁻¹ ^ 4⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈ε⁻¹ ^ 4⌉₊ : ℝ) ≤ (K : ℝ) :=
      Nat.cast_le.mpr (le_max_right 1 ⌈ε⁻¹ ^ (4 : ℕ)⌉₊)
    linarith
  refine ⟨K, hK1, ?_⟩
  have hK0 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK1
  have hεinv : (0 : ℝ) < ε⁻¹ := by positivity
  have hroot : ε⁻¹ ≤ (K : ℝ) ^ ((1 : ℝ) / 4) := by
    have h4 : (ε⁻¹ ^ 4 : ℝ) ^ ((1 : ℝ) / 4) = ε⁻¹ := by
      rw [← Real.rpow_natCast ε⁻¹ 4, ← Real.rpow_mul hεinv.le]
      norm_num
    calc ε⁻¹ = (ε⁻¹ ^ 4 : ℝ) ^ ((1 : ℝ) / 4) := h4.symm
      _ ≤ (K : ℝ) ^ ((1 : ℝ) / 4) :=
          Real.rpow_le_rpow (by positivity) hKge (by norm_num)
  have hneg : geomRatio K = ((K : ℝ) ^ ((1 : ℝ) / 4))⁻¹ := by
    rw [geomRatio, show (-(1 : ℝ) / 4) = -((1 : ℝ) / 4) by ring, Real.rpow_neg hK0.le]
  rw [hneg]
  rw [inv_le_comm₀ (Real.rpow_pos_of_pos hK0 _) hε]
  exact hroot

end Sandpile
