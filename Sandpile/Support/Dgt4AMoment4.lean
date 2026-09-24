/-
Uniform moments for `D_n`.  Its coordinate Lipschitz coefficients `2G(0,z)` are square
summable in `d\geq5` (`eq:dgt4-green-l2`, `sandpile.tex:1299-1300`) and do not depend on
`n`, so the product moment bound of `Support/Concentration.lean` gives a bound on the
`p`-th moment of `D_n` about its mean that is uniform in `n`.
-/
import Sandpile.Support.Dgt4ABoxDeviation
import Sandpile.Support.Concentration
import Sandpile.Support.LinGreenTail

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- A bound on the `p`-th moment of `D_n` about its mean, uniform in `n`. -/
theorem exists_sceneryDeviation_moment_bound (hd : 5 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] {p : ℝ} (hp : 2 ≤ p)
    (hmom : Integrable (fun z => |z| ^ p) ν) :
    ∃ M : ℝ, ∀ n : ℕ,
      (∫ ζ, |sceneryDeviation d ζ n
          - ∫ η, sceneryDeviation d η n ∂LatticeProb.iidLaw d ν| ^ p
          ∂LatticeProb.iidLaw d ν) ≤ M := by
  obtain ⟨C, hC, hb⟩ := Sandpile.exists_pick_moment_bound (d := d) hp
  refine ⟨C * LatticeProb.pairMoment ν p
    * (∑' z : Site d, (2 * Sandpile.green d 0 z) ^ 2) ^ (p / 2), ?_⟩
  intro n
  have hb0 : ∀ z : Site d, (0 : ℝ) ≤ 2 * Sandpile.green d 0 z := by
    intro z
    have := Sandpile.green_nonneg (0 : Site d) z
    linarith
  have h := hb ν inferInstance hmom (Sandpile.boxFinset (0 : Site d) (n + 1)).card
    (Sandpile.siteEnum (Sandpile.boxFinset (0 : Site d) (n + 1)))
    (Sandpile.siteEnum_injective _)
    (Sandpile.boxDeviation n) (Sandpile.measurable_boxDeviation n)
    (fun i => 2 * Sandpile.green d 0
      (Sandpile.siteEnum (Sandpile.boxFinset (0 : Site d) (n + 1)) i))
    (fun i => hb0 _)
    (Sandpile.abs_boxDeviation_update_le hd n)
  simp only [Sandpile.boxDeviation_pick n] at h
  refine h.trans ?_
  have hsummable : Summable fun z : Site d => (2 * Sandpile.green d 0 z) ^ 2 := by
    have h4 := (Sandpile.summable_green_sq hd 0).mul_left 4
    refine h4.congr fun z => ?_
    ring
  have hsum : (∑ i : Fin (Sandpile.boxFinset (0 : Site d) (n + 1)).card,
        (2 * Sandpile.green d 0
          (Sandpile.siteEnum (Sandpile.boxFinset (0 : Site d) (n + 1)) i)) ^ 2)
      ≤ ∑' z : Site d, (2 * Sandpile.green d 0 z) ^ 2 := by
    rw [Sandpile.sum_siteEnum (Sandpile.boxFinset (0 : Site d) (n + 1))
      (fun z => (2 * Sandpile.green d 0 z) ^ 2)]
    exact hsummable.sum_le_tsum _ (fun _ _ => sq_nonneg _)
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (Finset.sum_nonneg fun _ _ => sq_nonneg _) hsum (by linarith))
    (mul_nonneg hC.le (LatticeProb.pairMoment_nonneg ν p))

end Sandpile
