import Sandpile.Support.Dgt4ACondMeas

/-!
# The union bound of Step 3

The union bound of Step 3 (`sandpile.tex:5180-5189`): "A union bound and the Gaussian tail
estimate `eq:dgt4-gaussian-height-order` therefore give
`\P(\min_{0<|z|\leq k_n+1}(V_\infty(z)+\E u_n(0))\leq0\mid\cdot)\leq Ck_n^d
\exp\{-c(\E u_n(0))^2\}`." The union bound itself is subadditivity over the punctured box, which
needs no measurability; `Support/Dgt4ACorrGap.lean` supplies the conditional mean at each site of
the box and `Support/Dgt4ACondMeas.lean` the measurability that makes each term a probability.
What is left for the successor is the Gaussian tail at a single site of the residual law.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The event that the conditioned field fails to be positive somewhere on the punctured box
is the union over the box of the one-site events. -/
theorem setOf_exists_eq_biUnion (hd : 5 ≤ d) (c s a : ℝ) (m : ℕ) :
    {r : Site d → ℝ | ∃ z ∈ (boxFinset (0 : Site d) m).erase 0,
        infiniteGreenField (condScenery d hd c r s) z + a ≤ 0}
      = ⋃ z ∈ (boxFinset (0 : Site d) m).erase 0,
        {r : Site d → ℝ | infiniteGreenField (condScenery d hd c r s) z + a ≤ 0} := by
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]

/-- **The union bound of Step 3** (`sandpile.tex:5175-5178`). -/
theorem measure_exists_nonpos_le (hd : 5 ≤ d) (μ : Measure (Site d → ℝ)) (c s a : ℝ) (m : ℕ) :
    μ {r : Site d → ℝ | ∃ z ∈ (boxFinset (0 : Site d) m).erase 0,
        infiniteGreenField (condScenery d hd c r s) z + a ≤ 0}
      ≤ ∑ z ∈ (boxFinset (0 : Site d) m).erase 0,
        μ {r : Site d → ℝ | infiniteGreenField (condScenery d hd c r s) z + a ≤ 0} := by
  rw [setOf_exists_eq_biUnion hd c s a m]
  exact measure_biUnion_finset_le _ _

/-- The union bound in the form Step 3 uses it: a uniform one-site bound times the number of
sites of the box. -/
theorem measure_exists_nonpos_le_card (hd : 5 ≤ d) (μ : Measure (Site d → ℝ)) (c s a : ℝ)
    (m : ℕ) (p : ℝ≥0∞)
    (hp : ∀ z ∈ (boxFinset (0 : Site d) m).erase 0,
      μ {r : Site d → ℝ | infiniteGreenField (condScenery d hd c r s) z + a ≤ 0} ≤ p) :
    μ {r : Site d → ℝ | ∃ z ∈ (boxFinset (0 : Site d) m).erase 0,
        infiniteGreenField (condScenery d hd c r s) z + a ≤ 0}
      ≤ ((boxFinset (0 : Site d) m).erase 0).card * p := by
  refine (measure_exists_nonpos_le hd μ c s a m).trans ?_
  calc (∑ z ∈ (boxFinset (0 : Site d) m).erase 0,
          μ {r : Site d → ℝ | infiniteGreenField (condScenery d hd c r s) z + a ≤ 0})
      ≤ ∑ _z ∈ (boxFinset (0 : Site d) m).erase 0, p := Finset.sum_le_sum hp
    _ = ((boxFinset (0 : Site d) m).erase 0).card * p := by
        rw [Finset.sum_const, nsmul_eq_mul]

end Sandpile
