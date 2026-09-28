import LatticeProb.Walk.ExteriorDirichlet
import LatticeProb.Walk.Range
import Sandpile.Walk
import Sandpile.External.GaussianUpperProved

/-!
# The hitting probability of the origin and the exterior Dirichlet problem

`sandpile.tex:4924-4929` identifies the limit of `E w_n(x)/E u_n(0)` as the unique bounded
solution of the exterior Dirichlet problem on `ℤ^d ∖ {0}`, and identifies that solution with
`1 - G(x,0)/G(0,0)` using the hitting probability `P_x(τ_0 < ∞) = G(x,0)/G(0,0)`. Both facts are
already theorems of the shared library; this module only transports them across the two
identifications of the walk and of the Green function used in the paper's vocabulary.
-/

open MeasureTheory
open scoped ENNReal

namespace Sandpile.External.Sec16

/-- The two walk laws are the same measure. -/
theorem walkLaw_eq (d : ℕ) (x : Sandpile.Site d) :
    Sandpile.walkLaw d x = LatticeProb.siteWalkLaw d x := rfl

/-- The Green function of the paper is the library's, read at the difference. -/
theorem green_eq (d : ℕ) (x y : Sandpile.Site d) :
    Sandpile.green d x y = LatticeProb.srwGreenInf d (x - y) :=
  tsum_congr fun k => Sandpile.External.heatKernel_eq_srwHeat d k x y

/-- **The hitting probability of the origin.**  `P_x(τ_0 < ∞) = G(x,0)/G(0,0)`
for the simple random walk on `ℤ^d` with `d ≥ 3`. -/
theorem hitting_probability (d : ℕ) (hd : 3 ≤ d) [NeZero d] (x : Sandpile.Site d) :
    Sandpile.walkLaw d x {X : ℕ → Sandpile.Site d | ∃ j : ℕ, X j = 0}
      = ENNReal.ofReal (Sandpile.green d x 0 / Sandpile.green d 0 0) := by
  rw [walkLaw_eq, green_eq, green_eq, sub_zero, sub_zero]
  exact LatticeProb.siteWalkLaw_hitOrigin_eq_green_ratio hd x

/-- **Uniqueness for the exterior Dirichlet problem on `ℤ^d ∖ {0}`.** -/
theorem exterior_dirichlet (d : ℕ) (hd : 3 ≤ d) [NeZero d] {f : Sandpile.Site d → ℝ}
    (hharm : ∀ x : Sandpile.Site d, x ≠ 0 →
      (∑ i : Fin d, (f (x + Sandpile.unit i) + f (x - Sandpile.unit i))) / (2 * (d : ℝ)) = f x)
    (hzero : f 0 = 0)
    (hlim : ∀ ε : ℝ, 0 < ε → ∃ R : ℕ, ∀ x : Sandpile.Site d,
      R ≤ LatticeProb.graphNorm x → |f x - 1| ≤ ε) :
    ∀ x : Sandpile.Site d, f x = 1 - Sandpile.green d x 0 / Sandpile.green d 0 0 := by
  intro x
  rw [green_eq, green_eq, sub_zero, sub_zero]
  exact LatticeProb.exterior_dirichlet_unique hd hharm hzero hlim x

/-- The return probability of the origin. -/
theorem return_probability (d : ℕ) (hd : 3 ≤ d) :
    (∑ i : Fin d, (LatticeProb.srwHitProb d (Sandpile.unit i)
        + LatticeProb.srwHitProb d (-Sandpile.unit i))) / (2 * (d : ℝ))
      = 1 - 1 / Sandpile.green d 0 0 := by
  have h := LatticeProb.walkOp_srwHitProb_origin (d := d) hd
  rw [green_eq, sub_zero]
  rw [LatticeProb.walkOp, LatticeProb.nbrSum] at h
  simpa using h

end Sandpile.External.Sec16
