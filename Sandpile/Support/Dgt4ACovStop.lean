import Sandpile.Support.Dgt4ACovSuper
import Sandpile.Support.ExitGreen

/-!
# Optional stopping for the Green covariance

**`eq:dgt4-gaussian-covariance-sampling`** (`sandpile.tex:5115-5123`): "Since
`(I-P)\Cov(V_\infty(\cdot),V_\infty(0))(x)=\Var(\zeta(0))G(x,0)\geq0`, optional stopping gives
`0\leq\E_x\Cov(V_\infty(X_\tau),V_\infty(0))\leq\Cov(V_\infty(x),V_\infty(0))` for every
stopping time `\tau`."

`Support/Dgt4ACovSuper.lean` proved the superharmonicity. The optional stopping
(`integral_stopped_super_le`) is a corollary of the Poisson identity
`integral_stopped_poisson` of `Support/ExitGreen.lean`, which holds at every field with no
growth hypothesis: the stopped value plus the sum of `(I-P)f` along the path is the value at
the start, and the sum is nonnegative exactly when `f` is superharmonic. The lower bound is
the nonnegativity of the Green covariance (`greenCovariance_nonneg`).

The covariance is also bounded, uniformly in the site (`greenCovariance_le`): the
Cauchy-Schwarz inequality in `\ell^2` and the translation invariance `G(x,z)=G(0,z-x)`
(`norm_greenLp_eq`) give `\sum_zG(x,z)G(0,z)\leq\sum_zG(0,z)^2`, which is what makes every
integral here finite. `integral_stopped_greenCovariance_le` and
`integrable_stopped_greenCovariance` package these facts into the display above.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- **Optional stopping for a superharmonic field**: the expectation at a bounded
stopping time is at most the value at the start.  No growth hypothesis is needed,
because the Poisson identity already holds at every field. -/
theorem integral_stopped_super_le (hd : 1 ≤ d) (x : Site d) (f : Site d → ℝ)
    (hsuper : ∀ y, avg f y ≤ f y) (t : ℕ)
    {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) (hτt : ∀ X, τ X ≤ t) :
    (∫ X, f (X (τ X)) ∂walkLaw d x) ≤ f x := by
  have hp := integral_stopped_poisson hd x f t hτ hτt
  rw [integral_add (integrable_stoppedScenery_walk hd x (fun y => f y - avg f y) t hτ hτt)
    (integrable_stopped_value hd x t (fun _ => f) hτ hτt)] at hp
  have hnn : (0 : ℝ) ≤ ∫ X, sceneryPartialSum (fun y => f y - avg f y) (τ X) X ∂walkLaw d x := by
    refine integral_nonneg fun X => Finset.sum_nonneg fun k _ => ?_
    have := hsuper (X k)
    linarith
  linarith

/-- The Green coefficient family has the same norm at every site, by the translation
invariance `G(x,z)=G(0,z-x)`. -/
theorem norm_greenLp_eq (hd : 5 ≤ d) (x : Site d) :
    ‖greenLp d hd x‖ = ‖greenLp d hd (0 : Site d)‖ := by
  have hx := inner_greenLp hd x x
  have h0 := inner_greenLp hd (0 : Site d) 0
  rw [real_inner_self_eq_norm_sq] at hx h0
  have hshift : (∑' z : Site d, green d x z * green d x z)
      = ∑' z : Site d, green d 0 z * green d 0 z := by
    have he : ∀ z : Site d, green d x z * green d x z
        = (fun w : Site d => green d 0 w * green d 0 w) (z - x) := by
      intro z
      rw [green_shift x z]
    rw [tsum_congr he]
    exact (Equiv.subRight x).tsum_eq (fun w : Site d => green d 0 w * green d 0 w)
  have hxy := hx.trans (hshift.trans h0.symm)
  nlinarith [norm_nonneg (greenLp d hd x), norm_nonneg (greenLp d hd (0 : Site d))]

/-- `\Cov(V_\infty(x),V_\infty(0))\leq\Var(V_\infty(0))`, by Cauchy-Schwarz. -/
theorem greenCovariance_le (hd : 5 ≤ d) (x : Site d) :
    (∑' z : Site d, green d x z * green d 0 z) ≤ greenSqSum d := by
  have hinner := inner_greenLp hd x (0 : Site d)
  have hcs : (inner ℝ (greenLp d hd x) (greenLp d hd (0 : Site d)) : ℝ)
      ≤ ‖greenLp d hd x‖ * ‖greenLp d hd (0 : Site d)‖ := real_inner_le_norm _ _
  rw [hinner, norm_greenLp_eq hd x] at hcs
  have hsq := norm_greenLp_sq hd
  nlinarith [hcs, hsq, norm_nonneg (greenLp d hd (0 : Site d))]

/-- The Green covariance is nonnegative. -/
theorem greenCovariance_nonneg (x : Site d) :
    0 ≤ ∑' z : Site d, green d x z * green d 0 z :=
  tsum_nonneg fun _ => mul_nonneg (green_nonneg _ _) (green_nonneg _ _)

/-- **`eq:dgt4-gaussian-covariance-sampling`** (`sandpile.tex:5113-5117`):
`0\leq\E_x\Cov(V_\infty(X_\tau),V_\infty(0))\leq\Cov(V_\infty(x),V_\infty(0))` for every
bounded stopping time, in the normalisation where the one-site variance of the scenery is
one. -/
theorem integral_stopped_greenCovariance_le (hd : 5 ≤ d) (x : Site d) (t : ℕ)
    {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) (hτt : ∀ X, τ X ≤ t) :
    0 ≤ (∫ X, (∑' z : Site d, green d (X (τ X)) z * green d 0 z) ∂walkLaw d x) ∧
      (∫ X, (∑' z : Site d, green d (X (τ X)) z * green d 0 z) ∂walkLaw d x)
        ≤ ∑' z : Site d, green d x z * green d 0 z := by
  refine ⟨integral_nonneg fun X => greenCovariance_nonneg _, ?_⟩
  exact integral_stopped_super_le (by omega) x
    (fun w => ∑' z : Site d, green d w z * green d 0 z)
    (fun y => avg_greenCovariance_le hd y) t hτ hτt

/-- The Green covariance is integrable at a bounded stopping time. -/
theorem integrable_stopped_greenCovariance (hd : 5 ≤ d) (x : Site d) (t : ℕ)
    {τ : (ℕ → Site d) → ℕ} (hτ : IsWalkStopping τ) (hτt : ∀ X, τ X ≤ t) :
    Integrable (fun X : ℕ → Site d => ∑' z : Site d, green d (X (τ X)) z * green d 0 z)
      (walkLaw d x) :=
  integrable_stopped_value (by omega) x t
    (fun _ w => ∑' z : Site d, green d w z * green d 0 z) hτ hτt

end Sandpile
