/-
`\Theta_n` at the conditioned level, and its Lipschitz constant for the `\ell^2` distance of
the residual (`sandpile.tex:5266-5271`).

`\Theta_n=P^{k_n+1}(V_\infty-u_{n-k_n}+\E u_n(0))(0)` is read here as a function of the
residual field of the conditioning, at a fixed level.  The conditioned scenery is
`\zeta=c(r+se)`, so a move of the residual by `\ell^2` distance `\sqrt M` moves the scenery
by `|c|\sqrt M`, and the additive constant `\E u_n(0)` passes through the averages
untouched.  With the sharp constant of `Support/Dgt4AConcSharp.lean` this gives the
Lipschitz constant `|c|\,\|\sum_{j\geq k_n+1}p_j(0,\cdot)\|`, the square root of the
"Gaussian concentration proxy" of `sandpile.tex:5269`.
-/
import Sandpile.Support.Dgt4AConcSharp
import Sandpile.Support.Dgt4AShiftLip

open MeasureTheory Filter Topology

open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The iterated average of a function shifted by a constant. -/
theorem avg_iterate_add_const (hd : 1 ≤ d) (f : Site d → ℝ) (a : ℝ) (j : ℕ) (x : Site d) :
    (avg^[j] (fun y => f y + a)) x = (avg^[j] f) x + a := by
  induction j generalizing x with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [show avg (avg^[k] fun y => f y + a) x = avg (fun y => (avg^[k] f) y + a) x from
        congrArg (fun u => avg u x) (funext fun y => ih y)]
      rw [Sandpile.avg_add (avg^[k] f) (fun _ => a) x]
      congr 1
      exact LatticeProb.walkOp_const hd a x

/-- `\Theta_n` at the conditioned level, as a function of the residual. -/
noncomputable def condTheta (d : ℕ) (hd : 5 ≤ d) (c s a : ℝ) (t j : ℕ)
    (r : Site d → ℝ) : ℝ :=
  (avg^[j] (fun y => infiniteGreenField (condScenery d hd c r s) y
    - odometerOf (condScenery d hd c r s) t y + a)) 0

/-- A move of the residual moves the conditioned scenery by `|c|` times as much. -/
theorem hasSum_sq_condScenery_sub (hd : 5 ≤ d) (c s : ℝ) (r r' : Site d → ℝ) (M : ℝ)
    (h : HasSum (fun z => (r z - r' z) ^ 2) M) :
    HasSum (fun z => (condScenery d hd c r s z - condScenery d hd c r' s z) ^ 2)
      (c ^ 2 * M) := by
  refine (h.mul_left (c ^ 2)).congr_fun fun z => ?_
  rw [condScenery_apply, condScenery_apply]
  ring

/-- **`\Theta_n` is Lipschitz in the residual for the `\ell^2` distance**, with constant
`|c|` times the `\ell^2` norm of the tail kernel (`sandpile.tex:5262-5264`). -/
theorem abs_condTheta_sub_le (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d)
    (c s a : ℝ) (t j : ℕ) (hj : 1 ≤ j) (r r' : Site d → ℝ) (M : ℝ)
    (hM : HasSum (fun z => (r z - r' z) ^ 2) M)
    (hconv : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun m => infiniteGreenFieldPartial m (condScenery d hd c r s) y) atTop (𝓝 L)) :
    |condTheta d hd c s a t j r - condTheta d hd c s a t j r'|
      ≤ |c| * ‖(tailKernelLp hGH hd hj : lp (fun _ : Site d => ℝ) 2)‖ * Real.sqrt M := by
  have hd1 : (1 : ℕ) ≤ d := by omega
  have hshift : HasSum
      (fun z => (condScenery d hd c r s z - condScenery d hd c r' s z) ^ 2) (c ^ 2 * M) :=
    hasSum_sq_condScenery_sub hd c s r r' M hM
  have hsharp := abs_avgIterate_deviation_sub_le_tailKernelLp hGH hd
    (condScenery d hd c r s) (condScenery d hd c r' s) (c ^ 2 * M) hshift hconv t j hj
  have hconst : ∀ ρ : Site d → ℝ,
      condTheta d hd c s a t j ρ
        = (avg^[j] (fun y => infiniteGreenField (condScenery d hd c ρ s) y
            - odometerOf (condScenery d hd c ρ s) t y)) 0 + a := by
    intro ρ
    exact avg_iterate_add_const hd1 _ a j 0
  have hsqrt : Real.sqrt (c ^ 2 * M) = |c| * Real.sqrt M := by
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  rw [hconst r, hconst r']
  have habs : |(avg^[j] (fun y => infiniteGreenField (condScenery d hd c r s) y
        - odometerOf (condScenery d hd c r s) t y)) 0 + a
      - ((avg^[j] (fun y => infiniteGreenField (condScenery d hd c r' s) y
        - odometerOf (condScenery d hd c r' s) t y)) 0 + a)|
      = |(avg^[j] (fun y => infiniteGreenField (condScenery d hd c r s) y
        - odometerOf (condScenery d hd c r s) t y)) 0
      - (avg^[j] (fun y => infiniteGreenField (condScenery d hd c r' s) y
        - odometerOf (condScenery d hd c r' s) t y)) 0| := by
    congr 1
    ring
  rw [habs]
  rw [hsqrt] at hsharp
  calc |(avg^[j] (fun y => infiniteGreenField (condScenery d hd c r s) y
        - odometerOf (condScenery d hd c r s) t y)) 0
      - (avg^[j] (fun y => infiniteGreenField (condScenery d hd c r' s) y
        - odometerOf (condScenery d hd c r' s) t y)) 0|
      ≤ ‖(tailKernelLp hGH hd hj : lp (fun _ : Site d => ℝ) 2)‖ * (|c| * Real.sqrt M) := hsharp
    _ = |c| * ‖(tailKernelLp hGH hd hj : lp (fun _ : Site d => ℝ) 2)‖ * Real.sqrt M := by ring

end Sandpile
