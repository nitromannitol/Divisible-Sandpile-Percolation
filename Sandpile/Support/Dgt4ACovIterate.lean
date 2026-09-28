import Sandpile.Support.Dgt4AShiftIterate
import Sandpile.Support.RefinedIncrement

/-!
# The one-step Lipschitz bound of Step 2

The one-step form of the Lipschitz bound of Step 2, which is what Step 4 uses to dominate the
integrand for `y\geq0` (`sandpile.tex:5275-5277`): "For `y\geq0`,
`eq:dgt4-gaussian-covariance-sampling` shows that `m_n` is one-Lipschitz in `y`".

The averaging operator is monotone and the Green covariance is superharmonic, so every iterate
of the covariance at the origin is at most its value there, which is `\Sigma^2=\sum_zG(0,z)^2`.
Feeding that into `Support/Dgt4AShiftIterate.lean` at `j=1` bounds the change of
`P(V_\infty-u_n)(0)` under a change `\delta` of the conditioned level by
`|c\delta|\,\|G(0,\cdot)\|=|\delta|\Sigma`, which in the variable `y` of Step 4 is exactly the
shift `\Sigma^2\delta/\E u_n(0)` of the conditioned level itself.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- The Green covariance at the origin is `\Sigma^2` in the normalisation where the one-site
variance of the scenery is one. -/
theorem greenCovariance_origin (d : ℕ) :
    (∑' z : Site d, green d 0 z * green d 0 z) = greenSqSum d :=
  tsum_congr fun z => by rw [sq]

/-- Every averaging iterate of the Green covariance at the origin is at most `\Sigma^2`. -/
theorem avgIterate_greenCovariance_le_greenSqSum (hd : 5 ≤ d) (j : ℕ) :
    (avg^[j] (fun y => ∑' z : Site d, green d y z * green d 0 z)) 0 ≤ greenSqSum d := by
  induction j with
  | zero => simpa using le_of_eq (greenCovariance_origin d)
  | succ m ih =>
      have hstep : (avg^[m + 1] (fun y => ∑' z : Site d, green d y z * green d 0 z)) 0
          ≤ (avg^[m] (fun y => ∑' z : Site d, green d y z * green d 0 z)) 0 := by
        rw [Function.iterate_succ_apply]
        exact avg_iterate_mono m (fun y => avg_greenCovariance_le hd y) 0
      exact hstep.trans ih

/-- **The one-step Lipschitz bound in the conditioned level**: the change of
`P(V_\infty-u_n)(0)` under a change `\delta` of the level is at most `|c\delta|\Sigma`. -/
theorem abs_avg_condScenery_deviation_le (hd : 5 ≤ d) (c : ℝ) {r : Site d → ℝ}
    (hr : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun m : ℕ => ∑ z ∈ boxFinset (0 : Site d) m, green d y z * r z) atTop (𝓝 L))
    (s δ : ℝ) (n j : ℕ) :
    |(avg^[j] (fun y => infiniteGreenField (condScenery d hd c r (s + δ)) y
          - odometerOf (condScenery d hd c r (s + δ)) n y)) 0
        - (avg^[j] (fun y => infiniteGreenField (condScenery d hd c r s) y
          - odometerOf (condScenery d hd c r s) n y)) 0|
      ≤ ‖greenLp d hd (0 : Site d)‖ * |c * δ| := by
  refine (abs_avgIterate_condScenery_deviation_le hd c hr s δ n j).trans ?_
  have hinv : (0 : ℝ) < ‖greenLp d hd (0 : Site d)‖⁻¹ := inv_pos.mpr (norm_greenLp_pos hd)
  have hcd : (0 : ℝ) ≤ |c * δ| := abs_nonneg _
  refine mul_le_mul_of_nonneg_right ?_ hcd
  have h1 : ‖greenLp d hd (0 : Site d)‖⁻¹
        * (avg^[j] (fun y => ∑' z : Site d, green d y z * green d 0 z)) 0
      ≤ ‖greenLp d hd (0 : Site d)‖⁻¹ * greenSqSum d :=
    mul_le_mul_of_nonneg_left (avgIterate_greenCovariance_le_greenSqSum hd j) hinv.le
  refine h1.trans_eq ?_
  rw [← norm_greenLp_sq hd]
  have hne : ‖greenLp d hd (0 : Site d)‖ ≠ 0 := (norm_greenLp_pos hd).ne'
  field_simp

/-- **The Lipschitz bound for the object of `eq:dgt4-gaussian-conditional-terminal`**
(`sandpile.tex:5089-5094`): the change of `P^j|V_\infty-u_n+a|(0)` under a change `\delta` of
the conditioned level obeys the same bound as the change of `P^j(V_\infty-u_n)(0)`, because
the absolute value is one-Lipschitz and the centring constant cancels. -/
theorem abs_avgIterate_abs_condScenery_deviation_le (hd : 5 ≤ d) (c : ℝ) {r : Site d → ℝ}
    (hr : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun m : ℕ => ∑ z ∈ boxFinset (0 : Site d) m, green d y z * r z) atTop (𝓝 L))
    (s δ a : ℝ) (n j : ℕ) :
    |(avg^[j] (fun y => |infiniteGreenField (condScenery d hd c r (s + δ)) y
            - odometerOf (condScenery d hd c r (s + δ)) n y + a|)) 0
        - (avg^[j] (fun y => |infiniteGreenField (condScenery d hd c r s) y
            - odometerOf (condScenery d hd c r s) n y + a|)) 0|
      ≤ ‖greenLp d hd (0 : Site d)‖⁻¹
          * (avg^[j] (fun y => ∑' z : Site d, green d y z * green d 0 z)) 0 * |c * δ| := by
  have h := Sandpile.abs_avgIterate_sub_le
    (fun y => |infiniteGreenField (condScenery d hd c r (s + δ)) y
      - odometerOf (condScenery d hd c r (s + δ)) n y + a|)
    (fun y => |infiniteGreenField (condScenery d hd c r s) y
      - odometerOf (condScenery d hd c r s) n y + a|) j 0
  refine h.trans ?_
  have hstep := Sandpile.avg_iterate_abs_le
    (fun y => |infiniteGreenField (condScenery d hd c r (s + δ)) y
      - odometerOf (condScenery d hd c r (s + δ)) n y + a|)
    (fun y => |infiniteGreenField (condScenery d hd c r s) y
      - odometerOf (condScenery d hd c r s) n y + a|)
    (fun y => ‖greenLp d hd (0 : Site d)‖⁻¹ * ∑' z : Site d, green d y z * green d 0 z)
    |c * δ| j
    (fun y => by
      refine le_trans (abs_abs_sub_abs_le_abs_sub _ _) ?_
      have hcong : (infiniteGreenField (condScenery d hd c r (s + δ)) y
            - odometerOf (condScenery d hd c r (s + δ)) n y + a)
          - (infiniteGreenField (condScenery d hd c r s) y
            - odometerOf (condScenery d hd c r s) n y + a)
          = (infiniteGreenField (condScenery d hd c r (s + δ)) y
            - odometerOf (condScenery d hd c r (s + δ)) n y)
          - (infiniteGreenField (condScenery d hd c r s) y
            - odometerOf (condScenery d hd c r s) n y) := by ring
      rw [hcong, mul_comm]
      exact abs_condScenery_sub_odometer_le hd c y n hr s δ)
  refine hstep.trans_eq ?_
  rw [avg_iterate_mul_const j ‖greenLp d hd (0 : Site d)‖⁻¹
    (fun y => ∑' z : Site d, green d y z * green d 0 z) 0]

/-- The Lipschitz coefficient of the conditioned level after `j` averaging steps, in the form
`Ck_n^{(4-d)/4}\Sigma` of `sandpile.tex:5115-5119`. -/
theorem exists_greenCovariance_iterate_bound (hGH : Sandpile.External.GreenBoundsHigh)
    (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 1 ≤ j →
      ‖greenLp d hd (0 : Site d)‖⁻¹
          * (avg^[j] (fun y => ∑' z : Site d, green d y z * green d 0 z)) 0
        ≤ C * ‖greenLp d hd (0 : Site d)‖ * (j : ℝ) ^ ((4 - (d : ℝ)) / 4) := by
  obtain ⟨C, hC, hbnd⟩ := exists_avgIterate_greenCovariance_le hGH hd
  refine ⟨C, hC, fun j hj => ?_⟩
  have hgs : ‖greenLp d hd (0 : Site d)‖ ^ 2 = greenSqSum d := norm_greenLp_sq hd
  have hinv : (0 : ℝ) < ‖greenLp d hd (0 : Site d)‖⁻¹ := inv_pos.mpr (norm_greenLp_pos hd)
  have hgsp : (0 : ℝ) < greenSqSum d := lt_of_lt_of_le zero_lt_one (one_le_greenSqSum hd)
  have hb := hbnd j hj
  rw [div_le_iff₀ hgsp] at hb
  have hcov : (avg^[j] (fun y => ∑' z : Site d, green d y z * green d 0 z)) 0
      ≤ C * (j : ℝ) ^ ((4 - (d : ℝ)) / 4) * greenSqSum d := le_trans (le_abs_self _) hb
  have h1 : ‖greenLp d hd (0 : Site d)‖⁻¹
        * (avg^[j] (fun y => ∑' z : Site d, green d y z * green d 0 z)) 0
      ≤ ‖greenLp d hd (0 : Site d)‖⁻¹ * (C * (j : ℝ) ^ ((4 - (d : ℝ)) / 4) * greenSqSum d) :=
    mul_le_mul_of_nonneg_left hcov hinv.le
  refine h1.trans_eq ?_
  rw [← hgs]
  have hne : ‖greenLp d hd (0 : Site d)‖ ≠ 0 := (norm_greenLp_pos hd).ne'
  field_simp

/-- **The Lipschitz constant of Step 2 for the object of
`eq:dgt4-gaussian-conditional-terminal`** (`sandpile.tex:5115-5119`), with a constant that
does not depend on the level, the residual, the centring or the number of updates. -/
theorem exists_avgIterate_abs_condScenery_deviation_le
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℝ) (r : Site d → ℝ),
      (∀ y : Site d, ∃ L : ℝ,
        Tendsto (fun m : ℕ => ∑ z ∈ boxFinset (0 : Site d) m, green d y z * r z) atTop (𝓝 L)) →
      ∀ (s δ a : ℝ) (n j : ℕ), 1 ≤ j →
        |(avg^[j] (fun y => |infiniteGreenField (condScenery d hd c r (s + δ)) y
                - odometerOf (condScenery d hd c r (s + δ)) n y + a|)) 0
            - (avg^[j] (fun y => |infiniteGreenField (condScenery d hd c r s) y
                - odometerOf (condScenery d hd c r s) n y + a|)) 0|
          ≤ C * ‖greenLp d hd (0 : Site d)‖ * (j : ℝ) ^ ((4 - (d : ℝ)) / 4) * |c * δ| := by
  obtain ⟨C, hC, hbnd⟩ := exists_greenCovariance_iterate_bound hGH hd
  refine ⟨C, hC, fun c r hr s δ a n j hj => ?_⟩
  refine (abs_avgIterate_abs_condScenery_deviation_le hd c hr s δ a n j).trans ?_
  exact mul_le_mul_of_nonneg_right (hbnd j hj) (abs_nonneg _)

end Sandpile
