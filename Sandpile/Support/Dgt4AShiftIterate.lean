import Sandpile.Support.Dgt4AShiftLip
import Sandpile.Support.Dgt4AIterateLip
import Sandpile.Support.Dgt4AIterateMulConst
import Sandpile.Support.Dgt4AStep2Lip

/-!
# The Lipschitz constant of the conditioning after averaging

**The Lipschitz constant of the conditioning** (`sandpile.tex:5120-5124`): "propagating this by
`P^{k_n+1}` bounds this Lipschitz constant by
`P^{k_n+1}\Cov(V_\infty(\cdot),V_\infty(0))(0)/\Sigma^2`."

`Support/Dgt4AShiftLip.lean` bounds the change of `V_\infty(x)-u_n(x)` under a change
`\Sigma\delta` of the conditioned value by
`|c\delta|\,\Cov(V_\infty(x),V_\infty(0))/(c\|G(0,\cdot)\|)`, site by site, the parameter `\delta`
being the level in units of `\Sigma`. The `j`-step average is a positive averaging operator, so
the same bound holds after `P^j` with the covariance replaced by its `j`-step average, and
`Support/Dgt4AStep2Lip.lean` already bounds that by `Ck_n^{(4-d)/4}`.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- The `j`-step average of the deviation is Lipschitz in the conditioned level, with
constant the `j`-step average of the Green covariance. -/
theorem abs_avgIterate_condScenery_deviation_le (hd : 5 ≤ d) (c : ℝ) {r : Site d → ℝ}
    (hr : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun m : ℕ => ∑ z ∈ boxFinset (0 : Site d) m, green d y z * r z) atTop (𝓝 L))
    (s δ : ℝ) (n j : ℕ) :
    |(avg^[j] (fun y => infiniteGreenField (condScenery d hd c r (s + δ)) y
          - odometerOf (condScenery d hd c r (s + δ)) n y)) 0
        - (avg^[j] (fun y => infiniteGreenField (condScenery d hd c r s) y
          - odometerOf (condScenery d hd c r s) n y)) 0|
      ≤ ‖greenLp d hd (0 : Site d)‖⁻¹
          * (avg^[j] (fun y => ∑' z : Site d, green d y z * green d 0 z)) 0 * |c * δ| := by
  have h := Sandpile.abs_avgIterate_sub_le
    (fun y => infiniteGreenField (condScenery d hd c r (s + δ)) y
      - odometerOf (condScenery d hd c r (s + δ)) n y)
    (fun y => infiniteGreenField (condScenery d hd c r s) y
      - odometerOf (condScenery d hd c r s) n y) j 0
  refine h.trans ?_
  have hstep := Sandpile.avg_iterate_abs_le
    (fun y => infiniteGreenField (condScenery d hd c r (s + δ)) y
      - odometerOf (condScenery d hd c r (s + δ)) n y)
    (fun y => infiniteGreenField (condScenery d hd c r s) y
      - odometerOf (condScenery d hd c r s) n y)
    (fun y => ‖greenLp d hd (0 : Site d)‖⁻¹ * ∑' z : Site d, green d y z * green d 0 z)
    |c * δ| j
    (fun y => by
      rw [mul_comm]
      exact abs_condScenery_sub_odometer_le hd c y n hr s δ)
  refine hstep.trans_eq ?_
  rw [avg_iterate_mul_const j ‖greenLp d hd (0 : Site d)‖⁻¹
    (fun y => ∑' z : Site d, green d y z * green d 0 z) 0]

/-- **The Lipschitz constant of Step 2 at the conditioned level** (`sandpile.tex:5117-5119`):
the change of `P^j(V_\infty-u_n)(0)` under a change `\delta` of the conditioned level is at
most `C|c\delta|\,j^{(4-d)/4}\|G(0,\cdot)\|` for a constant `C` that does not depend on the
level, the residual or the number of updates. -/
theorem exists_avgIterate_condScenery_deviation_le (hGH : Sandpile.External.GreenBoundsHigh)
    (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (c : ℝ) (r : Site d → ℝ),
      (∀ y : Site d, ∃ L : ℝ,
        Tendsto (fun m : ℕ => ∑ z ∈ boxFinset (0 : Site d) m, green d y z * r z) atTop (𝓝 L)) →
      ∀ (s δ : ℝ) (n j : ℕ), 1 ≤ j →
        |(avg^[j] (fun y => infiniteGreenField (condScenery d hd c r (s + δ)) y
              - odometerOf (condScenery d hd c r (s + δ)) n y)) 0
            - (avg^[j] (fun y => infiniteGreenField (condScenery d hd c r s) y
              - odometerOf (condScenery d hd c r s) n y)) 0|
          ≤ C * ‖greenLp d hd (0 : Site d)‖ * (j : ℝ) ^ ((4 - (d : ℝ)) / 4) * |c * δ| := by
  obtain ⟨C, hC, hbnd⟩ := exists_avgIterate_greenCovariance_le hGH hd
  refine ⟨C, hC, fun c r hr s δ n j hj => ?_⟩
  refine (abs_avgIterate_condScenery_deviation_le hd c hr s δ n j).trans ?_
  have hgpos : (0 : ℝ) < ‖greenLp d hd (0 : Site d)‖ := norm_greenLp_pos hd
  have hgs : ‖greenLp d hd (0 : Site d)‖ ^ 2 = greenSqSum d := norm_greenLp_sq hd
  have hb := hbnd j hj
  have hcov : (avg^[j] (fun y => ∑' z : Site d, green d y z * green d 0 z)) 0
      ≤ C * (j : ℝ) ^ ((4 - (d : ℝ)) / 4) * greenSqSum d := by
    have hgsp : (0 : ℝ) < greenSqSum d :=
      lt_of_lt_of_le zero_lt_one (one_le_greenSqSum hd)
    rw [div_le_iff₀ hgsp] at hb
    exact le_trans (le_abs_self _) hb
  have hcd : (0 : ℝ) ≤ |c * δ| := abs_nonneg _
  have hinv : (0 : ℝ) < ‖greenLp d hd (0 : Site d)‖⁻¹ := inv_pos.mpr hgpos
  have hpow : (0 : ℝ) ≤ (j : ℝ) ^ ((4 - (d : ℝ)) / 4) := Real.rpow_nonneg (Nat.cast_nonneg j) _
  have hmain : ‖greenLp d hd (0 : Site d)‖⁻¹
        * (avg^[j] (fun y => ∑' z : Site d, green d y z * green d 0 z)) 0
      ≤ C * ‖greenLp d hd (0 : Site d)‖ * (j : ℝ) ^ ((4 - (d : ℝ)) / 4) := by
    have h1 : ‖greenLp d hd (0 : Site d)‖⁻¹
          * (avg^[j] (fun y => ∑' z : Site d, green d y z * green d 0 z)) 0
        ≤ ‖greenLp d hd (0 : Site d)‖⁻¹ * (C * (j : ℝ) ^ ((4 - (d : ℝ)) / 4) * greenSqSum d) :=
      mul_le_mul_of_nonneg_left hcov hinv.le
    refine h1.trans_eq ?_
    rw [← hgs]
    field_simp
  exact mul_le_mul_of_nonneg_right hmain hcd

end Sandpile
