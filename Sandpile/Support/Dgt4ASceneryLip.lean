import Sandpile.Support.Dgt4ADeviationScenery
import Sandpile.Support.GreenHigh
import Sandpile.Support.TightWeightedMembrane
import Sandpile.Support.ExitGreen
import Sandpile.Support.OriginKernel
import Sandpile.Support.HeightLower
import Sandpile.Support.Dgt4AIterateMulConst

/-!
# The coordinatewise Lipschitz coefficient of the finite-coordinate deviation

The coordinatewise Lipschitz coefficient of the finite-coordinate form of `D_n`
(`sandpile.tex:5057-5058`). Changing `\zeta(z)` changes `\zeta(0)` by the indicator of `z=0`,
changes `u_n(0)` by at most `G(0,z)` and changes `Pu_n(0)` by at most
`PG(\cdot,z)(0)=G(0,z)-\one_{z=0}`, so the total coefficient is at most `2G(0,z)`.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- The coefficient of `sandpile.tex:5052-5053`, bounded by `2G(0,z)`. -/
theorem abs_sceneryDeviation_update_le (hd : 5 ≤ d) (ζ : Site d → ℝ) (z : Site d) (v : ℝ)
    (n : ℕ) :
    |sceneryDeviation d ζ n - sceneryDeviation d (Function.update ζ z v) n|
      ≤ 2 * green d 0 z * |ζ z - v| := by
  classical
  set ζ' : Site d → ℝ := Function.update ζ z v with hζ'
  have hGH : Sandpile.External.GreenBoundsHigh := Sandpile.External.greenBoundsHigh
  have hc : 0 ≤ |ζ z - v| := abs_nonneg _
  have e0 : |ζ 0 - ζ' 0| ≤ (if (0 : Site d) = z then (1 : ℝ) else 0) * |ζ z - v| := by
    by_cases hz : (0 : Site d) = z
    · subst hz
      simp [hζ', Function.update_self]
    · rw [hζ', Function.update_of_ne hz]
      simp [hz]
  have e1 : |Sandpile.odometerOf ζ n 0 - Sandpile.odometerOf ζ' n 0|
      ≤ Sandpile.green d 0 z * |ζ z - v| := by
    refine (Sandpile.abs_odometerOf_update_le ζ z v n 0).trans ?_
    exact mul_le_mul_of_nonneg_right (Sandpile.greenTime_le_green hGH hd n z) hc
  have hptavg : ∀ y : Site d,
      |Sandpile.odometerOf ζ n y - Sandpile.odometerOf ζ' n y|
        ≤ Sandpile.green d y z * |ζ z - v| := by
    intro y
    refine (Sandpile.abs_odometerOf_update_le ζ z v n y).trans ?_
    exact mul_le_mul_of_nonneg_right
      (Sandpile.Support.greenTime_le_green_shift hGH hd n y z) hc
  have e2 : |Sandpile.avg (fun y => Sandpile.odometerOf ζ n y) 0
        - Sandpile.avg (fun y => Sandpile.odometerOf ζ' n y) 0|
      ≤ (Sandpile.green d 0 z - (if (0 : Site d) = z then (1 : ℝ) else 0)) * |ζ z - v| := by
    refine (Sandpile.abs_avg_sub_le_avg_abs _ _ 0).trans ?_
    have hmono : Sandpile.avg (fun y => |Sandpile.odometerOf ζ n y
          - Sandpile.odometerOf ζ' n y|) 0
        ≤ Sandpile.avg (fun y => Sandpile.green d y z * |ζ z - v|) 0 :=
      Sandpile.avg_mono_le hptavg 0
    refine hmono.trans ?_
    have hmul : Sandpile.avg (fun y => Sandpile.green d y z * |ζ z - v|) 0
        = Sandpile.avg (fun y => Sandpile.green d y z) 0 * |ζ z - v| := by
      have h := Sandpile.avg_iterate_mul_const (d := d) 1 (|ζ z - v|)
        (fun y => Sandpile.green d y z) 0
      simp only [Function.iterate_one] at h
      rw [show (fun y => Sandpile.green d y z * |ζ z - v|)
          = (fun y => |ζ z - v| * Sandpile.green d y z) from funext fun y => mul_comm _ _, h,
        mul_comm]
    rw [hmul, Sandpile.avg_green (by omega : 3 ≤ d)]
  have habs : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := by
    intro a b
    have h := abs_add_le a (-b)
    simpa [sub_eq_add_neg] using h
  have htri : |Sandpile.sceneryDeviation d ζ n - Sandpile.sceneryDeviation d ζ' n|
      ≤ |ζ 0 - ζ' 0| + |Sandpile.odometerOf ζ n 0 - Sandpile.odometerOf ζ' n 0|
        + |Sandpile.avg (fun y => Sandpile.odometerOf ζ n y) 0
            - Sandpile.avg (fun y => Sandpile.odometerOf ζ' n y) 0| := by
    rw [Sandpile.sceneryDeviation, Sandpile.sceneryDeviation]
    have hrw : (ζ 0 - (Sandpile.odometerOf ζ n 0
          - Sandpile.avg (fun y => Sandpile.odometerOf ζ n y) 0))
        - (ζ' 0 - (Sandpile.odometerOf ζ' n 0
          - Sandpile.avg (fun y => Sandpile.odometerOf ζ' n y) 0))
        = ((ζ 0 - ζ' 0) - (Sandpile.odometerOf ζ n 0 - Sandpile.odometerOf ζ' n 0))
          + (Sandpile.avg (fun y => Sandpile.odometerOf ζ n y) 0
            - Sandpile.avg (fun y => Sandpile.odometerOf ζ' n y) 0) := by ring
    rw [hrw]
    exact (abs_add_le _ _).trans (add_le_add (habs _ _) le_rfl)
  refine htri.trans ?_
  by_cases hz : (0 : Site d) = z
  · rw [if_pos hz] at e0 e2
    nlinarith [e0, e1, e2, hc]
  · rw [if_neg hz] at e0 e2
    nlinarith [e0, e1, e2, hc]


end Sandpile
