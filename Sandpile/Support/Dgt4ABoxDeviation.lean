import Sandpile.Support.Dgt4ASceneryBox
import Sandpile.Support.Dgt4ASceneryLip
import Sandpile.Support.BlockIncrement

/-!
# `D_n` as a function of finitely many box coordinates

`D_n` as a function of the finitely many coordinates of the box `Q(0,n+1)`, with its
measurability and its coordinate Lipschitz bound `2G(0,z)` in that reading. This is the form the
product concentration bounds of `Support/Concentration.lean` consume.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- `D_n` read as a function of the coordinates of `Q(0,n+1)`. -/
noncomputable def boxDeviation (n : ℕ)
    (ξ : Fin (boxFinset (0 : Site d) (n + 1)).card → ℝ) : ℝ :=
  sceneryDeviation d (siteExtend (boxFinset (0 : Site d) (n + 1)) ξ) n

/-- `sceneryDeviation d · n` is measurable in the full scenery, being built from the
coordinate projection at the origin, `odometerOf`, and the average of `odometerOf`, each of
which is measurable. -/
theorem measurable_sceneryDeviation (n : ℕ) :
    Measurable fun ζ : Site d → ℝ => sceneryDeviation d ζ n := by
  have havg : Measurable fun ζ : Site d → ℝ =>
      Sandpile.avg (fun y => Sandpile.odometerOf ζ n y) (0 : Site d) := by
    have h := Sandpile.measurable_avg_iterate_odometerOf (d := d) 1 n 0
    simpa using h
  exact (measurable_pi_apply (0 : Site d)).sub
    ((Sandpile.measurable_odometerOf n (0 : Site d)).sub havg)

/-- The box-coordinate reading `boxDeviation` is measurable, as the composite of
`measurable_sceneryDeviation` with the measurable extension map `siteExtend`. -/
theorem measurable_boxDeviation (n : ℕ) : Measurable (boxDeviation (d := d) n) :=
  (measurable_sceneryDeviation n).comp (measurable_siteExtend _)

/-- Evaluating `boxDeviation` at the coordinates a full scenery `ζ` has on the box, picked out
via `siteEnum`, recovers `sceneryDeviation d ζ n` directly. -/
theorem boxDeviation_pick (n : ℕ) (ζ : Site d → ℝ) :
    boxDeviation n (fun i => ζ (siteEnum (boxFinset (0 : Site d) (n + 1)) i))
      = sceneryDeviation d ζ n :=
  sceneryDeviation_congr_box n _ ζ fun _ hz => siteExtend_siteEnum _ ζ hz

/-- The coordinate Lipschitz bound in the box reading. -/
theorem abs_boxDeviation_update_le (hd : 5 ≤ d) (n : ℕ)
    (ξ : Fin (boxFinset (0 : Site d) (n + 1)).card → ℝ)
    (i : Fin (boxFinset (0 : Site d) (n + 1)).card) (v : ℝ) :
    |boxDeviation n ξ - boxDeviation n (Function.update ξ i v)|
      ≤ 2 * green d 0 (siteEnum (boxFinset (0 : Site d) (n + 1)) i) * |ξ i - v| := by
  have hval : siteExtend (boxFinset (0 : Site d) (n + 1)) ξ
      (siteEnum (boxFinset (0 : Site d) (n + 1)) i) = ξ i := by
    simp [siteExtend, siteEnum]
  have h := abs_sceneryDeviation_update_le hd
    (siteExtend (boxFinset (0 : Site d) (n + 1)) ξ)
    (siteEnum (boxFinset (0 : Site d) (n + 1)) i) v n
  simpa only [boxDeviation, siteExtend_update, hval] using h

end Sandpile
