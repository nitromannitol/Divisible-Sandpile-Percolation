/-
**Terminal domination** (`eq:dgt4-gaussian-terminal-domination`, `sandpile.tex:5241-5245`):
"iterate `u_{r+1}\geq\zeta+Pu_r` over the final `k_n` updates.  Conditionally on
`-V_\infty(0)=b`,

  `-\zeta(0)-Pu_n(0)\leq b-\E u_n(0)+P^{k_n+1}(V_\infty-u_{n-k_n}+\E u_n(0))(0)`."

With `V_\infty-PV_\infty=\zeta` the left side is `-V_\infty(0)+P(V_\infty-u_n)(0)`, and the
iteration is the monotonicity `V_\infty-u_{m+j}\leq P^j(V_\infty-u_m)` of the
dynamic-programming recursion, which is `dpValue_le_avgIterate` at the payoff `V_\infty`.
-/
import Sandpile.Support.Dgt4AStopCompare
import Sandpile.Support.Smoothed

open MeasureTheory Filter Topology

namespace Sandpile

variable {d : ℕ}

/-- `V_\infty-u_{m+j}\leq P^j(V_\infty-u_m)` at any scenery whose Green field converges. -/
theorem infiniteGreenField_sub_odometer_le_avgIterate (hd : 3 ≤ d) (ζ : Site d → ℝ)
    (hconv : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop (𝓝 L))
    (j m : ℕ) (x : Site d) :
    infiniteGreenField ζ x - odometerOf ζ (m + j) x
      ≤ (avg^[j] (fun y => infiniteGreenField ζ y - odometerOf ζ m y)) x :=
  dpValue_le_avgIterate
    (W := infiniteGreenField ζ) (F := fun r y => infiniteGreenField ζ y - odometerOf ζ r y)
    (fun r y => infiniteGreenField_sub_odometer_succ hd ζ hconv r y) j m x

/-- **`eq:dgt4-gaussian-terminal-domination`** (`sandpile.tex:5236-5240`). -/
theorem neg_scenery_sub_avg_odometer_le (hd : 3 ≤ d) (ζ : Site d → ℝ)
    (hconv : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop (𝓝 L))
    (a : ℝ) (k n : ℕ) (hk : k ≤ n) :
    -ζ 0 - avg (odometerOf ζ n) 0
      ≤ -infiniteGreenField ζ 0 - a
        + (avg^[k + 1] (fun y => infiniteGreenField ζ y - odometerOf ζ (n - k) y + a)) 0 := by
  have hd1 : (1 : ℕ) ≤ d := by omega
  have hζ : avg (infiniteGreenField ζ) 0 = infiniteGreenField ζ 0 - ζ 0 :=
    avg_infiniteGreenField hd ζ 0 hconv
  have hsplit : avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0
      = avg (infiniteGreenField ζ) 0 - avg (odometerOf ζ n) 0 :=
    LatticeProb.walkOp_sub _ _ _
  have hpt : ∀ y : Site d, infiniteGreenField ζ y - odometerOf ζ n y
      ≤ (avg^[k] (fun w => infiniteGreenField ζ w - odometerOf ζ (n - k) w)) y := by
    intro y
    have h := infiniteGreenField_sub_odometer_le_avgIterate hd ζ hconv k (n - k) y
    rwa [show n - k + k = n from by omega] at h
  have hmono : avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0
      ≤ avg (avg^[k] (fun w => infiniteGreenField ζ w - odometerOf ζ (n - k) w)) 0 :=
    Sandpile.avg_mono_le hpt 0
  have hiter : avg (avg^[k] (fun w => infiniteGreenField ζ w - odometerOf ζ (n - k) w)) 0
      = (avg^[k + 1] (fun w => infiniteGreenField ζ w - odometerOf ζ (n - k) w)) 0 := by
    rw [Function.iterate_succ_apply']
  have hconst : (avg^[k + 1] (fun y => infiniteGreenField ζ y - odometerOf ζ (n - k) y + a)) 0
      = (avg^[k + 1] (fun w => infiniteGreenField ζ w - odometerOf ζ (n - k) w)) 0 + a := by
    have h := avg_iterate_sub_const hd1 (k + 1)
      (fun w => infiniteGreenField ζ w - odometerOf ζ (n - k) w) (-a) 0
    have hfun : (fun z => (infiniteGreenField ζ z - odometerOf ζ (n - k) z) - (-a))
        = fun z => infiniteGreenField ζ z - odometerOf ζ (n - k) z + a := by
      funext z
      ring
    rw [hfun] at h
    rw [h]
    ring
  rw [hconst]
  rw [hsplit] at hmono
  rw [hiter] at hmono
  linarith [hζ, hmono]

/-- **`eq:dgt4-gaussian-reflected-expression`** (`sandpile.tex:5215-5219`): using
`V_\infty-PV_\infty=\zeta`, conditioning on `-V_\infty(0)=\E u_n(0)+\Sigma^2y/\E u_n(0)`
gives `-\zeta(0)-Pu_n(0)=\Sigma^2y/\E u_n(0)+P(V_\infty-u_n+\E u_n(0))(0)`.  Here the level
is carried as the identity itself: the reflected increment is the level
`-V_\infty(0)-\E u_n(0)` plus the one-step average of the centred value. -/
theorem neg_scenery_sub_avg_odometer_eq (hd : 3 ≤ d) (ζ : Site d → ℝ)
    (hconv : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop (𝓝 L))
    (a : ℝ) (n : ℕ) :
    -ζ 0 - avg (odometerOf ζ n) 0
      = (-infiniteGreenField ζ 0 - a)
        + avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y + a) 0 := by
  have hd1 : (1 : ℕ) ≤ d := by omega
  have hζ : avg (infiniteGreenField ζ) 0 = infiniteGreenField ζ 0 - ζ 0 :=
    avg_infiniteGreenField hd ζ 0 hconv
  have hsplit : avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y + a) 0
      = avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0 + a := by
    have h := avg_iterate_sub_const hd1 1
      (fun y => infiniteGreenField ζ y - odometerOf ζ n y) (-a) 0
    have hfun : (fun z => (infiniteGreenField ζ z - odometerOf ζ n z) - (-a))
        = fun z => infiniteGreenField ζ z - odometerOf ζ n z + a := by
      funext z
      ring
    rw [hfun] at h
    simp only [Function.iterate_one] at h
    rw [h]
    ring
  have hsub : avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0
      = avg (infiniteGreenField ζ) 0 - avg (odometerOf ζ n) 0 :=
    LatticeProb.walkOp_sub _ _ _
  rw [hsplit, hsub, hζ]
  ring

end Sandpile
