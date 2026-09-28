import Sandpile.Support.Dgt4ADeviationLip

/-!
# Splitting the centred deviation into an odometer increment minus an excess

The centred deviation `D_n = centeredDeviation d ζ n` at the origin splits as the odometer
increment `u_{n+1}(0) - u_n(0)` minus the positive part of the excess of the averaged field
`P(V_∞ - u_n)` over the limiting field `V_∞` at the origin. This is a rearrangement of the
recursion `V_∞ - u_{n+1} = min(V_∞, P(V_∞ - u_n))`, and it is the identity that turns a
mean-increment bound into the first-moment bound `E|D_n| ≤ 2 E u_n(0) / n`.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- `D_n` is the odometer increment minus the positive part of the excess
(`sandpile.tex:5047-5050`). -/
theorem centeredDeviation_eq_increment_sub (hd : 3 ≤ d) (ζ : Site d → ℝ)
    (hconv : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop (𝓝 L))
    (n : ℕ) :
    centeredDeviation d ζ n
      = (odometerOf ζ (n + 1) 0 - odometerOf ζ n 0)
        - max 0 (avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0
            - infiniteGreenField ζ 0) := by
  have hrec := Sandpile.infiniteGreenField_sub_odometer_succ hd ζ hconv n 0
  set V : ℝ := Sandpile.infiniteGreenField ζ 0 with hV
  set A : ℝ :=
    Sandpile.avg (fun y => Sandpile.infiniteGreenField ζ y - Sandpile.odometerOf ζ n y) 0
    with hA
  have hmax : Sandpile.odometerOf ζ (n + 1) 0 = max 0 (V - A) := by
    have h : Sandpile.odometerOf ζ (n + 1) 0 = V - min V A := by linarith [hrec]
    rw [h]
    rcases le_total V A with h' | h'
    · rw [min_eq_left h', max_eq_left (by linarith)]; try ring
    · rw [min_eq_right h', max_eq_right (by linarith)]; try ring
  unfold centeredDeviation
  rw [hmax]
  have h1 : max 0 (V - A) - Sandpile.odometerOf ζ n 0 - max 0 (A - V)
      = (V - Sandpile.odometerOf ζ n 0) - A := by
    rcases le_total V A with h' | h'
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; try ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; try ring
  linarith [h1]

end Sandpile
