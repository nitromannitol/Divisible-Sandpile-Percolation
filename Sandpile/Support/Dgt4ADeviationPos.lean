import Sandpile.Support.Dgt4ADeviationSplit

/-!
# Positive-part bound for the centred deviation `D_n`

The first-moment bound for the centred deviation `D_n` of `sandpile.tex:5050-5055`: the positive
part of `D_n` is at most the odometer increment at the origin. The recursion
`V_∞-u_{n+1}=\min\{V_∞,P(V_∞-u_n)\}` gives `D_n\leq u_{n+1}(0)-u_n(0)`, and the odometer is
nondecreasing in time.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- `(D_n)_+\leq u_{n+1}(0)-u_n(0)` (`sandpile.tex:5049-5050`). -/
theorem centeredDeviation_posPart_le_increment (hd : 3 ≤ d) (ζ : Site d → ℝ)
    (hconv : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop (𝓝 L))
    (n : ℕ) :
    max 0 (centeredDeviation d ζ n)
      ≤ odometerOf ζ (n + 1) 0 - odometerOf ζ n 0 := by
  have hsplit := Sandpile.centeredDeviation_eq_increment_sub hd ζ hconv n
  have hnn : 0 ≤ Sandpile.odometerOf ζ (n + 1) 0 - Sandpile.odometerOf ζ n 0 := by
    have h := Sandpile.odometerOf_le_succ ζ n 0
    linarith
  rw [hsplit]
  have h2 : max 0 ((Sandpile.odometerOf ζ (n + 1) 0 - Sandpile.odometerOf ζ n 0)
      - max 0 (Sandpile.avg
          (fun y => Sandpile.infiniteGreenField ζ y - Sandpile.odometerOf ζ n y) 0
          - Sandpile.infiniteGreenField ζ 0))
      ≤ Sandpile.odometerOf ζ (n + 1) 0 - Sandpile.odometerOf ζ n 0 := by
    rcases le_total 0 ((Sandpile.odometerOf ζ (n + 1) 0 - Sandpile.odometerOf ζ n 0)
        - max 0 (Sandpile.avg
            (fun y => Sandpile.infiniteGreenField ζ y - Sandpile.odometerOf ζ n y) 0
            - Sandpile.infiniteGreenField ζ 0)) with h | h
    · rw [max_eq_right h]
      have h3 : 0 ≤ max 0 (Sandpile.avg
          (fun y => Sandpile.infiniteGreenField ζ y - Sandpile.odometerOf ζ n y) 0
          - Sandpile.infiniteGreenField ζ 0) := le_max_left _ _
      linarith
    · rw [max_eq_left h]; exact hnn
  exact h2

end Sandpile
