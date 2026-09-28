import Sandpile.Support.Dgt4ADeviationSplit

/-!
# Pointwise bound on the centred deviation `D_n`

The pointwise first-moment ingredient for the centred deviation `D_n` of `sandpile.tex:5050-5055`:
`|D_n|` is at most the odometer increment plus the positive part of the excess of the averaged
field over the field. Both terms are nonnegative and their difference is `D_n`, so the mean-zero
property of `D_n` turns this into `E|D_n|\leq2E u_n(0)/n`.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- `|D_n|\leq(u_{n+1}(0)-u_n(0))+(P(V_∞-u_n)(0)-V_∞(0))_+` (`sandpile.tex:5049-5050`). -/
theorem abs_centeredDeviation_le_increment_add_excess (hd : 3 ≤ d) (ζ : Site d → ℝ)
    (hconv : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n ζ y) atTop (𝓝 L))
    (n : ℕ) :
    |centeredDeviation d ζ n|
      ≤ (odometerOf ζ (n + 1) 0 - odometerOf ζ n 0)
        + max 0 (avg (fun y => infiniteGreenField ζ y - odometerOf ζ n y) 0
            - infiniteGreenField ζ 0) := by
  have hsplit := Sandpile.centeredDeviation_eq_increment_sub hd ζ hconv n
  set I : ℝ := Sandpile.odometerOf ζ (n + 1) 0 - Sandpile.odometerOf ζ n 0 with hI
  set E : ℝ := max 0
      (Sandpile.avg (fun y => Sandpile.infiniteGreenField ζ y - Sandpile.odometerOf ζ n y) 0
        - Sandpile.infiniteGreenField ζ 0) with hE
  have hE0 : 0 ≤ E := le_max_left _ _
  have hI0 : 0 ≤ I := by
    have h := Sandpile.odometerOf_le_succ ζ n 0
    rw [hI]; linarith
  rw [hsplit]
  have h : |I - E| ≤ I + E := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
  exact h

end Sandpile
