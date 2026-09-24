/-
The centred deviation `D_n` of `sandpile.tex:5050-5051` is Lipschitz for the `\ell^2`
distance between sceneries, with the constant `2\|G(0,\cdot)\|` that Cauchy-Schwarz reads
off `eq:dgt4-green-l2`.  This is the form the Gaussian concentration of
`Sandpile.External.GaussianLipschitzConcentration` consumes: the coordinatewise bound
`abs_centeredDeviation_update_le` controls one coordinate at a time, while the conditioning
of `sandpile.tex:5270-5271` moves every coordinate at once.
-/
import Sandpile.Support.Dgt4AConcField
import Sandpile.Support.Dgt4ADeviationLip

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- **`D_n` moves by at most `2\|G(0,\cdot)\|` times the `\ell^2` distance.** -/
theorem abs_centeredDeviation_sub_le_of_hasSum_sq (hd : 5 ≤ d) (ξ η : Site d → ℝ) (M : ℝ)
    (h : HasSum (fun z => (ξ z - η z) ^ 2) M)
    (hξ : ∀ y : Site d, ∃ L : ℝ,
      Tendsto (fun n => infiniteGreenFieldPartial n ξ y) atTop (𝓝 L))
    (n : ℕ) :
    |centeredDeviation d ξ n - centeredDeviation d η n|
      ≤ 2 * ‖greenLp d hd (0 : Site d)‖ * Real.sqrt M := by
  have h1 := abs_deviation_sub_le_of_hasSum_sq hd ξ η M h hξ n 0
  have h2 := abs_avgIterate_deviation_sub_le_of_hasSum_sq hd ξ η M h hξ n 1
  have hsub : centeredDeviation d ξ n - centeredDeviation d η n
      = ((infiniteGreenField ξ 0 - odometerOf ξ n 0)
          - (infiniteGreenField η 0 - odometerOf η n 0))
        - (avg (fun y => infiniteGreenField ξ y - odometerOf ξ n y) 0
          - avg (fun y => infiniteGreenField η y - odometerOf η n y) 0) := by
    unfold centeredDeviation; ring
  rw [hsub]
  have h2' : |avg (fun y => infiniteGreenField ξ y - odometerOf ξ n y) 0
      - avg (fun y => infiniteGreenField η y - odometerOf η n y) 0|
      ≤ ‖greenLp d hd (0 : Site d)‖ * Real.sqrt M := by
    simpa using h2
  calc |((infiniteGreenField ξ 0 - odometerOf ξ n 0)
          - (infiniteGreenField η 0 - odometerOf η n 0))
        - (avg (fun y => infiniteGreenField ξ y - odometerOf ξ n y) 0
          - avg (fun y => infiniteGreenField η y - odometerOf η n y) 0)|
      ≤ |(infiniteGreenField ξ 0 - odometerOf ξ n 0)
          - (infiniteGreenField η 0 - odometerOf η n 0)|
        + |avg (fun y => infiniteGreenField ξ y - odometerOf ξ n y) 0
          - avg (fun y => infiniteGreenField η y - odometerOf η n y) 0| := by
        have h := abs_sub_le ((infiniteGreenField ξ 0 - odometerOf ξ n 0)
            - (infiniteGreenField η 0 - odometerOf η n 0)) 0
          (avg (fun y => infiniteGreenField ξ y - odometerOf ξ n y) 0
            - avg (fun y => infiniteGreenField η y - odometerOf η n y) 0)
        have h' : |avg (fun y => infiniteGreenField ξ y - odometerOf ξ n y) 0
            - avg (fun y => infiniteGreenField η y - odometerOf η n y) 0|
            = |avg (fun y => infiniteGreenField η y - odometerOf η n y) 0
              - avg (fun y => infiniteGreenField ξ y - odometerOf ξ n y) 0| :=
          abs_sub_comm _ _
        rw [h']
        simpa using h
    _ ≤ 2 * ‖greenLp d hd (0 : Site d)‖ * Real.sqrt M := by
        nlinarith [h1, h2', norm_nonneg (greenLp d hd (0 : Site d)), Real.sqrt_nonneg M]

end Sandpile
