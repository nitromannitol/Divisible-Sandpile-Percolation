import Sandpile.Support.Dgt4ASceneryMeanZero
import Sandpile.Support.Dgt4ABoxDeviation
import Sandpile.Support.Dgt4AMeanIncrement
import Sandpile.Support.Dgt4AMeanIncrementInt
import Sandpile.Support.D4Reflection

/-!
# First-moment bound in finite-coordinate form

The first-moment bound of Step 1 of case (a) of `prop:dgt4-contact-asymptotics`,
`\E|D_n|\leq2\E u_n(0)/n` (`sandpile.tex:5053-5055`), in the finite-coordinate form.
The odometer recursion `u_{n+1}=\zeta+Pu_n+r_n` with the reflection term `r_n\geq0` splits
`D_n=\zeta(0)-(u_n(0)-Pu_n(0))` into the increment minus the reflection, both nonnegative,
so `|D_n|\leq I_n+r_n`; the mean of `D_n` vanishes, so the two have the same mean, and
`eq:dgt4-mean-increment-bound` bounds the increment.
-/

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- `D_n=(u_{n+1}(0)-u_n(0))-r_n(0)` (`sandpile.tex:5045-5047`). -/
theorem sceneryDeviation_eq_increment_sub (ζ : Site d → ℝ) (n : ℕ) :
    sceneryDeviation d ζ n
      = (odometerOf ζ (n + 1) 0 - odometerOf ζ n 0) - reflectionTerm ζ n 0 := by
  rw [sceneryDeviation, odometerOf_succ_eq_add_reflection ζ n 0]
  ring

/-- `|D_n|\leq I_n+r_n`, both summands nonnegative. -/
theorem abs_sceneryDeviation_le_increment_add_reflection (ζ : Site d → ℝ) (n : ℕ) :
    |sceneryDeviation d ζ n|
      ≤ (odometerOf ζ (n + 1) 0 - odometerOf ζ n 0) + reflectionTerm ζ n 0 := by
  rw [sceneryDeviation_eq_increment_sub]
  have h1 : 0 ≤ odometerOf ζ (n + 1) 0 - odometerOf ζ n 0 := by
    have := odometerOf_le_succ ζ n 0
    linarith
  have h2 : 0 ≤ reflectionTerm ζ n 0 := reflectionTerm_nonneg ζ n 0
  rw [abs_le]
  constructor <;> linarith

/-- `\E|D_n|\leq2\E u_n(0)/n` (`sandpile.tex:5048-5050`). -/
theorem integral_abs_sceneryDeviation_le_two_mean_div (hd : 1 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0)
    (hpos : Integrable (fun z : ℝ => max z 0) ν) (n : ℕ) (hn : 1 ≤ n) :
    (∫ ζ, |sceneryDeviation d ζ n| ∂(LatticeProb.iidLaw d ν))
      ≤ 2 * meanOdometer (centeredMassLaw d ν) n / n := by
  have hIincr : Integrable (fun ζ : Site d → ℝ =>
      Sandpile.odometerOf ζ (n + 1) 0 - Sandpile.odometerOf ζ n 0) (LatticeProb.iidLaw d ν) :=
    (Sandpile.integrable_odometerOf d ν hpos (n + 1) 0).sub
      (Sandpile.integrable_odometerOf d ν hpos n 0)
  have hIrefl : Integrable (fun ζ : Site d → ℝ => Sandpile.reflectionTerm ζ n 0)
      (LatticeProb.iidLaw d ν) := Sandpile.integrable_reflectionTerm ν hint hpos n 0
  have hfun : (fun ζ : Site d → ℝ => Sandpile.sceneryDeviation d ζ n)
      = fun ζ => (Sandpile.odometerOf ζ (n + 1) 0 - Sandpile.odometerOf ζ n 0)
          - Sandpile.reflectionTerm ζ n 0 :=
    funext fun ζ => Sandpile.sceneryDeviation_eq_increment_sub ζ n
  have hIdev : Integrable (fun ζ : Site d → ℝ => Sandpile.sceneryDeviation d ζ n)
      (LatticeProb.iidLaw d ν) := by
    rw [hfun]; exact hIincr.sub hIrefl
  have hIabs : Integrable (fun ζ : Site d → ℝ => |Sandpile.sceneryDeviation d ζ n|)
      (LatticeProb.iidLaw d ν) := hIdev.abs
  have hsum : Integrable (fun ζ : Site d → ℝ =>
      (Sandpile.odometerOf ζ (n + 1) 0 - Sandpile.odometerOf ζ n 0)
        + Sandpile.reflectionTerm ζ n 0) (LatticeProb.iidLaw d ν) := hIincr.add hIrefl
  have hmono := integral_mono hIabs hsum
    (fun ζ => Sandpile.abs_sceneryDeviation_le_increment_add_reflection ζ n)
  have hzero := Sandpile.integral_sceneryDeviation_eq_zero (d := d) hd ν hint hmean hpos n
  have hsplit : (∫ ζ : Site d → ℝ, Sandpile.sceneryDeviation d ζ n ∂(LatticeProb.iidLaw d ν))
      = (∫ ζ : Site d → ℝ, (Sandpile.odometerOf ζ (n + 1) 0
          - Sandpile.odometerOf ζ n 0) ∂(LatticeProb.iidLaw d ν))
        - ∫ ζ : Site d → ℝ, Sandpile.reflectionTerm ζ n 0 ∂(LatticeProb.iidLaw d ν) := by
    rw [hfun, integral_sub hIincr hIrefl]
  rw [integral_add hIincr hIrefl] at hmono
  rw [hsplit] at hzero
  have heq : (∫ ζ : Site d → ℝ, Sandpile.reflectionTerm ζ n 0 ∂(LatticeProb.iidLaw d ν))
      = ∫ ζ : Site d → ℝ, (Sandpile.odometerOf ζ (n + 1) 0
          - Sandpile.odometerOf ζ n 0) ∂(LatticeProb.iidLaw d ν) := by linarith
  rw [heq, Sandpile.integral_odometerOf_increment (d := d) hd ν hpos n] at hmono
  have hbound := Sandpile.meanOdometer_increment_le_div (d := d) hd ν hint hmean hpos n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [le_div_iff₀ hnR] at hbound ⊢
  nlinarith [hmono, hbound, hnR]


end Sandpile
