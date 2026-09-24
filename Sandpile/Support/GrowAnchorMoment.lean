/-
A one-point absolute moment bound for the Gaussian heat potential, uniform over
the whole strip `[0,T] × ℝ^d`: neither the time (as long as it stays in `[0,T]`)
nor the space point moves the bound.

`Sandpile.Support.gaussianPotential_zero_time` (`MeanAZeroTime.lean`) already
records that the potential vanishes at `t = 0` at every point.  The one-point
moment of `Z(t,x)` is therefore the moment of the increment `Z(t,x) - Z(0,x)`,
which `MeanAGauss.integral_abs_rpow_gaussianPotential_sub` computes exactly, and
`MeanAIncrement.integral_greenTimeBM_sq_le` bounds the variance of that
increment uniformly in `x` and in `t ≤ T`.
-/
import Sandpile.Support.MeanAGauss
import Sandpile.Support.MeanAZeroTime

open MeasureTheory ProbabilityTheory

namespace Sandpile.Support

open Sandpile.Continuum

variable {d : ℕ}

/-- **A one-point moment bound for the potential, uniform on the whole strip.**
Neither the time (while it stays in `[0,T]`) nor the space point moves the
bound: the variance of the potential does not depend on `x`, and it is
nondecreasing in `t`. -/
theorem exists_anchor_moment (hd : 1 ≤ d) (hd3 : d ≤ 3) {ν2 : ℝ} (hν2 : 0 ≤ ν2)
    {T : ℝ} (hT : 0 ≤ T) {ΩW : Type*} [MeasurableSpace ΩW] (PW : Measure ΩW)
    [IsProbabilityMeasure PW] (W : (Space d → ℝ) → ΩW → ℝ) (hW : IsWhiteNoise d W PW)
    {p : ℝ} (hp : 0 < p) :
    ∃ Manc : ℝ, 0 ≤ Manc ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : Space d,
      Integrable (fun ω => |gaussianPotential d ν2 W t x ω| ^ p) PW ∧
        ∫ ω, |gaussianPotential d ν2 W t x ω| ^ p ∂PW ≤ Manc := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  set C : ℝ := (2 * Real.pi / (d : ℝ)) ^ (-(d : ℝ) / 2) * 2 ^ (-(d : ℝ) / 2) with hCdef
  have hC0 : (0 : ℝ) ≤ C := by positivity
  set V : ℝ := C * (greenTimeFactor d T * greenTimeFactor d T) with hVdef
  have hV0 : (0 : ℝ) ≤ V := by
    have := greenTimeFactor_nonneg (d := d) hd3 hT
    positivity
  set Manc : ℝ := (ν2 * V) ^ (p / 2) * gaussAbsMoment p with hMdef
  have hManc0 : 0 ≤ Manc := by
    rw [hMdef]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (gaussAbsMoment_nonneg p)
  refine ⟨Manc, hManc0, fun t ht x => ?_⟩
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have htT : t ≤ T := ht.2
  have hae : (fun ω => |gaussianPotential d ν2 W t x ω - gaussianPotential d ν2 W 0 x ω| ^ p)
      =ᵐ[PW] fun ω => |gaussianPotential d ν2 W t x ω| ^ p := by
    filter_upwards [gaussianPotential_zero_time PW W hW ν2 x] with ω hω
    rw [hω]; simp
  have hint0 := integrable_abs_rpow_gaussianPotential_sub PW W hW hd hd3 hν2 ht0 le_rfl x x hp
  have hint : Integrable (fun ω => |gaussianPotential d ν2 W t x ω| ^ p) PW :=
    hint0.congr hae
  refine ⟨hint, ?_⟩
  have heq := integral_abs_rpow_gaussianPotential_sub PW W hW hd hd3 hν2 ht0 le_rfl x x hp.le
  rw [integral_congr_ae hae] at heq
  rw [heq]
  have hg0 : ∀ w : Space d, greenTimeBM d t x w - greenTimeBM d 0 x w
      = greenTimeBM d t x w := by
    intro w
    have : greenTimeBM d 0 x w = 0 := congrFun (greenTimeBM_zero_time d x) w
    rw [this, sub_zero]
  have hsq : (∫ w : Space d, (greenTimeBM d t x w - greenTimeBM d 0 x w) ^ 2)
      = ∫ w : Space d, greenTimeBM d t x w * greenTimeBM d t x w := by
    simp_rw [hg0, pow_two]
  rw [hsq]
  have hle := integral_greenTimeBM_sq_le (d := d) hd hd3 ht0 htT x
  have hle2 : (ν2 * ∫ w : Space d, greenTimeBM d t x w * greenTimeBM d t x w) ≤ ν2 * V := by
    rw [hVdef, hCdef]
    exact mul_le_mul_of_nonneg_left hle hν2
  have hnn : (0 : ℝ) ≤ ν2 * ∫ w : Space d, greenTimeBM d t x w * greenTimeBM d t x w := by
    refine mul_nonneg hν2 (integral_nonneg fun w => ?_); exact mul_self_nonneg _
  have hp2 : (0 : ℝ) ≤ p / 2 := by linarith
  have h1 : (ν2 * ∫ w : Space d, greenTimeBM d t x w * greenTimeBM d t x w) ^ (p / 2)
      ≤ (ν2 * V) ^ (p / 2) := Real.rpow_le_rpow hnn hle2 hp2
  rw [hMdef]
  exact mul_le_mul_of_nonneg_right h1 (gaussAbsMoment_nonneg p)

end Sandpile.Support
