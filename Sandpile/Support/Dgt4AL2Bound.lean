import Sandpile.Support.Dgt4ASceneryFirstMoment
import Sandpile.Support.Dgt4AMoment4
import Sandpile.Support.Dgt4AL2Interp
import LatticeProb.Prob.LpSmooth

/-!
# The second moment of the centred deviation `D_n`

The second moment of `D_n`. Its coordinate Lipschitz coefficients `2G(0,z)` are square summable
and bounded, so `D_n` has moments of every order the one-site law has, uniformly in `n`;
interpolating between the first moment `2\E u_n(0)/n` and the fourth moment turns the first into
a bound on `(\E[D_n^2])^{1/2}` (`sandpile.tex:5053-5057`).
-/

open LatticeProb

open MeasureTheory Filter Topology Set

namespace Sandpile

variable {d : ℕ}

/-- The coordinate Lipschitz coefficient `2G(0,z)` of `D_n` in the box reading is nonnegative,
since the Green function is. -/
theorem green_two_nonneg (z : Site d) : (0 : ℝ) ≤ 2 * green d 0 z := by
  have := green_nonneg (0 : Site d) z
  linarith

/-- `D_n` has the `p`-th moment of the one-site law, for every `n`. -/
theorem integrable_abs_rpow_sceneryDeviation (hd : 5 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] {p : ℝ} (hp : 1 ≤ p)
    (hmom : Integrable (fun z : ℝ => |z| ^ p) ν) (n : ℕ) :
    Integrable (fun ζ : Site d → ℝ => |sceneryDeviation d ζ n| ^ p)
      (LatticeProb.iidLaw d ν) := by
  haveI : ∀ _i : Fin (boxFinset (0 : Site d) (n + 1)).card,
      IsProbabilityMeasure ((fun _ => ν) _i) := fun _ => ‹IsProbabilityMeasure ν›
  have hint := integrable_rpow_of_lip_fam
    (fun _ : Fin (boxFinset (0 : Site d) (n + 1)).card => ν) hp (fun _ => hmom)
    (boxDeviation n) (measurable_boxDeviation n)
    (fun i => 2 * green d 0 (siteEnum (boxFinset (0 : Site d) (n + 1)) i))
    (fun i => green_two_nonneg _) (abs_boxDeviation_update_le hd n)
  have hcomp := LatticeProb.integrable_comp_mp
    (LatticeProb.measurePreserving_pick _ ν (siteEnum (boxFinset (0 : Site d) (n + 1)))
      (siteEnum_injective _))
    (fun ξ => |boxDeviation n ξ| ^ p)
    (((measurable_boxDeviation n).abs.pow_const p).aestronglyMeasurable) hint
  simpa [boxDeviation_pick] using hcomp

/-- `\E[D_n^2]\leq2T\E u_n(0)/n+M/T^2` for every `T>0`, with `M` uniform in `n`
(`sandpile.tex:5048-5052`). -/
theorem exists_integral_sceneryDeviation_sq_le (hd : 5 ≤ d) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (hint : Integrable id ν) (hmean : ∫ w, w ∂ν = 0)
    (hpos : Integrable (fun z : ℝ => max z 0) ν)
    (hsq : Integrable (fun z : ℝ => |z| ^ (2 : ℝ)) ν)
    (hmom : Integrable (fun z : ℝ => |z| ^ (4 : ℝ)) ν) :
    ∃ M : ℝ, ∀ (n : ℕ), 1 ≤ n → ∀ T : ℝ, 0 < T →
      (∫ ζ, sceneryDeviation d ζ n ^ 2 ∂(LatticeProb.iidLaw d ν))
        ≤ T * (2 * meanOdometer (centeredMassLaw d ν) n / n) + M / T ^ 2 := by
  have hd1 : 1 ≤ d := by omega
  have hpt4 : ∀ x : ℝ, |x| ^ (4 : ℝ) = x ^ 4 := by
    intro x
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  have hpt2 : ∀ x : ℝ, |x| ^ (2 : ℝ) = x ^ 2 := by
    intro x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  have habs1 : Integrable (fun z : ℝ => |z| ^ (1 : ℝ)) ν := by
    refine hint.abs.congr (Filter.Eventually.of_forall fun z => ?_)
    simp [Real.rpow_one]
  obtain ⟨M, hM⟩ := exists_sceneryDeviation_moment_bound (d := d) hd ν
    (p := (4 : ℝ)) (by norm_num) hmom
  refine ⟨M, fun n hn T hT => ?_⟩
  have hzero := integral_sceneryDeviation_eq_zero (d := d) hd1 ν hint hmean hpos n
  have h1 : Integrable (fun ζ : Site d → ℝ => |sceneryDeviation d ζ n|)
      (LatticeProb.iidLaw d ν) := by
    have h := integrable_abs_rpow_sceneryDeviation hd ν (p := (1 : ℝ)) le_rfl habs1 n
    refine h.congr (Filter.Eventually.of_forall fun ζ => ?_)
    simp [Real.rpow_one]
  have h2 : Integrable (fun ζ : Site d → ℝ => sceneryDeviation d ζ n ^ 2)
      (LatticeProb.iidLaw d ν) := by
    have h := integrable_abs_rpow_sceneryDeviation hd ν (p := (2 : ℝ)) (by norm_num) hsq n
    refine h.congr (Filter.Eventually.of_forall fun ζ => ?_)
    simp only [hpt2]
  have h4 : Integrable (fun ζ : Site d → ℝ => sceneryDeviation d ζ n ^ 4)
      (LatticeProb.iidLaw d ν) := by
    have h := integrable_abs_rpow_sceneryDeviation hd ν (p := (4 : ℝ)) (by norm_num) hmom n
    refine h.congr (Filter.Eventually.of_forall fun ζ => ?_)
    simp only [hpt4]
  have hMn : (∫ ζ, sceneryDeviation d ζ n ^ 4 ∂(LatticeProb.iidLaw d ν)) ≤ M := by
    have h := hM n
    rw [hzero] at h
    refine le_trans (le_of_eq ?_) h
    refine integral_congr_ae (Filter.Eventually.of_forall fun ζ => ?_)
    simp only [sub_zero, hpt4]
  have hinterp := integral_sq_le_first_fourth (LatticeProb.iidLaw d ν)
    (fun ζ => sceneryDeviation d ζ n) T hT h1 h2 h4
  have hfirst := integral_abs_sceneryDeviation_le_two_mean_div (d := d) hd1 ν hint hmean hpos n hn
  have hT2 : (0 : ℝ) < T ^ 2 := by positivity
  have hdiv : (∫ ζ, sceneryDeviation d ζ n ^ 4 ∂(LatticeProb.iidLaw d ν)) / T ^ 2
      ≤ M / T ^ 2 := by
    exact div_le_div_of_nonneg_right hMn hT2.le
  nlinarith [hinterp, hfirst, hdiv, hT]

end Sandpile
