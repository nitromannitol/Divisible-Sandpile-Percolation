/-
**The comparison of Step 2 at the conditioned level** (`sandpile.tex:5125-5131`):
"Comparing the conditional expectation at `b=\E u_n(0)+\Sigma^2y/\E u_n(0)` with its
unconditional average, and bounding their difference by the Lipschitz constant times
`\E|b+V_\infty(0)|`".

The three inputs are now all in place: the Lipschitz bound in the level
(`exists_avgIterate_abs_condScenery_deviation_le`), the integrability of the conditional
expectation at every level and in the level (`Support/Dgt4ACondTerminal.lean` and
`Support/Dgt4ACondIntegrable.lean`), and the identification of the unconditional average
with the average over the level (`integral_iidLaw_gauss_shift`).  The conclusion is the
display of `sandpile.tex:5124-5131` with the mean distance to the level written out as
`|s|+\E|N(0,1)|`.
-/
import Sandpile.Support.Dgt4ACondTerminal
import Sandpile.Support.Dgt4ACondCompare

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace Sandpile

variable {d : ℕ}

/-- The absolute value is integrable against a centred Gaussian. -/
theorem integrable_abs_gaussianReal (v : ℝ≥0) :
    Integrable (fun z : ℝ => |z|) (gaussianReal 0 v) := by
  have hmem : MemLp (id : ℝ → ℝ) 1 (gaussianReal 0 v) := by
    simpa using memLp_id_gaussianReal (μ := 0) (v := v) 1
  exact (hmem.integrable le_rfl).abs

/-- The distance to a level, scaled by a constant, is integrable against a centred
Gaussian. -/
theorem integrable_const_mul_abs_sub_gaussianReal (v : ℝ≥0) (s L : ℝ) :
    Integrable (fun s' : ℝ => L * |s - s'|) (gaussianReal 0 v) := by
  have habs : Integrable (fun s' : ℝ => |s'|) (gaussianReal 0 v) := integrable_abs_gaussianReal v
  have hmaj : Integrable (fun s' : ℝ => |L| * (|s| + |s'|)) (gaussianReal 0 v) :=
    ((integrable_const |s|).add habs).const_mul |L|
  refine Integrable.mono' hmaj
    ((measurable_const.sub measurable_id).abs.const_mul L).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun s' => ?_
  have h1 : |s - s'| ≤ |s| + |s'| := by
    calc |s - s'| ≤ |s| + |(-s')| := by rw [sub_eq_add_neg]; exact abs_add_le _ _
      _ = |s| + |s'| := by rw [abs_neg]
  rw [Real.norm_eq_abs, abs_mul, abs_abs]
  have h2 : (0 : ℝ) ≤ |L| := abs_nonneg L
  nlinarith [abs_nonneg (s - s'), abs_nonneg s, abs_nonneg s']

/-- **The comparison of Step 2** (`sandpile.tex:5120-5126`): the conditional expectation of
`P^k|V_\infty-u_t+a|(0)` at the level `s` differs from its unconditional mean by at most the
Lipschitz constant in the level times the mean distance to that level. -/
theorem exists_abs_integral_condTerminal_sub_le
    (hGH : Sandpile.External.GreenBoundsHigh) (hd : 5 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : ℝ≥0), Integrable (fun z : ℝ => z ^ 2) (gaussianReal 0 v) →
      ∀ (a s : ℝ) (t k : ℕ), 1 ≤ k →
        |(∫ r, condTerminal d hd (Real.sqrt (v : ℝ)) s a t k r
              ∂((LatticeProb.gaussLaw (Site d)).map (residField d hd)))
            - ∫ ζ, (avg^[k] (fun x => |infiniteGreenField ζ x - odometerOf ζ t x + a|)) 0
              ∂(LatticeProb.iidLaw d (gaussianReal 0 v))|
          ≤ C * ‖greenLp d hd (0 : Site d)‖ * (k : ℝ) ^ ((4 - (d : ℝ)) / 4)
              * |Real.sqrt (v : ℝ)| * (|s| + ∫ z, |z| ∂(gaussianReal 0 1)) := by
  obtain ⟨C, hC, hlip⟩ := exists_avgIterate_abs_condScenery_deviation_le hGH hd
  refine ⟨C, hC, fun v hsq a s t k hk => ?_⟩
  set ρ : Measure (Site d → ℝ) := (LatticeProb.gaussLaw (Site d)).map (residField d hd) with hρ
  haveI : IsProbabilityMeasure ρ :=
    Measure.isProbabilityMeasure_map (measurable_residField hd).aemeasurable
  set cc : ℝ := Real.sqrt (v : ℝ) with hcc
  set L : ℝ := C * ‖greenLp d hd (0 : Site d)‖ * (k : ℝ) ^ ((4 - (d : ℝ)) / 4) * |cc| with hL
  have hL0 : 0 ≤ L := by
    have h1 : (0 : ℝ) ≤ ‖greenLp d hd (0 : Site d)‖ := norm_nonneg _
    have h2 : (0 : ℝ) ≤ (k : ℝ) ^ ((4 - (d : ℝ)) / 4) := Real.rpow_nonneg (Nat.cast_nonneg k) _
    have h3 : (0 : ℝ) ≤ |cc| := abs_nonneg _
    rw [hL]
    positivity
  have hGint : Integrable (fun ζ : Site d → ℝ =>
      (avg^[k] (fun x => |infiniteGreenField ζ x - odometerOf ζ t x + a|)) 0)
      (LatticeProb.iidLaw d (gaussianReal 0 v)) :=
    (memLp_two_avgIterate (gaussianReal 0 v)
      (fun ζ y => |infiniteGreenField ζ y - odometerOf ζ t y + a|)
      (fun y => (memLp_two_centeredValue_site hd v hsq t a y).abs) k).integrable (by norm_num)
  have hres : ∀ᵐ r ∂ρ, ∀ y : Site d, ∃ M : ℝ,
      Tendsto (fun m : ℕ => ∑ z ∈ boxFinset (0 : Site d) m, green d y z * r z) atTop (𝓝 M) := by
    rw [ae_all_iff]
    exact fun y => ae_exists_tendsto_greenPartialSum_resid hd y
  have hunc : (∫ ζ, (avg^[k] (fun x => |infiniteGreenField ζ x - odometerOf ζ t x + a|)) 0
        ∂(LatticeProb.iidLaw d (gaussianReal 0 v)))
      = ∫ s', (∫ r, condTerminal d hd cc s' a t k r ∂ρ) ∂(gaussianReal 0 1) :=
    integral_iidLaw_gauss_shift hd v _ hGint
  have hlip' : ∀ s' : ℝ, |(∫ r, condTerminal d hd cc s a t k r ∂ρ)
      - ∫ r, condTerminal d hd cc s' a t k r ∂ρ| ≤ L * |s - s'| := by
    intro s'
    refine abs_integral_sub_integral_le_of_ae _ _ _
      (integrable_condTerminal hGH hd v hsq a t k hk s)
      (integrable_condTerminal hGH hd v hsq a t k hk s') ?_
    filter_upwards [hres] with r hr
    have h := hlip cc r hr s' (s - s') a t k hk
    rw [show s' + (s - s') = s by ring] at h
    have habs : |cc * (s - s')| = |cc| * |s - s'| := abs_mul _ _
    calc |condTerminal d hd cc s a t k r - condTerminal d hd cc s' a t k r|
        ≤ C * ‖greenLp d hd (0 : Site d)‖ * (k : ℝ) ^ ((4 - (d : ℝ)) / 4) * |cc * (s - s')| := h
      _ = L * |s - s'| := by rw [hL, habs]; ring
  have hcomp := abs_integral_sub_avgIntegral_le (μ := ρ) (ν := gaussianReal 0 1)
    (fun s' r => condTerminal d hd cc s' a t k r) L s hlip'
    (integrable_integral_iidLaw_gauss_shift hd v _ hGint)
    (integrable_const_mul_abs_sub_gaussianReal 1 s L)
  rw [← hunc] at hcomp
  refine hcomp.trans ?_
  have hint : (∫ s', L * |s - s'| ∂(gaussianReal 0 1)) = L * ∫ s', |s - s'| ∂(gaussianReal 0 1) :=
    integral_const_mul _ _
  rw [hint, hL]
  have hdist := integral_abs_sub_le (ν := gaussianReal 0 1) s (integrable_abs_gaussianReal 1)
  have hLmul : C * ‖greenLp d hd (0 : Site d)‖ * (k : ℝ) ^ ((4 - (d : ℝ)) / 4) * |cc|
      * (∫ s', |s - s'| ∂(gaussianReal 0 1))
      ≤ C * ‖greenLp d hd (0 : Site d)‖ * (k : ℝ) ^ ((4 - (d : ℝ)) / 4) * |cc|
        * (|s| + ∫ z, |z| ∂(gaussianReal 0 1)) :=
    mul_le_mul_of_nonneg_left hdist (by rw [← hL]; exact hL0)
  exact hLmul

end Sandpile
